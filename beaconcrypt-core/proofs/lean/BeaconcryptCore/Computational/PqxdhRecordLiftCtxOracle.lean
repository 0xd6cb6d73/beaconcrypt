-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices
import BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle

/-! The selected-key CTX interpreter retains actual opaque source requests and derives their opening admission facts. Private tables, writer frames and the shared ROM remain on the service side. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle
open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable PqxdhRecordLiftMaterialTable
open PqxdhRecordLiftChainCompiler PqxdhRecordLiftOpaqueDrivers
variable {Slot Context Plaintext SealContext Output : Type}

/-- The requested source sequence is retained through every future derivation and actual opening. -/
def Aimed (target : Std.U64) : Effect Slot Context → Prop
  | .rejected _ _ => True
  | .kdfRequested pending => pending.target = target
  | .openRequested pending => RawCtxInterpretedOpening.sequence pending = ok target

set_option maxHeartbeats 1200000 in
/-- Actual resume checks the final sequence before it creates an opening capability. -/
theorem resume_aimed (pending : RawCtxChainReceive.Kdf (Label Slot) (Label Slot) (Label Slot) Context)
    (reply : Label Slot × Label Slot) :
    Aimed pending.target (RawCtxChainReceive.normalResume pending reply) := by
  have run := RawCtxChainReceive.normalResume_exact pending reply
  generalize RawCtxChainReceive.normalResume pending reply = effect at run ⊢
  unfold RawCtxChainReceive.resume at run
  repeat' first | (obtain ⟨_, _, run⟩ := PqxdhFirstRecordReplay.rust_bind_ok run) | split at run
  all_goals simp only [RawCtxChainReceive.rejected, RustM.ok.injEq] at run
  all_goals subst effect
  all_goals simp_all only [Aimed, RawCtxInterpretedOpening.sequence]

/-- Admission retains the requested sequence on cached and future source paths. -/
theorem begin_aimed (entry : LabeledKernel Slot) (target : Std.U64) (context : Context) :
    Aimed target (RawCtxChainReceive.normalBegin entry target context) := by
  have run := RawCtxChainReceive.normalBegin_exact entry target context
  generalize RawCtxChainReceive.normalBegin entry target context = effect at run ⊢
  unfold RawCtxChainReceive.beginReceive at run
  obtain ⟨plan, planned, run⟩ := PqxdhFirstRecordReplay.rust_bind_ok run
  rcases PqxdhFirstRecordReplay.plan_cases entry.control target plan planned with absent | ⟨aimed, _⟩
  · simp only [absent, RawCtxChainReceive.rejected, RustM.ok.injEq] at run
    subst effect
    trivial
  · simp only [aimed] at run
    split at run
    · obtain ⟨prepared, preparedRun, run⟩ := PqxdhFirstRecordReplay.rust_bind_ok run
      cases prepared with
      | none =>
          simp only [RawCtxChainReceive.rejected, RustM.ok.injEq] at run
          subst effect
          trivial
      | some prepared =>
          cases RustM.ok.inj run
          exact congrArg RustM.ok (prepare_cached_receive_success_inv entry target prepared preparedRun).sequence_eq
    · repeat' first | (obtain ⟨_, _, run⟩ := PqxdhFirstRecordReplay.rust_bind_ok run) | split at run
      all_goals simp only [RawCtxChainReceive.rejected, RustM.ok.injEq] at run
      all_goals subst effect
      all_goals trivial

/-- Opening requests retain the admitted raw context and exactly its target sequence. Other services carry no opening obligation. -/
def OpeningAllowed (target : Std.U64) (context : Context) :
    (ServiceSpec Slot Context Plaintext SealContext Output).Domain → Prop
  | .inr (.inl pending) => pending.context = context ∧ RawCtxInterpretedOpening.sequence pending = ok target
  | _ => True

/-- Every actual recursive source opening carries the original admitted context and sequence, including cached and future paths. -/
theorem receive_queries (entry : LabeledKernel Slot) (target : Std.U64) (context : Context)
    (effect : Effect Slot Context) (tracked : Tracked entry context effect) (aimed : Aimed target effect) :
    (receiveProgram (Plaintext := Plaintext) (SealContext := SealContext) (Output := Output) effect).AllQueriesSatisfy
      (OpeningAllowed (Plaintext := Plaintext) (Output := Output) target context) := by
  generalize depthEq : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
    cases effect with
    | rejected original prior => simp only [receiveProgram, allQueriesSatisfy_pure]
    | openRequested pending =>
      simp only [receiveProgram, allQueriesSatisfy_query_bind_iff, allQueriesSatisfy_pure, implies_true, and_true,
        OpeningAllowed]
      exact ⟨tracked.2.1, aimed⟩
    | kdfRequested pending =>
      simp only [receiveProgram, allQueriesSatisfy_query_bind_iff, OpeningAllowed, true_and]
      intro _
      apply ih _ (depthEq ▸ RawCtxChainReceive.normalResume_rank pending (advance pending.request 1, pending.request))
        _ (resume_tracked entry context pending pending.request tracked)
      · simpa only [show pending.target = target from aimed] using resume_aimed pending (advance pending.request 1, pending.request)
      · rfl

/-- Exact source admission supplies the opening discipline for every kernel and target, with no reachability premise. -/
theorem admitted_receive_queries (entry : LabeledKernel Slot) (target : Std.U64) (context : Context) :
    (admittedReceive (Plaintext := Plaintext) (SealContext := SealContext) (Output := Output) entry target context).AllQueriesSatisfy
      (OpeningAllowed (Plaintext := Plaintext) (Output := Output) target context) :=
  receive_queries entry target context _ (begin_tracked entry context target) (begin_aimed entry target context)

open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxSharedModes AdaptiveCtxDynamicKnownKeys
open PqxdhRecordLiftProjectionCut PqxdhFullSecretInputKdf PqxdhSecretInputKdf

/-- Actual source-independent sampling forwards every uniform request to the ordinary component. -/
def coinLift : QueryImpl unifSpec (OracleComp Spec) := fun query => Spec.query (.inl (.inl (.inl query)))

/-- A forwarded uniform query changes no component history or shared cache. -/
theorem coin_step (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (query : unifSpec.Domain) (before : SourceState) :
    (simulateQ (sourceImpl real decode crypto key) (coinLift query)).run before =
      (fun result => (result, before)) <$> (unifSpec.query query : ProbComp _) := by
  cases real
  all_goals change (fun result => (result.1.1, { before with selected := result.1.2, cache := result.2 })) <$>
    (do let answer ← (unifSpec.query query : ProbComp _)
        pure ((answer, before.selected), before.cache)) = _
  all_goals simp only [bind_pure_comp, Functor.map_map]

/-- The entire underlying sampler retains every ordinary component field, not only its marginal sample. -/
theorem coin_program {Result : Type} (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (work : ProbComp Result) (before : SourceState) :
    (simulateQ (sourceImpl real decode crypto key) (simulateQ coinLift work)).run before =
      (fun result => (result, before)) <$> work := by
  induction work using OracleComp.inductionOn with
  | pure result => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, coin_step, bind_map_left, map_bind]
      exact bind_congr fun result => ih result

variable [DecidableEq Slot]

/-- The missing selected key is confined to this proof-side reconstruction, never to a reduction argument. -/
noncomputable def keyTable (masked : Mask Slot) (key : RootOutput) : Table Slot :=
  (realize .key masked key).2.1

def store (masked : Mask Slot) (coordinate : Coordinate Slot) (output : FullOutput) : Mask Slot :=
  { masked with before := masked.before.cacheQuery coordinate output }

/-- Unselected persistent table writes retain the full selected entry and all its other projections. -/
theorem store_realization (masked : Mask Slot) (key : RootOutput) (coordinate : Coordinate Slot)
    (output : FullOutput) (different : coordinate ≠ masked.coordinate) :
    keyTable (store masked coordinate output) key = (keyTable masked key).cacheQuery coordinate output := by
  apply QueryCache.ext
  intro query
  by_cases parent : query = masked.coordinate
  · subst query
    simp [keyTable, store, realize, QueryCache.cacheQuery_of_ne, Ne.symm different]
  · by_cases selected : query = coordinate
    · subst query
      simp [keyTable, store, realize, QueryCache.cacheQuery_of_ne, different]
    · simp [keyTable, store, realize, QueryCache.cacheQuery_of_ne, parent, selected]

/-- Actual real KDF evaluations depend on retained chain inputs, never the selected message-key projection. -/
theorem output_key_invariant (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (masked : Mask Slot) (left right : RootOutput) (coordinate : Coordinate Slot) :
    PqxdhRecordLiftRealTable.output source seeds (keyTable masked left) coordinate =
      PqxdhRecordLiftRealTable.output source seeds (keyTable masked right) coordinate := by
  simp only [PqxdhRecordLiftRealTable.output, PqxdhRecordLiftRealTable.request, keyTable,
    PqxdhRecordLiftMaskedReads.chain_key_read]

/-- The actual persistent lookup with only analysis instrumentation erased; real calls still recompute and ideal misses alone draw. -/
noncomputable def bareLookup (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) (coordinate : Coordinate Slot) : StateT (Table Slot) ProbComp Unit := fun table =>
  if ideal coordinate then
    match table coordinate with
    | some _ => pure ((), table)
    | none => do
        let output ← $ᵗ FullOutput
        pure ((), table.cacheQuery coordinate output)
  else pure ((), table.cacheQuery coordinate (PqxdhRecordLiftRealTable.output source seeds table coordinate))

/-- Erasing native analysis counts preserves the literal lookup law and unchanged complete shared ROM. -/
theorem lookup_native_erasure (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) (coordinate : Coordinate Slot) (table : Table Slot)
    (primitive : PqxdhRecordLiftWorld.Primitive) :
    (fun result => ((), (result.2.1, result.2.2.2))) <$>
      (PqxdhRecordLiftChainOracle.lookup source seeds ideal coordinate).run (table, primitive) =
        (fun result => ((), (result.2, primitive.2))) <$> (bareLookup source seeds ideal coordinate).run table := by
  have sampled := PqxdhRecordLiftChainOracle.sample_exact (PqxdhRecordLiftChainOracle.charge primitive)
  simp only [StateT.run, PqxdhRecordLiftChainOracle.charge] at sampled
  cases selected : ideal coordinate with
  | false => simp [PqxdhRecordLiftChainOracle.lookup, bareLookup, selected, StateT.run, PqxdhRecordLiftChainOracle.charge]
  | true =>
      cases found : table coordinate <;>
        simp [PqxdhRecordLiftChainOracle.lookup, bareLookup, selected, found, StateT.run,
          PqxdhRecordLiftChainOracle.charge, sampled]

/-- A public arbitrary message-key filling suffices for every real chain-input read. -/
def keyFilling : RootOutput := List.Vector.replicate 32 0

/-- Persistent coordinate lookup with the selected message key unavailable. All randomness is requested through the ordinary component; no selected bytes are returned. -/
noncomputable def keyLookup (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) (coordinate : Coordinate Slot) :
    StateT (Mask Slot) (OracleComp Spec) Unit := fun masked =>
  if coordinate = masked.coordinate then pure ((), masked) else
    if ideal coordinate then
      match masked.before coordinate with
      | some _ => pure ((), masked)
      | none => do
          let output ← simulateQ coinLift ($ᵗ FullOutput)
          pure ((), store masked coordinate output)
    else pure ((), store masked coordinate
      (PqxdhRecordLiftRealTable.output source seeds (keyTable masked keyFilling) coordinate))

/-- The key-free persistent lookup recovers the exact source table and complete ordinary component state, before any native opening/sealing call. -/
theorem keyLookup_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) (coordinate : Coordinate Slot) (masked : Mask Slot)
    (key : RootOutput) (real : Bool) (decode : RawDecoder) (before : SourceState)
    (parentIdeal : ideal masked.coordinate = true) :
    (fun result => (result.1.1, (keyTable result.1.2 key, result.2))) <$>
      (simulateQ (sourceImpl real decode source.crypto key) ((keyLookup source seeds ideal coordinate).run masked)).run before =
        (fun result => (result.1, (result.2, before))) <$>
          (bareLookup source seeds ideal coordinate).run (keyTable masked key) := by
  by_cases parent : coordinate = masked.coordinate
  · subst coordinate
    simp only [keyLookup, bareLookup, keyTable, realize, parentIdeal, StateT.run, ite_true, QueryCache.cacheQuery_self]
    rfl
  · cases selected : ideal coordinate with
    | false =>
        simp only [keyLookup, bareLookup, StateT.run, parent, ite_false, selected, Bool.false_eq_true,
          simulateQ_pure, map_pure]
        change (pure ((), (keyTable (store masked coordinate
          (PqxdhRecordLiftRealTable.output source seeds (keyTable masked keyFilling) coordinate)) key, before)) : ProbComp (Unit × (Table Slot × SourceState))) = _
        simp only [store_realization _ _ _ _ parent, output_key_invariant source seeds masked keyFilling key coordinate]
    | true =>
        have observed : keyTable masked key coordinate = masked.before coordinate := by
          simp [keyTable, realize, QueryCache.cacheQuery_of_ne, parent]
        simp only [keyLookup, bareLookup, StateT.run, parent, ite_false, selected, ite_true, observed]
        cases found : masked.before coordinate with
        | some output => rfl
        | none =>
            simp only [bind_pure_comp]
            change (fun result => (result.1.1, (keyTable result.1.2 key, result.2))) <$>
              (simulateQ (sourceImpl real decode source.crypto key)
                ((fun output => ((), store masked coordinate output)) <$> simulateQ coinLift ($ᵗ FullOutput))).run before = _
            rw [simulateQ_map, StateT.run_map, coin_program]
            simp only [Functor.map_map, store_realization _ _ _ _ parent]

/-- Only a fresh selected sealing attempt adds a nonce; raw replies, public work and known-key operations cannot change that history. -/
def nextNonces (query : Spec.Domain) (used : List CtxNonce) : List CtxNonce :=
  match query with
  | .inl (.inl (.inr (.inr input))) => if input.nonce ∈ used then used else input.nonce :: used
  | _ => used

/-- The selected nonce history is derived from actual ordinary component calls and replies; it is not a freshness premise. -/
theorem source_nonces (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (query : Spec.Domain) (before : SourceState) (result : Spec.Range query × SourceState)
    (supported : result ∈ support ((sourceImpl true decode crypto key query).run before)) :
    result.2.selected.1.usedNonces = nextNonces query before.selected.1.usedNonces := by
  have mapApply {A B S : Type} (f : A → B) (work : StateT S ProbComp A) (state : S) :
      (f <$> work) state = (fun reply => (f reply.1, reply.2)) <$> work state :=
    StateT.run_map _ _ _
  rcases query with selected | known
  · simp only [sourceImpl, AdaptiveCtxSharedModes.localImpl, ite_true, StateT.run] at supported
    rcases selected with front | raw
    · rcases front with coin | cryptoQuery
      · simp only [AdaptiveCtxSharedHash.localImpl, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
          mapApply, Functor.map_map, support_map, Set.mem_image] at supported
        obtain ⟨reply, _, rfl⟩ := supported
        rfl
      · rcases cryptoQuery with hash | input
        · simp only [AdaptiveCtxSharedHash.localImpl, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
            mapApply, Functor.map_map, support_map, Set.mem_image] at supported
          obtain ⟨reply, _, rfl⟩ := supported
          rfl
        · by_cases used : input.nonce ∈ before.selected.1.usedNonces
          all_goals simp only [AdaptiveCtxSharedHash.localImpl, AdaptiveCtxSharedHash.localSeal, used,
            ite_true, ite_false, pure_bind, simulateQ_pure] at supported
          · simp only [bind_pure_comp] at supported
            subst result
            simp only [nextNonces, used, ite_true]
          · simp only [bind_pure_comp, simulateQ_map, simulateQ_spec_query] at supported
            simp only [mapApply, Functor.map_map, support_map, Set.mem_image] at supported
            obtain ⟨reply, _, rfl⟩ := supported
            simp only [nextNonces, used, ite_false]
    · cases parsed : decode raw with
      | none =>
          simp only [AdaptiveCtxSharedHash.localImpl, AdaptiveCtxSharedHash.localRaw, parsed,
            simulateQ_pure, bind_pure_comp, map_pure] at supported
          subst result
          rfl
      | some target =>
          simp only [AdaptiveCtxSharedHash.localImpl, AdaptiveCtxSharedHash.localRaw, parsed,
            bind_pure_comp, simulateQ_map, simulateQ_spec_query,
            mapApply, Functor.map_map, support_map, Set.mem_image] at supported
          obtain ⟨reply, _, rfl⟩ := supported
          rfl
  · simp only [sourceImpl, StateT.run, bind_pure_comp, support_map, Set.mem_image] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    rfl


/-- A complete program with no selected seal preserves the selected nonce history on every supported execution. -/
theorem no_seal_nonces {Result : Type} (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (work : OracleComp Spec Result)
    (noSeal : work.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0)
    (before : SourceState) (result : Result × SourceState)
    (supported : result ∈ support ((simulateQ (sourceImpl true decode crypto key) work).run before)) :
    result.2.selected.1.usedNonces = before.selected.1.usedNonces := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure answer =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      rfl
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at noSeal
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, supported⟩ := supported
      have noQuery : ¬ AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal query := by
        simpa using noSeal.1
      have unchanged : nextNonces query before.selected.1.usedNonces = before.selected.1.usedNonces := by
        rcases query with ((coin | (hash | input)) | raw) | known
        all_goals try rfl
        simp [AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxQueryBounds.SourceSeal] at noQuery
      exact (ih middle.1 (by simpa using noSeal.2 middle.1) middle.2 supported).trans
        ((source_nonces decode crypto key query before middle reached).trans unchanged)


open PqxdhRecordLiftCtxServices PqxdhRecordLiftLoggedAdapters
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Native opening retains the exact component nonce ghost as well as its actual optional plaintext, cache and pending frames. -/
theorem opening_with_nonces (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (slot : Nat)
    (seeds : Seeds Slot) (masked : Mask Slot) (key : RootOutput)
    (pending : LabeledOpening Slot RawCtxWholeOwner.OpenContext) (before : SourceState) (frames : Frames)
    (nonempty : pending.context.raw.isEmpty = false)
    (decoded : codec.frameRead pending.context.raw = some pending.context.frame)
    (valid : RawCtxReceive.ValidFrame pending.context.frame.sender pending.context.associatedData pending.context.frame)
    (prepared : RawCtxInterpretedOpening.sequence pending = ok pending.context.frame.sequence) :
    (fun result => (result.1, (result.2.cache, frames, result.2.selected.1.usedNonces))) <$>
      (simulateQ (sourceImpl true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
        (openingService slot codec.frameRead pending.context.frame.sender seeds masked pending)).run before =
      (fun result => (result.1, (result.2.1, result.2.2, before.selected.1.usedNonces))) <$>
        (PqxdhRecordLiftNativeAdapters.receiveOpen (receiveNative (loggedNative (native setup codec)))
          (eraseOpening seeds (keyTable masked key) pending)).run (before.cache, frames) := by
  rw [show keyTable masked key = (realize .key masked key).2.1 from rfl,
    openingService_source setup codec slot pending.context.frame.sender seeds masked key pending before frames
      nonempty decoded valid prepared]
  simp only [Functor.map_map]
  simp only [← bind_pure_comp]
  apply bind_congr_of_forall_mem_support
  intro result supported
  have unchanged := no_seal_nonces (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key
    _ (openingService_other slot codec.frameRead pending.context.frame.sender seeds masked pending).1
    before result supported
  rw [unchanged]

/-- Only a selected valid-width seal changes this ghost history; the change precedes the caller's writer result. -/
noncomputable def sealNonces (masked : Mask Slot) (pending : LabeledSeal Slot RawCtxSourceSend.SealContext)
    (used : List CtxNonce) : List CtxNonce :=
  if pending.context.associatedData.length = 153 then
    match materialRoute masked pending.material with
    | .hidden nonce => if nonce ∈ used then used else nonce :: used
    | .known _ => used
  else used

/-- The selected seal's history update is an actual endpoint transition, including refusal and writer failure. -/
theorem sealing_nonces (crypto : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (decode : RawDecoder) (key : RootOutput) (masked : Mask Slot)
    (pending : LabeledSeal Slot RawCtxSourceSend.SealContext) (before : SourceState) (frames : Frames)
    (result : (Except Unit (Option RawCtxSourceSend.Encrypted) × Frames) × SourceState)
    (supported : result ∈ support ((simulateQ (sourceImpl true decode crypto key)
      ((sealingService crypto writer masked pending).run.run frames)).run before)) :
    result.2.selected.1.usedNonces = sealNonces masked pending before.selected.1.usedNonces := by
  by_cases width : pending.context.associatedData.length = 153
  · cases routed : materialRoute masked pending.material with
    | known material =>
        have bill := (sealingService_bills crypto writer masked pending frames).2
        simp only [routed] at bill
        simpa only [sealNonces, width, ite_true, routed] using
          no_seal_nonces decode crypto key _ bill before result supported
    | hidden nonce =>
        simp only [sealingService, ExceptT.run, ExceptT.mk, StateT.run_map, routed, simulateQ_map, StateT.run_map,
          support_map, Set.mem_image] at supported
        obtain ⟨middle, supported, rfl⟩ := supported
        by_cases used : nonce ∈ before.selected.1.usedNonces
        · rw [sealCall_selected_repeat decode crypto key writer nonce pending.sequence pending.context width before frames used]
            at supported
          simp only [mem_support_pure_iff] at supported
          subst middle
          simp only [sealNonces, width, ite_true, routed, used]
        · rw [sealCall_selected_fresh decode crypto key writer nonce pending.sequence pending.context width before frames used]
            at supported
          simp only [bind_pure_comp, support_map, Set.mem_image] at supported
          obtain ⟨reply, _, rfl⟩ := supported
          simp only [sealNonces, width, ite_true, routed, used, ite_false,
            RawCtxSelectedSealConsumer.install, RawCtxSharedSourceOpening.retain, RawCtxSelectedMessageSealing.afterSeal,
            canonicalProjection, AdaptiveCtxSharedHash.install, AdaptiveCtxSharedHash.separate,
            CtxHandlerState.addSeal, RawCtxSelectedMessageSealing.selectedInput]
  · simp only [sealingService, ExceptT.run, ExceptT.mk, StateT.run_map] at supported
    rw [sealCall_invalid _ _ _ width frames] at supported
    simp only [map_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    simp only [sealNonces, width, ite_false]


/-- The proof-side lookup uses actual real key bytes only to reconstruct native chain inputs; ideal hits and misses retain the persistent source table. -/
noncomputable def nativeLookup (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) (key : RootOutput) (coordinate : Coordinate Slot) :
    StateT (Mask Slot) ProbComp Unit := fun masked =>
  if coordinate = masked.coordinate then pure ((), masked) else
    if ideal coordinate then
      match masked.before coordinate with
      | some _ => pure ((), masked)
      | none => (fun output => ((), store masked coordinate output)) <$> ($ᵗ FullOutput)
    else pure ((), store masked coordinate
      (PqxdhRecordLiftRealTable.output source seeds (keyTable masked key) coordinate))

/-- The lookup simulation preserves the complete mask and component state, including all retained non-key projections. -/
theorem keyLookup_native (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) (coordinate : Coordinate Slot) (masked : Mask Slot)
    (key : RootOutput) (real : Bool) (decode : RawDecoder) (before : SourceState) :
    (simulateQ (sourceImpl real decode source.crypto key) ((keyLookup source seeds ideal coordinate).run masked)).run before =
      (fun result => (result, before)) <$> (nativeLookup source seeds ideal key coordinate).run masked := by
  by_cases parent : coordinate = masked.coordinate
  · simp only [keyLookup, nativeLookup, StateT.run, parent, ite_true, simulateQ_pure, map_pure]
    rfl
  · cases selected : ideal coordinate with
    | false =>
        simp only [keyLookup, nativeLookup, StateT.run, parent, ite_false, selected, Bool.false_eq_true,
          simulateQ_pure, map_pure,
          output_key_invariant source seeds masked keyFilling key coordinate]
        rfl
    | true =>
        simp only [keyLookup, nativeLookup, StateT.run, parent, ite_false, selected, ite_true]
        cases found : masked.before coordinate with
        | some output => rfl
        | none =>
            simp only [bind_pure_comp]
            change (simulateQ (sourceImpl real decode source.crypto key)
              ((fun output => ((), store masked coordinate output)) <$> simulateQ coinLift ($ᵗ FullOutput))).run before = _
            rw [simulateQ_map, StateT.run_map, coin_program]
            simp only [Functor.map_map]

abbrev LocalSpec (Slot : Type) := ServiceSpec Slot RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted
  RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted

/-- The reduction keeps only the mask and real pending writer log. The selected key stays exclusively in the challenger. -/
abbrev Private (Slot : Type) := Mask Slot × Frames

/-- The native comparator additionally retains the real ROM and a nonce-history ghost for its explicit stop. -/
abbrev NativePrivate (Slot : Type) := Private Slot × (CtxRO.QueryCache × List CtxNonce)

def project (state : Private Slot × SourceState) : NativePrivate Slot :=
  (state.1, (state.2.cache, state.2.selected.1.usedNonces))

/-- Every service reply is the actual source optional reply. Selected nonce refusal is an explicit outer stop, never a fabricated opening or writer failure. -/
noncomputable def interpreter (slot : Nat) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : Seeds Slot) (ideal : Coordinate Slot → Bool)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    QueryImpl (LocalSpec Slot) (ExceptT Unit (StateT (Private Slot) (OracleComp Spec)))
  | .inl coordinate => ExceptT.mk fun state => do
      let result ← (keyLookup source seeds ideal coordinate).run state.1
      pure (.ok (), (result.2, state.2))
  | .inr (.inl pending) => ExceptT.mk fun state => do
      let reply ← openingService slot codec.frameRead pending.context.frame.sender seeds state.1 pending
      pure (.ok reply, state)
  | .inr (.inr pending) => ExceptT.mk fun state => do
      let result ← (sealingService source.crypto codec.frameWrite state.1 pending).run.run state.2
      pure (result.1, (state.1, result.2))

/-- The source comparator stops exactly before a repeated selected valid-width seal; caller-known aliases carry no nonce restriction. -/
noncomputable def Refused (masked : Mask Slot) (pending : LabeledSeal Slot RawCtxSourceSend.SealContext)
    (used : List CtxNonce) : Prop :=
  pending.context.associatedData.length = 153 ∧
    ∃ nonce, materialRoute masked pending.material = .hidden nonce ∧ nonce ∈ used

open Classical in
/-- Literal native callbacks with a retained cut mask and explicit selected nonce stop. Only analysis counters and irrelevant component histories are erased. -/
noncomputable def nativeInterpreter (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (seeds : Seeds Slot) (ideal : Coordinate Slot → Bool) (key : RootOutput) :
    QueryImpl (LocalSpec Slot) (ExceptT Unit (StateT (NativePrivate Slot) ProbComp))
  | .inl coordinate => ExceptT.mk fun state => do
      let result ← (nativeLookup setup.source seeds ideal key coordinate).run state.1.1
      pure (.ok (), ((result.2, state.1.2), state.2))
  | .inr (.inl pending) => ExceptT.mk fun state => do
      let result ← (PqxdhRecordLiftNativeAdapters.receiveOpen
        (receiveNative (loggedNative (native setup codec)))
        (eraseOpening seeds (keyTable state.1.1 key) pending)).run (state.2.1, state.1.2)
      pure (.ok result.1, ((state.1.1, result.2.2), (result.2.1, state.2.2)))
  | .inr (.inr pending) => ExceptT.mk fun state =>
      if Refused state.1.1 pending state.2.2 then pure (.error (), state) else do
        let result ← (PqxdhRecordLiftNativeAdapters.sendSeal
          (sendNative (loggedNative (native setup codec)))
          (eraseSeal seeds (keyTable state.1.1 key) pending)).run (state.2.1, state.1.2)
        pure (.ok result.1, ((state.1.1, result.2.2), (result.2.1, sealNonces state.1.1 pending state.2.2)))

/-- The exact raw admission information needed by the source opening consumer. -/
def Admitted (read : RawCtxReceive.FrameDecoder) : (LocalSpec Slot).Domain → Prop
  | .inr (.inl pending) =>
      pending.context.raw.isEmpty = false ∧
      read pending.context.raw = some pending.context.frame ∧
      RawCtxReceive.ValidFrame pending.context.frame.sender pending.context.associatedData pending.context.frame ∧
      RawCtxInterpretedOpening.sequence pending = ok pending.context.frame.sequence
  | _ => True


def projectResult {Reply : Type} (result : (Reply × Private Slot) × SourceState) : Reply × NativePrivate Slot :=
  (result.1.1, project (result.1.2, result.2))

set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- Every admitted key-free service equals its stopped literal source callback, preserving the complete mask, ROM and pending writer frames. -/
theorem interpreter_source (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (slot : Nat)
    (seeds : Seeds Slot) (ideal : Coordinate Slot → Bool) (key : RootOutput)
    (query : (LocalSpec Slot).Domain) (state : Private Slot) (before : SourceState)
    (admitted : Admitted codec.frameRead query) :
    projectResult <$>
      (simulateQ (sourceImpl true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
        ((interpreter slot setup.source seeds ideal codec query).run.run state)).run before =
      ((nativeInterpreter setup codec seeds ideal key query).run.run (project (state, before))) := by
  rcases state with ⟨masked, frames⟩
  rcases query with coordinate | (pending | pending)
  · simp only [interpreter, ExceptT.run, ExceptT.mk, StateT.run, bind_pure_comp]
    change projectResult <$> (simulateQ (sourceImpl true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
      ((fun result => (Except.ok (), (result.2, frames))) <$> (keyLookup setup.source seeds ideal coordinate).run masked)).run before = _
    rw [simulateQ_map, StateT.run_map, keyLookup_native]
    simp only [Functor.map_map, nativeInterpreter, ExceptT.mk, StateT.run, bind_pure_comp,
      projectResult, project]
  · have exactOpen := congrArg (fun work =>
        (fun result => (Except.ok (ε := Unit) result.1, ((masked, result.2.2.1), (result.2.1, result.2.2.2)))) <$> work)
      (opening_with_nonces setup codec slot seeds masked key pending before frames
        admitted.1 admitted.2.1 admitted.2.2.1 admitted.2.2.2)
    simp only [interpreter, ExceptT.run, ExceptT.mk, StateT.run, bind_pure_comp]
    change projectResult <$> (simulateQ (sourceImpl true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
      ((fun reply => (Except.ok reply, (masked, frames))) <$>
        openingService slot codec.frameRead pending.context.frame.sender seeds masked pending)).run before = _
    rw [simulateQ_map, StateT.run_map]
    simpa only [Functor.map_map, nativeInterpreter, ExceptT.mk, StateT.run, bind_pure_comp,
      projectResult, project] using exactOpen
  · by_cases refused : Refused masked pending before.selected.1.usedNonces
    · obtain ⟨width, nonce, selected, used⟩ := refused
      simp only [interpreter, ExceptT.run, ExceptT.mk, StateT.run, bind_pure_comp]
      change projectResult <$> (simulateQ (sourceImpl true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
        ((fun result => (result.1, (masked, result.2))) <$>
          (sealingService setup.source.crypto codec.frameWrite masked pending).run.run frames)).run before = _
      rw [simulateQ_map, StateT.run_map,
        sealingService_repeat setup.source.crypto codec.frameWrite (RawCtxUniversalDecoder.decoder codec.frameRead)
          key masked pending nonce selected width before frames used]
      have stopped : Refused masked pending before.selected.1.usedNonces := ⟨width, nonce, selected, used⟩
      simp only [map_pure, nativeInterpreter, ExceptT.mk, StateT.run, stopped, ite_true, projectResult, project]
    · have fresh : ∀ nonce, materialRoute masked pending.material = .hidden nonce →
          pending.context.associatedData.length = 153 → nonce ∉ before.selected.1.usedNonces := by
        intro nonce selected width used
        exact refused ⟨width, nonce, selected, used⟩
      have sealed := sealingService_source setup codec (RawCtxUniversalDecoder.decoder codec.frameRead)
        seeds masked key pending before frames fresh
      have projected := congrArg (fun work =>
        (fun result => (result.1, ((masked, result.2.2),
          (result.2.1, sealNonces masked pending before.selected.1.usedNonces)))) <$> work) sealed
      simp only [interpreter, ExceptT.run, ExceptT.mk, StateT.run, bind_pure_comp]
      change projectResult <$> (simulateQ (sourceImpl true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
        ((fun result => (result.1, (masked, result.2))) <$>
          (sealingService setup.source.crypto codec.frameWrite masked pending).run.run frames)).run before = _
      rw [simulateQ_map, StateT.run_map]
      simp only [Functor.map_map, nativeInterpreter, ExceptT.run, ExceptT.mk, StateT.run, project, refused,
        ite_false, bind_pure_comp]
      simp only [Functor.map_map, Prod.map_def, id_eq, StateT.run] at projected
      change _ = (fun result => (Except.ok result.1, ((masked, result.2.2),
        (result.2.1, sealNonces masked pending before.selected.1.usedNonces)))) <$>
          (PqxdhRecordLiftNativeAdapters.sendSeal (sendNative (loggedNative (native setup codec)))
            (eraseSeal seeds (realize .key masked key).2.1 pending)) (before.cache, frames)
      rw [← projected]
      simp only [projectResult, project, callbackProjection]
      simp only [← bind_pure_comp]
      apply bind_congr_of_forall_mem_support
      intro result supported
      rw [sealing_nonces setup.source.crypto codec.frameWrite (RawCtxUniversalDecoder.decoder codec.frameRead)
        key masked pending before frames result supported]


/-- Running an exception-bearing stateful bind retains the state at an explicit stop. -/
theorem except_bind {S A B : Type} {m : Type → Type} [Monad m]
    (work : ExceptT Unit (StateT S m) A) (next : A → ExceptT Unit (StateT S m) B) (state : S) :
    ((work >>= next).run.run state) = (do
      let result ← work.run.run state
      match result.1 with
      | .error error => pure (.error error, result.2)
      | .ok answer => (next answer).run.run result.2) := by
  change (work.run.run state >>= fun result => (ExceptT.bindCont next result.1).run result.2) = _
  congr 1
  funext result
  cases result.1 <;> rfl

/-- A complete adaptive source continuation receives exactly the ordinary optional replies and stops at precisely the explicit nonce gate, with its full retained poststate. -/
theorem schedule_source {Result : Type} (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (slot : Nat)
    (seeds : Seeds Slot) (ideal : Coordinate Slot → Bool) (key : RootOutput)
    (client : OracleComp (LocalSpec Slot) Result) (state : Private Slot) (before : SourceState)
    (admitted : client.AllQueriesSatisfy (Admitted codec.frameRead)) :
    projectResult <$>
      (simulateQ (sourceImpl true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
        ((simulateQ (interpreter slot setup.source seeds ideal codec) client).run.run state)).run before =
      ((simulateQ (nativeInterpreter setup codec seeds ideal key) client).run.run (project (state, before))) := by
  induction client using OracleComp.inductionOn generalizing state before with
  | pure result => rfl
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at admitted
      simp only [simulateQ_bind, simulateQ_spec_query, except_bind, simulateQ_bind, StateT.run_bind, map_bind]
      rw [← interpreter_source setup codec slot seeds ideal key query state before admitted.1]
      rw [bind_map_left]
      apply bind_congr
      intro result
      rcases result with ⟨⟨reply, state'⟩, before'⟩
      cases reply with
      | error error =>
          simp only [projectResult, simulateQ_pure, StateT.run_pure, map_pure]
      | ok reply =>
          exact ih reply state' before' (admitted.2 reply)


/-- Reconstructing the cut mask gives exactly the literal persistent table after every source lookup; the already-ideal selected entry is a cache hit. -/
theorem nativeLookup_realization (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) (key : RootOutput) (coordinate : Coordinate Slot) (masked : Mask Slot)
    (parentIdeal : ideal masked.coordinate = true) :
    Prod.map id (fun next => keyTable next key) <$> (nativeLookup source seeds ideal key coordinate).run masked =
      (bareLookup source seeds ideal coordinate).run (keyTable masked key) := by
  have law := keyLookup_source source seeds ideal coordinate masked key true (fun _ => none) initialSource parentIdeal
  rw [keyLookup_native] at law
  have projected := congrArg (fun work => (fun result => (result.1, result.2.1)) <$> work) law
  simpa only [Functor.map_map, Prod.map_def, id_eq, Prod.mk.eta, id_map'] using projected

set_option maxRecDepth 2048 in
/-- A source lookup issues at most76 component queries, all from its one possible full76 miss draw; cache hits and real KDF evaluation need no component query. -/
theorem keyLookup_total (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) (coordinate : Coordinate Slot) (masked : Mask Slot) :
    ((keyLookup source seeds ideal coordinate).run masked).IsTotalQueryBound 76 := by
  have sampled : (simulateQ coinLift ($ᵗ FullOutput)).IsTotalQueryBound 76 :=
    (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76).simulateQ_of_step (by
      intro query
      simp [coinLift, IsTotalQueryBound])
  change (keyLookup source seeds ideal coordinate masked).IsTotalQueryBound 76
  unfold keyLookup
  split
  · trivial
  · split
    · split
      · trivial
      · simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using sampled
    · trivial

set_option maxRecDepth 2048 in
/-- Lookup's component interface contains only ordinary uniform queries; real HKDF work remains a separately charged native source operation. -/
theorem keyLookup_uniform (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) (coordinate : Coordinate Slot) (masked : Mask Slot) :
    ((keyLookup source seeds ideal coordinate).run masked).AllQueriesSatisfy AdaptiveCtxDynamicKnownBounds.UniformRoute := by
  have sampled {A : Type} (work : ProbComp A) :
      (simulateQ coinLift work).AllQueriesSatisfy AdaptiveCtxDynamicKnownBounds.UniformRoute := by
    induction work using OracleComp.inductionOn with
    | pure answer => simp
    | query_bind query next ih =>
        simp only [simulateQ_bind, simulateQ_spec_query, coinLift, allQueriesSatisfy_query_bind_iff]
        exact ⟨by trivial, ih⟩
  change (keyLookup source seeds ideal coordinate masked).AllQueriesSatisfy _
  unfold keyLookup
  split
  · trivial
  · split
    · split
      · trivial
      · exact allQueriesSatisfy_bind (sampled _) fun _ => by trivial
    · trivial

/-- The ordinary local interpreter charges each reached callback: up to76 uniform queries for lookup and one raw/hash/seal request for each opening or sealing. -/
theorem interpreter_total (slot : Nat) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : Seeds Slot) (ideal : Coordinate Slot → Bool)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : (LocalSpec Slot).Domain) (state : Private Slot) :
    ((interpreter slot source seeds ideal codec query).run.run state).IsTotalQueryBound
      (match query with | .inl _ => 76 | .inr _ => 1) := by
  rcases query with coordinate | (pending | pending)
  · simpa only [interpreter, ExceptT.run, ExceptT.mk, StateT.run, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
      using keyLookup_total source seeds ideal coordinate state.1
  · simpa only [interpreter, ExceptT.run, ExceptT.mk, StateT.run, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
      using openingService_total slot codec.frameRead pending.context.frame.sender seeds state.1 pending
  · simpa only [interpreter, ExceptT.run, ExceptT.mk, StateT.run, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
      using sealingService_total source.crypto codec.frameWrite state.1 pending state.2

omit [DecidableEq Slot] in
/-- Source opening context/sequence discipline supplies exactly the raw admission predicate. -/
theorem allowed_admitted {Result : Type} (read : RawCtxReceive.FrameDecoder)
    (context : RawCtxWholeOwner.OpenContext) (client : OracleComp (LocalSpec Slot) Result)
    (allowed : client.AllQueriesSatisfy (OpeningAllowed (Plaintext := RawCtxWholeOwner.Decrypted)
      (Output := RawCtxSourceSend.Encrypted) context.frame.sequence context))
    (nonempty : context.raw.isEmpty = false) (decoded : read context.raw = some context.frame)
    (valid : RawCtxReceive.ValidFrame context.frame.sender context.associatedData context.frame) :
    client.AllQueriesSatisfy (Admitted read) := by
  induction client using OracleComp.inductionOn with
  | pure result => trivial
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at allowed ⊢
      refine ⟨?_, fun reply => ih reply (allowed.2 reply)⟩
      rcases query with coordinate | (pending | pending)
      · trivial
      · obtain ⟨same, sequence⟩ := allowed.1
        simp only [Admitted, same, nonempty, decoded, valid, true_and]
        exact sequence
      · trivial

omit [DecidableEq Slot] in
/-- Cached and future receive programs satisfy source raw admission for any supplied kernel after the actual outer parser checks. -/
theorem receive_admitted (read : RawCtxReceive.FrameDecoder) (entry : LabeledKernel Slot)
    (context : RawCtxWholeOwner.OpenContext) (nonempty : context.raw.isEmpty = false)
    (decoded : read context.raw = some context.frame)
    (valid : RawCtxReceive.ValidFrame context.frame.sender context.associatedData context.frame) :
    (admittedReceive (Plaintext := RawCtxWholeOwner.Decrypted) (Output := RawCtxSourceSend.Encrypted)
      (SealContext := RawCtxSourceSend.SealContext) entry context.frame.sequence context).AllQueriesSatisfy (Admitted read) :=
  allowed_admitted read context _ (admitted_receive_queries entry context.frame.sequence context) nonempty decoded valid

omit [DecidableEq Slot] in
/-- Every actual send satisfies the opening discipline vacuously; source send invokes only lookup and sealing. -/
theorem send_admitted (read : RawCtxReceive.FrameDecoder) (entry : LabeledKernel Slot)
    (context : RawCtxSourceSend.SealContext) :
    (admittedSend (OpenContext := RawCtxWholeOwner.OpenContext) (Plaintext := RawCtxWholeOwner.Decrypted)
      (Output := RawCtxSourceSend.Encrypted) entry context).AllQueriesSatisfy (Admitted read) := by
  unfold admittedSend
  cases RawCtxChainSend.normalBegin entry context <;>
    simp only [sendProgram, allQueriesSatisfy_query_bind_iff, Admitted, allQueriesSatisfy_pure, implies_true, and_true]


/-- The constructed one-key reduction runs the actual opaque client and forwards every selected request to the ordinary CTX endpoint. No selected key is a parameter. -/
noncomputable def reduction {Result : Type} (slot : Nat)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (client : OracleComp (LocalSpec Slot) Result) (state : Private Slot)
    (others : ReductionState) :
    OracleComp ReceiveSpec ((Except Unit Result × Private Slot) × ReductionState) :=
  wrapped source.crypto ((simulateQ (interpreter slot source seeds ideal codec) client).run.run state) others

/-- Interpreting the actual reduction by the ordinary selected-key CTX endpoint yields the entire stopped native continuation with the same optional replies and retained cache/log state. -/
theorem reduction_source {Result : Type} (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (slot : Nat)
    (seeds : Seeds Slot) (ideal : Coordinate Slot → Bool) (key : RootOutput)
    (client : OracleComp (LocalSpec Slot) Result) (state : Private Slot)
    (others : ReductionState) (selected : AdaptiveCtxSharedModes.State)
    (admitted : client.AllQueriesSatisfy (Admitted codec.frameRead)) :
    (fun result => projectResult (AdaptiveCtxDynamicKnownKeys.erase result)) <$>
      (simulateQ (targetImpl true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
        (reduction slot setup.source seeds ideal codec client state others)).run selected =
      (simulateQ (nativeInterpreter setup codec seeds ideal key) client).run.run
        (project (state, AdaptiveCtxDynamicKnownKeys.project (others, selected))) := by
  have ordinary := AdaptiveCtxDynamicKnownKeys.schedule_interpretation true
    (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key
    ((simulateQ (interpreter slot setup.source seeds ideal codec) client).run.run state) others selected
  have mapped := congrArg (fun work => projectResult <$> work) ordinary
  simp only [Functor.map_map] at mapped
  exact mapped.trans (schedule_source setup codec slot seeds ideal key client state _ admitted)

end BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.resume_aimed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.resume_aimed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.begin_aimed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.begin_aimed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.receive_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.receive_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.admitted_receive_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.admitted_receive_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.coin_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.coin_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.coin_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.coin_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.store_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.store_realization

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.output_key_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.output_key_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.lookup_native_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.lookup_native_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.keyLookup_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.keyLookup_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.source_nonces' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.source_nonces

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.no_seal_nonces' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.no_seal_nonces

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.opening_with_nonces' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.opening_with_nonces

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.sealing_nonces' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.sealing_nonces

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.keyLookup_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.keyLookup_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.interpreter_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.interpreter_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.except_bind' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.except_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.schedule_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.schedule_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.nativeLookup_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.nativeLookup_realization

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.keyLookup_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.keyLookup_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.keyLookup_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.keyLookup_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.interpreter_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.interpreter_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.allowed_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.allowed_admitted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.receive_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.receive_admitted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.send_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.send_admitted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.reduction_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle.reduction_source
