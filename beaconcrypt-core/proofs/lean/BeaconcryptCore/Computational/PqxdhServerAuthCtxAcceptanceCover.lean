import BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory

/-! The actual acceptance event is covered by an ordinary observed forgery or a reached ordinary-root table entry. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxStop
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhJointIdentity PqxdhJointGapDh
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- An actual forwarded uniform query retains the entire ordinary observer and component state. -/
theorem observed_coin (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (query : unifSpec.Domain)
    (state : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState) :
    (simulateQ (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder read)
      source.crypto key) (PqxdhServerAuthCtxAmbient.coin query)).run state =
      (fun value => (value, state)) <$> (unifSpec.query query : ProbComp _) := by
  have map_apply {X Y σ : Type} (f : X → Y) (work : StateT σ ProbComp X) (initial : σ) :
      (f <$> work) initial = (fun result => (f result.1, result.2)) <$> work initial := by
    change (f <$> work).run initial = _
    rw [StateT.run_map]
    rfl
  have lift_apply {X σ : Type} (work : ProbComp X) (initial : σ) :
      (monadLift work : StateT σ ProbComp X) initial = (fun value => (value, initial)) <$> work := by
    change (work >>= fun value => pure (value, initial)) = _
    rw [bind_pure_comp]
  simp [PqxdhServerAuthCtxAmbient.coin, RawCtxSelectedAuthenticationObserver.observed,
    RawCtxSelectedAuthenticationObserver.step, AdaptiveCtxDynamicKnownKeys.sourceImpl,
    AdaptiveCtxSharedModes.localImpl, AdaptiveCtxSharedHash.localImpl, AdaptiveCtxSharedHash.hashImpl,
    StateT.run, map_apply, lift_apply]

/-- The complete probabilistic prefix or derivation preserves observer and component state while returning its exact original sampled result. -/
theorem observed_coins {α : Type} (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (work : ProbComp α)
    (state : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState) :
    (simulateQ (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder read)
      source.crypto key) (simulateQ PqxdhServerAuthCtxAmbient.coin work)).run state =
      (fun value => (value, state)) <$> work := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query continuation ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, observed_coin,
      bind_map_left, map_bind, ih]

/-- A reached ordinary root remains distinguishable from the omitted selected input by actual table occupancy, not by a key-byte inequality. -/
def Ordinary (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (state : PqxdhServerAuthCtxState.Local KemSK) : Prop :=
  ∃ bytes, beaconInput setup context.seed context.scalar state.1.1.ghost.touches = some bytes ∧
    state.1.2.2.cache bytes ≠ none

/-- The original acceptance violation is covered by an actual ordinary observer win or a reached ordinary-root entry. The second alternative is eliminated separately by the source designation and omission invariants. -/
def Covered (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (state : PqxdhServerAuthCtxState.Local KemSK)
    (observer : RawCtxSelectedAuthenticationObserver.State) : Prop :=
  (W1 setup context.seed context.scalar state.1.1.ghost ∨
    W2 setup context.seed context.scalar state.1.1.ghost) →
  RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) observer = true ∨
    Ordinary setup context state

/-- Actual table selection retains every previous seal-origin witness. A newly designated table has no previously selected receipt, while ordinary derivation retains the selected input exactly. -/
theorem derive_origins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (select : Bool) (state : PqxdhServerAuthCtxState.Local KemSK)
    (observer : RawCtxSelectedAuthenticationObserver.State)
    (origins : PqxdhServerAuthCtxOrigin.Origins setup context codec.frameWrite state.1.1.ghost
      state.1.2.2.hidden observer)
    (unselected : select = true → state.1.2.2.hidden = none)
    (message : PqxdhJointDhExtractFamily.Message) (result : Reply × HiddenTable)
    (supported : result ∈ support
      (((PqxdhServerAuthCtxState.tableServices (WireResponse := Response) setup context select).derive message).run state.1.2.2)) :
    PqxdhServerAuthCtxOrigin.Origins setup context codec.frameWrite
      (PqxdhServerAuthCtxFinish.touched state message result.2).1.1.ghost result.2.hidden observer := by
  intro entry found
  obtain ⟨index, inputMessage, reply, bytes, sealContext, sequence, touched, selected, input, bound,
    records, seq, sender, publication⟩ := origins entry found
  have retained : result.2.hidden = some bytes := by
    cases selectedRoute : select with
    | true =>
      have impossible := (unselected selectedRoute).symm.trans selected
      cases impossible
    | false =>
      have kept := derive_retains setup context message state.1.2.2 result
        (by simpa only [selectedRoute, PqxdhServerAuthCtxState.tableServices, Bool.false_eq_true, ite_false] using supported)
      exact kept.trans selected
  exact ⟨index, inputMessage, reply, bytes, sealContext, sequence,
    (List.prefix_append _ _).subset touched, retained, input, bound, records, seq, sender, publication⟩

/-- A failed staged finish cannot create an acceptance observation. -/
theorem rejected_no_event (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (control : pqxdh.BeaconInitSent) (state : PqxdhServerAuthCtxState.Local KemSK)
    (fresh : state.1.1.ghost.acceptance = none) :
    ¬ (W1 setup context.seed context.scalar (PqxdhServerAuthCtxFinish.complete control state none).2.1.1.ghost ∨
      W2 setup context.seed context.scalar (PqxdhServerAuthCtxFinish.complete control state none).2.1.1.ghost) := by
  intro failed
  simp only [PqxdhServerAuthCtxFinish.complete, finishOutcome, acceptedOf, Option.map_none,
    ite_self, Ghost.accept] at failed
  rcases failed with ⟨snap, captured, _⟩ | ⟨snap, captured, _⟩ <;> simp [fresh] at captured

/-- The literal ordinary post-root callback retains its reached input and actual occupied table entry through every optional native result. -/
theorem known_ordinary (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (key : RootOutput) (control : pqxdh.BeaconInitSent)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) (root : RootOutput)
    (state afterLocal : PqxdhServerAuthCtxState.Local KemSK)
    (ordinary : Ordinary setup context state)
    (before after : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (answer : Option Pqxdh.Bytes)
    (supported : ((answer, afterLocal), after) ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxFinish.known setup.source codec control pending root).run state)).run before)) :
    Ordinary setup context afterLocal := by
  change ((answer, afterLocal), after) ∈ support ((simulateQ
    (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto key) (PqxdhServerAuthCtxFinish.complete control state <$> _)).run before) at supported
  rw [simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨inner, _, equal⟩ := supported
  have localEqual := congrArg (fun result => result.1.2) equal
  dsimp only at localEqual
  rw [← localEqual]
  obtain ⟨bytes, input, present⟩ := ordinary
  refine ⟨bytes, ?_, present⟩
  simpa only [PqxdhServerAuthCtxFinish.complete, finishOutcome, Ghost.accept_touches] using input

/-- Every actual active finish either creates an ordinary observer win or uses an occupied ordinary-root entry. The source prefix, both table routes, actual optional plaintext and final registration gates all remain in the experiment. -/
theorem active_finish_cover (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (select : Bool) (raw : Pqxdh.Bytes)
    (state : PqxdhServerAuthCtxState.Local KemSK)
    (before : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (invariant : PqxdhServerAuthCtxObserverHistory.Joint setup codec context key Q j state before)
    (unselected : select = true → state.1.2.2.hidden = none)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (control : pqxdh.BeaconInitSent) (prekey oneTime : Unit ⊕ ScalarBytes) (kem : KemSK)
    (phase : state.1.1.beacon.beacon.phase = .initSent control prekey oneTime kem)
    (result : (Option Pqxdh.Bytes × PqxdhServerAuthCtxState.Local KemSK) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxFinish.finish setup codec context rest select raw).run state)).run before)) :
    Covered setup codec context result.1.2 result.2.1 := by
  have active : InitSent state.1.1 := ⟨control, prekey, oneTime, kem, phase⟩
  have fresh := invariant.history.fresh active
  have clean := invariant.trace.shape.clean active
  intro failed
  have runBind {σ α β : Type} (work : StateT σ ProbComp α)
      (next : α → StateT σ ProbComp β) (initial : σ) :
      (work >>= next) initial = work initial >>= fun result => next result.1 result.2 := rfl
  have runCoins {α : Type} (work : ProbComp α)
      (initial : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState) :=
    observed_coins setup.source key codec.frameRead work initial
  simp only [StateT.run] at runCoins
  simp only [PqxdhServerAuthCtxFinish.finish, StateT.run, phase, simulateQ_bind,
    runBind, runCoins, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨prepared, _, supported⟩ := supported
  cases prepared with
  | none =>
    simp only [simulateQ_pure] at supported
    subst supported
    exact ((rejected_no_event setup context control state fresh) failed).elim
  | some pending =>
    simp only [simulateQ_bind, runBind, runCoins, bind_map_left, mem_support_bind_iff] at supported
    obtain ⟨derived, reached, supported⟩ := supported
    cases reply : derived.1 with
    | rejected =>
      simp only [reply, simulateQ_pure] at supported
      subst supported
      exact ((rejected_no_event setup context control _ fresh) failed).elim
    | root root =>
      simp only [reply] at supported
      obtain ⟨bytes, input, occupied⟩ := PqxdhServerAuthCtxChronology.table_root setup context select
        (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected)
        state.1.2.2 derived.2 root (by rw [← reply]; exact reached)
      apply Or.inr
      apply known_ordinary setup codec context key control pending root _ result.1.2 _ before result.2 result.1.1 supported
      refine ⟨bytes, ?_, occupied⟩
      change beaconInput setup context.seed context.scalar
        (state.1.1.ghost.touches ++ [Touch.beacon _]) = some bytes
      rw [beaconInput, firstBeacon_after _ [] _ clean, Option.bind_some]
      exact input
    | hidden =>
      simp only [reply] at supported
      apply Or.inl
      exact PqxdhServerAuthCtxOrigin.touched_event setup codec context key rest pending control select state
        result.1.2 (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected)
        derived.2 result.1.1 before result.2
        (derive_origins setup codec context select state before.1 invariant.origins unselected _ derived reached)
        writable invariant.good fresh clean (by rw [← reply]; exact reached) supported failed

/-- The complete finish capability preserves acceptance coverage through all actual source phases, including rejection without a new Beacon attempt. -/
theorem finish_cover (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (select : Bool) (raw : Pqxdh.Bytes)
    (state : PqxdhServerAuthCtxState.Local KemSK)
    (before : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (invariant : PqxdhServerAuthCtxObserverHistory.Joint setup codec context key Q j state before)
    (covered : Covered setup codec context state before.1)
    (unselected : select = true → state.1.2.2.hidden = none)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (result : (Option Pqxdh.Bytes × PqxdhServerAuthCtxState.Local KemSK) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxFinish.finish setup codec context rest select raw).run state)).run before)) :
    Covered setup codec context result.1.2 result.2.1 := by
  cases phase : state.1.1.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
    exact active_finish_cover setup codec context key rest Q j select raw state before invariant
      unselected writable control prekey oneTime kem phase result supported
  | _ =>
    simp only [PqxdhServerAuthCtxFinish.finish, StateT.run, phase, simulateQ_pure] at supported
    subst supported
    exact covered

/-- Every source capability other than the one actual Beacon finish retains the exact first-acceptance field, including all failed native builds and public calls. -/
theorem skeleton_acceptance (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (services : Services Response HiddenTable) (query : ServerAuthSpec.Domain)
    (notFinish : ∀ raw, query ≠ .inr (.finish raw)) (state : FlatState KemSK HiddenTable)
    (result : ServerAuthSpec.Range query × FlatState KemSK HiddenTable)
    (supported : result ∈ support ((skeleton setup codec checks (context.publicValue setup)
      context.beaconSeed services query).run state)) :
    result.2.1.ghost.acceptance = state.1.ghost.acceptance := by
  cases query with
  | inl coin =>
    simp only [skeleton, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨_, _, rfl⟩ := supported
    rfl
  | inr query =>
    cases query with
    | accept raw =>
      simp only [skeleton, acceptStep, StateT.run, mem_support_bind_iff] at supported
      obtain ⟨collected, _, supported⟩ := supported
      cases prepared : collected.1 with
      | none =>
        simp only [prepared, support_pure, Set.mem_singleton_iff] at supported
        subst supported
        rfl
      | some input =>
        simp only [prepared] at supported
        split_ifs at supported
        · obtain ⟨derived, _, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
          simp only [support_pure, Set.mem_singleton_iff] at supported
          subst supported
          cases derived.1 <;> rfl
        · simp only [support_pure, Set.mem_singleton_iff] at supported
          subst supported
          rfl
    | build session payload =>
      simp only [skeleton, buildStep, StateT.run] at supported
      cases pending : state.1.pending session with
      | none =>
        simp only [pending, support_pure, Set.mem_singleton_iff] at supported
        subst supported
        rfl
      | some token =>
        simp only [pending, mem_support_bind_iff] at supported
        obtain ⟨built, _, supported⟩ := supported
        simp only [support_pure, Set.mem_singleton_iff] at supported
        subst supported
        rfl
    | finish raw => exact (notFinish raw rfl).elim
    | hmac key bytes =>
      simp only [skeleton, hmacStep, StateT.run] at supported
      split_ifs at supported
      · obtain ⟨read, _, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
        simp only [support_pure, Set.mem_singleton_iff] at supported
        subst supported
        rfl
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst supported
        rfl
    | hash bytes =>
      simp only [skeleton, hashStep, StateT.run, mem_support_bind_iff] at supported
      obtain ⟨read, _, supported⟩ := supported
      simp only [support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl
    | reveal key =>
      simp only [skeleton, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl

/-- Actual source designation and sticky refusal do not change the exact acceptance-retention result for nonfinish API operations. -/
theorem handler_acceptance (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (services : Services Response HiddenTable) (Q : Nat) (j : Fin (Q + 1))
    (query : ServerAuthSpec.Domain) (notFinish : ∀ raw, query ≠ .inr (.finish raw))
    (state : HiddenState KemSK) (result : ServerAuthSpec.Range query × HiddenState KemSK)
    (supported : result ∈ support ((hiddenHandler setup codec checks context Q j services query).run state)) :
    result.2.1.1.ghost.acceptance = state.1.1.ghost.acceptance := by
  simp only [hiddenHandler, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨middle, supported, rfl⟩ := supported
  rw [keepHiddenBad_game]
  simp only [once, StateT.run] at supported
  split_ifs at supported
  all_goals
    simp only [latch, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨step, reached, rfl⟩ := supported
    exact skeleton_acceptance setup codec checks context _ query notFinish state.1 step reached

/-- A complete nonfinish compiled operation preserves the same acceptance coverage. Earlier wins persist, while an ordinary input remains occupied through the actual source table continuation. -/
theorem quiet_handler_cover (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (notFinish : ∀ raw, query ≠ .inr (.finish raw))
    (state : PqxdhServerAuthCtxState.Local KemSK)
    (before : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (ready : PqxdhServerAuthCtxHandler.Ready query (state, before.2))
    (invariant : PqxdhServerAuthCtxObserverHistory.Joint setup codec context key Q j state before)
    (covered : Covered setup codec context state before.1)
    (result : (Option (ServerAuthSpec.Range query) × PqxdhServerAuthCtxState.Local KemSK) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j query).run.run state)).run before)) :
    Covered setup codec context result.1.2 result.2.1 := by
  obtain ⟨answer, _, reached⟩ := PqxdhServerAuthCtxObserverHistory.handler_source_support setup codec checks context
    rest key Q j query state before ready result supported
  have accepted := handler_acceptance setup codec checks context
    (factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest)) Q j query notFinish
    (PqxdhServerAuthCtxState.project (state, before.2)) _ reached
  have grown := PqxdhServerAuthCtxAcceptanceHistory.handler_grows setup codec checks context Q j
    (factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest)) query
    (PqxdhServerAuthCtxState.project (state, before.2)) _ reached
  have retained := (PqxdhServerAuthCtxChronology.handler_history setup codec checks context
    (PqxdhServerAuthCtxMaterial.output key rest) Q j query
    (PqxdhServerAuthCtxState.project (state, before.2)) invariant.clean _ reached).1
  intro failed
  have previous : W1 setup context.seed context.scalar state.1.1.ghost ∨
      W2 setup context.seed context.scalar state.1.1.ghost := by
    change result.1.2.1.1.ghost.acceptance = state.1.1.ghost.acceptance at accepted
    simpa only [W1, W2, accepted] using failed
  rcases covered previous with winning | ⟨bytes, input, present⟩
  · exact Or.inl (PqxdhFirstBeaconRecordCanonical.observed_won _ _ _ _ before winning result supported)
  · exact Or.inr ⟨bytes, beaconInput_prefix setup context.seed context.scalar _ _ bytes input grown.touches,
      retained bytes present⟩

/-- Actual complete finish dispatch and designation settlement preserve the proved acceptance alternatives without observing an invented plaintext or assuming the finish succeeds. -/
theorem finish_handler_cover (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (raw : Pqxdh.Bytes)
    (state : PqxdhServerAuthCtxState.Local KemSK)
    (before : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (invariant : PqxdhServerAuthCtxObserverHistory.Joint setup codec context key Q j state before)
    (covered : Covered setup codec context state before.1)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (result : (Option (Option Pqxdh.Bytes) × PqxdhServerAuthCtxState.Local KemSK) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j (.inr (.finish raw))).run.run state)).run before)) :
    Covered setup codec context result.1.2 result.2.1 := by
  change result ∈ support ((simulateQ
    (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto key) (PqxdhServerAuthCtxHandler.settle Q j (.inr (.finish raw)) state <$>
        ((PqxdhServerAuthCtxHandler.route setup codec checks context rest
          (!state.2 && hiddenDesignated Q j (.inr (.finish raw)) state.1)
          (.inr (.finish raw))).run.run state))).run before) at supported
  simp only [PqxdhServerAuthCtxHandler.route, OptionT.run_lift, bind_pure_comp, StateT.run_map,
    Functor.map_map, simulateQ_map, support_map, Set.mem_image] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  have retained := finish_cover setup codec context key rest Q j
    (!state.2 && hiddenDesignated Q j (.inr (.finish raw)) state.1) raw state before invariant covered
    (by
      intro selected
      cases flag : state.2
      · exact invariant.trace.unselected flag
      · simp only [flag, Bool.not_true, Bool.false_and, Bool.false_eq_true] at selected)
    writable inner reached
  unfold PqxdhServerAuthCtxHandler.settle keepHiddenBad
  split <;> exact retained

/-- Every original compiled API operation preserves acceptance coverage on the same full observed execution. -/
theorem handler_cover (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (state : PqxdhServerAuthCtxState.Local KemSK)
    (before : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (ready : PqxdhServerAuthCtxHandler.Ready query (state, before.2))
    (invariant : PqxdhServerAuthCtxObserverHistory.Joint setup codec context key Q j state before)
    (covered : Covered setup codec context state before.1)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (result : (Option (ServerAuthSpec.Range query) × PqxdhServerAuthCtxState.Local KemSK) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j query).run.run state)).run before)) :
    Covered setup codec context result.1.2 result.2.1 := by
  classical
  by_cases finish : ∃ raw, query = .inr (.finish raw)
  · obtain ⟨raw, rfl⟩ := finish
    exact finish_handler_cover setup codec checks context key rest Q j raw state before
      invariant covered writable result supported
  · exact quiet_handler_cover setup codec checks context key rest Q j query
      (fun raw equal => finish ⟨raw, equal⟩) state before ready invariant covered result supported

/-- The actual post-callback checkpoint preserves acceptance coverage, including the complete callback work before an outer stop. -/
theorem stopped_cover (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (state : PqxdhServerAuthCtxState.Local KemSK × Option Nat)
    (before : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (ready : PqxdhServerAuthCtxHandler.Ready query (state.1, before.2))
    (invariant : PqxdhServerAuthCtxObserverHistory.Joint setup codec context key Q j state.1 before)
    (covered : Covered setup codec context state.1 before.1)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (result : (Option (ServerAuthSpec.Range query) × (PqxdhServerAuthCtxState.Local KemSK × Option Nat)) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run state)).run before)) :
    Covered setup codec context result.1.2.1 result.2.1 := by
  simp only [PqxdhServerAuthCtxReserve.stopped, stopped_step, simulateQ_map,
    StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  have retained := handler_cover setup codec checks context key rest Q j query state.1 before ready invariant
    covered writable inner reached
  simpa only [observe_state] using retained

/-- The ordinary interpreted callback supplies the next acceptance alternative from the actual joint source invariant and reservation. -/
theorem interpreted_cover (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (state : PqxdhServerAuthCtxObserverHistory.ObservedState KemSK)
    (invariant : PqxdhServerAuthCtxObserverHistory.Invariant setup codec context key Q j state)
    (covered : Covered setup codec context state.1.1 state.2.1)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (result : Option (ServerAuthSpec.Range query) × PqxdhServerAuthCtxObserverHistory.ObservedState KemSK)
    (supported : result ∈ support ((PqxdhServerAuthCtxObserverHistory.interpreted
      setup codec checks context rest key Q j query).run.run state)) :
    Covered setup codec context result.2.1.1 result.2.2.1 := by
  simp only [PqxdhServerAuthCtxObserverHistory.interpreted, OptionT.run_mk,
    PqxdhSelectedStateInterpreter.evaluate, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact stopped_cover setup codec checks context key rest Q j query state.1 state.2
    (PqxdhServerAuthCtxReserve.valid_ready query (state.1, state.2.2) invariant.1)
    invariant.2 covered writable inner reached

/-- The complete adaptive optional continuation preserves acceptance coverage using the actual source/observer invariant after every continuing reply. -/
theorem program_cover {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) (client : OracleComp ServerAuthSpec α)
    (state : PqxdhServerAuthCtxObserverHistory.ObservedState KemSK)
    (invariant : PqxdhServerAuthCtxObserverHistory.Invariant setup codec context key Q j state)
    (covered : Covered setup codec context state.1.1 state.2.1)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (result : Option α × PqxdhServerAuthCtxObserverHistory.ObservedState KemSK)
    (supported : result ∈ support ((simulateQ
      (PqxdhServerAuthCtxObserverHistory.interpreted setup codec checks context rest key Q j) client).run.run state))
    (answer : α) (continues : result.1 = some answer) :
    Covered setup codec context result.2.1.1 result.2.2.1 := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value =>
    simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact covered
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
      StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, reached, supported⟩ := supported
    cases reply : middle.1 with
    | none =>
      simp only [reply, Option.elim_none, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      cases continues
    | some value =>
      simp only [reply, Option.elim_some] at supported
      exact ih value middle.2
        (PqxdhServerAuthCtxObserverHistory.interpreted_invariant setup codec checks context rest key Q j
          query state invariant middle reached value reply)
        (interpreted_cover setup codec checks context rest key Q j query state invariant covered writable middle reached)
        supported

/-- The actual initial experiment has no acceptance to cover. -/
theorem initial_cover (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) :
    Covered setup codec context (PqxdhServerAuthCtxObserverHistory.initial setup context).1.1
      (PqxdhServerAuthCtxObserverHistory.initial setup context).2.1 := by
  rintro (⟨snap, captured, _⟩ | ⟨snap, captured, _⟩) <;> cases captured

/-- The original adversary's literal complete observed execution derives its acceptance alternative with no supplied trace, origin, selected-freshness or success premise. -/
theorem run_cover (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) (adversary : Adversary)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (result : (Option Unit × (PqxdhServerAuthCtxState.Local KemSK × Option Nat)) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((simulateQ (PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j))
        (adversary (contextInput setup false context))).run.run
        (PqxdhServerAuthCtxObserverHistory.initial setup context).1)).run
      (PqxdhServerAuthCtxObserverHistory.initial setup context).2))
    (continues : result.1.1 = some ()) :
    Covered setup codec context result.1.2.1 result.2.1 := by
  have evaluated : (result.1.1, (result.1.2, result.2)) ∈ support
      ((PqxdhSelectedStateInterpreter.evaluate
        (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
          setup.source.crypto key)
        (simulateQ (PqxdhServerAuthCtxReserve.stopped
          (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j))
          (adversary (contextInput setup false context))).run).run
        (PqxdhServerAuthCtxObserverHistory.initial setup context)) := by
    change (result.1.1, (result.1.2, result.2)) ∈ support (PqxdhSelectedStateInterpreter.pair <$> _)
    rw [support_map]
    exact ⟨result, supported, rfl⟩
  rw [PqxdhServerAuthCtxObserverHistory.program_interpreted] at evaluated
  exact program_cover setup codec checks context rest key Q j _ (PqxdhServerAuthCtxObserverHistory.initial setup context)
    (PqxdhServerAuthCtxObserverHistory.initial_invariant setup codec context key Q j)
    (initial_cover setup codec context) writable _ evaluated () continues

/-- The actual selected input and omission invariant exclude the ordinary-root alternative; every remaining source violation is the same all-attempt observer's ordinary winning event. -/
theorem covered_won (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (state : PqxdhServerAuthCtxState.Local KemSK)
    (observer : RawCtxSelectedAuthenticationObserver.State)
    (covered : Covered setup codec context state observer) (clean : state.1.2.2.Clean)
    (bytes : Pqxdh.Bytes) (hidden : state.1.2.2.hidden = some bytes)
    (input : beaconInput setup context.seed context.scalar state.1.1.ghost.touches = some bytes)
    (failed : W1 setup context.seed context.scalar state.1.1.ghost ∨
      W2 setup context.seed context.scalar state.1.1.ghost) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) observer = true := by
  rcases covered failed with won | ⟨other, inputOther, occupied⟩
  · exact won
  · have same : other = bytes := Option.some.inj (inputOther.symm.trans input)
    subst other
    exact (occupied (clean bytes hidden)).elim

end BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.observed_coin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.observed_coin

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.observed_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.observed_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.derive_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.derive_origins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.rejected_no_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.rejected_no_event

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.known_ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.known_ordinary

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.active_finish_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.active_finish_cover

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.finish_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.finish_cover

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.skeleton_acceptance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.skeleton_acceptance

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.handler_acceptance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.handler_acceptance

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.quiet_handler_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.quiet_handler_cover

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.finish_handler_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.finish_handler_cover

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.handler_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.handler_cover

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.stopped_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.stopped_cover

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.interpreted_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.interpreted_cover

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.program_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.program_cover

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.initial_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.initial_cover

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.run_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.run_cover

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.covered_won' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover.covered_won
