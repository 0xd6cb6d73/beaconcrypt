-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource

/-! The actual hidden seal expressed with an explicit coordinate-tagged private digest query. -/
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw
open CtxRomAuth CtxSplitCache AdaptiveCtxReceive
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (KeyMode CtxPrivate materialAt)
open PqxdhRecordFactsPrivateCache (State sealing)
open PqxdhRecordFactsPrivateCacheFresh (sealResult)
variable {n : Nat}

/-- Exact common digest interface: private coordinate/suffix inputs are separate from ordinary hash bytes. -/
abbrev HashInput (n : Nat) := (Label n × Pqxdh.Bytes) ⊕ Pqxdh.Bytes
abbrev Spec (n : Nat) := (HashInput n →ₒ CtxDigest) + unifSpec

/-- Local fresh-query evaluator; the supplied ordinary hash is preserved and never used by the hidden seal compiler. -/
noncomputable def evaluate (ordinary : Pqxdh.Bytes → ProbComp CtxDigest) : QueryImpl (Spec n) ProbComp
  | .inl (.inl _) => $ᵗ CtxDigest
  | .inl (.inr bytes) => ordinary bytes
  | .inr coin => unifSpec.query coin

/-- Lifted finite coins retain their complete evaluated distribution. -/
theorem evaluate_coins (ordinary : Pqxdh.Bytes → ProbComp CtxDigest) {X : Type} (work : ProbComp X) :
    simulateQ (evaluate (n := n) ordinary) (OracleComp.liftComp work (Spec n)) = work := by
  rw [QueryImpl.simulateQ_liftComp_right_eq_of_apply (evaluate ordinary)
    HasQuery.toQueryImpl (fun _ => rfl)]
  exact QueryImpl.simulateQ_toQueryImpl work

/-- A literal seal with its digest request exposed. The real mode branch is retained only as a total definition; the source equality below is restricted to replay/random modes. -/
noncomputable def compileSeal (crypto : Pqxdh.Crypto) (key : CtxKey) (mode : KeyMode)
    (label : Label n) (input : CtxSealInput) (state : State) :
    OracleComp (Spec n) (Option CtxRomRecord × State) := do
  if mode = .random then
    let body ← OracleComp.liftComp ($ᵗ (FixedBytes input.plaintext.length)) (Spec n)
    let tag ← OracleComp.liftComp ($ᵗ (FixedBytes 16)) (Spec n)
    let digest ← (Spec n).query (.inl (.inl (label, outerSuffix input.nonce input.context tag.toList)))
    pure (sealResult input body.toList tag.toList tag.toList_length digest state)
  else
    let ciphertext := crypto.aeadSeal key.toList input.nonce.toList input.context.ad.bytes input.plaintext
    let digest ← (Spec n).query (.inl (.inl (label, outerSuffix input.nonce input.context ciphertext.2)))
    pure (sealResult input ciphertext.1 ciphertext.2 (crypto.aeadSeal_tag_length _ _ _ _) digest state)

/-- On a virgin local entry the exposed digest query reproduces the whole original erased seal state, in the original order. -/
theorem seal_exact (ordinary : Pqxdh.Bytes → ProbComp CtxDigest)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey) (mode : KeyMode)
    (label : Label n) (input : CtxSealInput) (state : State)
    (supported : mode ≠ .real) (empty : state.1.2 = ∅) (unused : state.1.1.usedNonces = []) :
    simulateQ (evaluate ordinary) (compileSeal crypto key mode label input state) =
      (PqxdhRecordFactsPrivateCacheRandom.erased decode crypto key mode
        (.inl (.inr (.inr input)))).run state := by
  have freshNonce : input.nonce ∉ state.1.1.usedNonces := by simp [unused]
  cases mode with
  | real => exact (supported rfl).elim
  | replay =>
      have same := PqxdhRecordFactsPrivateCacheFresh.sealing_fresh crypto key input state freshNonce
        (by simp [empty])
      rw [PqxdhRecordFactsPrivateCacheRandom.erased,
        PqxdhRecordFactsPrivateCacheRandom.modePointed]
      simp only [StateT.run_map, Functor.map_map]
      rw [show (PqxdhRecordFactsPrivateCacheRandom.linked decode crypto key .replay
        (.inl (.inr (.inr input)))).run state = (sealing crypto key input).run state from
          (PqxdhRecordFactsPrivateCache.sealing_exact decode crypto key input state).symm]
      rw [same]
      simp only [compileSeal, reduceCtorEq, ↓reduceIte, bind_pure_comp, simulateQ_map,
        simulateQ_spec_query, evaluate, Functor.map_map, Prod.eta]
      rfl
  | random =>
      have same := PqxdhRecordFactsPrivateCacheFresh.randomSealing_fresh input state freshNonce
        (fun _ => by simp [empty])
      rw [PqxdhRecordFactsPrivateCacheRandom.erased,
        PqxdhRecordFactsPrivateCacheRandom.modePointed]
      simp only [StateT.run_map, Functor.map_map]
      rw [show (PqxdhRecordFactsPrivateCacheRandom.linked decode crypto key .random
        (.inl (.inr (.inr input)))).run state =
          (PqxdhRecordFactsPrivateCacheRandom.randomSealing input).run state from
          (PqxdhRecordFactsPrivateCacheRandom.randomSealing_exact decode crypto key input state).symm]
      rw [same]
      simp only [compileSeal, ↓reduceIte, simulateQ_bind, evaluate_coins, simulateQ_spec_query,
        evaluate, simulateQ_pure]
      simp only [map_bind, map_pure, Prod.eta]
      rfl

/-- The selected coordinate entry and shared ROM are reinstalled exactly; every unrelated field is retained. -/
noncomputable def compileKeyedSeal (modes : Label n → KeyMode) (crypto : Pqxdh.Crypto)
    (label : Label n) (input : CtxSealInput) (state : CtxPrivate n) :
    OracleComp (Spec n) (Option CtxRomRecord × CtxPrivate n) :=
  (fun result => (result.1, { state with
    base := { state.base with primitive := (state.base.primitive.1, result.2.2) }
    keys := Function.update state.keys label result.2.1 })) <$>
      compileSeal crypto (materialAt state.base.chain label).1 (modes label) label input
        (state.keys label, state.base.primitive.2)

/-- A fresh selected entry gives the exact full keyed-state equality. -/
theorem keyedSeal_exact (ordinary : Pqxdh.Bytes → ProbComp CtxDigest)
    (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (label : Label n) (input : CtxSealInput) (state : CtxPrivate n)
    (supported : modes label ≠ .real) (empty : (state.keys label).2 = ∅)
    (unused : (state.keys label).1.usedNonces = []) :
    simulateQ (evaluate ordinary) (compileKeyedSeal modes crypto label input state) =
      (PqxdhRecordFactsPrivateCacheFamily.erasedKeyed modes decode crypto
        (label, .inl (.inr (.inr input)))).run state := by
  rw [compileKeyedSeal, simulateQ_map, seal_exact ordinary decode crypto _ _ _ _ _ supported empty unused,
    PqxdhRecordFactsPrivateCacheSource.erasedKeyed_run]
  rfl

/-- The original hidden seal with its explicit private digest query, including narrow-input rejection and the literal failed-writer frame buffer. -/
noncomputable def compileHiddenSeal (modes : Label n → KeyMode) (crypto : Pqxdh.Crypto)
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (state : CtxPrivate n) :
    OracleComp (Spec n) (Option RawCtxSourceSend.Encrypted × CtxPrivate n) :=
  if width : (PqxdhRecordLiftIdeal.replaceContext replace pending.context).associatedData.length = 281 then do
    let result ← compileKeyedSeal modes crypto pending.material
      (RawCtxSelectedMessageSealing.selectedInput (materialAt state.base.chain pending.material).2
        pending.sequence (PqxdhRecordLiftIdeal.replaceContext replace pending.context) width) state
    match result.1 with
    | none => pure (none, { result.2 with base := { result.2.base with pending := state.base.pending } })
    | some record =>
        let frame : RawCtxReceive.DecodedFrame := ⟨pending.sequence, pending.context.senderId, record.encode⟩
        pure ((writer frame).map fun ciphertext => ⟨ciphertext, pending.context.targetId, pending.sequence⟩,
          { result.2 with base := { result.2.base with pending := state.base.pending ++ [frame] } })
  else pure (none, state)

private theorem apply_bind {S X Y : Type} (work : StateT S ProbComp X)
    (next : X → StateT S ProbComp Y) (state : S) :
    (work >>= next) state = work state >>= fun result => next result.1 result.2 := rfl

private theorem apply_pure {S X : Type} (value : X) (state : S) :
    (pure value : StateT S ProbComp X) state = pure (value, state) := rfl

open PqxdhServerAuthExperiment (Setup Codec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The complete hidden service equality follows from its pre-query freshness, before the writer or endpoint replies. -/
theorem hiddenSeal_exact (ordinary : Pqxdh.Bytes → ProbComp CtxDigest)
    (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (state : CtxPrivate n)
    (supported : modes pending.material ≠ .real)
    (fresh : PqxdhRecordFactsPrivateCacheSource.FreshPoint state (.sealing pending)) :
    simulateQ (evaluate ordinary)
      (compileHiddenSeal modes setup.source.crypto codec.frameWrite replace pending state) =
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.sealing pending)).run state := by
  change _ = (simulateQ
    (PqxdhRecordFactsPrivateCacheServices.erased modes _ setup.source.crypto
      (PqxdhRecordFactsPrivateCacheCompiler.base
        (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec)))
    (PqxdhRecordFactsPrivateCacheCompiler.compile codec.frameWrite replace (.sealing pending))).run state
  rw [PqxdhRecordFactsPrivateCacheSource.erased_sealing]
  unfold compileHiddenSeal PqxdhRecordLiftIdeal.hiddenSealing
  split
  · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run, apply_bind]
    rw [keyedSeal_exact ordinary modes (RawCtxUniversalDecoder.decoder codec.frameRead) _ _ _ _
      supported fresh.1 fresh.2]
    simp only [StateT.run, bind_assoc]
    refine bind_congr fun result => ?_
    cases reply : result.1 <;> simp only [simulateQ_pure, apply_pure, pure_bind]
  · simp only [StateT.run, simulateQ_pure, apply_pure, pure_bind]

/-- Only the hidden sealing callback is exposed here. All other source services execute their actual erased endpoint and retain their full costs. -/
noncomputable def service (ordinary : Pqxdh.Bytes → ProbComp CtxDigest)
    (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT (CtxPrivate n) ProbComp)
  | .sealing pending => fun state => simulateQ (evaluate ordinary)
      (compileHiddenSeal modes setup.source.crypto codec.frameWrite replace pending state)
  | query => PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec query

/-- Under the actual pre-query condition the modified service returns the exact reply and state of every source constructor. -/
theorem service_exact (ordinary : Pqxdh.Bytes → ProbComp CtxDigest)
    (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : PqxdhRecordLiftProtocol.Service n) (state : CtxPrivate n)
    (supported : ∀ label, modes label ≠ .real)
    (fresh : PqxdhRecordFactsPrivateCacheSource.FreshPoint state query) :
    (service ordinary modes replace setup codec query).run state =
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec query).run state := by
  cases query with
  | sealing pending => exact hiddenSeal_exact ordinary modes replace setup codec pending state (supported _) fresh
  | _ => rfl

/-- Through a complete adaptive service continuation the explicit digest callback is exact, deriving each cache miss from the original attempted-coordinate history. -/
theorem program_exact (ordinary : Pqxdh.Bytes → ProbComp CtxDigest)
    (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (supported : ∀ label, modes label ≠ .real) {Result : Type}
    (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result)
    (state : CtxPrivate n) (past : List (Label n))
    (good : PqxdhRecordFactsPrivateCacheSource.Virgin state past)
    (fresh : (PqxdhRecordLiftProtocolHistory.annotated client past).AllQueriesSatisfy
      PqxdhRecordLiftProtocolHistory.Fresh) :
    (simulateQ (service ordinary modes replace setup codec) client).run state =
      (simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) client).run state := by
  induction client using OracleComp.inductionOn generalizing state past with
  | pure value => rfl
  | query_bind query next ih =>
      rw [PqxdhRecordLiftProtocolHistory.annotated_query_bind, allQueriesSatisfy_query_bind_iff] at fresh
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [service_exact ordinary modes replace setup codec query state supported
        (PqxdhRecordFactsPrivateCacheSource.freshPoint query state past good fresh.1)]
      apply bind_congr_of_forall_mem_support
      intro result reached
      exact ih result.1 result.2 _
        (PqxdhRecordFactsPrivateCacheSource.query_virgin modes replace setup codec query state past good result reached)
        (fresh.2 result.1)

open PqxdhRecordLiftInterface (Environment)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)

/-- The actual initialized source schedule satisfies the callback equality without an added freshness premise. -/
theorem source_exact {E X : Type} (ordinary : Pqxdh.Bytes → ProbComp CtxDigest)
    (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Aeneas.Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (supported : ∀ label, modes label ≠ .real) :
    (simulateQ (service ordinary modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) =
      PqxdhRecordFactsPrivateCacheWorld.erasedRun modes replace setup codec route env serverKid bounds mode adversary :=
  program_exact ordinary modes replace setup codec supported _ _ []
    PqxdhRecordFactsPrivateCacheSource.initial_virgin
    (PqxdhRecordLiftProtocolHistory.program_fresh env setup.source.crypto codec route serverKid bounds mode adversary)

/-- A seal may query only its own private digest address and finite coins. Ordinary hashes are absent from this compiler. -/
def Addressed (label : Label n) : (Spec n).Domain → Prop
  | .inl (.inl address) => address.1 = label
  | .inl (.inr _) => False
  | .inr _ => True

private theorem coins_addressed (label : Label n) {X : Type} (work : ProbComp X) :
    (OracleComp.liftComp work (Spec n)).AllQueriesSatisfy (Addressed label) := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [OracleComp.liftComp_pure, allQueriesSatisfy_pure]
  | query_bind coin next ih =>
      rw [OracleComp.liftComp_bind, OracleComp.liftComp_query]
      change ((liftM ((Spec n).query (.inr coin)) : OracleComp (Spec n) _) >>= _).AllQueriesSatisfy _
      rw [allQueriesSatisfy_query_bind_iff]
      exact ⟨True.intro, ih⟩

/-- The concrete private address is chosen before the returned digest and remains within the selected coordinate. -/
theorem seal_addressed (crypto : Pqxdh.Crypto) (key : CtxKey) (mode : KeyMode)
    (label : Label n) (input : CtxSealInput) (state : State) :
    (compileSeal crypto key mode label input state).AllQueriesSatisfy (Addressed label) := by
  unfold compileSeal
  split
  · apply allQueriesSatisfy_bind (coins_addressed label _)
    intro body
    apply allQueriesSatisfy_bind (coins_addressed label _)
    intro tag
    simp only [allQueriesSatisfy_query_bind_iff, Addressed, allQueriesSatisfy_pure, and_self, implies_true]
  · simp only [allQueriesSatisfy_query_bind_iff, Addressed, allQueriesSatisfy_pure, and_self, implies_true]

private theorem coins_total {X : Type} (work : ProbComp X) (cap : Nat)
    (bounded : work.IsTotalQueryBound cap) :
    (OracleComp.liftComp work (Spec n)).IsTotalQueryBound cap := by
  induction work using OracleComp.inductionOn generalizing cap with
  | pure value => trivial
  | query_bind coin next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      rw [OracleComp.liftComp_bind, OracleComp.liftComp_query]
      change ((liftM ((Spec n).query (.inr coin)) : OracleComp (Spec n) _) >>= _).IsTotalQueryBound cap
      rw [isTotalQueryBound_query_bind_iff]
      exact ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply)⟩

/-- Exact local source query allowance: one digest query, plus plaintext-length body coins and sixteen tag coins in random mode. Digest interpretation and ambient source costs are additional obligations. -/
theorem seal_queries (crypto : Pqxdh.Crypto) (key : CtxKey) (mode : KeyMode)
    (label : Label n) (input : CtxSealInput) (state : State) :
    (compileSeal crypto key mode label input state).IsTotalQueryBound
      (if mode = .random then input.plaintext.length + 16 + 1 else 1) := by
  unfold compileSeal
  split
  · rw [Nat.add_assoc]
    apply isTotalQueryBound_bind
      (coins_total _ _ (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound input.plaintext.length))
    intro body
    apply isTotalQueryBound_bind
      (coins_total _ _ (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 16))
    intro tag
    simp [IsTotalQueryBound]
  · simp [IsTotalQueryBound]

/-- Hash requests, independently of the separate finite-coin bill. -/
def digestQuery : (Spec n).Domain → Bool
  | .inl _ => true
  | .inr _ => false

private theorem coins_no_digest {X : Type} (work : ProbComp X) :
    (OracleComp.liftComp work (Spec n)).IsQueryBoundP (fun query => digestQuery query) 0 := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind coin next ih =>
      rw [OracleComp.liftComp_bind, OracleComp.liftComp_query]
      change ((liftM ((Spec n).query (.inr coin)) : OracleComp (Spec n) _) >>= _).IsQueryBoundP _ 0
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp [digestQuery]), ih⟩

/-- At most one explicit digest query occurs, even with adaptive finite-coin replies. -/
theorem seal_digest_queries (crypto : Pqxdh.Crypto) (key : CtxKey) (mode : KeyMode)
    (label : Label n) (input : CtxSealInput) (state : State) :
    (compileSeal crypto key mode label input state).IsQueryBoundP (fun query => digestQuery query) 1 := by
  unfold compileSeal
  split
  · apply isQueryBoundP_bind (n := 0) (m := 1) (coins_no_digest _)
    intro body _
    apply isQueryBoundP_bind (n := 0) (m := 1) (coins_no_digest _)
    intro tag _
    simp [digestQuery]
  · simp [digestQuery]

/-- The entire hidden sealing service exposes only the original selected coordinate, never ordinary hash queries. -/
theorem hiddenSeal_addressed (modes : Label n → KeyMode) (crypto : Pqxdh.Crypto)
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (state : CtxPrivate n) :
    (compileHiddenSeal modes crypto writer replace pending state).AllQueriesSatisfy (Addressed pending.material) := by
  unfold compileHiddenSeal
  split
  · apply allQueriesSatisfy_bind
    · unfold compileKeyedSeal AllQueriesSatisfy
      rw [isQueryBound_map_iff]
      exact seal_addressed crypto _ _ _ _ _
    · intro result
      cases result.1 <;> exact allQueriesSatisfy_pure _ _
  · exact allQueriesSatisfy_pure _ _

/-- Narrow rejection and writer outcomes add no digest request; the complete hidden compiler has cap one. -/
theorem hiddenSeal_digest_queries (modes : Label n → KeyMode) (crypto : Pqxdh.Crypto)
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (state : CtxPrivate n) :
    (compileHiddenSeal modes crypto writer replace pending state).IsQueryBoundP (fun query => digestQuery query) 1 := by
  unfold compileHiddenSeal
  split
  · apply isQueryBoundP_bind (n := 1) (m := 0)
    · unfold compileKeyedSeal
      rw [isQueryBoundP_map_iff]
      exact seal_digest_queries crypto _ _ _ _ _
    · intro result _
      cases result.1 <;> exact isQueryBoundP_pure _ _ _
  · exact isQueryBoundP_pure _ _ _

/-- The complete hidden compiler retains the full local query allowance, including every random body and tag byte. One interpreted digest still costs its separately charged 64 uniform byte queries. -/
theorem hiddenSeal_queries (modes : Label n → KeyMode) (crypto : Pqxdh.Crypto)
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (state : CtxPrivate n) :
    (compileHiddenSeal modes crypto writer replace pending state).IsTotalQueryBound
      (if modes pending.material = .random then (replace pending.context.plaintext).length + 16 + 1 else 1) := by
  unfold compileHiddenSeal
  split
  · have keyBound := seal_queries crypto (materialAt state.base.chain pending.material).1
      (modes pending.material) pending.material
      (RawCtxSelectedMessageSealing.selectedInput (materialAt state.base.chain pending.material).2
        pending.sequence (PqxdhRecordLiftIdeal.replaceContext replace pending.context) (by assumption))
      (state.keys pending.material, state.base.primitive.2)
    have selectedBound : (compileKeyedSeal modes crypto pending.material _ state).IsTotalQueryBound _ :=
      (isQueryBound_map_iff _ _ _ _ _).mpr keyBound
    apply (show _ = _ + 0 from (Nat.add_zero _).symm) ▸
      isTotalQueryBound_bind selectedBound ?_
    intro result
    cases result.1 <;> trivial
  · trivial

end BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw.evaluate_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw.evaluate_coins
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw.seal_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw.seal_exact
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw.keyedSeal_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw.keyedSeal_exact
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw.hiddenSeal_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw.hiddenSeal_exact
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw.service_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw.service_exact
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw.program_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw.program_exact
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw.source_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw.source_exact
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw.seal_addressed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw.seal_addressed
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw.seal_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw.seal_queries
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw.seal_digest_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw.seal_digest_queries
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw.hiddenSeal_addressed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw.hiddenSeal_addressed
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw.hiddenSeal_digest_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw.hiddenSeal_digest_queries
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw.hiddenSeal_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw.hiddenSeal_queries
