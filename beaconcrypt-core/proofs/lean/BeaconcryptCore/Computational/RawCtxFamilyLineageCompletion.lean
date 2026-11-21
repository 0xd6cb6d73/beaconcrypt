import BeaconcryptCore.Computational.RawCtxFiniteLineageCheck

/-!
The finite lineage checker runs after the complete original family continuation has stopped. It uses the same private derivation interface and candidate ledger, returns no adversary reply, and retains the entire original family, history and shared primitive state. Its extra private calls are reduction bookkeeping, not free source operations. The final freshness event is derived from this actual checked execution.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxFamilyLineageCompletion
open RawCtxSelectedChain RawCtxFamilySourceFreshness RawCtxFamilyPendingCompiler
open RawCtxFamilyCompletionFreshness RawCtxFamilyFreshnessProxy
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf
variable {M P I D K A Value : Type} {S B : Nat}

def derivation : QueryImpl (RawCtxFiniteLineageCheck.Spec Slot) (OracleComp PrimitiveSpec) :=
  fun input => PrimitiveSpec.query (.inl (.inl input))

def forward : QueryImpl (RawCtxFiniteLineageCheck.Spec Slot) (OracleComp Spec) :=
  RawCtxSelectedLiveCompiler.primitiveForward ∘ₛ derivation

noncomputable def checker (n : Nat) : OracleComp Spec (List Slot) :=
  simulateQ forward (RawCtxFiniteLineageCheck.program RawCtxFiniteLineageCheck.labelKey n .hidden)

noncomputable def checked (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (history : RawCtxProtocolReveals.History S B)
    (outside : Value → OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool)
    (work : OracleComp PrimitiveSpec (Value × Roles M P I D K S B)) (n : Nat) :
    OracleComp Spec ((Bool × State M P I D K S B) × List Slot) := do
  let original ← completion sender route decode history outside work
  let lineage ← checker n
  pure (original, lineage)

/-- The appended checker is literally a forwarded non-read primitive program, so it shares every candidate and preserves the actual disclosure flag. -/
theorem checker_primitive (n : Nat) : checker n =
    simulateQ RawCtxSelectedLiveCompiler.primitiveForward
      (simulateQ derivation (RawCtxFiniteLineageCheck.program RawCtxFiniteLineageCheck.labelKey n .hidden)) := by
  rw [checker, forward, QueryImpl.simulateQ_compose]

/-- The original source-derived disclosure invariant survives all appended checker operations, with every earlier candidate and the original family history retained. -/
theorem checked_invariant (parameters : Parameters) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (prior : List RatchetChain) (history : RawCtxProtocolReveals.History S B)
    (outside : Value → OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool)
    (work : OracleComp PrimitiveSpec (Value × Roles M P I D K S B)) (n : Nat)
    (state : RawCtxSharedPrimitive.SharedState A) (candidates : List RootOutput)
    (result : ((Bool × State M P I D K S B) × List Slot) × RawCtxSelectedParentLive.State A)
    (supported : result ∈ support ((simulateQ (observed parameters)
      (checked sender route decode history outside work n)).run (initial prior history state candidates))) :
    Invariant parameters.target prior (result.1.1.2, result.2) := by
  simp only [checked, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
    simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
  obtain ⟨original, before, tail, after, rfl⟩ := supported
  have keep := prefix_state parameters (simulateQ derivation
    (RawCtxFiniteLineageCheck.program RawCtxFiniteLineageCheck.labelKey n .hidden)) original.2 tail
    (by simpa only [checker_primitive] using after)
  have established := completion_invariant parameters sender route decode prior history outside work state candidates original before
  exact ⟨fun exposed => established.1 (keep.1 ▸ exposed),
    fun clear => List.Subset.trans (established.2 (keep.1 ▸ clear)) keep.2⟩

/-- Every complete checked execution retains the hidden input in its returned finite lineage, under either actual or masked primitive callbacks. -/
theorem checked_contains {Store : Type} (backend : QueryImpl Spec (StateT Store ProbComp))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (history : RawCtxProtocolReveals.History S B)
    (outside : Value → OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool)
    (work : OracleComp PrimitiveSpec (Value × Roles M P I D K S B)) (n : Nat)
    (state : Store) (result : ((Bool × State M P I D K S B) × List Slot) × Store)
    (supported : result ∈ support ((simulateQ backend
      (checked sender route decode history outside work n)).run state)) : Slot.hidden ∈ result.1.2 := by
  simp only [checked, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
    simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
  obtain ⟨original, _, tail, after, rfl⟩ := supported
  exact RawCtxFiniteLineageCheck.returned_contains RawCtxFiniteLineageCheck.labelKey
    (backend ∘ₛ forward) n .hidden original.2 tail
    (by simpa only [checker, QueryImpl.simulateQ_compose] using after)

/-- The returned checker supplies the exact native value-freshness condition while retaining every earlier ancestor and every repeated known value. -/
theorem checked_fresh (parameters : Parameters) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (earlier prior : List RatchetChain) (history : RawCtxProtocolReveals.History S B)
    (outside : Value → OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool)
    (work : OracleComp PrimitiveSpec (Value × Roles M P I D K S B)) (n : Nat)
    (state : RawCtxSharedPrimitive.SharedState A) (candidates : List RootOutput)
    (result : ((Bool × State M P I D K S B) × List Slot) × RawCtxSelectedParentLive.State A)
    (supported : result ∈ support ((simulateQ (observed parameters)
      (checked sender route decode history outside work n)).run (initial prior history state candidates))) :
    RawCtxLiveLineage.Fresh
      (result.1.2.map (interpret (RawCtxFreshChainCut.concreteChain parameters.target)) ++ earlier) prior result.1.1.2.2 ↔
    RawCtxLiveLineage.Fresh
      (RawCtxFreshChainCut.concreteChain parameters.target :: RawCtxFiniteLineageCheck.knownValues result.1.2 ++ earlier) prior result.1.1.2.2 := by
  have hidden := checked_contains (observed parameters) sender route decode history outside work n
    (initial prior history state candidates) result supported
  unfold RawCtxLiveLineage.Fresh RawCtxLiveLineage.FreshValues
  apply forall_congr'
  intro value
  simp only [List.mem_append, List.mem_cons, RawCtxFiniteLineageCheck.interpreted_mem, hidden, and_true, or_assoc]

/-- Outside the same final candidate event, original value freshness for the entire returned checker and prior ancestors is exactly its target-free proxy. -/
theorem checked_fresh_proxy (parameters : Parameters) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (earlier prior : List RatchetChain) (history : RawCtxProtocolReveals.History S B)
    (outside : Value → OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool)
    (work : OracleComp PrimitiveSpec (Value × Roles M P I D K S B)) (n : Nat)
    (state : RawCtxSharedPrimitive.SharedState A) (candidates : List RootOutput)
    (result : ((Bool × State M P I D K S B) × List Slot) × RawCtxSelectedParentLive.State A)
    (supported : result ∈ support ((simulateQ (observed parameters)
      (checked sender route decode history outside work n)).run (initial prior history state candidates)))
    (safe : parameters.target ∉ result.2.1.2) :
    RawCtxLiveLineage.Fresh
      (result.1.2.map (interpret (RawCtxFreshChainCut.concreteChain parameters.target)) ++ earlier) prior result.1.1.2.2 ↔
      Proxy (RawCtxFiniteLineageCheck.knownValues result.1.2 ++ earlier) prior result.1.1.2.2 result.2.2 := by
  rw [checked_fresh parameters sender route decode earlier prior history outside work n state candidates result supported]
  have after := checked_invariant parameters sender route decode prior history outside work n state candidates result supported
  exact fresh_proxy parameters.target _ prior result.1.1.2.2 result.2.2 after.1
    (fun clear present => safe (after.2 clear present))

/-- The checker calls precisely the same private derivation operation as receive, including actual byte-alias routing and the full supplied response. -/
theorem derivation_response (parameters : Parameters) (input : Slot) :
    ((handler (A := A) parameters) ∘ₛ forward) input =
      pure (RawCtxFiniteLineageCheck.routedStep parameters.prior parameters.entry parameters.target parameters.output input) := by
  simp [QueryImpl.compose, forward, derivation, RawCtxSelectedLiveCompiler.primitiveForward]
  cases input
  all_goals first | exact RawCtxSelectedParentPrivate.hidden_receive _ _ _ _ _ _ _ _ |
    exact RawCtxSelectedParentPrivate.known_receive _ _ _ _ _ _ _ _ _

/-- Without erasing any primitive state, the appended checker evaluates the actual routed private derivation function. -/
theorem checker_evaluate (parameters : Parameters) (n : Nat) :
    simulateQ (handler (A := A) parameters) (checker n) =
      pure (RawCtxFiniteLineageCheck.trace RawCtxFiniteLineageCheck.labelKey
        (RawCtxFiniteLineageCheck.routedStep parameters.prior parameters.entry parameters.target parameters.output) n .hidden) := by
  rw [checker, ← QueryImpl.simulateQ_compose, funext (derivation_response parameters)]
  exact RawCtxFiniteLineageCheck.evaluate RawCtxFiniteLineageCheck.labelKey
    (RawCtxFiniteLineageCheck.routedStep parameters.prior parameters.entry parameters.target parameters.output) n Slot.hidden

/-- Erasing only private candidate and disclosure instrumentation preserves every callback result and complete shared primitive state. -/
theorem recording_erasure {Result : Type} (parameters : Parameters) (program : OracleComp Spec Result)
    (state : RawCtxSelectedParentLive.State A) :
    (fun result => (result.1, result.2.1.1)) <$> (simulateQ (observed parameters) program).run state =
      (simulateQ (handler parameters) program).run state.1.1 := by
  apply map_run_simulateQ_eq_of_query_map_eq (observed parameters) (handler parameters) (fun before => before.1.1)
  intro query before
  simp [observed, RawCtxSelectedParentPrivate.observed, RawCtxFlaggedQueryTrace.trace, handler,
    StateT.run, bind_pure_comp, Functor.map_map]

/-- Every actual returned checker list interprets to the entire native private lineage, using the same patched private function and retaining the selected material key. -/
theorem checker_native (parameters : Parameters) (n : Nat)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress parameters.target ≠ parameters.entry.address)
    (state : RawCtxSelectedParentLive.State A) (result : List Slot × RawCtxSelectedParentLive.State A)
    (supported : result ∈ support ((simulateQ (observed parameters) (checker n)).run state)) :
    result.1.map (interpret (RawCtxFreshChainCut.concreteChain parameters.target)) =
      RawCtxFiniteLineageCheck.trace RawCtxFiniteLineageCheck.nativeKey
        (RawCtxSelectedParentTable.nativeStep
          (RawCtxSelectedParentPrivatePatch.privatePatch parameters.prior parameters.target parameters.output)
          parameters.entry parameters.target) n (RawCtxFreshChainCut.concreteChain parameters.target) := by
  have mapped : (result.1, result.2.1.1) ∈ support
      ((fun reply => (reply.1, reply.2.1.1)) <$> (simulateQ (observed parameters) (checker n)).run state) := by
    rw [support_map]
    exact ⟨result, supported, rfl⟩
  rw [recording_erasure, checker_evaluate, StateT.run_pure, mem_support_pure_iff] at mapped
  rw [congrArg Prod.fst mapped]
  exact RawCtxFiniteLineageCheck.native_trace parameters.prior parameters.entry parameters.target parameters.output separate n .hidden

end BeaconcryptCore.Computational.RawCtxFamilyLineageCompletion

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyLineageCompletion.checker_primitive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyLineageCompletion.checker_primitive

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyLineageCompletion.checked_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyLineageCompletion.checked_invariant

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyLineageCompletion.checked_contains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyLineageCompletion.checked_contains

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyLineageCompletion.checked_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyLineageCompletion.checked_fresh

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyLineageCompletion.checked_fresh_proxy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyLineageCompletion.checked_fresh_proxy

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyLineageCompletion.derivation_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyLineageCompletion.derivation_response

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyLineageCompletion.checker_evaluate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyLineageCompletion.checker_evaluate

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyLineageCompletion.recording_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyLineageCompletion.recording_erasure

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyLineageCompletion.checker_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyLineageCompletion.checker_native
