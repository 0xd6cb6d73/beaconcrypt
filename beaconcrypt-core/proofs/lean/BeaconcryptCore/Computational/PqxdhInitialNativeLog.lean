import BeaconcryptCore.Computational.PqxdhInitialPostContext
import BeaconcryptCore.Computational.PqxdhInitialBeaconAmbient
import BeaconcryptCore.Computational.RawCtxSelectiveFamilyLog

/-!
The full pending source interpreter retains the selective private table, cursor and chronological input log together with the original shared primitive state, private identity state and root cache. Actual preparation, application, initializer, selector and publication callbacks run in their original ambient interface. They cannot overwrite the separate selective table or its input history. The log records executed private steps after their replies, so an unexecuted selected request is not counted as an earlier input.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialNativeLog
open PqxdhJointKdf PqxdhJointKdfGame PqxdhInitialBeaconAmbient
variable {ι I D K X Response Shared A N C Result : Type} {extra : OracleSpec ι} {S B : Nat}
abbrev Spec := @PqxdhInitialPendingPost.Spec ι
abbrev External := @PqxdhInitialPendingPost.External ι
abbrev State (A N C : Type) := RawCtxSelectiveFamilyLog.LoggedState A × (N × C)
abbrev Bare (A N C : Type) := RawCtxPendingSelectiveFamily.State A × (N × C)

def erase (state : State A N C) : Bare A N C := (state.1.1, state.2)

def liftExternal {α : Type} (work : Ambient A N C α) : StateT (Bare A N C) ProbComp α :=
  fun state => do
    let result ← (work (state.1.1, state.2.1)).run state.2.2
    pure (result.1.1, ((result.1.2.1, state.1.2), (result.1.2.2, result.2)))

noncomputable def bare (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C)) :
    QueryImpl (Spec extra RatchetChain I D K X Response Shared S B) (StateT (Bare A N C) ProbComp)
  | .inl query => fun state => do
      let result ← (RawCtxPendingSelectiveFamily.handler source writer stage query).run state.1
      pure (result.1, (result.2, state.2))
  | .inr query => liftExternal (external query)

def inputs (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain)
    (past : List JointKdfAddress) : List JointKdfAddress :=
  match query with
  | .inl query => RawCtxSelectiveFamilyLog.inputs query past
  | .inr _ => past

noncomputable def handler (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C)) :
    QueryImpl (Spec extra RatchetChain I D K X Response Shared S B) (StateT (State A N C) ProbComp) :=
  fun query state => do
    let result ← (bare source writer stage external query).run (erase state)
    pure (result.1, ((result.2.1, inputs query state.1.2), result.2.2))

/-- Erasing only the private chronological list recovers the full original interpreter execution, including external callback effects, private table and both ambient state components. -/
theorem program_projection (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B) Result) (state : State A N C) :
    Prod.map id erase <$> ((simulateQ (handler source writer stage external) client).run state) =
      (simulateQ (bare source writer stage external) client).run (erase state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure result => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      simp only [handler, StateT.run, map_bind, bind_assoc, pure_bind]
      exact bind_congr fun result => ih result.1 ((result.2.1, inputs query state.1.2), result.2.2)

def Covered (state : State A N C) : Prop := RawCtxSelectiveFamilyLog.Covered state.1

/-- The original enriched LIVE callback keeps exactly its existing logged interpreter and preserves the private identity and root cache. -/
theorem live_handler (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (query : (RawCtxPendingSelectiveFamily.Spec S B).Domain) (state : State A N C) :
    (handler source writer stage external (.inl query)).run state =
      (fun result => (result.1, (result.2, state.2))) <$>
        (RawCtxSelectiveFamilyLog.handler source writer stage query).run state.1 := by
  simp only [handler, bare, erase, StateT.run, inputs, RawCtxSelectiveFamilyLog.handler,
    bind_assoc, pure_bind, map_bind, map_pure]
  rfl

/-- An actual external callback retains the complete selective table and prior-input list while updating the actual shared, identity and root-cache state. -/
theorem external_handler (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (query : (External extra RatchetChain I D K X Response Shared).Domain) (state : State A N C) :
    (handler (S := S) (B := B) source writer stage external (.inr query)).run state =
      (fun result => (result.1.1, (((result.1.2.1, state.1.1.2), state.1.2), (result.1.2.2, result.2)))) <$>
        ((external query (state.1.1.1, state.2.1)).run state.2.2) := by
  simp only [handler, bare, erase, liftExternal, StateT.run, inputs, bind_pure_comp, Functor.map_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every supported callback preserves actual cache-input provenance over the full source interface. -/
theorem step_covered (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain) (state : State A N C)
    (covered : Covered state)
    (result : (Spec extra RatchetChain I D K X Response Shared S B).Range query × State A N C)
    (supported : result ∈ support ((handler source writer stage external query).run state)) : Covered result.2 := by
  cases query with
  | inl query =>
      rw [live_handler] at supported
      simp only [support_map, Set.mem_image] at supported
      obtain ⟨reply, actual, rfl⟩ := supported
      exact RawCtxSelectiveFamilyLog.step_covered source writer stage query state.1 covered reply actual
  | inr query =>
      rw [external_handler] at supported
      simp only [support_map, Set.mem_image] at supported
      obtain ⟨reply, actual, rfl⟩ := supported
      exact covered

/-- Actual empty selective storage is covered without enumerating or assuming any earlier input. -/
theorem empty_covered (primitive : RawCtxSharedPrimitive.SharedState A) (cursor : RawCtxSelectiveChainGame.Cursor)
    (past : List JointKdfAddress) (privateState : N) (cache : C) :
    Covered (((primitive, ((fun _ => none), cursor)), past), (privateState, cache)) :=
  RawCtxSelectiveFamilyLog.empty_covered primitive cursor past

/-- Every completed source execution derives its private-cache provenance from the same actual callback history. -/
theorem program_covered (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B) Result)
    (state : State A N C) (covered : Covered state) (result : Result × State A N C)
    (supported : result ∈ support ((simulateQ (handler source writer stage external) client).run state)) :
    Covered result.2 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact covered
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, head, tail⟩ := supported
      exact ih reply.1 reply.2 (step_covered source writer stage external query state covered reply head) result tail

/-- A source prefix retains the same chronological cache provenance whether it completes or stops before the original dependent callback. -/
theorem scan_covered (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (selected : (Spec extra RatchetChain I D K X Response Shared S B).Domain → State A N C → Bool)
    (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B) Result)
    (state : State A N C) (covered : Covered state)
    (result : RawCtxPendingMixedPrefix.Prefix (Spec extra RatchetChain I D K X Response Shared S B) Result (State A N C))
    (supported : result ∈ support (RawCtxStatefulPendingPrefix.scan selected (handler source writer stage external) client state)) :
    Covered result.2 :=
  RawCtxStatefulPrefixInvariant.scan_valid selected (handler source writer stage external) Covered
    (fun query before valid _ reply head => step_covered source writer stage external query before valid reply head)
    client state covered result supported

end BeaconcryptCore.Computational.PqxdhInitialNativeLog

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeLog.program_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeLog.program_projection
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeLog.live_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeLog.live_handler
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeLog.external_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeLog.external_handler
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeLog.step_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeLog.step_covered
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeLog.empty_covered' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeLog.empty_covered
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeLog.program_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeLog.program_covered
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeLog.scan_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeLog.scan_covered
