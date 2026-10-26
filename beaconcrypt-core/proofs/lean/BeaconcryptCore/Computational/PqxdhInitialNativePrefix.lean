import BeaconcryptCore.Computational.PqxdhInitialNativeLog
import BeaconcryptCore.Computational.RawCtxFirstParentPrefix

/-!
The complete post interface uses the original first-hit/predecessor selector. External preparation, initializer, application, selector and publication callbacks preserve its private cursor. Both adjacent evolving-chain stages therefore share the same complete source prefix, including retained private identity and root-cache state. Cache hits remain explicit collision branches; they are not resampled as uniform predecessors.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialNativePrefix
open PqxdhJointKdf PqxdhJointKdfGame PqxdhInitialBeaconAmbient PqxdhInitialNativeLog
variable {ι I D K X Response Shared A N C Result : Type} {extra : OracleSpec ι} {S B : Nat}

def selected (depth : Nat) : (Spec extra RatchetChain I D K X Response Shared S B).Domain → State A N C → Bool
  | .inl query, state => RawCtxFirstParentPrefix.selected depth query state.1
  | .inr _, _ => false

def Depth (depth : Nat) (state : State A N C) : Prop := state.1.1.2.2.depth ≤ depth

/-- Every callback before the predecessor depth has exactly the same complete evaluated computation in the two adjacent private-table stages. -/
theorem step_same (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain) (state : State A N C)
    (valid : Depth depth state) :
    (handler source writer (depth + 1) external query).run state =
      (handler source writer (depth + 2) external query).run state := by
  cases query with
  | inl query =>
      simp only [handler, bare, erase, StateT.run, bind_pure_comp, Functor.map_map]
      exact congrArg (fun work => (fun result =>
        (result.1, ((result.2, inputs (.inl query) state.1.2), state.2))) <$> work)
        (RawCtxPendingSelectiveFamily.handler_same source writer (depth + 1) query state.1.1
          (RawCtxPendingParentCallbacks.before_child depth query state.1.1 valid))
  | inr query => rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every actually executed unselected callback preserves the predecessor depth, including all original external effects. -/
theorem step_preserve (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage depth : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain) (state : State A N C)
    (valid : Depth depth state) (unchosen : selected depth query state = false)
    (result : (Spec extra RatchetChain I D K X Response Shared S B).Range query × State A N C)
    (supported : result ∈ support ((handler source writer stage external query).run state)) : Depth depth result.2 := by
  cases query with
  | inl query =>
      rw [live_handler] at supported
      simp only [support_map, Set.mem_image] at supported
      obtain ⟨logged, actual, rfl⟩ := supported
      simp only [RawCtxSelectiveFamilyLog.handler, StateT.run, bind_pure_comp, support_map, Set.mem_image] at actual
      obtain ⟨reply, actual, rfl⟩ := actual
      exact RawCtxPendingParentPrefix.step_preserve source writer stage depth query state.1.1 valid
        (RawCtxFirstParentPrefix.unchosen depth query state.1 unchosen).1 reply actual
  | inr query =>
      rw [external_handler] at supported
      simp only [support_map, Set.mem_image] at supported
      obtain ⟨reply, actual, rfl⟩ := supported
      exact valid

/-- Both adjacent full executions use the same source-derived prefix, with the complete original continuation, private state, cache and executed-input log. -/
theorem scan_same (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B) Result)
    (state : State A N C) (valid : Depth depth state) :
    RawCtxStatefulPendingPrefix.scan (selected (extra := extra) depth) (handler source writer (depth + 1) external) client state =
      RawCtxStatefulPendingPrefix.scan (selected (extra := extra) depth) (handler source writer (depth + 2) external) client state :=
  RawCtxStatefulPrefixInvariant.scan_same (selected (extra := extra) depth) _ _ (Depth depth)
    (fun query reached invariant _ => step_same source writer depth external query reached invariant)
    (fun query reached invariant unchosen result supported =>
      step_preserve source writer (depth + 1) depth external query reached invariant unchosen result supported)
    client state valid

/-- The complete source selector names the actual private request; external effects can never become a selected predecessor. -/
theorem selected_private (depth : Nat)
    (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain) (state : State A N C)
    (chosen : selected (extra := extra) depth query state = true) :
    ∃ address, PqxdhInitialPostContext.queryAddress query = some address := by
  cases query with
  | inl query =>
      have privateQuery := RawCtxFirstParentPrefix.selected_private depth query state.1 chosen
      rcases query with ((request | opening) | ((request | sealing) | request)) | request
      all_goals first | exact ⟨_, rfl⟩ | cases privateQuery
  | inr query => cases chosen

/-- Each actual selected predecessor is a recorded cache hit or a fresh cache miss at the requested depth, with no honest-target or miss assumption. -/
theorem selected_cases (depth : Nat)
    (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain) (state : State A N C)
    (covered : Covered state) (address : JointKdfAddress)
    (found : PqxdhInitialPostContext.queryAddress query = some address)
    (chosen : selected (extra := extra) depth query state = true) :
    RawCtxSelectiveChainGame.matched state.1.1.2.2 address = true ∧
      ((address ∈ state.1.2 ∧ ∃ output, state.1.1.2.1 address = some output) ∨
        (state.1.1.2.1 address = none ∧ state.1.1.2.2.depth = depth)) := by
  cases query with
  | inl query =>
      obtain ⟨matching, hit | miss⟩ := RawCtxFirstParentPrefix.selected_cases depth query state.1 address found chosen
      · obtain ⟨output, cached⟩ := hit
        exact ⟨matching, Or.inl ⟨covered address output cached, output, cached⟩⟩
      · exact ⟨matching, Or.inr miss⟩
  | inr query => cases chosen

/-- Completing either adjacent source prefix executes its exact original dependent callback and all remaining full-interface work. -/
theorem scan_finish (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B) Result) (state : State A N C) :
    (RawCtxStatefulPendingPrefix.scan (selected (extra := extra) depth) (handler source writer stage external) client state >>=
      RawCtxPendingMixedPrefix.finish (handler source writer stage external)) =
      (simulateQ (handler source writer stage external) client).run state :=
  RawCtxStatefulPendingPrefix.scan_finish (selected (extra := extra) depth) (handler source writer stage external) client state

end BeaconcryptCore.Computational.PqxdhInitialNativePrefix

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativePrefix.step_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativePrefix.step_same
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativePrefix.step_preserve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativePrefix.step_preserve
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativePrefix.scan_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativePrefix.scan_same
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativePrefix.selected_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativePrefix.selected_private
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativePrefix.selected_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativePrefix.selected_cases
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativePrefix.scan_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativePrefix.scan_finish
