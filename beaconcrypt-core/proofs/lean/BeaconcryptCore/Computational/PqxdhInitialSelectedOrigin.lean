import BeaconcryptCore.Computational.PqxdhInitialFinishOriginLog
import BeaconcryptCore.Computational.PqxdhInitialSelectedService

/-!
The private installation marker uses the actual selected-key initializer coordinate. Known-root requests remain unselected even if their root bytes happen to equal another root. The actual response-only initializer returns its selected-half representation exactly on this coordinate; its cache effects are retained.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSelectedOrigin
open PqxdhInitialRootLabelService PqxdhInitialSelectedService PqxdhCorrelatedExtractFamily
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhInitialSelectedBeacon
open PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid

noncomputable def selectedRequest (selected : Message) : Request → Bool
  | .known _ => false
  | .family message => decide (message = selected)

noncomputable def mark (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared) : Bool :=
  selectedRequest selected (PqxdhInitialRootLabelBridge.request fixed secrets)

/-- The private origin marker names the complete actual initializer coordinate, without an injectivity premise on root values. -/
theorem selectedRequest_iff (selected : Message) (query : Request) :
    selectedRequest selected query = true ↔ query = .family selected := by
  cases query with
  | known root => simp only [selectedRequest, Bool.false_eq_true, false_iff]; intro h; cases h
  | family message => simp only [selectedRequest, decide_eq_true_eq, Request.family.injEq]

/-- Every actual service outcome has the selected-half representation exactly when its complete source request is the selected coordinate; all root-cache state remains in support. -/
theorem value_origin (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (second : Bool) (other : RootOutput) (query : Request) (cache : RootOracle.QueryCache)
    (result : InitialValue × RootOracle.QueryCache)
    (supported : result ∈ support ((value fixed selected second other query).run cache)) :
    result.1.isRight = selectedRequest selected query := by
  cases query with
  | known root =>
    simp only [value, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    rfl
  | family message =>
    by_cases same : message = selected
    · simp only [value, same, ite_true, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      simp only [selectedRequest, same, decide_true, Sum.isRight_inr]
    · simp only [value, same, ite_false, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨root, rootReached, final⟩ := supported
      simp only [StateT.run_pure, mem_support_pure_iff] at final
      subst result
      simp only [known, Sum.isRight_inl, selectedRequest, same, decide_false]

/-- The actual compiled initializer service returns the same selected-coordinate marker, while retaining its complete root-cache response and state. -/
theorem service_origin (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (second : Bool) (other : RootOutput)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared)
    (cache : RootOracle.QueryCache) (result : Option InitialValue × RootOracle.QueryCache)
    (supported : result ∈ support ((service fixed selected second other secrets).run cache)) :
    result.1.map Sum.isRight = some (mark fixed selected secrets) := by
  simp only [service, StateT.run_map, support_map] at supported
  obtain ⟨original, reached, equality⟩ := supported
  subst result
  simp only [Option.map_some]
  exact congrArg some (value_origin fixed selected second other _ cache original reached)

/-- A recorded selected installation is a successful execution of the original finish using the exact matching initializer message, not merely the same Beacon index or equal root bytes. -/
theorem finish_origin {Kernel I D K X Response State : Type}
    (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT State ProbComp))
    (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (application : Response → StateT State ProbComp (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared → StateT State ProbComp (Option Kernel))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (entry : RawCtxGenericRoleStorage.BeaconState Kernel I D K) (before : State)
    (result : PqxdhInitialFinishOrigin.Result Kernel Bool I D K × State)
    (supported : result ∈ support ((PqxdhInitialFinishOrigin.owner (mark fixed selected) pre calls
      application initial decode raw entry).run before))
    (recorded : result.1.2 = some true) :
    ∃ control prekey oneTime kem,
      ∃ (prepared : PqxdhBeaconPhase2Shared.Prepared Response PqxdhPhase2DecapsulationRouting.Shared)
        (atTail : State) (staged : Option (PqxdhInitialGenericBeacon.Staged Kernel)),
      entry.beacon.phase = .initSent control prekey oneTime kem ∧
      (some prepared, atTail) ∈ support ((simulateQ pre
        (PqxdhBeaconPhase2Shared.prepare control entry.beacon.identity prekey oneTime kem raw)).run before) ∧
      (staged, result.2) ∈ support ((PqxdhInitialGenericBeacon.tail calls application initial decode prepared).run atTail) ∧
      result.1.1 = PqxdhInitialGenericBeacon.finish control entry staged ∧ result.1.1.1.isSome = true ∧
      PqxdhInitialRootLabelBridge.request fixed prepared.root = .family selected := by
  obtain ⟨control, prekey, oneTime, kem, prepared, atTail, staged, phase, preparation, tail, returned, success, marker⟩ :=
    PqxdhInitialFinishOrigin.origin (mark fixed selected) pre calls application initial decode raw entry before
      result supported true recorded
  exact ⟨control, prekey, oneTime, kem, prepared, atTail, staged, phase, preparation, tail, returned, success,
    (selectedRequest_iff selected _).mp marker.symm⟩

end BeaconcryptCore.Computational.PqxdhInitialSelectedOrigin

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedOrigin.selectedRequest_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedOrigin.selectedRequest_iff
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedOrigin.value_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedOrigin.value_origin
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedOrigin.service_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedOrigin.service_origin
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedOrigin.finish_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedOrigin.finish_origin
