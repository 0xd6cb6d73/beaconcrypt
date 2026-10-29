-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRootCandidates

/-! The concrete native candidate prefix is an actual related-family program. Each reached root-valued preparation compiles to one family derive and a real public expansion; all native World/KEM/signing work retains its zero-derive bill. Both the derive cap and every returned list length are the original accept-plus-finish budget, with no target multiplier. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRootCandidatesFamily
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRootCandidates (familyClient rootClient IsRootDerive)
open RegistrationNativeKnownInputBatchCounting (IsDerive)
open PqxdhJointIdentity (DhOutput)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

private theorem reduction_step (query : RegistrationNativeRelatedRoot.RootSpec.Domain) :
    (RegistrationNativeRelatedRoot.reduction query).IsQueryBoundP IsDerive
      (if IsRootDerive query then 1 else 0) := by
  cases query with
  | inl coin => simp [RegistrationNativeRelatedRoot.reduction, IsRootDerive, IsDerive, isQueryBoundP_query_iff]
  | inr request => cases request with
    | sign bytes => simp [RegistrationNativeRelatedRoot.reduction, IsRootDerive, IsDerive, isQueryBoundP_query_iff]
    | publicHmac key bytes => simp [RegistrationNativeRelatedRoot.reduction, IsRootDerive, IsDerive, isQueryBoundP_query_iff]
    | derive message =>
        simp only [RegistrationNativeRelatedRoot.reduction, RegistrationNativeRelatedRoot.root, IsRootDerive, ite_true]
        rw [isQueryBoundP_query_bind_iff]
        constructor
        · right; decide
        · intro reply
          cases reply <;> simp [IsDerive, isQueryBoundP_pure]

/-- The actual whole generated native prefix uses at most the original qAccept+qFinish family derive calls. -/
theorem family_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (publicValue : PqxdhJointGapDh.PublicChallenge) :
    (familyClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept
      bounds mode adversary publicValue).IsQueryBoundP IsDerive (budget.cap 3 + budget.cap 5) :=
  RawCtxSourceOpen.simulate_bound _ IsRootDerive IsDerive _ _
    (RegistrationNativeRootCandidates.root_bound setup checks wire route source ensureInit identityIndex serverKeyId
      selectedOwner selectedAccept bounds mode adversary budget bounded publicValue) reduction_step

/-- Every returned candidate list obeys the same derived budget under every possible family-oracle reply. -/
theorem family_length (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (publicValue : PqxdhJointGapDh.PublicChallenge) (candidates : List DhOutput)
    (supported : candidates ∈ support (familyClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      selectedOwner selectedAccept bounds mode adversary publicValue)) :
    candidates.length ≤ budget.cap 3 + budget.cap 5 := by
  apply RegistrationNativeRootCandidates.root_length setup checks wire route source ensureInit identityIndex serverKeyId
    selectedOwner selectedAccept bounds mode adversary budget bounded publicValue candidates
  apply support_simulateQ_run'_subset
    (RegistrationNativeRelatedRoot.reduction.liftTarget (StateT Unit (OracleComp RegistrationNativeRelatedFamily.Spec))) _ ()
  simpa only [familyClient, simulateQ_liftTarget, StateT.run'_eq, OracleComp.liftM_run_StateT, bind_pure_comp,
    Functor.map_map, id_map'] using supported

end BeaconcryptCore.Computational.RegistrationNativeRootCandidatesFamily
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRootCandidatesFamily.family_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRootCandidatesFamily.family_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRootCandidatesFamily.family_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRootCandidatesFamily.family_length
