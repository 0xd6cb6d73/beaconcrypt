-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeDecisionOpenKeySource
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemSource
import BeaconcryptCore.Computational.RegistrationNativePublicSourceBound
import BeaconcryptCore.Computational.RegistrationNativeG2Observer

/-! Every arbitrary literal original-ledger decision in the generated native ML profile reaches the actual open G2 experiment with the literal private indexed KEM pool and lazy uniform108 table. The ordinary related-input and five key-schedule losses are exactly those already derived for the closed source experiment. The chronological observer is an exact augmentation of that game. No hidden-record origin, role-alias bound or final entropy substitution is assumed here. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeDecisionG2Bound
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

noncomputable def client (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool) :
    OracleComp (RegistrationNativeOpenKey.NativeSpec KemSK) Bool :=
  RegistrationNativeOpenKeyStartup.nativeClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
    selectedOwner selectedAccept bounds mode adversary
    decision

/-- The actual real indexed KEM service and lazy table close to exactly the previously proved global G2 experiment. -/
theorem normal_eq (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool) :
    RegistrationNativeOpenKeyKemGame.normal setup.baseImpl setup.kem
      (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary decision) =
      RegistrationNativeKeyHybrid.uniform (RegistrationNativeDecisionKeyExperiment.entryClient (n := n) setup checks wire route source
        ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary decision) := by
  unfold client RegistrationNativeOpenKeyStartup.nativeClient
  rw [RegistrationNativeOpenKeyKemSource.normal_source, RegistrationNativeDecisionOpenKeySource.client_real]
  rfl

/-- The actual populated native ML source profile incurs its derived related-input and five primitive losses to the same concrete open G2 game used by the KEM/alias observer. -/
theorem source_distance (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (selectedOwner selectedAccept : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue)) :
    (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode
      adversary ((fun result => decision (result.1, result.2.1)))).boolDistance
      (RegistrationNativeOpenKeyKemGame.normal setup.baseImpl setup.kem
        (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary decision)) ≤
      RegistrationNativeRelatedFamily.advantage setup.hmac setup.joint setup.dh
        (fun publicValue => simulateQ RegistrationNativeRelatedRoot.reduction
          (RegistrationNativePublicSourceProfile.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept
            bounds mode adversary decision publicValue)) +
      ∑ index ∈ Finset.range (budget.cap 4 + budget.cap 5), RegistrationBoundKeySchedule.keyLoss setup.source setup.hmac
        (RegistrationNativeKeyHybrid.reduction setup.source setup.hmac
          (RegistrationNativeDecisionKeyExperiment.entryClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
            selectedOwner selectedAccept bounds mode adversary decision) index) := by
  rw [normal_eq]
  have triangle := ProbComp.boolDistance_triangle
    (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode
      adversary (fun result => decision (result.1, result.2.1)))
    (RegistrationNativeRelatedRoot.idealRootGame setup.hmac setup.joint setup.dh
      (RegistrationNativePublicSourceProfile.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        selectedOwner selectedAccept bounds mode adversary decision))
    (RegistrationNativeKeyHybrid.uniform (RegistrationNativeDecisionKeyExperiment.entryClient (n := n) setup checks wire route source ensureInit
      identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary decision))
  exact triangle.trans (add_le_add
    (le_of_eq (RegistrationNativePublicSourceBound.family_distance (n := n) setup checks wire route representation correct.root source ensureInit
      identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary decision))
    (RegistrationNativeDecisionKeyExperiment.key_bound (n := n) setup checks wire route source correct ensureInit identityIndex serverKeyId
      selectedOwner selectedAccept bounds mode adversary decision budget bounded))

/-- The actual chronological G2 observer with a ledger-only decision gives precisely the same arbitrary original-ledger decision. -/
theorem observer_eq (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool) :
    RegistrationNativeG2Observer.nativeClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      selectedOwner selectedAccept bounds mode adversary
      (fun _ _ result => decision result.1) =
      client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary decision := by
  unfold RegistrationNativeG2Observer.nativeClient
  rw [RegistrationNativeG2Observer.client_erase]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeDecisionG2Bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDecisionG2Bound.normal_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDecisionG2Bound.normal_eq
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDecisionG2Bound.source_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDecisionG2Bound.source_distance
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDecisionG2Bound.observer_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDecisionG2Bound.observer_eq
