-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicKeyExperiment

/-! The complete actual native source APP owner-coordinate event reaches the uniform108 entry experiment through the explicitly broader ordinary related-input advantage and the five standard key-schedule losses. The owner coordinate includes both original peer and owner handles. This does not replace the uniform entry experiment by a hidden-slot entropy experiment: repeated-role aliases and actual target protection must be established separately. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceKeyBound
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

noncomputable def decision (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (serverKeyId : U64) (budget : PqxdhDeploymentInterface.Budget) (selected : Nat)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (result : Value × RegistrationNativeLedger.State) : Bool :=
  RegistrationNativeSelectedEvents.ceAppOwnerEvent crypto wire serverKeyId budget selected claim
    (result.1, (result.2, ()))

/-- The source compiler's generic literal-ledger decision specializes to the complete broad original APP owner coordinate, without restricting accepted bytes or either handle side. -/
theorem client_owner (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (budget : PqxdhDeploymentInterface.Budget) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value) :
    RegistrationNativePublicSourceProfile.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      selectedOwner selectedAccept bounds .P adversary (decision setup.source.crypto wire serverKeyId budget selectedOwner claim) =
      RegistrationNativePublicStartup.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept
        bounds budget claim adversary := by
  funext publicValue
  rfl

/-- Actual generated source APP and the concrete root-ideal reference experiment have the stated ordinary related-input distance; no source-startup or event correspondence is assumed. -/
theorem family_distance (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (selectedOwner selectedAccept : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (budget : PqxdhDeploymentInterface.Budget)
    (claim : Value → Option (Nat × Pqxdh.Bytes))
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value) :
    (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P
      adversary (RegistrationNativeSelectedEvents.ceAppOwnerEvent setup.source.crypto wire serverKeyId budget selectedOwner claim)).boolDistance
      (RegistrationNativeRelatedRoot.idealRootGame setup.hmac setup.joint setup.dh
        (RegistrationNativePublicStartup.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept
          bounds budget claim adversary)) =
      RegistrationNativeRelatedFamily.advantage setup.hmac setup.joint setup.dh
        (fun publicValue => simulateQ RegistrationNativeRelatedRoot.reduction
          (RegistrationNativePublicStartup.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept
            bounds budget claim adversary publicValue)) := by
  have actual := RegistrationNativePublicSourceBound.family_distance (n := n) setup checks wire route representation correct source ensureInit
    identityIndex serverKeyId selectedOwner selectedAccept bounds .P adversary
    (decision setup.source.crypto wire serverKeyId budget selectedOwner claim)
  rw [client_owner] at actual
  exact actual

attribute [local irreducible] RegistrationNativePublicStartup.client RegistrationNativePublicKeyExperiment.entryClient
  RegistrationNativeExperiment.profile

/-- The entire actual populated native ML profile and original broad APP owner-coordinate event incur one ordinary native related-input advantage plus the five primitive losses for each allowed admitted material demand. -/
theorem key_distance (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (selectedOwner selectedAccept : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (budget : PqxdhDeploymentInterface.Budget)
    (claim : Value → Option (Nat × Pqxdh.Bytes))
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue)) :
    (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P
      adversary (RegistrationNativeSelectedEvents.ceAppOwnerEvent setup.source.crypto wire serverKeyId budget selectedOwner claim)).boolDistance
      (RegistrationNativeKeyHybrid.uniform (RegistrationNativePublicKeyExperiment.entryClient (n := n) setup checks wire route source ensureInit
        identityIndex serverKeyId selectedOwner selectedAccept bounds budget claim adversary)) ≤
      RegistrationNativeRelatedFamily.advantage setup.hmac setup.joint setup.dh
        (fun publicValue => simulateQ RegistrationNativeRelatedRoot.reduction
          (RegistrationNativePublicStartup.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept
            bounds budget claim adversary publicValue)) +
      ∑ index ∈ Finset.range (budget.cap 4 + budget.cap 5), RegistrationBoundKeySchedule.keyLoss setup.source setup.hmac
        (RegistrationNativeKeyHybrid.reduction setup.source setup.hmac
          (RegistrationNativePublicKeyExperiment.entryClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
            selectedOwner selectedAccept bounds budget claim adversary) index) := by
  have triangle := ProbComp.boolDistance_triangle
    (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P
      adversary (RegistrationNativeSelectedEvents.ceAppOwnerEvent setup.source.crypto wire serverKeyId budget selectedOwner claim))
    (RegistrationNativeRelatedRoot.idealRootGame setup.hmac setup.joint setup.dh
      (RegistrationNativePublicStartup.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept
        bounds budget claim adversary))
    (RegistrationNativeKeyHybrid.uniform (RegistrationNativePublicKeyExperiment.entryClient (n := n) setup checks wire route source ensureInit
      identityIndex serverKeyId selectedOwner selectedAccept bounds budget claim adversary))
  exact triangle.trans (add_le_add
    (le_of_eq (family_distance (n := n) setup checks wire route representation correct.root source ensureInit identityIndex serverKeyId
      selectedOwner selectedAccept bounds budget claim adversary))
    (RegistrationNativePublicKeyExperiment.key_bound (n := n) setup checks wire route source correct ensureInit identityIndex serverKeyId
      selectedOwner selectedAccept bounds budget claim adversary bounded))

end BeaconcryptCore.Computational.RegistrationNativePublicSourceKeyBound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceKeyBound.client_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceKeyBound.client_owner
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceKeyBound.family_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceKeyBound.family_distance
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceKeyBound.key_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceKeyBound.key_distance
