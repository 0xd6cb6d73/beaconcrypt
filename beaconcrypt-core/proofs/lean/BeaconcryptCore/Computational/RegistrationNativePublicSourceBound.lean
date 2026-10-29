-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceProfile

/-! The real generated native deployment pays the explicit ordinary native related-input distinguishing advantage for its actual full-ledger client. This first hop is independent of any later hidden-record origin, alias or ideal fresh-message bound. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceBound
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceProfile (client)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

/-- The whole original source profile, including generated startup and the literal original secrecy ledger, has exactly this ordinary related-input distinguishing distance from the root-ideal reference execution. -/
theorem family_distance (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (selectedOwner selectedAccept : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool) :
    (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode
      adversary (fun result => decision (result.1, result.2.1))).boolDistance
      (RegistrationNativeRelatedRoot.idealRootGame setup.hmac setup.joint setup.dh
        (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary decision)) =
      RegistrationNativeRelatedFamily.advantage setup.hmac setup.joint setup.dh
        (fun publicValue => simulateQ RegistrationNativeRelatedRoot.reduction
          (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary decision publicValue)) := by
  have original := RegistrationNativePublicSourceProfile.profile_source (n := n) setup checks wire route representation correct
    source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary decision
  unfold ProbComp.boolDistance
  rw [original.evalDist_eq]
  exact RegistrationNativeRelatedRoot.advantage_exact setup.source setup.hmac correct setup.joint setup.dh _

/-- The first actual native security hop bounds any original full-ledger success decision by its concrete root-ideal execution plus the stated ordinary related-input advantage. -/
theorem success_le (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (selectedOwner selectedAccept : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool) :
    𝒟[RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode
      adversary (fun result => decision (result.1, result.2.1))] {true} ≤
      𝒟[RegistrationNativeRelatedRoot.idealRootGame setup.hmac setup.joint setup.dh
        (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary decision)] {true} +
      ENNReal.ofReal (RegistrationNativeRelatedFamily.advantage setup.hmac setup.joint setup.dh
        (fun publicValue => simulateQ RegistrationNativeRelatedRoot.reduction
          (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary decision publicValue))) := by
  have compared := ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance
    (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode
      adversary (fun result => decision (result.1, result.2.1)))
    (RegistrationNativeRelatedRoot.idealRootGame setup.hmac setup.joint setup.dh
      (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary decision))
  rwa [family_distance setup checks wire route representation correct] at compared

end BeaconcryptCore.Computational.RegistrationNativePublicSourceBound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceBound.family_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceBound.family_distance
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceBound.success_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceBound.success_le
