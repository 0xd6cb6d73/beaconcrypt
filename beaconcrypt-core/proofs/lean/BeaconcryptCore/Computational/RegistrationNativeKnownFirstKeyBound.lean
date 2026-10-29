-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeyExperiment
import BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeyFamilySource
import BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamilyBound

/-! The actual normal G2 chronological known-first event is bounded by the executable public-only Family batch adversary, its explicit fresh-suffix/point allowance, and the five ordinary key-schedule losses. Source/cache and observer identifications are derived from the concrete native execution; no matching, protection or whole-game simulation premise is supplied. -/
open OracleComp OracleSpec CoreModels ENNReal Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeyBound
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKnownFirstKeyExperiment (g1 entryClient)
open RegistrationNativeKnownFirstKeySource (observe)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

attribute [local irreducible] g1 entryClient RegistrationNativeG2Observer.nativeClient

theorem family_eq (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac) :
    RegistrationNativeKnownFirstFamily.matchingGame (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary = g1 (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary := by
  unfold RegistrationNativeKnownFirstFamily.matchingGame g1
  apply bind_congr
  intro seed
  apply bind_congr
  intro scalar
  rw [bind_pure_comp]
  exact RegistrationNativeKnownFirstKeyFamilySource.point_source setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary correct seed scalar _

/-- The complete native normal G2 known-first probability has an explicit public Family adversary and five standard key losses, with all original command bills derived internally. -/
theorem g2_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue)) :
    𝒟[RegistrationNativeOpenKeyKemGame.normal setup.baseImpl setup.kem
      (RegistrationNativeG2Observer.nativeClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary (observe setup))] {true} ≤
      (ENNReal.ofReal (RegistrationNativeRelatedFamily.advantage setup.hmac setup.joint setup.dh
        (RegistrationNativeRootCandidateBatch.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary)) +
        RegistrationNativeKnownFirstFamily.slack budget) +
      ENNReal.ofReal (∑ index ∈ Finset.range (budget.cap 4 + budget.cap 5), RegistrationBoundKeySchedule.keyLoss setup.source setup.hmac
        (RegistrationNativeKeyHybrid.reduction setup.source setup.hmac (entryClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary) index)) := by
  have first := RegistrationNativeKnownFirstFamily.bound_ennreal (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary budget bounded
  rw [family_eq setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary correct.root,
    prEvent_eq_evalDist_singleton] at first
  have keys := RegistrationNativeKnownFirstKeyExperiment.key_bound (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary correct budget bounded
  have compared := ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance
    (RegistrationNativeOpenKeyKemGame.normal setup.baseImpl setup.kem
      (RegistrationNativeG2Observer.nativeClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary (observe setup)))
    (g1 (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary)
  rw [ProbComp.boolDistance_comm] at compared
  exact compared.trans (add_le_add first (ENNReal.ofReal_le_ofReal keys))

end BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeyBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeyBound.family_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeyBound.family_eq
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeyBound.g2_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeyBound.g2_bound
