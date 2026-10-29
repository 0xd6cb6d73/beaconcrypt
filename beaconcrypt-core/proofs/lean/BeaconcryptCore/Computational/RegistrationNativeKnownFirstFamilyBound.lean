-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamily

/-! The actual generated native candidate match is bounded by one ordinary public-challenge related-Family advantage and its explicit finite fresh-batch slack. Actual prefix/list caps derive from the original public Respects contract; all selected-secret draws and randomized suffix checks remain in the experiment. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal Classical
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamily
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointIdentity (sampleSeed)
open PqxdhJointGapDh (sampleScalar)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

noncomputable def slack (budget : PqxdhDeploymentInterface.Budget) : ℝ≥0∞ :=
  (((budget.cap 3 + budget.cap 5) + (budget.cap 3 + budget.cap 5) : Nat) : ℝ≥0∞) *
    (256 ^ 32 : ℝ≥0∞)⁻¹ + (2 ^ 512 : ℝ≥0∞)⁻¹

private theorem slack_ne_top (budget : PqxdhDeploymentInterface.Budget) : slack budget ≠ ⊤ := by
  unfold slack
  finiteness

/-- Averaging the actual selected-secret draws keeps the same finite matching-list miss allowance, without a target multiplier. -/
theorem joint_miss (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue)) :
    Pr{let result ← idealJoint (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary}[
      matchEvent setup result ∧ ¬positiveEvent result] ≤ slack budget := by
  unfold idealJoint
  apply prEvent_bind_le_of_forall_le
  intro seed
  apply prEvent_bind_le_of_forall_le
  intro scalar
  simp only [bind_pure_comp, prEvent_map, matchEvent, positiveEvent, Bool.not_eq_true]
  exact RegistrationNativeRootCandidateBatch.ideal_false setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary budget bounded
    (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) seed scalar

/-- The full actual matching probability is at most the actual ideal Boolean tester probability plus its derived miss allowance. -/
theorem matching_le_positive (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue)) :
    Pr{let result ← matchingGame (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary}[result = true] ≤
      Pr{let result ← (RegistrationNativeRelatedFamily.idealGame setup.hmac setup.joint setup.dh (RegistrationNativeRootCandidateBatch.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary))}[result = true] + slack budget := by
  have split := prEvent_le_prEvent_add_prEvent_and_not
    (idealJoint (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary) (matchEvent setup) positiveEvent
  rw [← matching_joint (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary, positive_joint (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary] at split
  exact split.trans (add_le_add le_rfl (joint_miss (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary budget bounded))

/-- One concrete ordinary Family tester bounds the generated native candidate match, with only the explicit twice-accept-plus-finish suffix and512-bit point slack. -/
theorem bound_ennreal (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue)) :
    Pr{let result ← matchingGame (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary}[result = true] ≤
      ENNReal.ofReal (RegistrationNativeRelatedFamily.advantage setup.hmac setup.joint setup.dh (RegistrationNativeRootCandidateBatch.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary)) + slack budget := by
  have estimate := matching_le_positive (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary budget bounded
  have positive := advantage_eq_ideal (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary
  calc
    _ ≤ Pr{let result ← (RegistrationNativeRelatedFamily.idealGame setup.hmac setup.joint setup.dh (RegistrationNativeRootCandidateBatch.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary))}[result = true] + slack budget := estimate
    _ = _ := by rw [positive, ENNReal.ofReal_toReal (prEvent_ne_top _)]

/-- The same global generated-candidate bound uses the existing real-valued ordinary related-Family advantage. -/
theorem bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue)) :
    (Pr{let result ← matchingGame (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary}[result = true]).toReal ≤
      RegistrationNativeRelatedFamily.advantage setup.hmac setup.joint setup.dh (RegistrationNativeRootCandidateBatch.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary) + (slack budget).toReal := by
  have estimate := matching_le_positive (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary budget bounded
  have finite : Pr{let result ← (RegistrationNativeRelatedFamily.idealGame setup.hmac setup.joint setup.dh (RegistrationNativeRootCandidateBatch.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary))}[result = true] + slack budget ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, slack_ne_top budget⟩
  have converted := ENNReal.toReal_mono finite estimate
  rw [ENNReal.toReal_add (prEvent_ne_top _) (slack_ne_top budget),
    ← advantage_eq_ideal (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary] at converted
  exact converted

end BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamily
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamily.joint_miss' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamily.joint_miss
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamily.matching_le_positive' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamily.matching_le_positive
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamily.bound_ennreal' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamily.bound_ennreal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamily.bound' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamily.bound
