-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamilyAlgebra

/-! The executable native Family tester receives only its public challenge. Selected identity and prekey secrets occur solely in the experiments and matching predicates. The analysis joint trace retains the real randomized test after the literal candidate prefix, so its first-result marginal and Boolean observation are exact probability equalities. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal Classical
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamily
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointIdentity (IdentitySeed DhOutput sampleSeed)
open PqxdhJointGapDh (ScalarBytes sampleScalar)
open RegistrationNativeRelatedFamily (Spec empty)
open RegistrationNativeKnownInputBatchBound (Matches)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

abbrev Trace := IdentitySeed × ScalarBytes × (List DhOutput × Bool)

def matchEvent (setup : Setup base KemSK) (result : Trace) : Prop :=
  Matches setup.joint setup.dh result.1 result.2.1 result.2.2.1

def positiveEvent (result : Trace) : Prop := result.2.2.2 = true

noncomputable def matchingGame (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) : ProbComp Bool := do
  let seed ← sampleSeed
  let scalar ← sampleScalar
  let candidates ← (simulateQ (RegistrationNativeRelatedFamily.idealImpl setup.hmac setup.joint setup.dh seed scalar)
    (RegistrationNativeRootCandidates.familyClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar))).run' empty
  pure (decide (Matches setup.joint setup.dh seed scalar candidates))

noncomputable def idealJoint (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) : ProbComp Trace := do
  let seed ← sampleSeed
  let scalar ← sampleScalar
  let result ← (simulateQ (RegistrationNativeRelatedFamily.idealImpl setup.hmac setup.joint setup.dh seed scalar)
    (RegistrationNativeRootCandidateBatch.program (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar))).run' empty
  pure (seed, scalar, result)

/-- Testing the actual returned list retains its exact matching probability, with all suffix draws still executed. -/
theorem matching_joint (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) :
    Pr{let result ← matchingGame (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary}[result = true] =
      Pr{let result ← idealJoint (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary}[matchEvent setup result] := by
  unfold matchingGame idealJoint
  apply prEvent_bind_congr
  intro seed
  apply prEvent_bind_congr
  intro scalar
  simp only [bind_pure_comp, prEvent_map, decide_eq_true_eq, matchEvent]
  exact (RegistrationNativeKnownFirstFamilyAlgebra.first_marginal
    (RegistrationNativeRelatedFamily.idealImpl setup.hmac setup.joint setup.dh seed scalar)
    (RegistrationNativeRootCandidates.familyClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)) empty (Matches setup.joint setup.dh seed scalar)).symm

/-- The analysis joint trace's positive flag is exactly the ordinary public-challenge Family tester. -/
theorem positive_joint (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) :
    Pr{let result ← idealJoint (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary}[positiveEvent result] =
      Pr{let result ← (RegistrationNativeRelatedFamily.idealGame setup.hmac setup.joint setup.dh
        (RegistrationNativeRootCandidateBatch.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary))}[result = true] := by
  unfold idealJoint RegistrationNativeRelatedFamily.idealGame
  apply prEvent_bind_congr
  intro seed
  apply prEvent_bind_congr
  intro scalar
  simp only [bind_pure_comp, prEvent_map, positiveEvent]
  exact (RegistrationNativeKnownFirstFamilyAlgebra.positive
    (RegistrationNativeRelatedFamily.idealImpl setup.hmac setup.joint setup.dh seed scalar)
    (RegistrationNativeRootCandidateBatch.program (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)) empty).symm

/-- The actual real public-challenge Family tester has zero positive probability after the genuine selected-secret sampling. -/
theorem real_true_zero (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) :
    Pr{let result ← (RegistrationNativeRelatedFamily.realGame setup.hmac setup.joint setup.dh
      (RegistrationNativeRootCandidateBatch.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary))}[result = true] = 0 := by
  apply le_antisymm _ zero_le
  unfold RegistrationNativeRelatedFamily.realGame
  apply prEvent_bind_le_of_forall_le
  intro seed
  apply prEvent_bind_le_of_forall_le
  intro scalar
  rw [RegistrationNativeRootCandidateBatch.client, RegistrationNativeKnownFirstFamilyAlgebra.positive]
  exact (RegistrationNativeRootCandidateBatch.real_true_zero setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) seed scalar).le

/-- The concrete ordinary Family advantage is the real success mass of its ideal tester, since the actual real tester is always negative. -/
theorem advantage_eq_ideal (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) :
    RegistrationNativeRelatedFamily.advantage setup.hmac setup.joint setup.dh (RegistrationNativeRootCandidateBatch.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary) =
      (Pr{let result ← RegistrationNativeRelatedFamily.idealGame setup.hmac setup.joint setup.dh (RegistrationNativeRootCandidateBatch.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary)}[result = true]).toReal := by
  have realZero := real_true_zero (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary
  rw [prEvent_eq_evalDist_singleton] at realZero ⊢
  simp only [RegistrationNativeRelatedFamily.advantage, ProbComp.boolDistance, realZero,
    ENNReal.toReal_zero, zero_sub, abs_neg, abs_of_nonneg ENNReal.toReal_nonneg]

end BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamily
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamily.matching_joint' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamily.matching_joint
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamily.positive_joint' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamily.positive_joint
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamily.real_true_zero' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamily.real_true_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamily.advantage_eq_ideal' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamily.advantage_eq_ideal
