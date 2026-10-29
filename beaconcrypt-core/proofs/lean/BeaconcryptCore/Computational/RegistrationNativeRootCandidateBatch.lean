-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRootCandidatesFamily
import BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchWorkBound

/-! The actual generated native candidate prefix is followed by the fresh batch checker in its reached Family state. Root-query and candidate-list caps come from the original mode-dependent public budget. The real batch has zero positive probability; an ideal matching list is missed only with the displayed finite suffix/point error. Matching this list to a native or G2 bad event remains a separate event theorem. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRootCandidateBatch
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRelatedFamily (Spec State empty)
open RegistrationNativeKnownInputBatchBound (Matches)
open PqxdhJointIdentity (DhOutput IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

noncomputable def program (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (publicValue : PqxdhJointGapDh.PublicChallenge) : OracleComp Spec (List DhOutput × Bool) :=
  RegistrationNativeKnownInputBatchWork.program
    (RegistrationNativeRootCandidates.familyClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      selectedOwner selectedAccept bounds mode adversary publicValue)

noncomputable def client (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (publicValue : PqxdhJointGapDh.PublicChallenge) : OracleComp Spec Bool :=
  Prod.snd <$> program (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
    selectedOwner selectedAccept bounds mode adversary publicValue

/-- The literal actual frontend prefix and randomized batch share the same reached cache, history and private execution state. -/
theorem program_run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (publicValue : PqxdhJointGapDh.PublicChallenge)
    (implementation : QueryImpl Spec (StateT State ProbComp)) :
    (simulateQ implementation (program (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      selectedOwner selectedAccept bounds mode adversary publicValue)).run empty =
      ((simulateQ implementation (RegistrationNativeRootCandidates.familyClient (n := n) setup checks wire route source
        ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary publicValue)).run empty >>= fun leading =>
          (fun result => ((leading.1, result.1), result.2)) <$>
            (simulateQ implementation (RegistrationNativeKnownInputBatchProgram.test leading.1)).run leading.2) :=
  RegistrationNativeKnownInputBatchWork.program_run implementation _ empty

/-- The complete actual prefix and fresh batch have zero positive real-family probability from the actual empty state. -/
theorem real_true_zero (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (publicValue : PqxdhJointGapDh.PublicChallenge) (seed : IdentitySeed) (scalar : ScalarBytes) :
    Pr{let result ← (simulateQ (RegistrationNativeRelatedFamily.realImpl setup.hmac setup.joint setup.dh seed scalar)
      (program (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept
        bounds mode adversary publicValue)).run' empty}[result.2 = true] = 0 :=
  RegistrationNativeKnownInputBatchWork.real_true_zero setup.hmac setup.joint setup.dh seed scalar _ empty

/-- An actual ideal matching list is missed with at most twice the sum of the accept and finish budgets in the suffix allowance and one 512-bit point term. All caps derive internally. -/
theorem ideal_false (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (publicValue : PqxdhJointGapDh.PublicChallenge) (seed : IdentitySeed) (scalar : ScalarBytes) :
    Pr{let result ← (simulateQ (RegistrationNativeRelatedFamily.idealImpl setup.hmac setup.joint setup.dh seed scalar)
      (program (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept
        bounds mode adversary publicValue)).run' empty}[
          Matches setup.joint setup.dh seed scalar result.1 ∧ result.2 = false] ≤
      (((budget.cap 3 + budget.cap 5) + (budget.cap 3 + budget.cap 5) : Nat) : ℝ≥0∞) *
        (256 ^ 32 : ℝ≥0∞)⁻¹ + (2 ^ 512 : ℝ≥0∞)⁻¹ := by
  apply RegistrationNativeKnownInputBatchWorkBound.ideal_false_of_source_cap setup.hmac setup.joint setup.dh seed scalar
    _ (budget.cap 3 + budget.cap 5) (budget.cap 3 + budget.cap 5)
    (RegistrationNativeRootCandidatesFamily.family_bound setup checks wire route source ensureInit identityIndex serverKeyId
      selectedOwner selectedAccept bounds mode adversary budget bounded publicValue)
  intro candidates supported
  exact RegistrationNativeRootCandidatesFamily.family_length setup checks wire route source ensureInit identityIndex serverKeyId
    selectedOwner selectedAccept bounds mode adversary budget bounded publicValue candidates supported

end BeaconcryptCore.Computational.RegistrationNativeRootCandidateBatch
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRootCandidateBatch.program_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRootCandidateBatch.program_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRootCandidateBatch.real_true_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRootCandidateBatch.real_true_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRootCandidateBatch.ideal_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRootCandidateBatch.ideal_false
