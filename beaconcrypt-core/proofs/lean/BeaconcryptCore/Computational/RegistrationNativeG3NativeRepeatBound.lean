-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeRepeatUniformBound
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedReal

/-! The original complete native client's explicit real candidate-observed repeat source is bounded by one ordinary KEM-CCA advantage, one unconditional KEM correctness error and twice one whole-prior suffix-key recovery loss. The actual pure observer retains the candidate while the running original client and recovery adversary remain candidate independent. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeRepeatBound
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhKemIndCca
open RegistrationNativeG3NativeRepeatUniformBound (observation actual)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
attribute [local irreducible] uniformSample actual RegistrationNativeG3NativeRepeatUniformBound.prior RegistrationNativeSuffixKeyPrf.value
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
  (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (front : RegistrationNativeSecretWordMessage.State source) (ordinary : RegistrationNativePublicInterpreter.State n KemSK)

noncomputable def program (selected : Nat) :=
  RegistrationNativeG3NativeCheckedUniformSource.openProgram setup checks wire source route sign selected selectedAccept publicPrekey serverKeyId bounds mode
    seed scalar (setup.joint.staticDh seed (setup.dh.publicKey scalar)) work front ordinary

noncomputable def real (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) :=
  RegistrationNativeOpenKeyKemEarlyObservedReal.source setup.baseImpl setup.kem
    (program setup checks wire source route sign selectedAccept publicPrekey serverKeyId bounds mode seed scalar work front ordinary selected.val)
    (observation setup seed scalar) budget.create selected

noncomputable def loss (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) : ℝ≥0∞ :=
  ENNReal.ofReal ((setup.kem.IND_CCA_Advantage
    (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
    (RegistrationNativeKemEarlyObservedGame.adversary setup.baseImpl setup.kem
      (RegistrationNativeOpenKeyKemGame.other setup.baseImpl setup.kem) (pure ∅)
      (simulateQ RegistrationNativeOpenKey.native
        (program setup checks wire source route sign selectedAccept publicPrekey serverKeyId bounds mode seed scalar work front ordinary selected.val))
      (observation setup seed scalar) budget.create selected).toINDCCA).toReal +
    RegistrationNativeKemEarlyCorrectness.correctnessError setup.baseImpl setup.kem) +
  2 * (ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage setup.source
    (RegistrationNativeSuffixKeyRecovery.adversary setup.source
      (RegistrationNativeSecretWordRecoveryCompiler.guesses
        (actual setup checks wire source route sign selectedAccept publicPrekey serverKeyId bounds mode seed scalar work front ordinary budget selected)))) +
    (budget.cap 4 + budget.cap 5) * (256 ^ 160 : ℝ≥0∞)⁻¹ +
    (budget.cap 4 + budget.cap 5) * (256 ^ 32 : ℝ≥0∞)⁻¹)

attribute [local irreducible] real loss

/-- The complete original observed real repeat source has only the explicit ordinary KEM and whole-prior recovery losses, with every resource certificate derived from original Respects. -/
theorem bound (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (selected : Fin (budget.create + 1))
    (sessions : front.server.sessions = []) (parsed : front.parsedAccepts = 0) (owners : front.beacons = []) :
    Pr{let result ← real setup checks wire source route sign selectedAccept publicPrekey serverKeyId bounds mode seed scalar work front ordinary budget selected}[result = true] ≤
      loss setup checks wire source route sign selectedAccept publicPrekey serverKeyId bounds mode seed scalar work front ordinary budget selected := by
  have bills := RegistrationNativeG3NativeCheckedUniformSource.resource_bounds setup checks wire source route sign selected.val selectedAccept publicPrekey serverKeyId
    bounds mode seed scalar (setup.joint.staticDh seed (setup.dh.publicKey scalar)) work front ordinary budget bounded
  have close := RegistrationNativeOpenKeyKemEarlyObservedReal.source_close setup.baseImpl setup.kem functional
    (program setup checks wire source route sign selectedAccept publicPrekey serverKeyId bounds mode seed scalar work front ordinary selected.val)
    (observation setup seed scalar) budget.create selected bills.1 bills.2
  have uniform := RegistrationNativeG3NativeRepeatUniformBound.bound setup checks wire source route sign selectedAccept publicPrekey serverKeyId
    bounds mode seed scalar work front ordinary budget bounded selected sessions parsed owners
  have compared := ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance
    (real setup checks wire source route sign selectedAccept publicPrekey serverKeyId bounds mode seed scalar work front ordinary budget selected)
    (RegistrationNativeKemEarlyObservedGame.branch setup.baseImpl setup.kem
      (RegistrationNativeOpenKeyKemGame.other setup.baseImpl setup.kem) (pure ∅)
      (simulateQ RegistrationNativeOpenKey.native
        (program setup checks wire source route sign selectedAccept publicPrekey serverKeyId bounds mode seed scalar work front ordinary selected.val))
      (observation setup seed scalar) budget.create selected false)
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true] at compared
  apply compared.trans
  have lifted := ENNReal.ofReal_le_ofReal close
  simpa only [real, program, loss] using
    (add_le_add uniform lifted).trans (le_of_eq (add_comm _ _))

end BeaconcryptCore.Computational.RegistrationNativeG3NativeRepeatBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeRepeatBound.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeRepeatBound.bound
