-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeDecisionG2Bound
import BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupNormalSource

/-! Event-generic source, key-schedule and ordinary KEM comparisons for the unchanged native profile. Each event reads the literal value and original ledger. In particular, a public selector and a correct-guess event may use separate, explicitly constructed reductions on the same executing client. No equality between different target ideal games is asserted. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeObservableHybrid
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (bounds : FreshBounds) (mode : Mode)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (budget : Budget) (selectedOwner : Fin (budget.create + 1)) (selectedAccept : Nat)
  (observe : Value × RegistrationNativeLedger.State → Bool)

noncomputable def work :=
  RegistrationNativeG3NativeStartupUniformValue.program (n := n) setup checks wire source route ensureInit identityIndex serverKeyId
    selectedOwner.val selectedAccept bounds mode adversary

noncomputable def normal : ProbComp Bool :=
  RegistrationNativeOpenKeyKemGame.normal setup.baseImpl setup.kem
    (RegistrationNativeDecisionG2Bound.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      selectedOwner.val selectedAccept bounds mode adversary observe)

noncomputable def uniform : ProbComp Bool :=
  RegistrationNativeKemEarlyObservedGame.branch setup.baseImpl setup.kem
    (RegistrationNativeOpenKeyKemGame.other setup.baseImpl setup.kem) (pure ∅)
    (simulateQ RegistrationNativeOpenKey.native
      (work (n := n) setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept))
    (fun _ result => RegistrationNativeG3NativeStartupDecision.decision observe result) budget.create selectedOwner false

noncomputable def adversaryKem : PqxdhKemIndCca.OneKeyAdversary setup.kem :=
  RegistrationNativeKemEarlyObservedGame.adversary setup.baseImpl setup.kem
    (RegistrationNativeOpenKeyKemGame.other setup.baseImpl setup.kem) (pure ∅)
    (simulateQ RegistrationNativeOpenKey.native
      (work (n := n) setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept))
    (fun _ result => RegistrationNativeG3NativeStartupDecision.decision observe result) budget.create selectedOwner

noncomputable def keyLoss : ℝ :=
  RegistrationNativeRelatedFamily.advantage setup.hmac setup.joint setup.dh
    (fun publicValue => simulateQ RegistrationNativeRelatedRoot.reduction
      (RegistrationNativePublicSourceProfile.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        selectedOwner.val selectedAccept bounds mode adversary observe publicValue)) +
  ∑ index ∈ Finset.range (budget.cap 4 + budget.cap 5), RegistrationBoundKeySchedule.keyLoss setup.source setup.hmac
    (RegistrationNativeKeyHybrid.reduction setup.source setup.hmac
      (RegistrationNativeDecisionKeyExperiment.entryClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        selectedOwner.val selectedAccept bounds mode adversary observe) index)

noncomputable def kemLoss : ℝ :=
  (setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
    (adversaryKem (n := n) setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept observe).toINDCCA).toReal +
    RegistrationNativeKemEarlyCorrectness.correctnessError setup.baseImpl setup.kem

/-- A candidate-independent literal ledger event pays one ordinary KEM reduction, including complete startup and failed callbacks. -/
theorem kem_distance
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication)) :
    (normal (n := n) setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept observe).boolDistance
      (uniform (n := n) setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept observe) ≤
      kemLoss (n := n) setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept observe := by
  change (RegistrationNativeOpenKeyKemGame.normal setup.baseImpl setup.kem
    (RegistrationNativeOpenKeyStartup.nativeClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      selectedOwner.val selectedAccept bounds mode adversary observe)).boolDistance _ ≤ _
  rw [RegistrationNativeG3NativeStartupNormalSource.normal_source]
  have bills := RegistrationNativeG3NativeStartupUniformValue.resource_bounds (n := n) setup checks wire source route ensureInit identityIndex serverKeyId
    selectedOwner.val selectedAccept bounds mode adversary budget bounded
  exact RegistrationNativeOpenKeyKemEarlyObservedMarginal.normal_close setup.baseImpl setup.kem functional
    (work (n := n) setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept)
    (RegistrationNativeG3NativeStartupDecision.decision observe) budget.create selectedOwner bills.1 bills.2

/-- Every literal ledger event in the original native experiment transfers through source, KDF and KEM hybrids without changing eligibility or observations. -/
theorem source_distance (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication)) :
    (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
      bounds mode adversary (fun result => observe (result.1, result.2.1))).boolDistance
      (uniform (n := n) setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept observe) ≤
      keyLoss (n := n) setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept observe +
      kemLoss (n := n) setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept observe := by
  exact (ProbComp.boolDistance_triangle _
    (normal (n := n) setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept observe) _).trans
    (add_le_add
      (RegistrationNativeDecisionG2Bound.source_distance (n := n) setup checks wire route representation correct source ensureInit identityIndex serverKeyId
        selectedOwner.val selectedAccept bounds mode adversary observe budget bounded)
      (kem_distance (n := n) setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept observe
        functional bounded))

/-- One-sided probability transport for the same arbitrary event, with its own explicit reductions. -/
theorem source_probability (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication)) :
    Pr{let won ← (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
      bounds mode adversary (fun result => observe (result.1, result.2.1)))}[won = true] ≤
      Pr{let won ← (uniform (n := n) setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept observe)}[won = true] +
      ENNReal.ofReal (keyLoss (n := n) setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept observe +
        kemLoss (n := n) setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept observe) := by
  simpa only [← prEvent_eq_evalDist_singleton] using
    (ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance
      (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
        bounds mode adversary (fun result => observe (result.1, result.2.1)))
      (uniform (n := n) setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept observe)).trans
      (add_le_add le_rfl (ENNReal.ofReal_le_ofReal
        (source_distance (n := n) setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept observe
          representation correct functional bounded)))

end BeaconcryptCore.Computational.RegistrationNativeObservableHybrid

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeObservableHybrid.kem_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeObservableHybrid.kem_distance
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeObservableHybrid.source_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeObservableHybrid.source_distance
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeObservableHybrid.source_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeObservableHybrid.source_probability
