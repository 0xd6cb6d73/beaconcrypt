-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeDecisionG2Bound
import BeaconcryptCore.Computational.RegistrationNativePrekeyProbability

/-! Each original canonical good target keeps its literal complementary public-prekey decision through the actual generated native source, related-input hop and five-loss key schedule. The sole target sum and real-source origin charge are composed only after every target's later uniform/record bound is established. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProductionKeyBound
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

noncomputable def decision (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (result : Value × RegistrationNativeLedger.State) : Bool :=
  RegistrationNativePrekeyEvents.targetEvent setup.source.crypto wire serverKeyId budget target claim (result.1, (result.2, ()))

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
  (budget : Budget) (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))

noncomputable def normal : ProbComp Bool :=
  RegistrationNativeOpenKeyKemGame.normal setup.baseImpl setup.kem
    (RegistrationNativeDecisionG2Bound.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId target.2.val target.1.val
      bounds .P adversary (decision setup wire serverKeyId budget target claim))

noncomputable def keyLoss : ℝ :=
  RegistrationNativeRelatedFamily.advantage setup.hmac setup.joint setup.dh
    (fun publicValue => simulateQ RegistrationNativeRelatedRoot.reduction
      (RegistrationNativePublicSourceProfile.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId target.2.val target.1.val
        bounds .P adversary (decision setup wire serverKeyId budget target claim) publicValue)) +
  ∑ index ∈ Finset.range (budget.cap 4 + budget.cap 5), RegistrationBoundKeySchedule.keyLoss setup.source setup.hmac
    (RegistrationNativeKeyHybrid.reduction setup.source setup.hmac
      (RegistrationNativeDecisionKeyExperiment.entryClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId target.2.val target.1.val
        bounds .P adversary (decision setup wire serverKeyId budget target claim)) index)

/-- The actual original good-target probability reaches the concrete open G2 normal game with its derived related-input and five primitive losses. -/
theorem source_bound (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue)) :
    Pr{let won ← (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
      (RegistrationNativePrekeyEvents.targetEvent setup.source.crypto wire serverKeyId budget target claim))}[won = true] ≤
      Pr{let won ← (normal (n := n) setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim)}[won = true] +
        ENNReal.ofReal (keyLoss (n := n) setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim) := by
  have same : (fun (result : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source)) =>
      decision setup wire serverKeyId budget target claim (result.1, result.2.1)) =
      RegistrationNativePrekeyEvents.targetEvent setup.source.crypto wire serverKeyId budget target claim := by
    funext result
    rfl
  have compared := RegistrationNativeDecisionG2Bound.source_distance (n := n) setup checks wire route representation correct source ensureInit identityIndex serverKeyId
    target.2.val target.1.val bounds .P adversary (decision setup wire serverKeyId budget target claim) budget bounded
  rw [same] at compared
  change (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
    (RegistrationNativePrekeyEvents.targetEvent setup.source.crypto wire serverKeyId budget target claim)).boolDistance
      (normal (n := n) setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim) ≤
        keyLoss (n := n) setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim at compared
  have probability := ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance
    (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
      (RegistrationNativePrekeyEvents.targetEvent setup.source.crypto wire serverKeyId budget target claim))
    (normal (n := n) setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim)
  simpa only [← prEvent_eq_evalDist_singleton] using probability.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal compared))

end BeaconcryptCore.Computational.RegistrationNativeProductionKeyBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProductionKeyBound.source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProductionKeyBound.source_bound
