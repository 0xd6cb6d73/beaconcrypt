-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProductionUniformBound
import BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupNormalSource

/-! The original actual native good target retains its literal public prekey condition through every hop. Exact whole-startup marginal source laws connect the original KDF game to one ordinary observed KEM comparison; the uniform-side selected-origin, repeat and record proofs discharge the remaining target event. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProductionTargetBound
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds)
open PqxdhRecordLiftInterface (EffectKind)
variable {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
  (budget : Budget) (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))
  (allowance : Fin 14 → EffectKind → Nat) (constructorCoins mlCoins : Nat)
  (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)

noncomputable def loss : ℝ≥0∞ :=
  ENNReal.ofReal (RegistrationNativeProductionKeyBound.keyLoss (n := budget.cap 4 + budget.cap 5) setup checks wire route source ensureInit identityIndex serverKeyId
    bounds adversary budget target claim) +
  ENNReal.ofReal (RegistrationNativeProductionPrior.kemLoss setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim) +
  RegistrationNativeProductionUniformBound.loss setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim
    allowance constructorCoins mlCoins fallback

attribute [local irreducible] RegistrationNativeOpenKeyKemGame.normal RegistrationNativeExperiment.profile
  RegistrationNativeRelatedFamily.advantage RegistrationBoundKeySchedule.keyLoss
  RegistrationNativeKemEarlyObservedGame.branch

/-- Every original canonical native good-target probability has the explicit related-input, five KDF, one KEM, repeat, record and byte-entropy bound. -/
theorem bound (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (readback : RegistrationNativeWire.InitReadBack wire) (responseReadback : RegistrationNativeWire.ResponseReadBack wire)
    (framed : ∀ context ∈ support (RegistrationNativeSelectiveRecordTraceUniformSecurity.prior setup budget target.2),
      RegistrationNativeSelectiveRecordFrame.Frame (n := budget.cap 4 + budget.cap 5) setup checks wire source
        context.seed context.scalar context.candidate (RegistrationNativeSelectiveRecordTraceUniformSecurity.provider setup target.2.val context)
        target.2.val target.1.val allowance)
    (constructorBound : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound constructorCoins)
    (mlBound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound mlCoins) :
    Pr{let won ← (RegistrationNativeExperiment.profile (n := budget.cap 4 + budget.cap 5) setup checks wire route representation source ensureInit identityIndex serverKeyId
      bounds .P adversary (RegistrationNativePrekeyEvents.targetEvent setup.source.crypto wire serverKeyId budget target claim))}[won = true] ≤
      loss setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim allowance constructorCoins mlCoins fallback := by
  have original := RegistrationNativeProductionKeyBound.source_bound (n := budget.cap 4 + budget.cap 5) setup checks wire route source ensureInit identityIndex serverKeyId
    bounds adversary budget target claim representation correct bounded
  have normalEq := RegistrationNativeG3NativeStartupNormalSource.normal_source (n := budget.cap 4 + budget.cap 5) setup checks wire source route ensureInit identityIndex serverKeyId
    target.2.val target.1.val bounds .P adversary (RegistrationNativeProductionKeyBound.decision setup wire serverKeyId budget target claim)
  have observerEq : RegistrationNativeG3NativeStartupDecision.decision
      (RegistrationNativeProductionKeyBound.decision setup wire serverKeyId budget target claim) =
      (RegistrationNativeProductionPrior.decision (n := budget.cap 4 + budget.cap 5) (source := source) setup wire serverKeyId budget target claim) := by
    funext result
    rcases result with ⟨context, _ | outcome⟩ <;> rfl
  rw [observerEq] at normalEq
  change RegistrationNativeProductionKeyBound.normal (n := budget.cap 4 + budget.cap 5) setup checks wire route source ensureInit identityIndex serverKeyId
    bounds adversary budget target claim =
      RegistrationNativeProductionPrior.normal setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim at normalEq
  rw [normalEq] at original
  have kem := RegistrationNativeProductionPrior.kem_bound setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim functional bounded
  have compare := ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance
    (RegistrationNativeProductionPrior.normal setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim)
    (RegistrationNativeProductionPrior.uniform setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim)
  have viaKem := compare.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal kem))
  rw [← prEvent_eq_evalDist_singleton, ← prEvent_eq_evalDist_singleton] at viaKem
  have uniform := RegistrationNativeProductionUniformBound.bound setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim
    allowance constructorCoins mlCoins fallback bounded readback responseReadback framed constructorBound mlBound correct
  have all := original.trans (add_le_add (viaKem.trans (add_le_add uniform le_rfl)) le_rfl)
  simpa only [loss, add_assoc, add_comm, add_left_comm] using all

end BeaconcryptCore.Computational.RegistrationNativeProductionTargetBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProductionTargetBound.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProductionTargetBound.bound
