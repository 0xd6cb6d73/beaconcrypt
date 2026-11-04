-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeLorWeightedSecurity

/-! The two original native LR probability directions give the stated centered absolute advantage. Infinite loss is handled directly; otherwise only finite probability and loss values are converted to real numbers. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeLorAbsoluteSecurity

theorem absolute_of_centered (win select loss : ℝ≥0∞) (finiteWin : win ≠ ⊤) (finiteSelect : select ≠ ⊤)
    (upper : win ≤ 2⁻¹ * select + loss) (lower : 2⁻¹ * select ≤ win + loss) :
    ENNReal.ofReal |win.toReal - (1 / 2 : ℝ) * select.toReal| ≤ loss := by
  by_cases finiteLoss : loss = ⊤
  · rw [finiteLoss]; exact le_top
  · have finiteHalf : (2⁻¹ : ℝ≥0∞) ≠ ⊤ := by norm_num
    have first := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top finiteHalf finiteSelect, finiteLoss⟩) upper
    have second := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨finiteWin, finiteLoss⟩) lower
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top finiteHalf finiteSelect) finiteLoss, ENNReal.toReal_mul] at first
    rw [ENNReal.toReal_add finiteWin finiteLoss, ENNReal.toReal_mul] at second
    have half : (2⁻¹ : ℝ≥0∞).toReal = (1 / 2 : ℝ) := by norm_num
    rw [half] at first second
    apply (ENNReal.ofReal_le_iff_le_toReal finiteLoss).mpr
    exact abs_le.mpr ⟨by linarith, by linarith⟩

open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds)
open PqxdhRecordLiftInterface (EffectKind)
open RegistrationNativeSelectiveRecordTraceUniformSecurity (Context prior provider)
open RegistrationNativeLorWeightedSecurity (broadGame delta originLoss)
variable {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (bounds : FreshBounds)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
  (budget : Budget) (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
  (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (allowance : Fin 14 → EffectKind → Nat) (constructorCoins mlCoins : Nat)
  (hmac : PqxdhSecretInputKdf.HmacSha512) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
local notation "worldCount" => budget.cap 4 + budget.cap 5

set_option maxHeartbeats 1200000 in
/-- The unchanged broad native experiment satisfies its original centered absolute LR expression, including startup failure and failed admitted sends. -/
theorem centered_absolute
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (framed : ∀ chosen : Fin budget.accept × Fin budget.capacity, ∀ context ∈ support (prior setup budget chosen.2), RegistrationNativeSelectiveRecordFrame.Frame (n := worldCount) setup checks wire source
      context.seed context.scalar context.candidate (provider setup chosen.2.val context) chosen.2.val chosen.1.val allowance)
    (constructorBound : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound constructorCoins)
    (mlBound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound mlCoins)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac)
    (sourceCorrect : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (readback : RegistrationNativeWire.InitReadBack wire) (responseReadback : RegistrationNativeWire.ResponseReadBack wire)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes,
      bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
    (count : Nat) (room : budget.create ≤ count + 1)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    ENNReal.ofReal |(𝒟[broadGame setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget filter guess representation true] {true}).toReal -
      (1 / 2 : ℝ) * (𝒟[broadGame setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget filter guess representation false] {true}).toReal| ≤
      originLoss setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget representation count identityFallback ordinaryFallback +
      (∑ chosen : Fin budget.accept × Fin budget.capacity, delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget chosen filter guess allowance constructorCoins mlCoins hmac fallback true) +
      2⁻¹ * (∑ chosen : Fin budget.accept × Fin budget.capacity, delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget chosen filter guess allowance constructorCoins mlCoins hmac fallback false) := by
  have both := RegistrationNativeLorWeightedSecurity.centered setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget filter guess representation
    allowance constructorCoins mlCoins hmac fallback bounded framed constructorBound mlBound correct sourceCorrect functional readback responseReadback shortRejects count room identityFallback ordinaryFallback
  apply absolute_of_centered
  · rw [← prEvent_eq_evalDist_singleton _ true]; exact prEvent_ne_top _
  · rw [← prEvent_eq_evalDist_singleton _ true]; exact prEvent_ne_top _
  · simpa only [add_assoc] using both.1
  · simpa only [add_assoc] using both.2

end BeaconcryptCore.Computational.RegistrationNativeLorAbsoluteSecurity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorAbsoluteSecurity.absolute_of_centered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorAbsoluteSecurity.absolute_of_centered

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorAbsoluteSecurity.centered_absolute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorAbsoluteSecurity.centered_absolute
