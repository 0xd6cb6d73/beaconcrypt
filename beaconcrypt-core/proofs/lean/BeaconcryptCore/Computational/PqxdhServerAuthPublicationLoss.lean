import BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivacy
import BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent

/-! Explicit ordinary advantages and statistical coefficients in the publication comparison. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationLoss
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor
open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The original raw authentication comparison and the unpublished-prefix comparison are both charged. Their validation distinguishers remain distinct. -/
noncomputable def recordLoss (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (fallback : ModifiedNonceAeadForgery) (H : Nat) : ℝ :=
  PqxdhServerAuthCtxObserverEvent.ctxLoss setup codec checks adversary Q j fallback H +
    PqxdhServerAuthPublicationPrivacy.loss setup codec checks adversary Q j
      (RawCtxUniversalDecoder.decoder codec.frameRead) H

/-- Expanding the finite ordinary losses exposes three separately constructed IND$ distinguishers, the existing integrity reduction with coefficient two and every statistical term. -/
theorem recordLoss_expanded (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (fallback : ModifiedNonceAeadForgery) (H : Nat) :
    recordLoss setup codec checks adversary Q j fallback H =
      modifiedNonceAeadINDDollarAdvantage setup.source.crypto
        (PqxdhServerAuthCtxObserverEvent.validation setup codec checks adversary Q j H) +
      2 * (modifiedNonceAeadINTCTXTAdvantage setup.source.crypto
        (PqxdhServerAuthCtxObserverEvent.integrity setup codec checks adversary Q j fallback)).toReal +
      modifiedNonceAeadINDDollarAdvantage setup.source.crypto
        (PqxdhServerAuthPublicationPrivacy.validation setup codec checks adversary Q j
          (RawCtxUniversalDecoder.decoder codec.frameRead) H) +
      modifiedNonceAeadINDDollarAdvantage setup.source.crypto
        (PqxdhServerAuthPublicationPrivacy.view setup codec checks adversary Q j
          (RawCtxUniversalDecoder.decoder codec.frameRead)) +
      (2 * (H : ℝ) + 1) / 2 ^ 128 + 1 / 2 ^ 512 := by
  have nonnegative (reduction : ModifiedNonceAeadINDDollarAdversary) :
      0 ≤ modifiedNonceAeadINDDollarAdvantage setup.source.crypto reduction := abs_nonneg _
  have integrityFinite : modifiedNonceAeadINTCTXTAdvantage setup.source.crypto
      (PqxdhServerAuthCtxObserverEvent.integrity setup codec checks adversary Q j fallback) ≠ ⊤ := prEvent_ne_top _
  simp only [recordLoss, PqxdhServerAuthCtxObserverEvent.ctxLoss, PqxdhServerAuthCtxObserverEvent.ctxLossENN,
    PqxdhServerAuthPublicationPrivacy.loss, PqxdhServerAuthPublicationPrivacy.lossENN]
  have finiteStat : (H : ℝ≥0∞) * ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.inv_ne_top.mpr
      (Nat.cast_ne_zero.mpr (pow_ne_zero 128 (by decide : (2 : Nat) ≠ 0))))
  have finiteIntegrity : 2 * modifiedNonceAeadINTCTXTAdvantage setup.source.crypto
      (PqxdhServerAuthCtxObserverEvent.integrity setup codec checks adversary Q j fallback) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) integrityFinite
  have finiteGuesses : (1 : ℝ≥0∞) / (2 ^ 512 : Nat) ≠ ⊤ ∧
      ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ⟨ENNReal.div_ne_top (by norm_num) (Nat.cast_ne_zero.mpr (pow_ne_zero 512 (by decide : (2 : Nat) ≠ 0))),
      ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (pow_ne_zero 128 (by decide : (2 : Nat) ≠ 0)))⟩
  rw [ENNReal.toReal_add
      (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, finiteStat⟩, finiteIntegrity⟩) finiteGuesses.1,
    ENNReal.toReal_add
      (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, finiteStat⟩, ENNReal.ofReal_ne_top⟩) finiteGuesses.2]
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, finiteStat⟩) finiteIntegrity,
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, finiteStat⟩) ENNReal.ofReal_ne_top,
    ENNReal.toReal_add ENNReal.ofReal_ne_top finiteStat, ENNReal.toReal_add ENNReal.ofReal_ne_top finiteStat]
  simp only [ENNReal.toReal_ofReal (nonnegative _), ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_ofNat, ENNReal.toReal_one, Nat.cast_pow, Nat.cast_ofNat, ENNReal.toReal_pow]
  simp only [div_eq_mul_inv, add_mul, two_mul, one_mul]
  ac_rfl

/-- Every ordinary loss remains nonnegative before the owner-family sum. -/
theorem recordLoss_nonneg (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (fallback : ModifiedNonceAeadForgery) (H : Nat) :
    0 ≤ recordLoss setup codec checks adversary Q j fallback H :=
  add_nonneg (PqxdhServerAuthCtxObserverEvent.ctxLoss_nonneg setup codec checks adversary Q j fallback H)
    ENNReal.toReal_nonneg

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationLoss

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationLoss.recordLoss_expanded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationLoss.recordLoss_expanded
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationLoss.recordLoss_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationLoss.recordLoss_nonneg
