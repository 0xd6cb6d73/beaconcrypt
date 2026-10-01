import BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivacy

/-! Exact ordinary reduction and challenger bills for the complete pre-raw reference decision. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivacyResources
open AdaptiveCtxReceive PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor
open PqxdhServerAuthSourceCosts PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh
open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation PqxdhServerAuthPublicationPrivacy
variable {ι KemSK Reader WireResponse : Type} {baseSpec : OracleSpec ι}

/-- Every ordinary source coin and every possible shared/selected hash miss, with one selected seal and no raw opening. -/
def primitiveBudget (H : Nat) : Nat := H + 64 * (H + 1)

/-- Both concrete ordinary reductions retain all source work. Prefix validation adds one encryption, while the view reduction forwards only the original selected seal. -/
theorem primitive_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) (decode : RawDecoder) :
    let H := entryReductionBudget caps qCoin Q qHash qH + 76
    (validation setup codec checks adversary Q j decode H).main.IsQueryBoundP
        AdaptiveRawNonceAead.IsPrimitiveUniformQuery (primitiveBudget H) ∧
      (validation setup codec checks adversary Q j decode H).main.IsQueryBoundP
        IsModifiedNonceAeadSealQuery 2 ∧
      (view setup codec checks adversary Q j decode).main.IsQueryBoundP
        AdaptiveRawNonceAead.IsPrimitiveUniformQuery (primitiveBudget H) ∧
      (view setup codec checks adversary Q j decode).main.IsQueryBoundP
        IsModifiedNonceAeadSealQuery 1 := by
  have bills := PqxdhServerAuthPublicationRandom.decision_bills setup codec checks caps bounded adversary
    qCoin Q qHash qH coins accepts hashes rom j decode
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [validation, primitiveBudget, Nat.add_zero] using
      AdaptiveCtxPrefixValidation.validationReduction_uniform_bound decode setup.source.crypto _ _ _ 1 0
        bills.1 bills.2.1 bills.2.2.1 bills.2.2.2
  · exact AdaptiveCtxPrefixValidation.validationReduction_seal_bound decode setup.source.crypto _ _ 1 bills.2.2.1
  · simpa only [view, primitiveBudget, Nat.add_zero] using
      AdaptiveCtxPrivacyQueryBounds.viewReduction_uniform_bound decode _ _ _ 1 0
        bills.1 bills.2.1 bills.2.2.1 bills.2.2.2
  · exact AdaptiveCtxPrivacyQueryBounds.viewReduction_seal_bound decode _ 1 bills.2.2.1

/-- Each complete ordinary real IND$ challenger additionally samples its 32-byte selected key; every source and digest draw remains charged. -/
theorem real_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) (decode : RawDecoder) :
    let H := entryReductionBudget caps qCoin Q qHash qH + 76
    (modifiedNonceAeadINDDollarRealExp setup.source.crypto
      (validation setup codec checks adversary Q j decode H)).IsTotalQueryBound (32 + primitiveBudget H) ∧
      (modifiedNonceAeadINDDollarRealExp setup.source.crypto
        (view setup codec checks adversary Q j decode)).IsTotalQueryBound (32 + primitiveBudget H) := by
  have bills := PqxdhServerAuthPublicationRandom.decision_bills setup codec checks caps bounded adversary
    qCoin Q qHash qH coins accepts hashes rom j decode
  constructor
  · simpa only [validation, primitiveBudget, Nat.add_zero] using
      AdaptiveCtxPrefixValidation.validationReal_uniform_bound decode setup.source.crypto _ _ _ 1 0
        bills.1 bills.2.1 bills.2.2.1 bills.2.2.2
  · simpa only [view, primitiveBudget, Nat.add_zero] using
      AdaptiveCtxPrivacyQueryBounds.viewReal_uniform_bound decode setup.source.crypto _ _ _ 1 0
        bills.1 bills.2.1 bills.2.2.1 bills.2.2.2

/-- Random challengers charge the source-bounded ciphertext body plus their actual tags. Prefix validation adds a second 16-byte tag; neither random experiment samples a hidden record key. -/
theorem random_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) (decode : RawDecoder) :
    let H := entryReductionBudget caps qCoin Q qHash qH + 76
    (modifiedNonceAeadINDDollarRandomExp
      (validation setup codec checks adversary Q j decode H)).IsTotalQueryBound
        (primitiveBudget H + Aeneas.Std.Usize.max + 32) ∧
      (modifiedNonceAeadINDDollarRandomExp
        (view setup codec checks adversary Q j decode)).IsTotalQueryBound
        (primitiveBudget H + Aeneas.Std.Usize.max + 16) := by
  have bills := PqxdhServerAuthPublicationRandom.decision_bills setup codec checks caps bounded adversary
    qCoin Q qHash qH coins accepts hashes rom j decode
  have bytes := PqxdhServerAuthPublicationRandom.decision_plaintext setup codec checks adversary Q j decode
  constructor
  · simpa only [validation, primitiveBudget, Nat.add_zero] using
      AdaptiveCtxPlaintextQueryBounds.validationRandom_uniform_bound decode setup.source.crypto _ _ _ 1 0
        Aeneas.Std.Usize.max bills.1 bills.2.1 bills.2.2.1 bills.2.2.2 bytes
  · simpa only [view, primitiveBudget, Nat.add_zero, Nat.mul_one, AdaptiveCtxPrivacyGuard.randomView, Nat.add_assoc] using
      AdaptiveCtxPrivacyQueryBounds.viewRandom_uniform_bound decode _ _ _ 1 0
        Aeneas.Std.Usize.max bills.1 bills.2.1 bills.2.2.1 bills.2.2.2 bytes

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivacyResources

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivacyResources.primitive_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivacyResources.primitive_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivacyResources.real_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivacyResources.real_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivacyResources.random_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivacyResources.random_bills
