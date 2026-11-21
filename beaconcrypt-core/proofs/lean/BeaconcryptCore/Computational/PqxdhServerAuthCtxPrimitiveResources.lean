import BeaconcryptCore.Computational.PqxdhServerAuthCtxResources
import BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent

/-! Explicit ordinary primitive and challenger resource ledgers for the same two reductions in the actual CTX authentication loss. -/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxPrimitiveResources
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthSourceCosts
open PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh
open PqxdhSecretInputKdf PqxdhJointKdfGame CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Every digest-generation request of the actual ordinary primitive reductions is charged in addition to the explicit source randomness. -/
def primitiveUniformBudget (caps : KemCaps) (qCoin Q qHash qH : Nat) : Nat :=
  let H := entryReductionBudget caps qCoin Q qHash qH + 76
  H + 64 * (H + 1 + 1)

/-- The two exact reductions appearing in the final CTX loss retain their full source randomness and attempted primitive sealing allowances. -/
theorem primitive_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) (fallback : ModifiedNonceAeadForgery) :
    let H := entryReductionBudget caps qCoin Q qHash qH + 76
    let validation := PqxdhServerAuthCtxObserverEvent.validation setup codec checks adversary Q j H
    let integrity := PqxdhServerAuthCtxObserverEvent.integrity setup codec checks adversary Q j fallback
    validation.main.IsQueryBoundP AdaptiveRawNonceAead.IsPrimitiveUniformQuery
        (primitiveUniformBudget caps qCoin Q qHash qH) ∧
      validation.main.IsQueryBoundP IsModifiedNonceAeadSealQuery 2 ∧
      integrity.main.IsQueryBoundP AdaptiveRawNonceAead.IsPrimitiveUniformQuery
        (primitiveUniformBudget caps qCoin Q qHash qH) ∧
      integrity.MakesAtMostSealQueries 1 := by
  have bills := PqxdhServerAuthCtxResources.reduction_bills setup codec checks caps bounded adversary
    qCoin Q qHash qH coins accepts hashes rom j
  exact ⟨AdaptiveCtxPrefixValidation.validationReduction_uniform_bound _ setup.source.crypto _ _ _ 1 1
      bills.1 bills.2.1 bills.2.2.1 bills.2.2.2,
    AdaptiveCtxPrefixValidation.validationReduction_seal_bound _ setup.source.crypto _ _ 1 bills.2.2.1,
    AdaptiveCtxQueryBounds.indexedReduction_bounds _ fallback _ _ _ 1 1 0
      bills.1 bills.2.1 bills.2.2.1 bills.2.2.2⟩

/-- The exact real validation and integrity challengers each add their own 32-byte key draw to the constructed reduction's full uniform ledger. -/
theorem real_game_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) (fallback : ModifiedNonceAeadForgery) :
    (modifiedNonceAeadINDDollarRealExp setup.source.crypto
      (PqxdhServerAuthCtxObserverEvent.validation setup codec checks adversary Q j
        (entryReductionBudget caps qCoin Q qHash qH + 76))).IsTotalQueryBound
        (32 + primitiveUniformBudget caps qCoin Q qHash qH) ∧
      (modifiedNonceAeadINTCTXTGame setup.source.crypto
        (PqxdhServerAuthCtxObserverEvent.integrity setup codec checks adversary Q j fallback)).IsTotalQueryBound
        (32 + primitiveUniformBudget caps qCoin Q qHash qH) := by
  have bills := PqxdhServerAuthCtxResources.reduction_bills setup codec checks caps bounded adversary
    qCoin Q qHash qH coins accepts hashes rom j
  exact ⟨AdaptiveCtxPrefixValidation.validationReal_uniform_bound _ setup.source.crypto _ _ _ 1 1
      bills.1 bills.2.1 bills.2.2.1 bills.2.2.2,
    CtxComputationalSecurity.modifiedNonceAeadINTCTXTGame_total_of_uniform_query_bound setup.source.crypto _ _
      (primitive_bills setup codec checks caps bounded adversary qCoin Q qHash qH
        coins accepts hashes rom j fallback).2.2.1⟩

/-- Recording exact oracle replies preserves the weighted selected plaintext-byte ledger on every branch. -/
theorem monitor_plaintext {Result : Type} (client : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result)
    (state : RawCtxSelectedAuthenticationObserver.State) (qBytes : Nat) :
    AdaptiveCtxDynamicKnownBounds.PlaintextBound
      (RawCtxSelectedAuthenticationObserver.monitor client state) qBytes ↔
      AdaptiveCtxDynamicKnownBounds.PlaintextBound client qBytes := by
  induction client using OracleComp.inductionOn generalizing state qBytes with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [RawCtxSelectedAuthenticationObserver.monitor_query,
        AdaptiveCtxDynamicKnownBounds.PlaintextBound, isQueryBound_query_bind_iff] at ih ⊢
      simp only [ih]

/-- Computing the actual authentication observer bit preserves its client's exact selected plaintext-byte budget. -/
theorem observer_plaintext {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (client : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result) (qBytes : Nat) :
    AdaptiveCtxDynamicKnownBounds.PlaintextBound
      (RawCtxSelectedAuthenticationObserver.decision decode client) qBytes ↔
      AdaptiveCtxDynamicKnownBounds.PlaintextBound client qBytes := by
  simpa only [RawCtxSelectedAuthenticationObserver.decision, AdaptiveCtxDynamicKnownBounds.PlaintextBound,
    isQueryBound_map_iff] using monitor_plaintext client RawCtxSelectedAuthenticationObserver.initialState qBytes

/-- The random IND$ challenger pays all submitted body bytes and both 16-byte tags separately; it samples no hidden encryption key. -/
theorem validation_random_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) (qBytes : Nat)
    (bytes : AdaptiveCtxDynamicKnownBounds.PlaintextBound
      (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j) qBytes) :
    (modifiedNonceAeadINDDollarRandomExp
      (PqxdhServerAuthCtxObserverEvent.validation setup codec checks adversary Q j
        (entryReductionBudget caps qCoin Q qHash qH + 76))).IsTotalQueryBound
      (primitiveUniformBudget caps qCoin Q qHash qH + qBytes + 32) := by
  have bills := PqxdhServerAuthCtxResources.reduction_bills setup codec checks caps bounded adversary
    qCoin Q qHash qH coins accepts hashes rom j
  exact AdaptiveCtxPlaintextQueryBounds.validationRandom_uniform_bound _ setup.source.crypto _ _ _ 1 1 qBytes
    bills.1 bills.2.1 bills.2.2.1 bills.2.2.2
    (AdaptiveCtxDynamicKnownBounds.decision_plaintext_bound setup.source.crypto _ qBytes
      ((observer_plaintext _ _ qBytes).2 bytes))

end BeaconcryptCore.Computational.PqxdhServerAuthCtxPrimitiveResources

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxPrimitiveResources.primitive_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxPrimitiveResources.primitive_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxPrimitiveResources.real_game_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxPrimitiveResources.real_game_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxPrimitiveResources.monitor_plaintext' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxPrimitiveResources.monitor_plaintext
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxPrimitiveResources.observer_plaintext' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxPrimitiveResources.observer_plaintext
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxPrimitiveResources.validation_random_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxPrimitiveResources.validation_random_uniform
