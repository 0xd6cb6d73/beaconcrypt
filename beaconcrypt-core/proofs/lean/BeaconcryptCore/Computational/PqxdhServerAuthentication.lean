import BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent
import BeaconcryptCore.Computational.PqxdhServerAuthCtxResources
import BeaconcryptCore.Computational.PqxdhServerAuthCtxPrimitiveResources
import BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds
import BeaconcryptCore.Computational.PqxdhServerAuthIntermediate
import BeaconcryptCore.Computational.PqxdhServerAuthNative

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthentication
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor
open PqxdhServerAuthGapDh PqxdhServerAuthAssumptions PqxdhServerAuthSourceCosts
open PqxdhServerAuthBodyCosts PqxdhServerAuthCtxPrimitiveResources
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf CtxNonceAeadIntCtxt
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The complete original R1 authentication event is reduced to the constructed Gap-DH extractor, actual scalar-collision term, five per-entry schedule reductions and concrete ordinary AEAD reductions. All entry-game probabilities are discharged for the same original adversary without an honest-target premise. -/
theorem authentication_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps)
    (adversary : Adversary) (qCoin Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (law : X25519ClassLaw setup.source.crypto)
    (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (fallback : ModifiedNonceAeadForgery) :
    (𝒟[serverAuthGame setup codec checks false adversary] {true}).toReal ≤
      (serverGapDhAdvantage setup.source.crypto setup.joint setup.secretOfSeed setup.wiring
        (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).toReal +
      (Q.choose 2 : ℝ) * 64 / (2 ^ 256 : ℝ) +
      ∑ j : Fin (Q + 1), (PqxdhServerAuthCtxObserverEvent.ctxLoss setup codec checks adversary Q j
        fallback (entryReductionBudget caps qCoin Q qHash qH + 76) +
        entryScheduleLoss setup codec checks adversary false Q j) := by
  apply (PqxdhServerAuthIntermediate.authentication_intermediate_scalar setup codec checks adversary
    Q qH qHash budget law spread correct).trans
  apply add_le_add le_rfl
  refine Finset.sum_le_sum (fun j _ => add_le_add ?_ le_rfl)
  exact PqxdhServerAuthCtxObserverEvent.authentication_bound setup codec checks adversary Q j writable
    fallback _ (PqxdhServerAuthCtxResources.client_hash setup codec checks caps bounded adversary
      qCoin Q qHash qH coins budget.accept budget.hash budget.rom j)

/-- The same explicit reduction bound holds for the production-order native experiment. The complete-continuation constructor theorem preserves every source field, oracle effect and original event without a marginal sampling shortcut. -/
theorem source_order_authentication (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps)
    (adversary : Adversary) (qCoin Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (law : X25519ClassLaw setup.source.crypto)
    (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (fallback : ModifiedNonceAeadForgery) :
    (𝒟[PqxdhServerAuthNative.sourceOrdered setup codec checks false adversary] {true}).toReal ≤
      (serverGapDhAdvantage setup.source.crypto setup.joint setup.secretOfSeed setup.wiring
        (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).toReal +
      (Q.choose 2 : ℝ) * 64 / (2 ^ 256 : ℝ) +
      ∑ j : Fin (Q + 1), (PqxdhServerAuthCtxObserverEvent.ctxLoss setup codec checks adversary Q j
        fallback (entryReductionBudget caps qCoin Q qHash qH + 76) +
        entryScheduleLoss setup codec checks adversary false Q j) := by
  simpa only [PqxdhServerAuthNative.source_order_game] using
    authentication_bound setup codec checks caps bounded adversary qCoin Q qH qHash budget coins
      law spread correct writable fallback

/-- Complete ledgers for the exact finite family of reductions in the authentication bound. The weighted byte bill is derived from the original builder, not an adversary promise. -/
structure ReductionBills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (caps : KemCaps) (qCoin Q qH qHash : Nat)
    (fallback : ModifiedNonceAeadForgery) : Prop where
  components : PqxdhServerAuthIntermediate.ReductionBills setup codec checks adversary caps qCoin Q qH qHash
  ctxSource : ∀ j : Fin (Q + 1),
    (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j).IsTotalQueryBound
      (entryReductionBudget caps qCoin Q qHash qH + 76)
  ctxBytes : ∀ j : Fin (Q + 1), AdaptiveCtxDynamicKnownBounds.PlaintextBound
    (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j) Aeneas.Std.Usize.max
  ctxGame : ∀ j : Fin (Q + 1),
    (AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j)).IsTotalQueryBound
      (entryReductionBudget caps qCoin Q qHash qH + 108)
  ctxOrdinary : ∀ j : Fin (Q + 1),
    let observer := RawCtxSelectedAuthenticationObserver.decision
      (RawCtxUniversalDecoder.decoder codec.frameRead)
      (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j)
    let reduction := AdaptiveCtxDynamicKnownKeys.decisionClient setup.source.crypto observer
    reduction.IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform
        (entryReductionBudget caps qCoin Q qHash qH + 76) ∧
      reduction.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash
        (entryReductionBudget caps qCoin Q qHash qH + 76) ∧
      reduction.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 1 ∧
      reduction.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery 1
  ctxPrimitives : ∀ j : Fin (Q + 1),
    let validation := PqxdhServerAuthCtxObserverEvent.validation setup codec checks adversary Q j
      (entryReductionBudget caps qCoin Q qHash qH + 76)
    let integrity := PqxdhServerAuthCtxObserverEvent.integrity setup codec checks adversary Q j fallback
    validation.main.IsQueryBoundP AdaptiveRawNonceAead.IsPrimitiveUniformQuery
        (primitiveUniformBudget caps qCoin Q qHash qH) ∧
      validation.main.IsQueryBoundP IsModifiedNonceAeadSealQuery 2 ∧
      integrity.main.IsQueryBoundP AdaptiveRawNonceAead.IsPrimitiveUniformQuery
        (primitiveUniformBudget caps qCoin Q qHash qH) ∧
      integrity.MakesAtMostSealQueries 1
  ctxReal : ∀ j : Fin (Q + 1),
    (CtxNonceAeadIndDollarValidation.modifiedNonceAeadINDDollarRealExp setup.source.crypto
      (PqxdhServerAuthCtxObserverEvent.validation setup codec checks adversary Q j
        (entryReductionBudget caps qCoin Q qHash qH + 76))).IsTotalQueryBound
        (32 + primitiveUniformBudget caps qCoin Q qHash qH) ∧
      (modifiedNonceAeadINTCTXTGame setup.source.crypto
        (PqxdhServerAuthCtxObserverEvent.integrity setup codec checks adversary Q j fallback)).IsTotalQueryBound
        (32 + primitiveUniformBudget caps qCoin Q qHash qH)
  ctxRandom : ∀ j : Fin (Q + 1),
    (CtxNonceAeadIndDollarValidation.modifiedNonceAeadINDDollarRandomExp
      (PqxdhServerAuthCtxObserverEvent.validation setup codec checks adversary Q j
        (entryReductionBudget caps qCoin Q qHash qH + 76))).IsTotalQueryBound
      (primitiveUniformBudget caps qCoin Q qHash qH + Aeneas.Std.Usize.max + 32)

/-- Every final reduction ledger is derived from the original source budgets and the concrete overflow gate. No component query count or weighted plaintext budget is left as an ambient premise. -/
theorem reduction_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps)
    (adversary : Adversary) (qCoin Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (fallback : ModifiedNonceAeadForgery) :
    ReductionBills setup codec checks adversary caps qCoin Q qH qHash fallback := by
  exact ⟨PqxdhServerAuthIntermediate.intermediate_reduction_bills setup codec checks caps bounded
      adversary qCoin Q qH qHash budget coins,
    fun j => PqxdhServerAuthCtxResources.client_total setup codec checks caps bounded adversary
      qCoin Q qHash qH coins budget.accept budget.hash budget.rom j,
    fun j => PqxdhServerAuthCtxByteBounds.client_plaintext setup codec checks adversary Q j,
    fun j => PqxdhServerAuthCtxResources.source_game_uniform setup codec checks caps bounded adversary
      qCoin Q qHash qH coins budget.accept budget.hash budget.rom j,
    fun j => PqxdhServerAuthCtxResources.reduction_bills setup codec checks caps bounded adversary
      qCoin Q qHash qH coins budget.accept budget.hash budget.rom j,
    fun j => PqxdhServerAuthCtxPrimitiveResources.primitive_bills setup codec checks caps bounded adversary
      qCoin Q qHash qH coins budget.accept budget.hash budget.rom j fallback,
    fun j => PqxdhServerAuthCtxPrimitiveResources.real_game_uniform setup codec checks caps bounded adversary
      qCoin Q qHash qH coins budget.accept budget.hash budget.rom j fallback,
    fun j => PqxdhServerAuthCtxPrimitiveResources.validation_random_uniform setup codec checks caps bounded adversary
      qCoin Q qHash qH coins budget.accept budget.hash budget.rom j Aeneas.Std.Usize.max
      (PqxdhServerAuthCtxByteBounds.client_plaintext setup codec checks adversary Q j)⟩

/-- Production-order authentication and the complete resource ledger for every constructed reduction, in one statement over the same original adversary. -/
theorem source_order_authentication_with_resources (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps)
    (adversary : Adversary) (qCoin Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (law : X25519ClassLaw setup.source.crypto)
    (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (fallback : ModifiedNonceAeadForgery) :
    (𝒟[PqxdhServerAuthNative.sourceOrdered setup codec checks false adversary] {true}).toReal ≤
      (serverGapDhAdvantage setup.source.crypto setup.joint setup.secretOfSeed setup.wiring
        (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).toReal +
      (Q.choose 2 : ℝ) * 64 / (2 ^ 256 : ℝ) +
      ∑ j : Fin (Q + 1), (PqxdhServerAuthCtxObserverEvent.ctxLoss setup codec checks adversary Q j
        fallback (entryReductionBudget caps qCoin Q qHash qH + 76) +
        entryScheduleLoss setup codec checks adversary false Q j) ∧
    ReductionBills setup codec checks adversary caps qCoin Q qH qHash fallback := by
  exact ⟨source_order_authentication setup codec checks caps bounded adversary qCoin Q qH qHash
    budget coins law spread correct writable fallback,
    reduction_bills setup codec checks caps bounded adversary qCoin Q qH qHash budget coins fallback⟩

end BeaconcryptCore.Computational.PqxdhServerAuthentication

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthentication.authentication_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthentication.authentication_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthentication.source_order_authentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthentication.source_order_authentication

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthentication.reduction_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthentication.reduction_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthentication.source_order_authentication_with_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthentication.source_order_authentication_with_resources
