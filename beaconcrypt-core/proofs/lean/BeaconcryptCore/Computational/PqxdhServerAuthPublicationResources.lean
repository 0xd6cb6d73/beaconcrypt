import BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler
import BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixSource
import BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivacyResources
import BeaconcryptCore.Computational.PqxdhServerAuthentication

/-! Complete source and constructed-reduction ledgers for the owner-indexed publication observation. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationResources
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthSourceCosts
open PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh PqxdhServerAuthCtxPrimitiveResources
open PqxdhSecretInputKdf CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

private theorem source_map {Result Mapped : Type} (real : Bool) (decode : AdaptiveCtxReceive.RawDecoder)
    (crypto : Pqxdh.Crypto) (f : Result → Mapped)
    (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result) :
    AdaptiveCtxDynamicKnownKeys.sourceGame real decode crypto (f <$> work) =
      Prod.map f id <$> AdaptiveCtxDynamicKnownKeys.sourceGame real decode crypto work := by
  simp only [AdaptiveCtxDynamicKnownKeys.sourceGame, simulateQ_map, StateT.run_map, map_bind]
  rfl

/-- Pure terminal projections retain the entire interpreted query tree, including the selected key draw, shared cache and source generator order. -/
theorem client_source_budget {Budget : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (observer : PqxdhServerAuthObservedEntry.Observer) (available : Budget)
    (allowed : unifSpec.Domain → Budget → Prop) (cost : unifSpec.Domain → Budget → Budget) :
    (AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto (PqxdhServerAuthPublicationObservedCompiler.client setup codec checks adversary Q j observer)).IsQueryBound
        available allowed cost ↔
    (AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j)).IsQueryBound
        available allowed cost := by
  rw [← PqxdhServerAuthPublicationObservedCompiler.full_client setup codec checks adversary Q j observer,
    ← PqxdhServerAuthPublicationObservedCompiler.full_original setup codec checks adversary Q j]
  simp only [source_map, isQueryBound_map_iff]

/-- Complete resource statement for the actual observation client and its interpreted game. The public journal and terminal observer add local work but no component requests. -/
def SourceBills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (observer : PqxdhServerAuthObservedEntry.Observer) (H : Nat) : Prop :=
  let client := PqxdhServerAuthPublicationObservedCompiler.client setup codec checks adversary Q j observer
  client.IsTotalQueryBound H ∧
    client.IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute H ∧
    client.IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute H ∧
    client.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 1 ∧
    client.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 1 ∧
    AdaptiveCtxDynamicKnownBounds.PlaintextBound client Aeneas.Std.Usize.max ∧
    (AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto client).IsTotalQueryBound (H + 32)

/-- The unchanged original budgets pay for the whole observed program and actual interpreted source; neither opaque base work nor a hidden key draw is omitted. -/
theorem source_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps)
    (adversary : Adversary) (qCoin Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (j : Fin (Q + 1)) (observer : PqxdhServerAuthObservedEntry.Observer) :
    SourceBills setup codec checks adversary Q j observer (entryReductionBudget caps qCoin Q qHash qH + 76) := by
  have total : (PqxdhServerAuthPublicationObservedCompiler.client setup codec checks adversary Q j observer).IsTotalQueryBound
      (entryReductionBudget caps qCoin Q qHash qH + 76) := (PqxdhServerAuthPublicationObservedCompiler.client_budget setup codec checks adversary Q j observer
    _ _ _).mpr (PqxdhServerAuthCtxResources.client_total setup codec checks caps bounded adversary
      qCoin Q qHash qH coins budget.accept budget.hash budget.rom j)
  have records := PqxdhServerAuthPublicationObservedCompiler.client_record_bills setup codec checks adversary Q j observer
  refine ⟨total, IsQueryBoundP.of_imp (fun _ _ => True.intro) total.isQueryBoundP,
    IsQueryBoundP.of_imp (fun _ _ => True.intro) total.isQueryBoundP, records.1, records.2.1, records.2.2, ?_⟩
  apply (client_source_budget setup codec checks adversary Q j observer _ _ _).mpr
  simpa only [Nat.add_assoc, Nat.reduceAdd, IsTotalQueryBound] using PqxdhServerAuthCtxResources.source_game_uniform setup codec checks caps bounded
    adversary qCoin Q qHash qH coins budget.accept budget.hash budget.rom j

/-- Every constructed endpoint in the publication bound has a concrete ledger. Observation-dependent schedule reductions are separate from the reused ordinary authentication reductions and the unpublished-prefix privacy reductions. -/
structure ReductionBills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (caps : KemCaps) (qCoin Q qH qHash : Nat)
    (observers : Fin (Q + 1) → PqxdhServerAuthObservedEntry.Observer)
    (fallback : ModifiedNonceAeadForgery) : Prop where
  components : PqxdhServerAuthPublicationOwnerFamily.ObservedBills setup codec checks adversary Q observers caps qCoin qH qHash
  source : ∀ j : Fin (Q + 1), SourceBills setup codec checks adversary Q j (observers j)
    (entryReductionBudget caps qCoin Q qHash qH + 76)
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
  capture : ∀ j : Fin (Q + 1),
    let work := PqxdhServerAuthPublicationPrefixStop.capture
      (PqxdhServerAuthPublicationPrefixSource.client setup codec checks adversary Q j) none false
    let H := entryReductionBudget caps qCoin Q qHash qH + 76
    work.IsTotalQueryBound H ∧
      work.IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute H ∧
      work.IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute H ∧
      work.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 1 ∧
      work.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 ∧
      AdaptiveCtxDynamicKnownBounds.PlaintextBound work Aeneas.Std.Usize.max
  privacyPrimitives : ∀ j : Fin (Q + 1),
    let H := entryReductionBudget caps qCoin Q qHash qH + 76
    let decode := RawCtxUniversalDecoder.decoder codec.frameRead
    (PqxdhServerAuthPublicationPrivacy.validation setup codec checks adversary Q j decode H).main.IsQueryBoundP
        AdaptiveRawNonceAead.IsPrimitiveUniformQuery (PqxdhServerAuthPublicationPrivacyResources.primitiveBudget H) ∧
      (PqxdhServerAuthPublicationPrivacy.validation setup codec checks adversary Q j decode H).main.IsQueryBoundP
        IsModifiedNonceAeadSealQuery 2 ∧
      (PqxdhServerAuthPublicationPrivacy.view setup codec checks adversary Q j decode).main.IsQueryBoundP
        AdaptiveRawNonceAead.IsPrimitiveUniformQuery (PqxdhServerAuthPublicationPrivacyResources.primitiveBudget H) ∧
      (PqxdhServerAuthPublicationPrivacy.view setup codec checks adversary Q j decode).main.IsQueryBoundP
        IsModifiedNonceAeadSealQuery 1
  privacyReal : ∀ j : Fin (Q + 1),
    let H := entryReductionBudget caps qCoin Q qHash qH + 76
    let decode := RawCtxUniversalDecoder.decoder codec.frameRead
    (modifiedNonceAeadINDDollarRealExp setup.source.crypto
      (PqxdhServerAuthPublicationPrivacy.validation setup codec checks adversary Q j decode H)).IsTotalQueryBound
        (32 + PqxdhServerAuthPublicationPrivacyResources.primitiveBudget H) ∧
      (modifiedNonceAeadINDDollarRealExp setup.source.crypto
        (PqxdhServerAuthPublicationPrivacy.view setup codec checks adversary Q j decode)).IsTotalQueryBound
        (32 + PqxdhServerAuthPublicationPrivacyResources.primitiveBudget H)
  privacyRandom : ∀ j : Fin (Q + 1),
    let H := entryReductionBudget caps qCoin Q qHash qH + 76
    let decode := RawCtxUniversalDecoder.decoder codec.frameRead
    (modifiedNonceAeadINDDollarRandomExp
      (PqxdhServerAuthPublicationPrivacy.validation setup codec checks adversary Q j decode H)).IsTotalQueryBound
        (PqxdhServerAuthPublicationPrivacyResources.primitiveBudget H + Aeneas.Std.Usize.max + 32) ∧
      (modifiedNonceAeadINDDollarRandomExp
        (PqxdhServerAuthPublicationPrivacy.view setup codec checks adversary Q j decode)).IsTotalQueryBound
        (PqxdhServerAuthPublicationPrivacyResources.primitiveBudget H + Aeneas.Std.Usize.max + 16)

/-- All ledgers follow from the same original adversary caps and source sampler. No reduction or challenger bill is supplied as a security premise. -/
theorem reduction_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps)
    (adversary : Adversary) (qCoin Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (observers : Fin (Q + 1) → PqxdhServerAuthObservedEntry.Observer) (fallback : ModifiedNonceAeadForgery) :
    ReductionBills setup codec checks adversary caps qCoin Q qH qHash observers fallback := by
  have ordinary := PqxdhServerAuthentication.reduction_bills setup codec checks caps bounded adversary
    qCoin Q qH qHash budget coins fallback
  exact ⟨PqxdhServerAuthPublicationOwnerFamily.observed_bills setup codec checks caps bounded adversary
      qCoin Q qH qHash observers budget coins,
    fun j => source_bills setup codec checks caps bounded adversary qCoin Q qH qHash budget coins j (observers j),
    ordinary.ctxOrdinary, ordinary.ctxPrimitives, ordinary.ctxReal, ordinary.ctxRandom,
    fun j => PqxdhServerAuthPublicationPrefixSource.capture_bills setup codec checks caps bounded adversary
      qCoin Q qHash qH coins budget.accept budget.hash budget.rom j,
    fun j => PqxdhServerAuthPublicationPrivacyResources.primitive_bills setup codec checks caps bounded adversary
      qCoin Q qHash qH coins budget.accept budget.hash budget.rom j _,
    fun j => PqxdhServerAuthPublicationPrivacyResources.real_bills setup codec checks caps bounded adversary
      qCoin Q qHash qH coins budget.accept budget.hash budget.rom j _,
    fun j => PqxdhServerAuthPublicationPrivacyResources.random_bills setup codec checks caps bounded adversary
      qCoin Q qHash qH coins budget.accept budget.hash budget.rom j _⟩

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationResources

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationResources.client_source_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationResources.client_source_budget

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationResources.source_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationResources.source_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationResources.reduction_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationResources.reduction_bills
