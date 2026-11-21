import BeaconcryptCore.Computational.PqxdhServerAuthPublicationProbability

/-! Source-order authentication against missing outer publication at the accepted root owner. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublication
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthSourceCosts
open PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh PqxdhServerAuthAssumptions
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf CtxNonceAeadIntCtxt
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Each public source coordinate is observed at its actual root owner. Publication means a successful outer builder reply before the first successful Beacon finish. -/
noncomputable def observers (Q : Nat) : Fin (Q + 1) → PqxdhServerAuthObservedEntry.Observer :=
  fun j => PqxdhServerAuthPublicationOccurrence.observer j.val

/-- The literal native source experiment accepts without an earlier publication at its root owner only with the original disclosure/collision loss, the observation-specific five schedule reductions, and the fully charged ordinary authentication and unpublished-prefix losses. The theorem claims owner publication, not equality of outer assigned IDs or a complete response tuple. -/
theorem owner_publication_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (law : X25519ClassLaw setup.source.crypto) (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (fallback : ModifiedNonceAeadForgery) :
    (𝒟[PqxdhServerAuthObservedExecution.orderedGame setup codec checks adversary false
      (PqxdhServerAuthPublicationOwnerFamily.observation setup Q (observers Q))] {true}).toReal ≤
      (serverGapDhAdvantage setup.source.crypto setup.joint setup.secretOfSeed setup.wiring
        (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).toReal +
      (Q.choose 2 : ℝ) * 64 / (2 ^ 256 : ℝ) +
      ∑ j : Fin (Q + 1), (PqxdhServerAuthPublicationLoss.recordLoss setup codec checks adversary Q j fallback
        (entryReductionBudget caps qCoin Q qHash qH + 76) +
        PqxdhServerAuthObservedSchedule.scheduleLoss setup codec checks adversary false Q j ((observers Q) j)) := by
  have source := (PqxdhServerAuthPublicationOwnerFamily.ordered_bound_with_resources setup codec checks caps bounded
    adversary qCoin Q qH qHash (observers Q) budget coins law spread correct).1
  refine source.trans (add_le_add le_rfl (Finset.sum_le_sum fun j _ => ?_))
  exact add_le_add
    (PqxdhServerAuthPublicationProbability.uniform_bound setup codec checks caps bounded adversary
      qCoin Q qH qHash budget coins j fallback writable) le_rfl

/-- The numerical source theorem and every constructed reduction ledger hold together for the same observation family and original adversary caps. -/
theorem owner_publication_with_resources (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (law : X25519ClassLaw setup.source.crypto) (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (fallback : ModifiedNonceAeadForgery) :
    (𝒟[PqxdhServerAuthObservedExecution.orderedGame setup codec checks adversary false
      (PqxdhServerAuthPublicationOwnerFamily.observation setup Q (observers Q))] {true}).toReal ≤
      (serverGapDhAdvantage setup.source.crypto setup.joint setup.secretOfSeed setup.wiring
        (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).toReal +
      (Q.choose 2 : ℝ) * 64 / (2 ^ 256 : ℝ) +
      ∑ j : Fin (Q + 1), (PqxdhServerAuthPublicationLoss.recordLoss setup codec checks adversary Q j fallback
        (entryReductionBudget caps qCoin Q qHash qH + 76) +
        PqxdhServerAuthObservedSchedule.scheduleLoss setup codec checks adversary false Q j ((observers Q) j)) ∧
    PqxdhServerAuthPublicationResources.ReductionBills setup codec checks adversary caps
      qCoin Q qH qHash (observers Q) fallback := by
  exact ⟨owner_publication_bound setup codec checks caps bounded adversary qCoin Q qH qHash budget coins
      law spread correct writable fallback,
    PqxdhServerAuthPublicationResources.reduction_bills setup codec checks caps bounded adversary
      qCoin Q qH qHash budget coins (observers Q) fallback⟩

end BeaconcryptCore.Computational.PqxdhServerAuthPublication

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublication.owner_publication_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublication.owner_publication_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublication.owner_publication_with_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublication.owner_publication_with_resources

