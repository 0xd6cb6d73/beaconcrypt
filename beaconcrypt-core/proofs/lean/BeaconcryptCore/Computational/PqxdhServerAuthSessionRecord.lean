import BeaconcryptCore.Computational.PqxdhServerAuthSessionRecordProbability

/-! Source-order joint authentication of the accepted seal fields and the decoded record in an earlier successful owner response. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthSessionRecord
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthSourceCosts
open PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh PqxdhServerAuthAssumptions
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf CtxNonceAeadIntCtxt
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Each source coordinate observes both matching authenticated seal fields and exact decoded-record publication in the chronological public journal, with no supplied private target state. -/
noncomputable def observers (codec : Codec Reader Response) (Q : Nat) : Fin (Q + 1) → PqxdhServerAuthObservedEntry.Observer :=
  fun j => PqxdhServerAuthSessionRecordEvent.observer codec j.val

/-- The actual source-order experiment accepts without both a same-owner matching seal and an earlier owner response containing the same decoded record only with the original disclosure/collision loss, five reductions for this stronger observer and the fully charged record losses. Outer assigned-ID equality and full eleven-field session attribution are not asserted. -/
theorem session_record_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (law : X25519ClassLaw setup.source.crypto) (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (responseBack : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (fallback : ModifiedNonceAeadForgery) :
    (𝒟[PqxdhServerAuthObservedExecution.orderedGame setup codec checks adversary false
      (PqxdhServerAuthPublicationOwnerFamily.observation setup Q (observers codec Q))] {true}).toReal ≤
      (serverGapDhAdvantage setup.source.crypto setup.joint setup.secretOfSeed setup.wiring
        (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).toReal +
      (Q.choose 2 : ℝ) * 64 / (2 ^ 256 : ℝ) +
      ∑ j : Fin (Q + 1), (PqxdhServerAuthPublicationLoss.recordLoss setup codec checks adversary Q j fallback
        (entryReductionBudget caps qCoin Q qHash qH + 76) +
        PqxdhServerAuthObservedSchedule.scheduleLoss setup codec checks adversary false Q j ((observers codec Q) j)) := by
  have source := (PqxdhServerAuthPublicationOwnerFamily.ordered_bound_with_resources setup codec checks caps bounded
    adversary qCoin Q qH qHash (observers codec Q) budget coins law spread correct).1
  refine source.trans (add_le_add le_rfl (Finset.sum_le_sum fun j _ => ?_))
  exact add_le_add
    (PqxdhServerAuthSessionRecordProbability.uniform_bound setup codec checks caps bounded adversary
      qCoin Q qH qHash budget coins j fallback writable responseBack frameBack) le_rfl

/-- The combined seal/record inequality and complete constructed reduction ledger use the same source adversary and this exact same-owner seal/record observation family. -/
theorem session_record_with_resources (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (law : X25519ClassLaw setup.source.crypto) (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (responseBack : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (fallback : ModifiedNonceAeadForgery) :
    (𝒟[PqxdhServerAuthObservedExecution.orderedGame setup codec checks adversary false
      (PqxdhServerAuthPublicationOwnerFamily.observation setup Q (observers codec Q))] {true}).toReal ≤
      (serverGapDhAdvantage setup.source.crypto setup.joint setup.secretOfSeed setup.wiring
        (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).toReal +
      (Q.choose 2 : ℝ) * 64 / (2 ^ 256 : ℝ) +
      ∑ j : Fin (Q + 1), (PqxdhServerAuthPublicationLoss.recordLoss setup codec checks adversary Q j fallback
        (entryReductionBudget caps qCoin Q qHash qH + 76) +
        PqxdhServerAuthObservedSchedule.scheduleLoss setup codec checks adversary false Q j ((observers codec Q) j)) ∧
    PqxdhServerAuthPublicationResources.ReductionBills setup codec checks adversary caps
      qCoin Q qH qHash (observers codec Q) fallback :=
  ⟨session_record_bound setup codec checks caps bounded adversary qCoin Q qH qHash budget coins
      law spread correct writable responseBack frameBack fallback,
    PqxdhServerAuthPublicationResources.reduction_bills setup codec checks caps bounded adversary
      qCoin Q qH qHash budget coins (observers codec Q) fallback⟩

end BeaconcryptCore.Computational.PqxdhServerAuthSessionRecord

/-! Checked theorem dependencies. -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSessionRecord.session_record_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSessionRecord.session_record_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSessionRecord.session_record_with_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSessionRecord.session_record_with_resources
