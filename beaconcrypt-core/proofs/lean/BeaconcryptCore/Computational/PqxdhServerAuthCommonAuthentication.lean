import BeaconcryptCore.Computational.PqxdhServerAuthCommonProbability
import BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts

/-! Complete R1 session and record authentication with constructed reductions and their concrete resource bills. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthCommonAuthentication
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthSourceCosts
open PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh PqxdhServerAuthAssumptions
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhEd25519EufCma CtxNonceAeadIntCtxt
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The complete actual R1 source session/decoded-record failure, or a collision of the final BLAKE2b cache, has one concrete joint-use signature reduction, the original disclosure/collision losses, the exact same-owner record and five schedule reductions, and the transcript-hash birthday term `PqxdhServerAuthTranscriptCollision.term`. No honest target candidate, partner, matching seal, successful publication or unchanged signed tuple is assumed. -/
theorem collision_authentication (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (law : X25519ClassLaw setup.source.crypto) (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (responseBack : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (fallback : ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[PqxdhServerAuthCommonProbability.collisionDecision setup codec checks <$>
      PqxdhServerAuthRootObserved.orderedGame setup codec checks false adversary] {true}).toReal ≤
      (serverGapDhAdvantage setup.source.crypto setup.joint setup.secretOfSeed setup.wiring
        (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).toReal +
      (Q.choose 2 : ℝ) * 64 / (2 ^ 256 : ℝ) +
      ∑ j : Fin (Q + 1), (PqxdhServerAuthPublicationLoss.recordLoss setup codec checks adversary Q j fallback
        (entryReductionBudget caps qCoin Q qHash qH + 76) +
        PqxdhServerAuthObservedSchedule.scheduleLoss setup codec checks adversary false Q j
          (PqxdhServerAuthSessionRecord.observers codec Q j)) +
      (PqxdhJointIdentity.advantage setup.joint
        (PqxdhServerAuthJointIdentityEuf.reduction setup codec checks adversary signatureFallback)).toReal +
      PqxdhServerAuthTranscriptCollision.term Q qHash := by
  refine (PqxdhServerAuthCommonProbability.collision_split setup codec checks adversary Q qH qHash budget
    adapter).trans (add_le_add (add_le_add (PqxdhServerAuthSessionRecord.session_record_bound setup codec checks caps
      bounded adversary qCoin Q qH qHash budget coins law spread correct writable responseBack frameBack fallback) ?_)
    (PqxdhServerAuthTranscriptCollision.ordered_bound setup codec checks adversary Q qH qHash budget))
  exact ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one _))
    (PqxdhServerAuthJointIdentityEuf.source_bound setup codec checks adversary signatureFallback)

/-- The complete actual R1 source session/decoded-record failure has one concrete joint-use signature reduction, the original disclosure/collision losses, and the exact same-owner record and five schedule reductions. No honest target candidate, partner, matching seal, successful publication or unchanged signed tuple is assumed. The bound carries the transcript-hash birthday term last, because the accepted associated data is a hash of the registration transcript. -/
theorem common_authentication (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (law : X25519ClassLaw setup.source.crypto) (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (responseBack : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (fallback : ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[PqxdhServerAuthCommonProbability.decision setup codec checks <$>
      PqxdhServerAuthRootObserved.orderedGame setup codec checks false adversary] {true}).toReal ≤
      (serverGapDhAdvantage setup.source.crypto setup.joint setup.secretOfSeed setup.wiring
        (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).toReal +
      (Q.choose 2 : ℝ) * 64 / (2 ^ 256 : ℝ) +
      ∑ j : Fin (Q + 1), (PqxdhServerAuthPublicationLoss.recordLoss setup codec checks adversary Q j fallback
        (entryReductionBudget caps qCoin Q qHash qH + 76) +
        PqxdhServerAuthObservedSchedule.scheduleLoss setup codec checks adversary false Q j
          (PqxdhServerAuthSessionRecord.observers codec Q j)) +
      (PqxdhJointIdentity.advantage setup.joint
        (PqxdhServerAuthJointIdentityEuf.reduction setup codec checks adversary signatureFallback)).toReal +
      PqxdhServerAuthTranscriptCollision.term Q qHash := by
  exact (PqxdhServerAuthCommonProbability.decision_le_collision setup codec checks adversary).trans
    (collision_authentication setup codec checks caps bounded adversary qCoin Q qH qHash budget coins law spread
      correct adapter writable responseBack frameBack fallback signatureFallback)

/-- All bills refer to the reductions used in the complete session inequality. The signature simulation includes the local KEM base work and pays the challenge identity's sampler in its whole game. -/
structure ReductionBills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (adversary : Adversary) (qCoin Q qH qHash qTotal qFinish : Nat)
    (fallback : ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) : Prop where
  record : PqxdhServerAuthPublicationResources.ReductionBills setup codec checks adversary caps
    qCoin Q qH qHash (PqxdhServerAuthSessionRecord.observers codec Q) fallback
  signatures : ∀ target,
    (PqxdhServerAuthJointIdentityEuf.reduction setup codec checks adversary signatureFallback target).IsQueryBoundP
      PqxdhServerAuthJointIdentityLog.IsSign 3
  convertedDh : ∀ target,
    (PqxdhServerAuthJointIdentityEuf.reduction setup codec checks adversary signatureFallback target).IsQueryBoundP
      PqxdhServerAuthJointIdentityDhBudget.IsDh qFinish
  localUniform : ∀ target,
    (PqxdhServerAuthJointIdentityEuf.reduction setup codec checks adversary signatureFallback target).IsQueryBoundP
      (PqxdhJointIdentityFamily.IsClass .uniform)
      (PqxdhServerAuthJointIdentityUniformCosts.reductionCost caps qTotal)
  jointGame : (PqxdhJointIdentity.game setup.joint
    (PqxdhServerAuthJointIdentityEuf.reduction setup codec checks adversary signatureFallback)).IsTotalQueryBound
      (32 + PqxdhServerAuthJointIdentityUniformCosts.reductionCost caps qTotal)

/-- The complete actual-source failure-or-collision bound and the full query accounting for every constructed reduction in that same bound. The total source cap counts every attempted API call, and the finish cap includes rejected raw attempts. -/
theorem collision_authentication_with_resources (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (law : X25519ClassLaw setup.source.crypto) (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (responseBack : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (qTotal qFinish : Nat)
    (totalBound : ∀ input, (adversary input).IsTotalQueryBound qTotal)
    (finishBound : ∀ input, (adversary input).IsQueryBoundP PqxdhServerAuthJointIdentityDhBudget.IsFinish qFinish)
    (fallback : ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[PqxdhServerAuthCommonProbability.collisionDecision setup codec checks <$>
      PqxdhServerAuthRootObserved.orderedGame setup codec checks false adversary] {true}).toReal ≤
      (serverGapDhAdvantage setup.source.crypto setup.joint setup.secretOfSeed setup.wiring
        (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).toReal +
      (Q.choose 2 : ℝ) * 64 / (2 ^ 256 : ℝ) +
      ∑ j : Fin (Q + 1), (PqxdhServerAuthPublicationLoss.recordLoss setup codec checks adversary Q j fallback
        (entryReductionBudget caps qCoin Q qHash qH + 76) +
        PqxdhServerAuthObservedSchedule.scheduleLoss setup codec checks adversary false Q j
          (PqxdhServerAuthSessionRecord.observers codec Q j)) +
      (PqxdhJointIdentity.advantage setup.joint
        (PqxdhServerAuthJointIdentityEuf.reduction setup codec checks adversary signatureFallback)).toReal +
      PqxdhServerAuthTranscriptCollision.term Q qHash ∧
    ReductionBills setup codec checks caps adversary qCoin Q qH qHash qTotal qFinish fallback signatureFallback := by
  refine ⟨collision_authentication setup codec checks caps bounded adversary qCoin Q qH qHash budget coins
    law spread correct adapter writable responseBack frameBack fallback signatureFallback, ?_⟩
  have joint := PqxdhServerAuthJointIdentityUniformCosts.source_bound_with_resources setup codec checks caps bounded
    adversary qTotal qFinish totalBound finishBound signatureFallback
  exact ⟨PqxdhServerAuthPublicationResources.reduction_bills setup codec checks caps bounded adversary
    qCoin Q qH qHash budget coins (PqxdhServerAuthSessionRecord.observers codec Q) fallback,
    joint.2.1, joint.2.2.1, joint.2.2.2.1, joint.2.2.2.2⟩

/-- The complete actual-source authentication bound and the full query accounting for every constructed reduction in that same bound. The total source cap counts every attempted API call, and the finish cap includes rejected raw attempts. -/
theorem common_authentication_with_resources (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (law : X25519ClassLaw setup.source.crypto) (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (responseBack : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (qTotal qFinish : Nat)
    (totalBound : ∀ input, (adversary input).IsTotalQueryBound qTotal)
    (finishBound : ∀ input, (adversary input).IsQueryBoundP PqxdhServerAuthJointIdentityDhBudget.IsFinish qFinish)
    (fallback : ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[PqxdhServerAuthCommonProbability.decision setup codec checks <$>
      PqxdhServerAuthRootObserved.orderedGame setup codec checks false adversary] {true}).toReal ≤
      (serverGapDhAdvantage setup.source.crypto setup.joint setup.secretOfSeed setup.wiring
        (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).toReal +
      (Q.choose 2 : ℝ) * 64 / (2 ^ 256 : ℝ) +
      ∑ j : Fin (Q + 1), (PqxdhServerAuthPublicationLoss.recordLoss setup codec checks adversary Q j fallback
        (entryReductionBudget caps qCoin Q qHash qH + 76) +
        PqxdhServerAuthObservedSchedule.scheduleLoss setup codec checks adversary false Q j
          (PqxdhServerAuthSessionRecord.observers codec Q j)) +
      (PqxdhJointIdentity.advantage setup.joint
        (PqxdhServerAuthJointIdentityEuf.reduction setup codec checks adversary signatureFallback)).toReal +
      PqxdhServerAuthTranscriptCollision.term Q qHash ∧
    ReductionBills setup codec checks caps adversary qCoin Q qH qHash qTotal qFinish fallback signatureFallback := by
  have bound := collision_authentication_with_resources setup codec checks caps bounded adversary qCoin Q qH qHash
    budget coins law spread correct adapter writable responseBack frameBack qTotal qFinish totalBound finishBound
    fallback signatureFallback
  exact ⟨(PqxdhServerAuthCommonProbability.decision_le_collision setup codec checks adversary).trans bound.1,
    bound.2⟩

end BeaconcryptCore.Computational.PqxdhServerAuthCommonAuthentication

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCommonAuthentication.common_authentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCommonAuthentication.common_authentication

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCommonAuthentication.common_authentication_with_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCommonAuthentication.common_authentication_with_resources

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCommonAuthentication.collision_authentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCommonAuthentication.collision_authentication

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCommonAuthentication.collision_authentication_with_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCommonAuthentication.collision_authentication_with_resources
