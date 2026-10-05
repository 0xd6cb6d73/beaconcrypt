-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationR1RootProbability
import BeaconcryptCore.Computational.PqxdhServerAuthCommonAuthentication

/-! The actual generated-Server singleton source inherits the existing common session and decoded-record authentication reduction, with all original resource bills. This endpoint does not cover supplied Server seeds or arbitrary multi-owner schedules. -/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationR1Authentication
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthSourceCosts
open PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh PqxdhServerAuthAssumptions
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhEd25519EufCma CtxNonceAeadIntCtxt
open PqxdhRegistrationR1RootSurface PqxdhRegistrationR1RootProbability
variable {ι KemSK Reader Response Result A : Type} {baseSpec : OracleSpec ι}

/-- Discard only the caller's final return value, retaining every adaptive query and reply. -/
def unitWork (work : AuthInput → OracleComp ServerAuthSpec Result) : Adversary :=
  fun input => (fun _ => ()) <$> work input

/-- Every selective query cap is unchanged by discarding the final return value. -/
theorem unit_queries (work : AuthInput → OracleComp ServerAuthSpec Result) (input : AuthInput)
    (predicate : ServerAuthSpec.Domain → Prop) [DecidablePred predicate] (q : Nat) :
    (unitWork work input).IsQueryBoundP predicate q ↔ (work input).IsQueryBoundP predicate q :=
  isQueryBoundP_map_iff _ _ _

/-- The source's three existing authentication caps, now permitting an arbitrary caller return type. -/
structure SourceBudget (work : AuthInput → OracleComp ServerAuthSpec Result) (Q qH qHash : Nat) : Prop where
  accept : ∀ input, (work input).IsQueryBoundP IsAcceptQuery Q
  rom : ∀ input, (work input).IsQueryBoundP IsRomQuery qH
  hash : ∀ input, (work input).IsQueryBoundP IsHashQuery qHash

/-- The ordinary authentication budget is exactly the same three source caps. -/
theorem budget_iff (work : AuthInput → OracleComp ServerAuthSpec Result) (Q qH qHash : Nat) :
    AuthBudget (unitWork work) Q qH qHash ↔ SourceBudget work Q qH qHash := by
  constructor
  · intro bounded
    exact ⟨fun input => (unit_queries work input _ _).mp (bounded.accept input),
      fun input => (unit_queries work input _ _).mp (bounded.rom input),
      fun input => (unit_queries work input _ _).mp (bounded.hash input)⟩
  · intro bounded
    exact ⟨fun input => (unit_queries work input _ _).mpr (bounded.accept input),
      fun input => (unit_queries work input _ _).mpr (bounded.rom input),
      fun input => (unit_queries work input _ _).mpr (bounded.hash input)⟩

/-- The actual generated-Server singleton has the published full common session/decoded-record authentication bound and the identical constructed reductions. Both source initialization calls are retained on the left and removed only by the checked gate inequality. Every primitive, resource and codec contract is the original endpoint's contract; supplied Server seeds have no such conclusion. -/
theorem generated_authentication (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (work : AuthInput → OracleComp ServerAuthSpec Result) (runtime : A)
    (qCoin Q qH qHash : Nat) (budget : SourceBudget work Q qH qHash)
    (coins : ∀ input, (work input).IsQueryBoundP IsAuthCoin qCoin)
    (law : X25519ClassLaw setup.source.crypto) (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (responseBack : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (qTotal qFinish : Nat)
    (totalBound : ∀ input, (work input).IsTotalQueryBound qTotal)
    (finishBound : ∀ input, (work input).IsQueryBoundP PqxdhServerAuthJointIdentityDhBudget.IsFinish qFinish)
    (fallback : ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[laneFailure setup codec checks <$>
      rootExperiment setup codec checks ensureInit none (fun _ => work) runtime] {true}).toReal ≤
      (serverGapDhAdvantage setup.source.crypto setup.joint setup.secretOfSeed setup.wiring
        (PqxdhJointGapDh.extractor (scanClient setup codec checks (unitWork work) qH))).toReal +
      (Q.choose 2 : ℝ) * 64 / (2 ^ 256 : ℝ) +
      ∑ j : Fin (Q + 1), (PqxdhServerAuthPublicationLoss.recordLoss setup codec checks (unitWork work) Q j fallback
        (entryReductionBudget caps qCoin Q qHash qH + 76) +
        PqxdhServerAuthObservedSchedule.scheduleLoss setup codec checks (unitWork work) false Q j
          (PqxdhServerAuthSessionRecord.observers codec Q j)) +
      (PqxdhJointIdentity.advantage setup.joint
        (PqxdhServerAuthJointIdentityEuf.reduction setup codec checks (unitWork work) signatureFallback)).toReal ∧
    PqxdhServerAuthCommonAuthentication.ReductionBills setup codec checks caps (unitWork work) qCoin Q qH qHash qTotal qFinish fallback signatureFallback := by
  have bound := PqxdhServerAuthCommonAuthentication.common_authentication_with_resources
    setup codec checks caps bounded (unitWork work) qCoin Q qH qHash
    ((budget_iff work Q qH qHash).mpr budget)
    (fun input => (unit_queries work input _ _).mpr (coins input))
    law spread correct adapter writable responseBack frameBack qTotal qFinish
    (fun input => by simpa only [unitWork, IsTotalQueryBound, isQueryBound_map_iff] using totalBound input)
    (fun input => (unit_queries work input _ _).mpr (finishBound input)) fallback signatureFallback
  have finite : 𝒟[PqxdhServerAuthCommonProbability.decision setup codec checks <$>
      PqxdhServerAuthRootObserved.orderedGame setup codec checks false (unitWork work)] {true} ≠ ⊤ := by
    rw [evalDist_apply_singleton]
    exact probOutput_ne_top
  exact ⟨(ENNReal.toReal_mono finite
    (generated_failure_le setup codec checks ensureInit work runtime)).trans bound.1, bound.2⟩

end BeaconcryptCore.Computational.PqxdhRegistrationR1Authentication

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Authentication.unit_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Authentication.unit_queries
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Authentication.budget_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Authentication.budget_iff
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Authentication.generated_authentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Authentication.generated_authentication
