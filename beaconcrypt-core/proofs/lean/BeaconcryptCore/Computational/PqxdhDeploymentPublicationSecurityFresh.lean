-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityClient
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionInitialized
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityCoupling

/-! The captured one-time field is an original field of the actual accepted candidate. Its absence is measured in the complete modified challenger's actual signing history, including every retained earlier request. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityFresh
open PqxdhServerAuthExperiment PqxdhJointIdentity PqxdhEd25519EufCma
open PqxdhDeploymentPublicationSuppression (Target Selection)
open PqxdhDeploymentPublicationSuppressionFreshness (Fresh)
open PqxdhDeploymentPublicationSecuritySelection (AcceptedAt ChosenCandidate)
open PqxdhDeploymentPublicationSecurityCoupling (Physical Related)
open PqxdhJointPhase1Reports (candidateFields)
variable {ι KemSK Reader Response Result A : Type} {baseSpec : OracleSpec ι}

/-- A literal accepted original candidate uses the fixed captured one-time key, whose message is absent from the complete real modified signing log. -/
def FreshAccepted (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (transcript : List PqxdhDeploymentInterface.Entry) (pool : PqxdhDynamicIdentityPool.SourceState)
    (selection : Selection) : Prop :=
  ∃ target candidate publicKey decoded,
    selection.pending = none ∧ selection.target = some target ∧ Fresh target pool ∧
    candidate ∈ PqxdhDeploymentProvenance.acceptedCandidates codec transcript ∧
    PqxdhDynamicIdentityReports.sourceKeys setup.joint pool.seeds target.identityIndex = some publicKey ∧
    acceptPhase1Candidate setup.joint.verify candidate = some (publicKey.ed25519, decoded) ∧
    decoded.oneTime = target.oneTime

def NativeEvent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (transcript : Result → List PqxdhDeploymentInterface.Entry)
    (outcome : Result × PqxdhDeploymentPublicationSuppressionSchedule.State KemSK) : Prop :=
  FreshAccepted setup codec (transcript outcome.1) outcome.2.1.pool.1 outcome.2.2

def SourceEvent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (transcript : Result → List PqxdhDeploymentInterface.Entry)
    (outcome : Option (PqxdhDeploymentPublicationSuppressionInitialized.SourceOutcome KemSK Result) ×
      PqxdhRegistrationJointServerPrefix.State KemSK A) : Prop :=
  ∃ created result state, outcome.1 = some (created, result, state) ∧ NativeEvent setup codec transcript (result, state)

def EncodedEvent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (transcript : Result → List PqxdhDeploymentInterface.Entry)
    (outcome : Option (PqxdhDeploymentPublicationSuppressionInitialized.EncodedOutcome KemSK Result) ×
      PqxdhRegistrationJointServerPrefix.State KemSK A) : Prop :=
  ∃ created result state, outcome.1 = some (created, result, state) ∧
    FreshAccepted setup codec (transcript result) state.1.pool.1 state.2

/-- Successful parsing retains the exact original one-time attached signature as a candidate field. -/
theorem oneTime_field (joint : Primitives) (candidate : Phase1Candidate) (identity : Ed25519PublicKey)
    (decoded : Phase1KeyTuple) (accepted : acceptPhase1Candidate joint.verify candidate = some (identity, decoded)) :
    ∃ field ∈ candidateFields candidate, field.message = oneTimeMessage decoded.oneTime := by
  obtain ⟨_, pqSignature, preSignature, oneSignature, pqAttached, _, preAttached, _, oneAttached, _⟩ :=
    acceptPhase1Candidate_some_witness joint.verify candidate identity decoded accepted
  refine ⟨⟨oneTimeMessage decoded.oneTime, oneSignature⟩, ?_, rfl⟩
  simp [candidateFields, pqAttached, preAttached, oneAttached]

/-- Freshness of the captured message is freshness of an original accepted field; no signature is reconstructed or changed. -/
theorem oneTime_unissued (joint : Primitives) (pool : PqxdhDynamicIdentityPool.SourceState)
    (target : Target) (candidate : Phase1Candidate) (identity : Ed25519PublicKey) (decoded : Phase1KeyTuple)
    (accepted : acceptPhase1Candidate joint.verify candidate = some (identity, decoded))
    (sameKey : decoded.oneTime = target.oneTime) (fresh : Fresh target pool) :
    ∃ field ∈ candidateFields candidate,
      field.message ∉ PqxdhRegistrationJointSigningTranscript.messagesAt target.identityIndex pool.transcript := by
  obtain ⟨field, member, same⟩ := oneTime_field joint candidate identity decoded accepted
  refine ⟨field, member, ?_⟩
  simpa only [Fresh, Target.message, sameKey, same] using fresh

/-- Encoding the genuine handle program preserves this event exactly: its private source pool and public transcript are unchanged. -/
theorem encode_event (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (transcript : Result → List PqxdhDeploymentInterface.Entry)
    (outcome : Option (PqxdhDeploymentPublicationSuppressionInitialized.SourceOutcome KemSK Result) ×
      PqxdhRegistrationJointServerPrefix.State KemSK A) :
    EncodedEvent setup codec transcript
      (outcome.1.map (PqxdhDeploymentPublicationSuppressionInitialized.encodeOutcome setup), outcome.2) ↔
      SourceEvent setup codec transcript outcome := by
  cases present : outcome.1 with
  | none => simp [EncodedEvent, SourceEvent, present]
  | some value =>
      rcases value with ⟨created, result, state⟩
      simp [EncodedEvent, SourceEvent, present, NativeEvent,
        PqxdhDeploymentPublicationSuppressionInitialized.encodeOutcome,
        PqxdhRegistrationJointGeneratedFinish.encodeState]

/-- The physical-state coupling preserves the actual source creation map and accepted raw candidate. -/
theorem chosen_fresh (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (transcript : List PqxdhDeploymentInterface.Entry) (ordinal : Nat)
    (real : PqxdhDeploymentPublicationSecurityCoupling.RealState KemSK)
    (modified : PqxdhDeploymentPublicationSuppressionSchedule.State KemSK)
    (related : Related ordinal real modified) (target : Target)
    (captured : modified.2.target = some target)
    (chosen : ChosenCandidate setup codec transcript real.1 target) :
    FreshAccepted setup codec transcript modified.1.pool.1 modified.2 := by
  obtain ⟨candidate, decoded, acceptedAt, sameKey⟩ := chosen
  obtain ⟨member, publicKey, keyFound, accepted⟩ := acceptedAt
  have armed := related.2.2.2.2 target captured
  have seeds : real.1.pool.1.seeds = modified.1.pool.1.seeds :=
    congrArg (fun native => native.pool.1.seeds) related.2.2.1
  exact ⟨target, candidate, publicKey, decoded, armed.1, captured, armed.2.2, member,
    seeds ▸ keyFound, accepted, sameKey⟩

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityFresh

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityFresh.oneTime_field' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityFresh.oneTime_field

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityFresh.oneTime_unissued' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityFresh.oneTime_unissued

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityFresh.encode_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityFresh.encode_event

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityFresh.chosen_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityFresh.chosen_fresh
