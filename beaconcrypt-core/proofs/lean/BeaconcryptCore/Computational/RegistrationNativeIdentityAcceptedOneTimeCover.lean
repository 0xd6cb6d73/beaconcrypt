-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhJointPhase1Reports
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStoppedReduction
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityAcceptedOneTimeCover
open PqxdhJointIdentity (Primitives History Forgery signedMessages)
open PqxdhEd25519EufCma

/-- The one-time field is one original publicly verified attached field, regardless of repeated or noncanonical signatures. -/
theorem field (primitive : Primitives) (candidate : Phase1Candidate) (identity : Ed25519PublicKey)
    (decoded : Phase1KeyTuple) (accepted : acceptPhase1Candidate primitive.verify candidate = some (identity, decoded)) :
    ∃ signature, (⟨oneTimeMessage decoded.oneTime, signature⟩ : Forgery) ∈ PqxdhJointPhase1Reports.candidateFields candidate ∧
      primitive.verify identity (oneTimeMessage decoded.oneTime) signature = true := by
  obtain ⟨_encoded, pqSignature, preSignature, oneSignature, pqAttached, _pqVerified,
    preAttached, _preVerified, oneAttached, oneVerified⟩ :=
    acceptPhase1Candidate_some_witness primitive.verify candidate identity decoded accepted
  refine ⟨oneSignature, ?_, oneVerified⟩
  simp [PqxdhJointPhase1Reports.candidateFields, pqAttached, preAttached, oneAttached]

/-- Every accepted candidate either contains an original unissued weak-EUF field or its exact valid one-time message already belongs to the same generated handle's signing history. -/
theorem cover (primitive : Primitives) (candidate : Phase1Candidate) (identity : Ed25519PublicKey)
    (decoded : Phase1KeyTuple) (accepted : acceptPhase1Candidate primitive.verify candidate = some (identity, decoded))
    (history : History) :
    (∃ forgery ∈ PqxdhJointPhase1Reports.candidateFields candidate, forgery.message ∉ signedMessages history) ∨
      (∃ signature, (⟨oneTimeMessage decoded.oneTime, signature⟩ : Forgery) ∈ PqxdhJointPhase1Reports.candidateFields candidate ∧
        primitive.verify identity (oneTimeMessage decoded.oneTime) signature = true ∧
        oneTimeMessage decoded.oneTime ∈ signedMessages history) := by
  classical
  by_cases unissued : ∃ forgery ∈ PqxdhJointPhase1Reports.candidateFields candidate, forgery.message ∉ signedMessages history
  · exact Or.inl unissued
  · obtain ⟨signature, member, valid⟩ := field primitive candidate identity decoded accepted
    exact Or.inr ⟨signature, member, valid, by
      by_contra fresh
      exact unissued ⟨⟨oneTimeMessage decoded.oneTime, signature⟩, member, fresh⟩⟩
end BeaconcryptCore.Computational.RegistrationNativeIdentityAcceptedOneTimeCover

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityAcceptedOneTimeCover.field' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityAcceptedOneTimeCover.field
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityAcceptedOneTimeCover.cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityAcceptedOneTimeCover.cover
