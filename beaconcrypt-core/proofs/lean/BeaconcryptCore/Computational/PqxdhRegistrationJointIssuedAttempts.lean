-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointReportEvents

/-! An issued tuple belongs to an actual complete source signing attempt, including an attempt whose later writer rejects. The source signs prekey, one-time, then PQ; verification still reads PQ, prekey, then one-time. The structural origin result needs the proved attempt-history invariant, not a latest-successful-bundle premise. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointIssuedAttempts
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhJointPhase1Reports

/-- One full signing block in literal source order. -/
def messages (keys : Phase1KeyTuple) : List Pqxdh.Bytes :=
  [prekeyMessage keys.prekey, oneTimeMessage keys.oneTime, pqMessage keys.pqKey]

/-- Chronological attempts retain repeated messages and failed publications. -/
def history (attempts : List Phase1KeyTuple) : List Pqxdh.Bytes := attempts.flatMap messages

/-- The constructor prekey and KEM public fields stay fixed across this owner's attempts. -/
def Fixed (prekey : X25519PublicKey) (pqKey : PqxdhKemIndCca.MlKem768PublicKey)
    (attempts : List Phase1KeyTuple) : Prop :=
  ∀ keys ∈ attempts, keys.prekey = prekey ∧ keys.pqKey = pqKey

/-- A complete chronological block appends after every prior attempt. -/
theorem history_append (attempts : List Phase1KeyTuple) (keys : Phase1KeyTuple) :
    history (attempts ++ [keys]) = history attempts ++ messages keys := by
  simp [history]

/-- Canonical prekey tags cannot be confused with one-time or KEM tags. -/
theorem prekey_member (key : X25519PublicKey) (attempts : List Phase1KeyTuple) :
    prekeyMessage key ∈ history attempts ↔ ∃ keys ∈ attempts, key = keys.prekey := by
  simp [history, messages, prekeyMessage_ne_oneTimeMessage, prekeyMessage_ne_pqMessage,
    prekeyMessage_injective.eq_iff]

/-- Canonical one-time messages identify an actual attempted one-time public key. -/
theorem oneTime_member (key : X25519PublicKey) (attempts : List Phase1KeyTuple) :
    oneTimeMessage key ∈ history attempts ↔ ∃ keys ∈ attempts, key = keys.oneTime := by
  simp [history, messages, Ne.symm (prekeyMessage_ne_oneTimeMessage _ _),
    oneTimeMessage_ne_pqMessage, oneTimeMessage_injective.eq_iff]

/-- Canonical KEM messages retain their actual tuple origin. -/
theorem pq_member (key : PqxdhKemIndCca.MlKem768PublicKey) (attempts : List Phase1KeyTuple) :
    pqMessage key ∈ history attempts ↔ ∃ keys ∈ attempts, key = keys.pqKey := by
  simp [history, messages, Ne.symm (prekeyMessage_ne_pqMessage _ _),
    Ne.symm (oneTimeMessage_ne_pqMessage _ _), pqMessage_injective.eq_iff]

/-- An accepted candidate whose three signed messages were issued has all its canonical messages in the exact chronological history. -/
theorem accepted_messages (primitives : Primitives) (identity : Ed25519PublicKey)
    (candidate : Phase1Candidate) (decoded : Phase1KeyTuple) (attempts : List Phase1KeyTuple)
    (accepted : acceptPhase1Candidate primitives.verify candidate = some (identity, decoded))
    (issued : ∀ field ∈ candidateFields candidate, field.message ∈ history attempts) :
    prekeyMessage decoded.prekey ∈ history attempts ∧
      oneTimeMessage decoded.oneTime ∈ history attempts ∧ pqMessage decoded.pqKey ∈ history attempts := by
  obtain ⟨_, pqSignature, preSignature, oneSignature, pqAttached, _, preAttached, _, oneAttached, _⟩ :=
    acceptPhase1Candidate_some_witness primitives.verify candidate identity decoded accepted
  simpa [candidateFields, pqAttached, preAttached, oneAttached, and_comm, and_left_comm] using issued

/-- With the owner's fixed prekey/KEM invariant, nonforged accepted fields reconstruct one complete issued tuple. Its publication need not have succeeded and it need not be the latest tuple. -/
theorem accepted_origin (primitives : Primitives) (identity : Ed25519PublicKey)
    (candidate : Phase1Candidate) (decoded : Phase1KeyTuple) (attempts : List Phase1KeyTuple)
    (prekey : X25519PublicKey) (pqKey : PqxdhKemIndCca.MlKem768PublicKey)
    (fixed : Fixed prekey pqKey attempts)
    (accepted : acceptPhase1Candidate primitives.verify candidate = some (identity, decoded))
    (issued : ∀ field ∈ candidateFields candidate, field.message ∈ history attempts) :
    decoded ∈ attempts := by
  obtain ⟨pre, one, pq⟩ := accepted_messages primitives identity candidate decoded attempts accepted issued
  obtain ⟨keys, member, oneEqual⟩ := (oneTime_member decoded.oneTime attempts).mp one
  obtain ⟨preKeys, preMember, preEqual⟩ := (prekey_member decoded.prekey attempts).mp pre
  obtain ⟨pqKeys, pqMember, pqEqual⟩ := (pq_member decoded.pqKey attempts).mp pq
  exact (Phase1KeyTuple.ext'
    (preEqual.trans ((fixed preKeys preMember).1.trans (fixed keys member).1.symm)) oneEqual
    (pqEqual.trans ((fixed pqKeys pqMember).2.trans (fixed keys member).2.symm))).symm ▸ member

/-- A fresh accepted tuple absent from the owner's issued attempts is exactly an eligible field-origin failure once the source history invariant is established. -/
theorem absent_fieldOrigin (primitives : Primitives) {count : Nat}
    (report : CandidateReport) (state : PqxdhDynamicIdentityReports.PublicSnapshot count)
    (valid : report.identity < count) (publicKey : PublicIdentity)
    (decoded : Phase1KeyTuple) (attempts : List Phase1KeyTuple)
    (prekey : X25519PublicKey) (pqKey : PqxdhKemIndCca.MlKem768PublicKey)
    (created : state.keys report.identity = some publicKey)
    (fresh : ⟨report.identity, valid⟩ ∉ state.history.reveals)
    (exactLog : signedMessages (state.history.histories ⟨report.identity, valid⟩) = history attempts)
    (fixed : Fixed prekey pqKey attempts)
    (accepted : acceptPhase1Candidate primitives.verify report.candidate = some (publicKey.ed25519, decoded))
    (absent : decoded ∉ attempts) : FieldOriginFailure primitives report state := by
  refine ⟨valid, publicKey, decoded, created, accepted, fresh, ?_⟩
  rw [exactLog]
  by_contra absentField
  exact absent (accepted_origin primitives publicKey.ed25519 report.candidate decoded attempts prekey pqKey fixed accepted (by simpa only [not_exists, not_and, not_not] using absentField))

end BeaconcryptCore.Computational.PqxdhRegistrationJointIssuedAttempts

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIssuedAttempts.history_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIssuedAttempts.history_append

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIssuedAttempts.prekey_member' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIssuedAttempts.prekey_member

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIssuedAttempts.oneTime_member' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIssuedAttempts.oneTime_member

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIssuedAttempts.pq_member' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIssuedAttempts.pq_member

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIssuedAttempts.accepted_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIssuedAttempts.accepted_messages

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIssuedAttempts.accepted_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIssuedAttempts.accepted_origin

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIssuedAttempts.absent_fieldOrigin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIssuedAttempts.absent_fieldOrigin
