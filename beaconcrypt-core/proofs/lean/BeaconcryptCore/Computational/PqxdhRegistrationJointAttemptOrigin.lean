-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInitialized

/-! Actual initialized source history supplies a complete earlier signing-attempt tuple for every accepted nonforged field set. A tuple absent from that chronological history has an unissued original field, including after failed publication and native erasure. The ordinary generated-index freshness/report reduction is joined separately. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptOrigin
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhEd25519EufCma
open PqxdhRegistrationJointAttemptLedger PqxdhRegistrationJointAttemptInvariant
open PqxdhRegistrationJointSigningTranscript (messagesAt)
open PqxdhRegistrationJointIssuedAttempts (history Fixed)
open PqxdhJointPhase1Reports (candidateFields)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result : Type}

/-- An original attached field carries a message absent from this exact source creation index's complete successful signing history. -/
def Unissued (state : PqxdhRegistrationJointSchedule.State KemSK) (index : Nat) (candidate : Phase1Candidate) : Prop :=
  ∃ field ∈ candidateFields candidate, field.message ∉ messagesAt index state.pool.1.transcript

/-- The derived source invariant turns absent complete-tuple origin into an unissued original field. It uses the immutable constructor fields and all signing attempts, without requiring successful or latest publication. -/
theorem absent_unissued (setup : Setup baseSpec KemSK) (state : State KemSK) (valid : Invariant setup state)
    (index : Nat) (receipt : Receipt) (recorded : state.2 index = some receipt)
    (candidate : Phase1Candidate) (identity : Ed25519PublicKey) (decoded : Phase1KeyTuple)
    (accepted : acceptPhase1Candidate setup.joint.verify candidate = some (identity, decoded))
    (absent : decoded ∉ receipt.attempts) : Unissued state.1 index candidate := by
  by_contra issued
  apply absent
  apply PqxdhRegistrationJointIssuedAttempts.accepted_origin setup.joint identity candidate decoded receipt.attempts receipt.prekey receipt.pqKey
    (valid.fixed index receipt recorded) accepted
  simpa only [Unissued, not_exists, not_and, not_not, valid.exactHistory index, attempts, recorded,
    Option.map_some, Option.getD_some] using issued

/-- A literal raw acceptance from an actually reached initialized source state either uses a complete earlier tuple of the addressed owner or has an unissued original field at that owner's exact source index. Constructor KEM provenance and chronological failed-writer history are derived from the same source execution. No honest selected identity or successful-bundle premise is imposed. -/
theorem raw_origin (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (work : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (runtime : A) (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (outcome : PqxdhRegistrationJointInitializedSchedule.SourceOutcome KemSK Result)
    (supported : (some outcome, after) ∈ support ((PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied work).run
      ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)))
    (address : Nat) (entry : PqxdhRegistrationJointOwnership.Entry KemSK)
    (found : outcome.2.2.owners[address]? = some entry)
    (seed : IdentitySeed) (raw : Pqxdh.Bytes) (received : NativeState KemSK) (session : Nat)
    (accepted : (some session, received) ∈ support ((nativeAccept setup codec checks seed
      PqxdhRegistrationSchedule.observationScalar raw).run outcome.2.2.shared)) :
    ∃ original identity decoded, ∃ receipt : Receipt,
      PqxdhRegistrationJointRawSignatures.candidate codec raw = some original ∧
      acceptPhase1Candidate setup.joint.verify original = some (identity, decoded) ∧
      Fixed receipt.prekey receipt.pqKey receipt.attempts ∧
      messagesAt entry.identityIndex outcome.2.2.pool.1.transcript = history receipt.attempts ∧
      (outcome.2.2.pool.2.keys[entry.kemIndex]?).map Prod.fst = some receipt.pqKey ∧
      PqxdhRegistrationJointAttemptTrace.LiveFixed setup entry.owner receipt.prekey receipt.pqKey ∧
      (decoded ∈ receipt.attempts ∨ Unissued outcome.2.2 entry.identityIndex original) := by
  obtain ⟨ledger, _, valid⟩ := PqxdhRegistrationJointAttemptInitialized.source_witness setup codec checks ensureInit supplied work runtime after outcome supported
  obtain ⟨receipt, recorded, kem, live⟩ := valid.live entry (List.mem_of_getElem? found)
  change ledger entry.identityIndex = some receipt at recorded
  obtain ⟨original, identity, decoded, parsed, verified⟩ :=
    PqxdhRegistrationJointRawSignatures.accept_candidate setup codec checks shortRejects seed raw outcome.2.2.shared received session accepted
  refine ⟨original, identity, decoded, receipt, parsed, verified, valid.fixed entry.identityIndex receipt recorded, ?_, ?_, live, ?_⟩
  · simpa only [attempts, recorded, Option.map_some, Option.getD_some] using valid.exactHistory entry.identityIndex
  · simpa only [kem] using valid.kem entry.identityIndex receipt recorded
  · by_cases issued : decoded ∈ receipt.attempts
    · exact Or.inl issued
    · exact Or.inr (absent_unissued setup (outcome.2.2, ledger) valid entry.identityIndex receipt recorded original identity decoded verified issued)

end BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptOrigin

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptOrigin.absent_unissued' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptOrigin.absent_unissued

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptOrigin.raw_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptOrigin.raw_origin
