-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCosts
import BeaconcryptCore.Computational.PqxdhJointPhase1Reports
import BeaconcryptCore.Computational.PqxdhRegistrationAdmission

/-! Original public raw registration fields at the actual native verification boundary. Public report extraction may inspect the supplied bytes, but never substitutes a recovered secret or assumes authentication. The existing attached-format/joint-use primitive contracts remain explicit. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointRawSignatures
open PqxdhJointIdentity PqxdhEd25519EufCma PqxdhServerAuthExperiment
open PqxdhServerRootPreparation (Verified verifyInput)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Read the original public four-field candidate through exactly the codec getters used by the native accept operation. No key or plaintext recovery enters these bytes. -/
def candidate (codec : Codec Reader Response) (raw : Pqxdh.Bytes) : Option Phase1Candidate := do
  let reader ← codec.read1 raw
  let identity ← codec.identity reader
  let pq ← codec.pqField reader
  let pre ← codec.preField reader
  let one ← codec.oneField reader
  pure ⟨identity, pre, one, pq⟩

/-- The literal pure native verification prefix, retaining the original candidate alongside the actual typed payloads. Point admission and all optional exits remain in source order. -/
def verified (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (raw : Pqxdh.Bytes) : Option (Verified Reader) := do
  let reader ← codec.read1 raw
  let encoded ← codec.identity reader
  let identity ← parseIdentity encoded
  if !checks.identityPoint identity then none else do
    let pqSigned ← codec.pqField reader
    let pqPayload ← setup.source.crypto.verify identity.toList pqSigned
    let preSigned ← codec.preField reader
    let prePayload ← setup.source.crypto.verify identity.toList preSigned
    let oneSigned ← codec.oneField reader
    let onePayload ← setup.source.crypto.verify identity.toList oneSigned
    let prekey ← parsePrekeyMessage prePayload
    let oneTime ← parseOneTimeMessage onePayload
    let pqKey ← parsePqMessage pqPayload
    pure ⟨reader, ⟨encoded, preSigned, oneSigned, pqSigned⟩, identity, ⟨prekey, oneTime, pqKey⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual native verification execution is exactly this public pure prefix and preserves the complete current consumed-registration list. Static DH and its instrumentation are not reached here. -/
theorem verifyInput_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (raw : Pqxdh.Bytes) (consumed : List Pqxdh.Bytes)
    (visit : PqxdhBeaconPhase2Preparation.Word32 → StateT (List Pqxdh.Bytes) ProbComp Unit) :
    (simulateQ (PqxdhServerStaticDhSource.nativeImpl setup.joint seed (serverAux setup codec checks) visit)
      (verifyInput raw)).run consumed = pure (verified setup codec checks raw, consumed) := by
  simp only [verifyInput, simulateQ_bind, simulateQ_spec_query, PqxdhServerStaticDhSource.nativeImpl,
    serverAux, pure_bind, verified]
  repeat' (first
    | rfl
    | (split <;> simp_all only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
        PqxdhServerStaticDhSource.nativeImpl, serverAux, StateT.run_pure,
        pure_bind, Option.bind] <;> try dsimp))

set_option backward.isDefEq.respectTransparency false in
/-- Every successfully verified native input consists of the exact original raw field getters and the actual source attached-verification result. -/
theorem verified_origin (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (raw : Pqxdh.Bytes) (value : Verified Reader) (accepted : verified setup codec checks raw = some value) :
    candidate codec raw = some value.candidate ∧
      PqxdhJointPhase1Reports.sourceAccept (fun publicKey => setup.source.crypto.verify publicKey.toList)
        value.candidate = some (value.identity, value.keys) := by
  unfold verified at accepted
  dsimp at accepted
  simp only [Option.bind_eq_some_iff] at accepted
  obtain ⟨reader, read, encoded, encodedField, identity, parsedIdentity, accepted⟩ := accepted
  split at accepted
  · cases accepted
  · simp only [Option.bind_eq_some_iff, Option.some.injEq] at accepted
    obtain ⟨pq, pqField, pqPayload, pqVerified, pre, preField, prePayload, preVerified,
      one, oneField, onePayload, oneVerified, prekey, parsedPre, oneTime, parsedOne, pqKey, parsedPq, rfl⟩ := accepted
    simp [candidate, PqxdhJointPhase1Reports.sourceAccept, read, encodedField, pqField, preField, oneField,
      parsedIdentity, pqVerified, preVerified, oneVerified, parsedPre, parsedOne, parsedPq]

/-- The ordinary detached endpoint recognizes the exact source-accepted fields under the existing attached-format contract, including rejection of inputs shorter than a signature. -/
theorem verified_detached (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (raw : Pqxdh.Bytes) (value : Verified Reader) (accepted : verified setup codec checks raw = some value) :
    acceptPhase1Candidate setup.joint.verify value.candidate = some (value.identity, value.keys) := by
  have source := (verified_origin setup codec checks raw value accepted).2
  rw [PqxdhJointPhase1Reports.sourceAccept_eq _ setup.joint
    (PqxdhJointPhase1Reports.source_attached_adapter setup.source.crypto setup.joint setup.secretOfSeed setup.wiring shortRejects)] at source
  exact source

/-- Every successfully collected actual native prefix keeps the exact original raw candidate and its actual attached-verification result. No source effect after verification can relabel those fields. -/
theorem prefix_candidate (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (raw : Pqxdh.Bytes) (consumed after : List Pqxdh.Bytes)
    (input : PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes PqxdhBeaconPhase2Preparation.Word32)
    (reached : (some input, after) ∈ support ((PqxdhServerAuthNative.nativePrefix setup codec checks seed raw).run consumed)) :
    candidate codec raw = some input.verified.candidate ∧
      PqxdhJointPhase1Reports.sourceAccept (fun publicKey => setup.source.crypto.verify publicKey.toList)
        input.verified.candidate = some (input.verified.identity, input.verified.keys) := by
  simp only [PqxdhServerAuthNative.nativePrefix, PqxdhServerRootPreparation.collect,
    simulateQ_bind, StateT.run_bind] at reached
  rw [verifyInput_source] at reached
  simp only [pure_bind] at reached
  cases checked : verified setup codec checks raw with
  | none =>
      simp only [checked, simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq,
        Option.some_ne_none, false_and] at reached
  | some value =>
      simp only [checked] at reached
      have same := PqxdhRegistrationAdmission.collect_verified _ value consumed after input reached
      rw [same]
      exact verified_origin setup codec checks raw value checked

set_option backward.isDefEq.respectTransparency false in
/-- A successful actual raw accept reached a successful native collection in the same run; allocation on failed attempts cannot manufacture a verified candidate. -/
theorem accept_prefix (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (raw : Pqxdh.Bytes) (state after : PqxdhServerAuthNative.NativeState KemSK) (index : Nat)
    (reached : (some index, after) ∈ support ((PqxdhServerAuthNative.nativeAccept setup codec checks seed
      PqxdhRegistrationSchedule.observationScalar raw).run state)) :
    ∃ input consumed, (some input, consumed) ∈ support ((PqxdhServerAuthNative.nativePrefix setup codec checks seed raw).run state.2.server.consumed) := by
  rw [PqxdhRegistrationJointServerAccept.native_run] at reached
  obtain ⟨⟨(_ | input), consumed⟩, collected, finished⟩ := (mem_support_bind_iff _ _ _).mp reached
  · simp only [PqxdhRegistrationJointServerAccept.tail, StateT.run_bind] at finished
    simp only [PqxdhServerAuthNative.nativeSet, PqxdhServerAuthNative.localState, StateT.run, pure_bind] at finished
    change (some index, after) ∈ support (pure (none, _) : ProbComp (Option Nat × PqxdhServerAuthNative.NativeState KemSK)) at finished
    simp only [mem_support_pure_iff, Prod.mk.injEq, Option.some_ne_none, false_and] at finished
  · exact ⟨input, consumed, collected⟩

/-- Every actual successful raw acceptance supplies the unchanged public four-field candidate to the ordinary detached verification endpoint. The additional premise is only the existing native attached-signature short-input format rule. -/
theorem accept_candidate (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (seed : IdentitySeed) (raw : Pqxdh.Bytes) (state after : PqxdhServerAuthNative.NativeState KemSK) (index : Nat)
    (reached : (some index, after) ∈ support ((PqxdhServerAuthNative.nativeAccept setup codec checks seed
      PqxdhRegistrationSchedule.observationScalar raw).run state)) :
    ∃ original identity keys, candidate codec raw = some original ∧
      acceptPhase1Candidate setup.joint.verify original = some (identity, keys) := by
  obtain ⟨input, consumed, collected⟩ := accept_prefix setup codec checks seed raw state after index reached
  have original := prefix_candidate setup codec checks seed raw state.2.server.consumed consumed input collected
  rw [PqxdhJointPhase1Reports.sourceAccept_eq _ setup.joint
    (PqxdhJointPhase1Reports.source_attached_adapter setup.source.crypto setup.joint setup.secretOfSeed setup.wiring shortRejects)] at original
  exact ⟨input.verified.candidate, input.verified.identity, input.verified.keys, original⟩

end BeaconcryptCore.Computational.PqxdhRegistrationJointRawSignatures

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRawSignatures.verifyInput_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRawSignatures.verifyInput_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRawSignatures.verified_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRawSignatures.verified_origin

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRawSignatures.verified_detached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRawSignatures.verified_detached

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRawSignatures.prefix_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRawSignatures.prefix_candidate

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRawSignatures.accept_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRawSignatures.accept_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRawSignatures.accept_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRawSignatures.accept_candidate
