-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInitAuthentication
import BeaconcryptCore.Refinement.PqxdhSurface

/-! Classical/PQ bundle fields alone do not pin the self-presented Beacon ML key. This module gives actual extracted continuation receipts for substituting that key and a fresh valid signature, while retaining the three honest attached Ed signatures. It identifies a stronger six-field byte-origin claim that must not be confused with protected-ML-key origin or with the unchanged broad APP eligibility event. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaSubstitution
open BeaconcryptCore.Refinement.RegistrationAuthentication
open BeaconcryptCore.Refinement.RegistrationInbound
open BeaconcryptCore.Refinement.RegistrationInputs
open BeaconcryptCore.Refinement.RegistrationBytePrimitives
open BeaconcryptCore.Refinement.RegistrationAuthenticationFlow

def packet (before : registration.InitPacket) (publicKey : Std.Array Std.U8 1952#usize)
    (signature : Std.Array Std.U8 3309#usize) : registration.InitPacket :=
  { before with mldsa_public_key := publicKey, signature := signature }

/-- The original broad CE classical/PQ candidate is literally unchanged by substituting the ML certificate. -/
theorem candidate (before : registration.InitPacket) (publicKey : Std.Array Std.U8 1952#usize)
    (signature : Std.Array Std.U8 3309#usize) :
    RegistrationRootInput.candidate (packet before publicKey signature) = RegistrationRootInput.candidate before := rfl

/-- A genuinely different ML key changes the full native packet despite its identical classical/PQ eligibility. -/
theorem different (before : registration.InitPacket) (publicKey : Std.Array Std.U8 1952#usize)
    (signature : Std.Array Std.U8 3309#usize) (changed : publicKey ≠ before.mldsa_public_key) :
    packet before publicKey signature ≠ before := by
  intro same
  exact changed (congrArg registration.InitPacket.mldsa_public_key same)

private theorem copy_array {size : Std.Usize} (value : Std.Array Std.U8 size) :
    core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
      size core.U8.Insts.CoreMarkerCopy (Std.Array.to_slice value) = .ok (.Ok value) := by
  obtain ⟨result, actual, facts⟩ := copied_slice_exact size (Std.Array.to_slice value)
  cases result with
  | Err error => exact False.elim (facts (by simpa only [Std.Array.to_slice] using value.property))
  | Ok copied =>
      have same : copied = value := Subtype.ext facts.1
      simpa only [same] using actual

private theorem pq_step (before : registration.InitEd25519Verification) (value : Std.Array Std.U8 1185#usize)
    (stage : before.stage = .PqKey) (suffix : before.state.packet.pq_key.val.drop 64 = value.val) :
    before.resume (.Some (Std.Array.to_slice value)) = .ok (.Ed25519VerificationRequested
      { before with stage := .PreKey, pq_key := value }) := by
  obtain ⟨request, requestRun, _key, signed, width⟩ := init_ed_request_exact before
  obtain ⟨tail, tailRun, tailBytes⟩ := attached_suffix_exact request.signed width
  have same : (Std.Array.to_slice value).val = tail.val := by
    rw [tailBytes, signed, edSignedBytes, stage]
    exact suffix.symm
  simp only [registration.InitEd25519Verification.resume, requestRun, bind_tc_ok, tailRun,
    core.Shared1A.Insts.CoreCmpPartialEqShared0B.ne, slice_ne_exact, same, ne_self_iff_false,
    decide_false, Bool.false_eq_true, ite_false, stage, copy_array]

private theorem pre_step (before : registration.InitEd25519Verification) (value : Std.Array Std.U8 34#usize)
    (stage : before.stage = .PreKey) (suffix : before.state.packet.pre_key.val.drop 64 = value.val) :
    before.resume (.Some (Std.Array.to_slice value)) = .ok (.Ed25519VerificationRequested
      { before with stage := .OneTimeKey, pre_key := value }) := by
  obtain ⟨request, requestRun, _key, signed, width⟩ := init_ed_request_exact before
  obtain ⟨tail, tailRun, tailBytes⟩ := attached_suffix_exact request.signed width
  have same : (Std.Array.to_slice value).val = tail.val := by
    rw [tailBytes, signed, edSignedBytes, stage]
    exact suffix.symm
  simp only [registration.InitEd25519Verification.resume, requestRun, bind_tc_ok, tailRun,
    core.Shared1A.Insts.CoreCmpPartialEqShared0B.ne, slice_ne_exact, same, ne_self_iff_false,
    decide_false, Bool.false_eq_true, ite_false, stage, copy_array]

private theorem one_step (before : registration.InitEd25519Verification) (value : Std.Array Std.U8 34#usize)
    (stage : before.stage = .OneTimeKey) (suffix : before.state.packet.one_time_key.val.drop 64 = value.val)
    (verified : pqxdh.VerifiedInitKex)
    (valid : pqxdh.validate_init_kex ⟨before.state.packet.identity_key, before.pre_key, value, before.pq_key⟩ = .ok (.Ok verified)) :
    before.resume (.Some (Std.Array.to_slice value)) = .ok (.ServerFingerprintRequested ⟨before.state, verified⟩) := by
  obtain ⟨request, requestRun, _key, signed, width⟩ := init_ed_request_exact before
  obtain ⟨tail, tailRun, tailBytes⟩ := attached_suffix_exact request.signed width
  have same : (Std.Array.to_slice value).val = tail.val := by
    rw [tailBytes, signed, edSignedBytes, stage]
    exact suffix.symm
  simp only [registration.InitEd25519Verification.resume, requestRun, bind_tc_ok, tailRun,
    core.Shared1A.Insts.CoreCmpPartialEqShared0B.ne, slice_ne_exact, same, ne_self_iff_false,
    decide_false, Bool.false_eq_true, ite_false, stage, copy_array, pqxdh.InitKex.from_encoded, valid]

private theorem mldsa_step (before : registration.InitMldsaVerification)
    (tag : before.state.packet.identity_key.val[0]! = pqxdh.SIGN_TYPE_ED25519) :
    ∃ next, before.resume true = .ok (.Ed25519VerificationRequested next) ∧
      next.state = before.state ∧ next.stage = .PqKey := by
  obtain ⟨result, actual, facts⟩ := init_mldsa_exact before true
  cases result <;> simp only [initMldsaOutcome] at facts
  case Rejected =>
    rcases facts with impossible | impossible
    · cases impossible
    · exact False.elim (impossible tag)
  case Ed25519VerificationRequested next => exact ⟨next, actual, facts.2.2.1, facts.2.2.2.1⟩

/-- A concrete seven-callback receipt consists exclusively of equations for the actual extracted entry point and retained continuations. -/
structure Receipt (pin : session.ServerAuthenticationPin) (received : registration.InitPacket)
    (digest serverFp beaconFp : Std.Array Std.U8 64#usize)
    (pq : Std.Array Std.U8 1185#usize) (pre one : Std.Array Std.U8 34#usize) where
  initial : registration.InitHash
  ml : registration.InitMldsaVerification
  pqPhase : registration.InitEd25519Verification
  prePhase : registration.InitEd25519Verification
  onePhase : registration.InitEd25519Verification
  server : registration.InitServerFingerprint
  beacon : registration.InitBeaconFingerprint
  accepted : registration.AuthenticatedInit
  start : registration.begin_init_authentication pin received = .ok (.HashRequested initial)
  hashed : initial.resume (.Some digest) = .ok (.MldsaVerificationRequested ml)
  verified : ml.resume true = .ok (.Ed25519VerificationRequested pqPhase)
  pqOpened : pqPhase.resume (.Some (Std.Array.to_slice pq)) = .ok (.Ed25519VerificationRequested prePhase)
  preOpened : prePhase.resume (.Some (Std.Array.to_slice pre)) = .ok (.Ed25519VerificationRequested onePhase)
  oneOpened : onePhase.resume (.Some (Std.Array.to_slice one)) = .ok (.ServerFingerprintRequested server)
  serverHashed : server.resume (.Some serverFp) = .ok (.BeaconFingerprintRequested beacon)
  beaconHashed : beacon.resume (.Some beaconFp) = .ok (.Accepted accepted)
  pqStage : pqPhase.stage = .PqKey
  preStage : prePhase.stage = .PreKey
  oneStage : onePhase.stage = .OneTimeKey
  mlPacket : ml.state.packet = received
  mlMessage : absBytes ml.input = Pqxdh.TranscriptAuth.signatureInput .beacon (absBytes digest)
  preimage : absBytes initial.input = initPreimage pin received

/-- The receipt is a complete actual finite authentication execution, not an assumed acceptance premise. -/
theorem Receipt.execution {pin : session.ServerAuthenticationPin} {received : registration.InitPacket}
    {digest serverFp beaconFp : Std.Array Std.U8 64#usize}
    {pq : Std.Array Std.U8 1185#usize} {pre one : Std.Array Std.U8 34#usize}
    (receipt : Receipt pin received digest serverFp beaconFp pq pre one) :
    Executes pin received
      [.hash (.Some digest), .mldsa true,
        .ed25519 .PqKey (.Some (Std.Array.to_slice pq)), .ed25519 .PreKey (.Some (Std.Array.to_slice pre)),
        .ed25519 .OneTimeKey (.Some (Std.Array.to_slice one)), .serverFingerprint (.Some serverFp),
        .beaconFingerprint (.Some beaconFp)] (.Accepted receipt.accepted) := by
  refine ⟨.HashRequested receipt.initial, receipt.start, ?_⟩
  have path := Run.step
    (Run.step
      (Run.step
        (Run.step
          (Run.step
            (Run.step
              (Run.step (Run.refl (.HashRequested receipt.initial)) (.hash receipt.initial _ _ receipt.hashed))
              (.mldsa receipt.ml _ _ receipt.verified))
            (.ed25519 receipt.pqPhase _ _ receipt.pqOpened))
          (.ed25519 receipt.prePhase _ _ receipt.preOpened))
        (.ed25519 receipt.onePhase _ _ receipt.oneOpened))
      (.serverFingerprint receipt.server _ _ receipt.serverHashed))
    (.beaconFingerprint receipt.beacon _ _ receipt.beaconHashed)
  simpa only [receipt.pqStage, receipt.preStage, receipt.oneStage, List.nil_append,
    List.cons_append] using path

/-- Exact typed ML verification operands used by this actual accepted controller path. -/
theorem Receipt.request {pin : session.ServerAuthenticationPin} {received : registration.InitPacket}
    {digest serverFp beaconFp : Std.Array Std.U8 64#usize}
    {pq : Std.Array Std.U8 1185#usize} {pre one : Std.Array Std.U8 34#usize}
    (receipt : Receipt pin received digest serverFp beaconFp pq pre one) :
    ∃ request, receipt.ml.request = .ok request ∧ request.public_key = received.mldsa_public_key ∧
      request.signature = received.signature ∧ request.context = authentication.SIGNING_CONTEXT ∧
      absBytes request.input = Pqxdh.TranscriptAuth.signatureInput .beacon (absBytes digest) := by
  refine ⟨⟨received.mldsa_public_key, receipt.ml.input, authentication.SIGNING_CONTEXT, received.signature⟩, ?_, rfl, rfl, rfl, receipt.mlMessage⟩
  simp only [registration.InitMldsaVerification.request, receipt.mlPacket]

/-- Every classically valid signed-key tuple admits an actual native authentication receipt for any self-presented ML key/signature whose mandatory verification replies true. Hash replies can be the correct values for the newly recomputed transcript and both actual keys. -/
theorem construct (pin : session.ServerAuthenticationPin) (received : registration.InitPacket)
    (tag : received.identity_key.val[0]! = pqxdh.SIGN_TYPE_ED25519)
    (pq : Std.Array Std.U8 1185#usize) (pre one : Std.Array Std.U8 34#usize)
    (pqSuffix : received.pq_key.val.drop 64 = pq.val)
    (preSuffix : received.pre_key.val.drop 64 = pre.val)
    (oneSuffix : received.one_time_key.val.drop 64 = one.val)
    (classical : pqxdh.VerifiedInitKex)
    (valid : pqxdh.validate_init_kex ⟨received.identity_key, pre, one, pq⟩ = .ok (.Ok classical))
    (digest serverFp beaconFp : Std.Array Std.U8 64#usize) :
    Nonempty (Receipt pin received digest serverFp beaconFp pq pre one) := by
  obtain ⟨initial, started, samePacket, _samePin, preimage⟩ := begin_init_exact pin received
  obtain ⟨ml, hashed, mlPacket, _mlPin, _mlHash, mlInput⟩ := init_hash_success initial digest
  have packetSame : ml.state.packet = received := mlPacket.trans samePacket
  obtain ⟨pqPhase, verified, stateSame, stage⟩ := mldsa_step ml (by rw [packetSame]; exact tag)
  have pqPacket : pqPhase.state.packet = received := (congrArg registration.InitAuthenticationState.packet stateSame).trans packetSame
  let prePhase : registration.InitEd25519Verification := { pqPhase with stage := .PreKey, pq_key := pq }
  let onePhase : registration.InitEd25519Verification := { prePhase with stage := .OneTimeKey, pre_key := pre }
  let server : registration.InitServerFingerprint := ⟨onePhase.state, classical⟩
  have pqOpened : pqPhase.resume (.Some (Std.Array.to_slice pq)) = .ok (.Ed25519VerificationRequested prePhase) :=
    pq_step pqPhase pq stage (by rw [pqPacket]; exact pqSuffix)
  have preOpened : prePhase.resume (.Some (Std.Array.to_slice pre)) = .ok (.Ed25519VerificationRequested onePhase) :=
    pre_step prePhase pre rfl (by change pqPhase.state.packet.pre_key.val.drop 64 = pre.val; rw [pqPacket]; exact preSuffix)
  have oneOpened : onePhase.resume (.Some (Std.Array.to_slice one)) = .ok (.ServerFingerprintRequested server) :=
    one_step onePhase one rfl (by change pqPhase.state.packet.one_time_key.val.drop 64 = one.val; rw [pqPacket]; exact oneSuffix)
      classical (by change pqxdh.validate_init_kex ⟨pqPhase.state.packet.identity_key, pre, one, pq⟩ = .ok (.Ok classical); rw [pqPacket]; exact valid)
  obtain ⟨beacon, serverHashed, _state, _registration, _binding, _publicKey, _fingerprint⟩ := init_server_fingerprint_exact server serverFp
  obtain ⟨accepted, beaconHashed, _registration, _pin, _digest, _identity, _beaconFp, _consistent⟩ := init_beacon_fingerprint_exact beacon beaconFp
  exact ⟨⟨initial, ml, pqPhase, prePhase, onePhase, server, beacon, accepted, started, hashed, verified,
    pqOpened, preOpened, oneOpened, serverHashed, beaconHashed, stage, rfl, rfl, packetSame, mlInput, preimage⟩⟩

/-- Replacing only the ML certificate preserves all honest classical/PQ checks but changes the full packet; the actual mandatory seven-callback controller still has a complete acceptance receipt under normal positive primitive replies for the substituted key. -/
theorem substitution (pin : session.ServerAuthenticationPin) (before : registration.InitPacket)
    (publicKey : Std.Array Std.U8 1952#usize) (signature : Std.Array Std.U8 3309#usize)
    (changed : publicKey ≠ before.mldsa_public_key)
    (tag : before.identity_key.val[0]! = pqxdh.SIGN_TYPE_ED25519)
    (pq : Std.Array Std.U8 1185#usize) (pre one : Std.Array Std.U8 34#usize)
    (pqSuffix : before.pq_key.val.drop 64 = pq.val) (preSuffix : before.pre_key.val.drop 64 = pre.val)
    (oneSuffix : before.one_time_key.val.drop 64 = one.val) (classical : pqxdh.VerifiedInitKex)
    (valid : pqxdh.validate_init_kex ⟨before.identity_key, pre, one, pq⟩ = .ok (.Ok classical))
    (digest serverFp beaconFp : Std.Array Std.U8 64#usize) :
    packet before publicKey signature ≠ before ∧
      RegistrationRootInput.candidate (packet before publicKey signature) = RegistrationRootInput.candidate before ∧
      Nonempty (Receipt pin (packet before publicKey signature) digest serverFp beaconFp pq pre one) := by
  exact ⟨different before publicKey signature changed, candidate before publicKey signature,
    construct pin (packet before publicKey signature) tag pq pre one pqSuffix preSuffix oneSuffix classical valid digest serverFp beaconFp⟩

/-- A correct ordinary signature under the self-presented substituted key produces exactly the source verifier's true reply. No signature under the earlier ML key is required. -/
theorem Receipt.verification {pin : session.ServerAuthenticationPin} {received : registration.InitPacket}
    {digest serverFp beaconFp : Std.Array Std.U8 64#usize}
    {pq : Std.Array Std.U8 1185#usize} {pre one : Std.Array Std.U8 34#usize}
    (receipt : Receipt pin received digest serverFp beaconFp pq pre one)
    (verify : MldsaTranscriptAuth.Verify)
    (correct : verify (absBytes received.mldsa_public_key) (absBytes authentication.SIGNING_CONTEXT)
      (Pqxdh.TranscriptAuth.signatureInput .beacon (absBytes digest)) (absBytes received.signature) = true) :
    ∃ request, receipt.ml.request = .ok request ∧ RegistrationAuthenticationShared.verifyMldsa verify request = true := by
  obtain ⟨request, called, publicKey, signature, context, input⟩ := receipt.request
  refine ⟨request, called, ?_⟩
  simpa only [RegistrationAuthenticationShared.verifyMldsa, publicKey, signature, context, input] using correct

/-- Ordinary native successful readback forces different ML-key fields to have different complete encoded bytes. This does not assume signature uniqueness or CBOR canonicalization. -/
theorem encoded_distinct (wire : RegistrationNativeWire.Wire) (readback : RegistrationNativeWire.InitReadBack wire)
    (before after : registration.SignedInitView) (beforeBytes afterBytes : Pqxdh.Bytes)
    (encodedBefore : wire.encodeInit before = .Some beforeBytes) (encodedAfter : wire.encodeInit after = .Some afterBytes)
    (changed : after.fields.mldsa_public_key ≠ before.fields.mldsa_public_key) : afterBytes ≠ beforeBytes := by
  intro same
  have original := readback before beforeBytes encodedBefore
  have replacement := readback after afterBytes encodedAfter
  rw [same] at replacement
  have packets : RegistrationNativeWire.initPacket after = RegistrationNativeWire.initPacket before :=
    Option.some.inj (replacement.symm.trans original)
  exact changed (congrArg registration.InitPacket.mldsa_public_key packets)

/-- All three actual Ed verification requests retain the original attached fields and the same honest identity key; none includes the substituted ML key. -/
theorem Receipt.ed_requests {pin : session.ServerAuthenticationPin} {received : registration.InitPacket}
    {digest serverFp beaconFp : Std.Array Std.U8 64#usize}
    {pq : Std.Array Std.U8 1185#usize} {pre one : Std.Array Std.U8 34#usize}
    (receipt : Receipt pin received digest serverFp beaconFp pq pre one) :
    ∃ pqRequest preRequest oneRequest,
      receipt.pqPhase.request = .ok pqRequest ∧ receipt.prePhase.request = .ok preRequest ∧
      receipt.onePhase.request = .ok oneRequest ∧
      pqRequest.public_key = preRequest.public_key ∧ preRequest.public_key = oneRequest.public_key ∧
      pqRequest.signed.val = received.pq_key.val ∧ preRequest.signed.val = received.pre_key.val ∧
      oneRequest.signed.val = received.one_time_key.val ∧
      pqRequest.public_key.val = (List.range (32#usize).val).map (fun index => received.identity_key.val[index + 1]!) := by
  obtain ⟨mlResult, mlRun, mlFacts⟩ := init_mldsa_exact receipt.ml true
  have mlSame : mlResult = .Ed25519VerificationRequested receipt.pqPhase := RustM.ok.inj (mlRun.symm.trans receipt.verified)
  rw [mlSame] at mlFacts
  obtain ⟨_true, _tag, pqState, _stage, pqPublic⟩ := mlFacts
  have pqPacket : receipt.pqPhase.state.packet = received :=
    (congrArg registration.InitAuthenticationState.packet pqState).trans receipt.mlPacket
  obtain ⟨preResult, preRun, preFacts⟩ := init_ed_resume_refines receipt.pqPhase (.Some (Std.Array.to_slice pq))
  have preSame : preResult = .Ed25519VerificationRequested receipt.prePhase := RustM.ok.inj (preRun.symm.trans receipt.pqOpened)
  rw [preSame] at preFacts
  obtain ⟨_pqBytes, _opened, _suffix, preState, prePublic, _transition⟩ := preFacts
  obtain ⟨oneResult, oneRun, oneFacts⟩ := init_ed_resume_refines receipt.prePhase (.Some (Std.Array.to_slice pre))
  have oneSame : oneResult = .Ed25519VerificationRequested receipt.onePhase := RustM.ok.inj (oneRun.symm.trans receipt.preOpened)
  rw [oneSame] at oneFacts
  obtain ⟨_preBytes, _opened, _suffix, oneState, onePublic, _transition⟩ := oneFacts
  obtain ⟨pqRequest, pqCalled, pqKey, pqSigned, _width⟩ := init_ed_request_exact receipt.pqPhase
  obtain ⟨preRequest, preCalled, preKey, preSigned, _width⟩ := init_ed_request_exact receipt.prePhase
  obtain ⟨oneRequest, oneCalled, oneKey, oneSigned, _width⟩ := init_ed_request_exact receipt.onePhase
  refine ⟨pqRequest, preRequest, oneRequest, pqCalled, preCalled, oneCalled,
    pqKey.trans (preKey.trans prePublic).symm, preKey.trans (oneKey.trans onePublic).symm, ?_, ?_, ?_, ?_⟩
  · simpa only [edSignedBytes, receipt.pqStage, pqPacket] using pqSigned
  · simpa only [edSignedBytes, receipt.preStage, preState, pqPacket] using preSigned
  · simpa only [edSignedBytes, receipt.oneStage, oneState, preState, pqPacket] using oneSigned
  · rw [pqKey, pqPublic, receipt.mlPacket]

end BeaconcryptCore.Computational.RegistrationNativeMldsaSubstitution

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSubstitution.candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSubstitution.candidate
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSubstitution.different' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSubstitution.different
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSubstitution.Receipt.execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSubstitution.Receipt.execution
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSubstitution.Receipt.request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSubstitution.Receipt.request
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSubstitution.construct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSubstitution.construct
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSubstitution.substitution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSubstitution.substitution
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSubstitution.Receipt.verification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSubstitution.Receipt.verification
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSubstitution.encoded_distinct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSubstitution.encoded_distinct

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSubstitution.Receipt.ed_requests' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSubstitution.Receipt.ed_requests
