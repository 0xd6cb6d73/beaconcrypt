-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.SessionTranscript
import BeaconcryptCore.Refinement.SessionBinding
import BeaconcryptCore.Refinement.RegistrationInputs
import BeaconcryptCore.PanicFreedom.SessionBinding
import BeaconcryptCore.PanicFreedom.Pqxdh
import BeaconcryptCore.Computational.PqxdhInitialRatchetComplementarity

/-!
Actual version-3 registration AD effects. These laws connect retained signed request buffers to the public response fields selected by each real role. Hash replies remain external; digest equality for different preimages is not asserted. Successful continuations retain context87 and the exact returned digest before initial record operations.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
namespace BeaconcryptCore.Refinement.RegistrationAd
open BeaconcryptCore.Refinement.SessionBinding
open BeaconcryptCore.Refinement.RegistrationInputs

def initView (fields : authentication.OwnedInitFields) : authentication.InitFields :=
  ⟨fields.identity_key, fields.pre_key, fields.one_time_key, fields.pq_key⟩

def responseView (response : agreement.ResponsePublic) : authentication.AdResponseFields :=
  ⟨response.identity_key, response.ephemeral_key, response.kem_cipher_text, response.key_id⟩

def serverView (candidate : pqxdh.ServerRegistrationCandidate) : authentication.AdResponseFields :=
  ⟨candidate.server_identity_public_key, candidate.ephemeral_public_key,
    candidate.kem_ciphertext, candidate.key_id⟩

def preimage (binding : session.RegistrationBinding) (response : authentication.AdResponseFields) : Pqxdh.Bytes :=
  Pqxdh.SessionTranscript.encode (SessionTranscriptRefinement.absInit (initView binding.init_fields))
    (SessionTranscriptRefinement.absResponse response)

/-- The pending binding supplies complete signed request buffers to the allocation-free encoder. -/
theorem pending_transcript_exact (binding : session.RegistrationBinding)
    (response : authentication.AdResponseFields) :
    ∃ bytes, binding.ad_transcript response = ok bytes ∧ absBytes bytes = preimage binding response := by
  obtain ⟨bytes, run, contents⟩ :=
    SessionTranscriptRefinement.build_record_ad_transcript_abs (initView binding.init_fields) response
  refine ⟨bytes, ?_, contents⟩
  simpa [session.RegistrationBinding.ad_transcript, authentication.OwnedInitFields.fields, initView] using run

/-- Pinned-Server verification must succeed before the real Beacon AD request can be emitted. -/
theorem verified_response_selects_exact_ad (before : registration.ResponseMldsaVerification) :
    ∃ next, before.resume true = ok (.Ok next) ∧ next.pending = before.pending ∧
      next.packet = before.packet ∧ absBytes next.input =
        preimage before.pending.binding (responseView before.packet.public) := by
  obtain ⟨bytes, run, contents⟩ := pending_transcript_exact before.pending.binding (responseView before.packet.public)
  refine ⟨⟨before.pending, before.packet, bytes⟩, ?_, rfl, rfl, contents⟩
  simpa [registration.ResponseMldsaVerification.resume, responseView] using
    congrArg (fun result => result >>= fun input => ok (core.result.Result.Ok
      (registration.BeaconAdHash.mk before.pending before.packet input))) run

/-- Both roles request exactly their selected fixed-width preimage, with no caller-selected AD. -/
theorem actual_hash_requests (beacon : registration.BeaconAdHash) (server : registration.ServerAdHash) :
    (∃ request, beacon.request = ok request ∧ hashBytes request = absBytes beacon.input) ∧
    (∃ request, server.request = ok request ∧ hashBytes request = absBytes server.input) :=
  ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩

/-- A missing digest aborts; it cannot install a placeholder binding or start record opening. -/
theorem missing_beacon_digest (before : registration.BeaconAdHash) :
    before.resume .None = (do
      let aborted ← before.pending.abort
      ok (core.result.Result.Err aborted)) := rfl

/-- A successful hash reply retains the exact digest and authoritative complete AD. -/
theorem beacon_digest_completes_binding (before : registration.BeaconAdHash)
    (digest : Std.Array Std.U8 64#usize) :
    ∃ accepted, before.resume (.Some digest) = ok (.Ok accepted) ∧
      accepted.control = before.pending.control ∧ accepted.packet = before.packet ∧
      accepted.binding.session_transcript_hash = digest ∧ registrationConsistent accepted.binding := by
  obtain ⟨binding, run, facts⟩ := complete_refines before.pending.binding digest
  refine ⟨⟨before.pending.control, binding, before.packet⟩, ?_, rfl, rfl, facts.2.2.2.1, facts.2.2.2.2⟩
  simp [registration.BeaconAdHash.resume, run]

/-- Actual successful Server preparation chooses all response fields and the assigned ID before hashing. -/
theorem server_preparation_selects_exact_ad (control : pqxdh.ServerState)
    (pin : session.ServerAuthenticationPin) (availability : pqxdh.KeyIdAvailability)
    (accepted : agreement.ServerAgreement) (application : Slice Std.U8)
    (candidate : pqxdh.ServerRegistrationCandidate)
    (nonempty : core.slice.Slice.is_empty application = ok false)
    (pinMatches : accepted.binding.matches_server pin = ok true)
    (prepared : pqxdh.server_prepare_commit control accepted.pending pin.binding availability = ok (.Ok candidate)) :
    ∃ next, registration.begin_server_completion control pin availability accepted application = ok (.Ok next) ∧
      next.candidate = candidate ∧ next.binding = accepted.binding ∧ next.root = accepted.root ∧
      next.application = application ∧ absBytes next.input = preimage accepted.binding (serverView candidate) := by
  obtain ⟨bytes, run, contents⟩ := pending_transcript_exact accepted.binding (serverView candidate)
  refine ⟨⟨candidate, accepted.binding, accepted.root, application, bytes⟩, ?_, rfl, rfl, rfl, rfl, contents⟩
  simp [registration.begin_server_completion, nonempty, pinMatches,
    session.ServerAuthenticationPin.impl.binding, prepared,
    pqxdh.ServerRegistrationCandidate.impl.server_identity_public_key,
    pqxdh.ServerRegistrationCandidate.impl.ephemeral_public_key,
    pqxdh.ServerRegistrationCandidate.impl.kem_ciphertext,
    pqxdh.ServerRegistrationCandidate.impl.key_id, serverView] at run ⊢
  simp only [run, bind_tc_ok]

/-- A failed Server AD hash returns the original candidate control with no initial KDF phase. -/
theorem missing_server_digest (before : registration.ServerAdHash) :
    before.resume .None = (do
      let rejected ← pqxdh.server_abort_candidate before.candidate
      ok (core.result.Result.Err rejected)) := rfl

/-- After the exact digest reply, the Server's initial KDF receives the completed binding. -/
theorem server_digest_completes_binding (before : registration.ServerAdHash)
    (digest : Std.Array Std.U8 64#usize) :
    ∃ next, before.resume (.Some digest) = ok (.Ok next) ∧
      next.candidate = before.candidate ∧ next.application = before.application ∧
      next.binding.session_transcript_hash = digest ∧ registrationConsistent next.binding := by
  obtain ⟨binding, run, facts⟩ := complete_refines before.binding digest
  simp only [registration.ServerAdHash.resume, ratchet.RatchetChain.as_bytes,
    pqxdh.concrete.start_server_candidate_ratchet_kdf,
    pqxdh.ServerRegistrationCandidate.ratchet_initialization,
    pqxdh.SERVER_RATCHETS, lift, UScalar.cast, pqxdh.RATCHET_CHAIN_SIZE,
    pqxdh.concrete.start_initial_ratchet_kdf, ratchet.InitialRatchetKdfRequest.new,
    run, bind_tc_ok]
  exact ⟨_, rfl, rfl, rfl, facts.2.2.2.1, facts.2.2.2.2⟩

/-- Matching actual role-selected fields give equal hash addresses before any collision assumption. -/
theorem matching_role_preimages (server : registration.ServerAdHash) (beacon : registration.BeaconAdHash)
    (fields : server.binding.init_fields = beacon.pending.binding.init_fields)
    (responseFields : serverView server.candidate = responseView beacon.packet.public)
    (serverInput : absBytes server.input = preimage server.binding (serverView server.candidate))
    (beaconInput : absBytes beacon.input = preimage beacon.pending.binding (responseView beacon.packet.public)) :
    absBytes server.input = absBytes beacon.input := by
  rw [serverInput, beaconInput, preimage, preimage, fields, responseFields]

/-- The actual allocator retains the exact public response fields. It does not construct record AD. -/
theorem server_prepare_fields (control : pqxdh.ServerState) (pending : pqxdh.PendingServerRegistration)
    (pin : pqxdh.ServerBinding) (availability : pqxdh.KeyIdAvailability)
    (candidate : pqxdh.ServerRegistrationCandidate)
    (actual : pqxdh.server_prepare_commit control pending pin availability = ok (.Ok candidate)) :
    candidate.beacon_identity_public_key = pending.beacon_identity_public_key ∧
      candidate.server_identity_public_key = pin.identity_public_key ∧
      candidate.server_identity_key_id = pin.identity_key_id ∧
      candidate.ephemeral_public_key = pending.ephemeral_public_key ∧
      candidate.kem_ciphertext = pending.kem_ciphertext := by
  obtain ⟨next, nextRun⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok control
  simp only [pqxdh.server_prepare_commit, array_eq_abs, bind_tc_ok, nextRun] at actual
  split_ifs at actual
  all_goals cases next
  all_goals cases availability
  all_goals simp_all
  all_goals cases actual
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A real initial-KDF capability requires both actual response-dependent selection and a successful AD-hash reply. The receipt asserts no hash injectivity or primitive correctness. -/
def ServerAdmission (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (accepted : agreement.ServerAgreement)
    (application : Slice Std.U8) (initial : registration.ServerInitialKdf) : Prop :=
  ∃ (pending : registration.ServerAdHash) (digest : Std.Array Std.U8 64#usize),
    registration.begin_server_completion control pin availability accepted application = ok (.Ok pending) ∧
      pending.resume (.Some digest) = ok (.Ok initial)

/-- Every successful Server preparation retains its actual root, request binding and application before the hash effect. -/
theorem server_ad_origin (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (accepted : agreement.ServerAgreement)
    (application : Slice Std.U8) (pending : registration.ServerAdHash)
    (actual : registration.begin_server_completion control pin availability accepted application = ok (.Ok pending)) :
    pending.root = accepted.root ∧ pending.binding = accepted.binding ∧ pending.application = application ∧
      pqxdh.server_prepare_commit control accepted.pending pin.binding availability = ok (.Ok pending.candidate) := by
  obtain ⟨empty, emptyRun⟩ : ∃ result, core.slice.Slice.is_empty application = ok result := ⟨_, rfl⟩
  obtain ⟨pinMatches, matchRun⟩ := BeaconcryptCore.PanicFreedom.SessionBinding.RegistrationBinding_matches_server_total
    accepted.binding pin
  obtain ⟨prepared, prepareRun⟩ := BeaconcryptCore.PanicFreedom.server_prepare_commit_ok
    control accepted.pending pin.binding availability
  cases prepared with
  | Err error =>
    cases empty <;> cases pinMatches <;> simp [registration.begin_server_completion,
      session.ServerAuthenticationPin.impl.binding, emptyRun, matchRun, prepareRun] at actual
  | Ok candidate =>
    obtain ⟨bytes, bytesRun, _⟩ := pending_transcript_exact accepted.binding (serverView candidate)
    simp only [serverView] at bytesRun
    cases empty <;> cases pinMatches
    all_goals simp only [registration.begin_server_completion, emptyRun, matchRun,
      session.ServerAuthenticationPin.impl.binding, prepareRun, bind_tc_ok,
      pqxdh.ServerRegistrationCandidate.impl.server_identity_public_key,
      pqxdh.ServerRegistrationCandidate.impl.ephemeral_public_key,
      pqxdh.ServerRegistrationCandidate.impl.kem_ciphertext,
      pqxdh.ServerRegistrationCandidate.impl.key_id, bytesRun,
      Bool.false_eq_true, ite_true, ite_false, RustM.ok.injEq,
      core.result.Result.Ok.injEq, reduceCtorEq] at actual
    cases actual
    exact ⟨rfl, rfl, rfl, prepareRun⟩

/-- Actual Server preparation retains the exact owned2638-byte AD preimage selected before any hash reply. -/
theorem server_ad_selected_input (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (accepted : agreement.ServerAgreement)
    (application : Slice Std.U8) (pending : registration.ServerAdHash)
    (actual : registration.begin_server_completion control pin availability accepted application = ok (.Ok pending)) :
    absBytes pending.input = preimage pending.binding (serverView pending.candidate) := by
  obtain ⟨empty, emptyRun⟩ : ∃ result, core.slice.Slice.is_empty application = ok result := ⟨_, rfl⟩
  obtain ⟨pinMatches, matchRun⟩ := BeaconcryptCore.PanicFreedom.SessionBinding.RegistrationBinding_matches_server_total
    accepted.binding pin
  obtain ⟨prepared, prepareRun⟩ := BeaconcryptCore.PanicFreedom.server_prepare_commit_ok
    control accepted.pending pin.binding availability
  cases prepared with
  | Err error =>
    cases empty <;> cases pinMatches <;> simp [registration.begin_server_completion,
      session.ServerAuthenticationPin.impl.binding, emptyRun, matchRun, prepareRun] at actual
  | Ok candidate =>
    obtain ⟨bytes, bytesRun, contents⟩ := pending_transcript_exact accepted.binding (serverView candidate)
    simp only [serverView] at bytesRun
    cases empty <;> cases pinMatches
    all_goals simp only [registration.begin_server_completion, emptyRun, matchRun,
      session.ServerAuthenticationPin.impl.binding, prepareRun, bind_tc_ok,
      pqxdh.ServerRegistrationCandidate.impl.server_identity_public_key,
      pqxdh.ServerRegistrationCandidate.impl.ephemeral_public_key,
      pqxdh.ServerRegistrationCandidate.impl.kem_ciphertext,
      pqxdh.ServerRegistrationCandidate.impl.key_id, bytesRun,
      Bool.false_eq_true, ite_true, ite_false, RustM.ok.injEq,
      core.result.Result.Ok.injEq, reduceCtorEq] at actual
    cases actual
    exact contents

/-- The initial KDF is selected from the retained actual root only after complete AD exists. -/
theorem server_ad_resume_pending (pending : registration.ServerAdHash)
    (digest : Std.Array Std.U8 64#usize) (initial : registration.ServerInitialKdf)
    (resumed : pending.resume (.Some digest) = ok (.Ok initial)) :
    initial.pending = BeaconcryptCore.Computational.PqxdhInitialRatchetComplementarity.serverPending pending.root.bytes := by
  obtain ⟨completed, completeRun, _⟩ := complete_refines pending.binding digest
  have initialRun : pqxdh.concrete.start_server_candidate_ratchet_kdf pending.candidate pending.root.bytes =
      ok (BeaconcryptCore.Computational.PqxdhInitialRatchetComplementarity.serverPending pending.root.bytes) := by
    simpa only [pqxdh.concrete.start_server_candidate_ratchet_kdf,
      pqxdh.ServerRegistrationCandidate.ratchet_initialization,
      pqxdh.concrete.start_server_ratchet_kdf,
      BeaconcryptCore.Computational.PqxdhInitialRatchetComplementarity.serverPending] using
      pqxdh.concrete.start_server_ratchet_kdf_exact pending.root.bytes
  simp only [registration.ServerAdHash.resume, ratchet.RatchetChain.as_bytes,
    initialRun, completeRun, bind_tc_ok, RustM.ok.injEq, core.result.Result.Ok.injEq] at resumed
  cases resumed
  rfl

/-- The initial-record phase retains exactly the completed binding produced by the successful hash reply. -/
theorem server_ad_resume_binding (pending : registration.ServerAdHash)
    (digest : Std.Array Std.U8 64#usize) (initial : registration.ServerInitialKdf)
    (resumed : pending.resume (.Some digest) = ok (.Ok initial)) :
    ∃ completed, pending.binding.complete digest = ok completed ∧ initial.binding = completed ∧
      registrationConsistent completed ∧ initial.candidate = pending.candidate := by
  obtain ⟨completed, completeRun, _, _, _, _, consistent⟩ := complete_refines pending.binding digest
  have initialRun : pqxdh.concrete.start_server_candidate_ratchet_kdf pending.candidate pending.root.bytes =
      ok (BeaconcryptCore.Computational.PqxdhInitialRatchetComplementarity.serverPending pending.root.bytes) := by
    simpa only [pqxdh.concrete.start_server_candidate_ratchet_kdf,
      pqxdh.ServerRegistrationCandidate.ratchet_initialization,
      pqxdh.concrete.start_server_ratchet_kdf,
      BeaconcryptCore.Computational.PqxdhInitialRatchetComplementarity.serverPending] using
      pqxdh.concrete.start_server_ratchet_kdf_exact pending.root.bytes
  simp only [registration.ServerAdHash.resume, ratchet.RatchetChain.as_bytes,
    initialRun, completeRun, bind_tc_ok, RustM.ok.injEq, core.result.Result.Ok.injEq] at resumed
  cases resumed
  exact ⟨completed, completeRun, rfl, consistent, rfl⟩

/-- Source admission includes a real completed-binding receipt, rather than an AD field on the accepted Init. -/
theorem server_admission_binding (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (accepted : agreement.ServerAgreement)
    (application : Slice Std.U8) (initial : registration.ServerInitialKdf)
    (admitted : ServerAdmission control pin availability accepted application initial) :
    ∃ digest completed, accepted.binding.complete digest = ok completed ∧ initial.binding = completed ∧
      registrationConsistent completed ∧
      pqxdh.server_prepare_commit control accepted.pending pin.binding availability = ok (.Ok initial.candidate) := by
  obtain ⟨pending, digest, selected, resumed⟩ := admitted
  obtain ⟨completed, run, same, consistent, candidate⟩ := server_ad_resume_binding pending digest initial resumed
  have origin := server_ad_origin control pin availability accepted application pending selected
  exact ⟨digest, completed, by simpa only [origin.2.1] using run, same, consistent,
    by simpa only [candidate] using origin.2.2.2⟩

/-- Completion retains the original request digest while adding the response-dependent AD. -/
theorem server_admission_init_hash (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (accepted : agreement.ServerAgreement)
    (application : Slice Std.U8) (initial : registration.ServerInitialKdf)
    (admitted : ServerAdmission control pin availability accepted application initial) :
    initial.binding.init_hash = accepted.binding.init_hash := by
  obtain ⟨digest, completed, run, same, _consistent, _candidate⟩ :=
    server_admission_binding control pin availability accepted application initial admitted
  obtain ⟨expected, expectedRun, _pin, initHash, _identity, _digest, _consistent⟩ := complete_refines accepted.binding digest
  have equal : expected = completed := RustM.ok.inj (expectedRun.symm.trans run)
  rw [same, ← equal]
  exact initHash

theorem server_admission_pending (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (accepted : agreement.ServerAgreement)
    (application : Slice Std.U8) (initial : registration.ServerInitialKdf)
    (admitted : ServerAdmission control pin availability accepted application initial) :
    initial.pending = BeaconcryptCore.Computational.PqxdhInitialRatchetComplementarity.serverPending accepted.root.bytes := by
  obtain ⟨pending, digest, selected, resumed⟩ := admitted
  rw [server_ad_resume_pending pending digest initial resumed,
    (server_ad_origin control pin availability accepted application pending selected).1]

end BeaconcryptCore.Refinement.RegistrationAd

/-- info: 'BeaconcryptCore.Refinement.RegistrationAd.pending_transcript_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAd.pending_transcript_exact

/-- info: 'BeaconcryptCore.Refinement.RegistrationAd.verified_response_selects_exact_ad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAd.verified_response_selects_exact_ad

/-- info: 'BeaconcryptCore.Refinement.RegistrationAd.actual_hash_requests' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAd.actual_hash_requests

/-- info: 'BeaconcryptCore.Refinement.RegistrationAd.missing_beacon_digest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAd.missing_beacon_digest

/-- info: 'BeaconcryptCore.Refinement.RegistrationAd.beacon_digest_completes_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAd.beacon_digest_completes_binding

/-- info: 'BeaconcryptCore.Refinement.RegistrationAd.server_preparation_selects_exact_ad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAd.server_preparation_selects_exact_ad

/-- info: 'BeaconcryptCore.Refinement.RegistrationAd.missing_server_digest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAd.missing_server_digest

/-- info: 'BeaconcryptCore.Refinement.RegistrationAd.server_digest_completes_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAd.server_digest_completes_binding

/-- info: 'BeaconcryptCore.Refinement.RegistrationAd.matching_role_preimages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAd.matching_role_preimages

/-- info: 'BeaconcryptCore.Refinement.RegistrationAd.server_ad_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAd.server_ad_origin

/-- info: 'BeaconcryptCore.Refinement.RegistrationAd.server_ad_resume_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAd.server_ad_resume_pending

/-- info: 'BeaconcryptCore.Refinement.RegistrationAd.server_admission_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAd.server_admission_pending

/-- info: 'BeaconcryptCore.Refinement.RegistrationAd.server_ad_resume_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAd.server_ad_resume_binding

/-- info: 'BeaconcryptCore.Refinement.RegistrationAd.server_admission_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAd.server_admission_binding

/-- info: 'BeaconcryptCore.Refinement.RegistrationAd.server_prepare_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAd.server_prepare_fields

/-- info: 'BeaconcryptCore.Refinement.RegistrationAd.server_admission_init_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAd.server_admission_init_hash

/-- info: 'BeaconcryptCore.Refinement.RegistrationAd.server_ad_selected_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAd.server_ad_selected_input
