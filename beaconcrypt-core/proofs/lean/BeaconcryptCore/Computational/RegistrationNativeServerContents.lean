-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeServerBindingReceipt

/-! Actual Server completion contents are retained at the initial-KDF and sequence-one seal stages. These receipts keep the consumed token's root, application and complete binding before later ratchet updates. They assert source-stage provenance; a matching Beacon execution is a separate obligation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerContents
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationServerFrontendCompiler (State)
open RegistrationSigningShared (SignReply)
open BeaconcryptCore.Refinement.RegistrationRecords
open BeaconcryptCore.Refinement.RegistrationPublication (completedBinding)
variable {n : Nat} {ι KemSK Reader Response : Type} {base : OracleSpec ι}

/-- The actual successful source record path retains its original initial reply/kernel and complete sequence-one seal context, including the application and LE64 identifier prefix. -/
theorem path_contents (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash)
    (path : RegistrationServerRecordExecutor.Path initial completed) :
    completed.binding = initial.binding ∧ completed.candidate = initial.candidate ∧
      ∃ (response : pqxdh.concrete.InitialRatchetKdfResponse)
        (kernel : ratchet.concrete.ConcreteRatchetKernel) (bound : pqxdh.RegistrationKeyIdBinding)
        (selected : ratchet.concrete.SendSeal record_effects.SealFrameContext),
        pqxdh.concrete.resume_initial_ratchet_kdf initial.pending response = .ok kernel ∧
        pqxdh.registration_key_id_binding initial.candidate.key_id = .ok bound ∧
        absBytes bound.bytes = Pqxdh.LE64 initial.candidate.key_id.val ∧
        completed.kernel = selected.advanced ∧ selected.sequence.val = 1 ∧
        selected.context = serverRecordContext initial bound := by
  cases path with
  | mk initialReply ratchetPhase initialResume ratchetReply aead ratchetResume aeadReply commitmentPhase
      aeadResume hashReply writePhase commitmentResume writeReply writeResume =>
    cases initialReply with
    | none => simp [registration.ServerInitialKdf.resume, pqxdh.server_abort_candidate] at initialResume
    | some initialResponse =>
      obtain ⟨kernel, bound, next, kernelRun, boundRun, boundBytes, resumed, stateSame, _, contextSame, sequence, _⟩ :=
        server_kdf_prefix_refines initial initialResponse
      have same : next = ratchetPhase := by simpa using resumed.symm.trans initialResume
      subst ratchetPhase
      cases ratchetReply with
      | none => simp [registration.ServerInitialSeal.resume, pqxdh.server_abort_candidate] at ratchetResume
      | some ratchetResponse =>
        obtain ⟨nextAead, resumed, aeadState, aeadContext, aeadSequence, _⟩ :=
          server_step_kdf_refines next ratchetResponse
        have same : nextAead = aead := by simpa using resumed.symm.trans ratchetResume
        subst aead
        cases aeadReply with
        | none =>
          simp [registration.ServerRecordAead.resume,
            BeaconcryptCore.Refinement.RecordEffects.seal_aead_missing_exact,
            pqxdh.server_abort_candidate] at aeadResume
        | some pair =>
          obtain ⟨ciphertext, tag⟩ := pair
          obtain ⟨nextCommitment, resumed, commitmentState, commitmentSeal, _⟩ :=
            server_aead_reply_refines nextAead ciphertext tag
          have same : nextCommitment = commitmentPhase := by simpa using resumed.symm.trans aeadResume
          subst commitmentPhase
          cases hashReply with
          | none =>
            simp [registration.ServerRecordCommitment.resume,
              BeaconcryptCore.Refinement.RecordEffects.seal_commitment_missing_exact,
              pqxdh.server_abort_candidate] at commitmentResume
          | some digest =>
            obtain ⟨nextWrite, resumed, writeState, writeSeal, _⟩ :=
              server_commitment_reply_refines nextCommitment digest
            have same : nextWrite = writePhase := by simpa using resumed.symm.trans commitmentResume
            subst writePhase
            obtain ⟨result, resumed, retained⟩ :=
              BeaconcryptCore.Refinement.RegistrationPublication.server_seal_retention_refines nextWrite writeReply
            have same : result = .Ok completed := by simpa using resumed.symm.trans writeResume
            rw [same] at retained
            refine ⟨?_, ?_, initialResponse, kernel, bound, nextAead.pending.seal,
              kernelRun, boundRun, boundBytes, ?_, ?_, ?_⟩
            · simpa only [BeaconcryptCore.Refinement.RegistrationPublication.serverSealRetains,
                writeState, commitmentState, aeadState, stateSame] using retained.2.1
            · simpa only [BeaconcryptCore.Refinement.RegistrationPublication.serverSealRetains,
                writeState, commitmentState, aeadState, stateSame] using retained.1
            · simpa only [writeSeal, commitmentSeal] using retained.2.2.1
            · rw [aeadSequence]
              exact sequence
            · exact aeadContext.trans contextSame

/-- Source-stage contents of the literal moved token, before an evolving ratchet can discard its root or initial capability. -/
structure Contents (token : peer.ConsumedRegistration) (pin : session.ServerAuthenticationPin)
    (application : Slice U8) (initial : registration.ServerInitialKdf)
    (hashed : registration.ServerResponseHash) (signed : registration.PublishedServerResponse Pqxdh.Bytes) : Prop where
  pin_matches : BeaconcryptCore.Refinement.SessionBinding.sameServerPin token.agreement.binding.server_pin pin
  binding : initial.binding = token.agreement.binding
  application : initial.application = application
  root : pqxdh.concrete.start_server_candidate_ratchet_kdf initial.candidate token.agreement.root.bytes = .ok initial.pending
  record_path : RegistrationServerRecordExecutor.Path initial hashed
  publication : RegistrationNativeServerBindingReceipt.Publication.Full hashed signed

/-- An actual successful SDK build has the exact taken token, root-derived initializer, real first-record callback path, and real response signing/publication stage from the same source execution. -/
theorem build_contents (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (handle : Nat) (application : Option (Slice U8)) (before after : State n)
    (keyId : U64) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some (keyId, bytes)), after) ∈ support
      ((RegistrationServerSdkSource.build setup codec checks sign encode handle application).run before)) :
    ∃ token current plaintext lookup requested occupied middle initial hashed signed recorded signedAt,
      RegistrationServerSdkSource.take handle before = (some token, current) ∧ application = some plaintext ∧
      peer.begin_completion_lookup current.control current.pin token plaintext = .ok (.Ok lookup) ∧
      lookup.request = .ok requested ∧
      (occupied, middle) ∈ support
        ((RegistrationServerSdkSource.world (RegistrationWorldServerCompletion.capability (.peerPresent requested))).run current) ∧
      lookup.resume occupied = .ok (.Ok initial) ∧
      Contents token current.pin plaintext initial hashed signed ∧
      (.ok (.Ok hashed), recorded) ∈ support
        ((simulateQ (RegistrationWorldRecords.handler setup codec)
          (RegistrationServerRecordExecutor.fromInitial initial)).run middle.world) ∧
      (.ok (.Ok signed), signedAt) ∈ support
        ((RegistrationWorldServerCompletion.signing sign encode hashed).run recorded) := by
  obtain ⟨token, current, plaintext, taken, input, completed⟩ :=
    RegistrationNativeServerReceipt.build_cut setup codec checks sign encode handle application before after keyId bytes supported
  obtain ⟨lookup, requested, occupied, middle, initial, looked, requestedAt, _fits, queried, resumed, _reserved, finished⟩ :=
    RegistrationNativeServerReceipt.complete_cut setup codec checks sign encode token plaintext current after keyId bytes completed
  obtain ⟨control, pin, tokenEq, applicationEq⟩ :=
    RegistrationNativeServerBindingReceipt.lookup_fields current.control current.pin token plaintext lookup looked
  have admitted : registration.begin_server_completion current.control current.pin
      (if occupied then .Occupied else .Available) token.agreement plaintext = .ok (.Ok initial) := by
    cases occupied <;> simpa only [peer.CompletionLookup.resume, Bool.false_eq_true, ite_false, ite_true, bind_tc_ok, control, pin, tokenEq, applicationEq] using resumed
  obtain ⟨pinMatches, binding, plain, root⟩ := RegistrationNativeServerBindingReceipt.initial_root _ _ _ _ _ _ admitted
  obtain ⟨published, world, completedAt, _id, _bytes, _final⟩ :=
    RegistrationNativeServerReceipt.fromInitial_cut setup codec sign encode current.control initial middle after keyId bytes finished
  obtain ⟨hashed, recorded, recordedAt, publishedAt⟩ :=
    RegistrationNativeServerReceipt.record_cut setup codec sign encode current.control initial middle.world world published completedAt
  obtain ⟨signed, signedAt, signingAt, _installed⟩ :=
    RegistrationNativeServerReceipt.publication_cut sign encode current.control hashed recorded world published publishedAt
  have path : RegistrationServerRecordExecutor.Path initial hashed := by
    apply RegistrationServerRecordExecutor.fromInitial_path
    apply OracleComp.support_simulateQ_run'_subset (RegistrationWorldRecords.handler setup codec)
      (RegistrationServerRecordExecutor.fromInitial initial) middle.world
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst recordedAt
  have fields := RegistrationNativeServerBindingReceipt.Publication.world_full sign encode hashed signed recorded signedAt signingAt
  exact ⟨token, current, plaintext, lookup, requested, occupied, middle, initial, hashed, signed, recorded, signedAt,
    taken, input, looked, requestedAt, queried, resumed, ⟨pinMatches, binding, plain, root, path, fields⟩, recordedAt, signingAt⟩

/-- Token root provenance, both complete pin/AD metadata and actual first application bytes stay attached to the exact consumed sequence-one kernel. -/
theorem contents_fields (token : peer.ConsumedRegistration) (pin : session.ServerAuthenticationPin)
    (application : Slice U8) (initial : registration.ServerInitialKdf)
    (hashed : registration.ServerResponseHash) (signed : registration.PublishedServerResponse Pqxdh.Bytes)
    (actual : Contents token pin application initial hashed signed) :
    signed.binding = completedBinding token.agreement.binding initial.candidate.key_id ∧
      signed.kernel = hashed.kernel ∧
      ∃ (response : pqxdh.concrete.InitialRatchetKdfResponse)
        (kernel : ratchet.concrete.ConcreteRatchetKernel) (bound : pqxdh.RegistrationKeyIdBinding)
        (selected : ratchet.concrete.SendSeal record_effects.SealFrameContext),
        pqxdh.concrete.resume_initial_ratchet_kdf initial.pending response = .ok kernel ∧
        pqxdh.registration_key_id_binding initial.candidate.key_id = .ok bound ∧
        absBytes bound.bytes = Pqxdh.LE64 initial.candidate.key_id.val ∧
        signed.kernel = selected.advanced ∧ selected.sequence.val = 1 ∧
        selected.context.plaintext = application ∧ selected.context.prefix = .Some bound.bytes ∧
        selected.context.associated_data = token.agreement.binding.associated_data ∧
        selected.context.target_kid = initial.candidate.key_id ∧
        selected.context.sender_kid = initial.candidate.server_identity_key_id ∧
        selected.context.encoding = .Raw := by
  obtain ⟨binding, candidate, response, kernel, bound, selected, resumed, boundRun, boundBytes,
    consumed, sequence, context⟩ := path_contents initial hashed actual.record_path
  refine ⟨?_, actual.publication.2.1, response, kernel, bound, selected, resumed, boundRun, boundBytes,
    actual.publication.2.1.trans consumed, sequence, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [binding, candidate, actual.binding] using actual.publication.1
  all_goals rw [context]
  · exact actual.application
  · rfl
  · exact congrArg session.RegistrationBinding.associated_data actual.binding
  · rfl
  · rfl
  · rfl

end BeaconcryptCore.Computational.RegistrationNativeServerContents
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerContents.path_contents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerContents.path_contents

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerContents.build_contents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerContents.build_contents

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerContents.contents_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerContents.contents_fields
