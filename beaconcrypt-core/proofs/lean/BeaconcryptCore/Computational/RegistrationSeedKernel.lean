-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerRecordExecutor
import BeaconcryptCore.Refinement.RegistrationAd
import BeaconcryptCore.Computational.PqxdhRecordLiftSeed

/-! The actual authenticated Server completion consumes its first send before publication. The equations here identify that complete consumed kernel with the existing seed constructor; the public binding changes only the record context. A private generated seed remains a private generated seed, rather than becoming a caller-known installation merely because the concrete controller returns a kernel. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
open BeaconcryptCore.Refinement.RegistrationRecords

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationSeedKernel

theorem server_pending (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : agreement.ServerAgreement) (application : Slice Std.U8)
    (initial : registration.ServerInitialKdf)
    (actual : BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission
      control current availability agreement application initial) :
    initial.pending = PqxdhInitialRatchetComplementarity.serverPending agreement.root.bytes :=
  BeaconcryptCore.Refinement.RegistrationAd.server_admission_pending
    control current availability agreement application initial actual

/-- Both supplied KDF replies follow the actual retained send capability; even an absent sealing result leaves its advanced kernel consumed. -/
theorem source_send (initial : registration.ServerInitialKdf)
    (initialResponse : pqxdh.concrete.InitialRatchetKdfResponse) (response : RatchetKdfResponse) :
    ∃ (kernel : ConcreteRatchetKernel) (next : registration.ServerInitialSeal)
        (selected : registration.ServerRecordAead) (context : record_effects.SealFrameContext),
      pqxdh.concrete.resume_initial_ratchet_kdf initial.pending initialResponse = .ok kernel ∧
      initial.resume (.Some initialResponse) = .ok (.Ok next) ∧
      next.resume (.Some response) = .ok (.Ok selected) ∧
      PqxdhRecordLiftSeed.sendOne kernel response context (.None : core.option.Option Unit) =
        .ok (some (selected.pending.seal.advanced, .None)) := by
  obtain ⟨kernel, kernelRun, sendZero, _receiveZero, _cacheZero⟩ :=
    initial_kernel_control_refines initial.pending initialResponse
  obtain ⟨bound, boundRun, _boundBytes⟩ := registration_key_id_binding_abs initial.candidate.key_id
  let context := serverRecordContext initial bound
  have contextRun : record_effects.SealFrameContext.registration initial.application
      initial.candidate.key_id initial.candidate.server_identity_key_id initial.binding.associated_data = .ok context := by
    simp [record_effects.SealFrameContext.registration, boundRun,
      pqxdh.RegistrationKeyIdBinding.as_bytes, context, serverRecordContext]
  have nonmax : kernel.refined.control.send_sequence ≠ core.num.U64.MAX := by
    rw [sendZero]
    decide
  obtain ⟨pending, pendingRun, _entry, _context, _input, _info, _sequence⟩ :=
    begin_send_nonexhausted_exact kernel context nonmax
  have recordRun : record_effects.begin_record_send kernel context = .ok (.KdfRequested ⟨pending⟩) := by
    have prefixRun : context.prefix = .Some bound.bytes := rfl
    obtain ⟨empty, emptyRun⟩ : ∃ result, core.slice.Slice.is_empty context.plaintext = .ok result := ⟨_, rfl⟩
    cases empty with
    | false => simp [record_effects.begin_record_send, emptyRun, pendingRun]
    | true => simp [record_effects.begin_record_send, emptyRun, prefixRun,
        core.option.Option.is_none, core.option.Option.is_some, pendingRun]
  let next : registration.ServerInitialSeal := ⟨⟨initial.candidate, initial.binding, initial.application⟩, ⟨pending⟩⟩
  let ready := RawCtxSourceSend.resumeSend pending response
  let selected : registration.ServerRecordAead := ⟨next.state, ⟨ready⟩⟩
  refine ⟨kernel, next, selected, context, kernelRun, ?_, ?_, ?_⟩
  · simp [registration.ServerInitialKdf.resume, pqxdh.server_abort_candidate,
      kernelRun, pqxdh.ServerRegistrationCandidate.impl.key_id,
      pqxdh.ServerRegistrationCandidate.impl.server_identity_key_id,
      session.CompletedRegistrationBinding.impl.associated_data, contextRun, recordRun, next]
  · simp only [registration.ServerInitialSeal.resume, record_effects.RecordSendKdf.resume,
      next, RawCtxSourceSend.resumeSend_exact, bind_tc_ok, selected, ready]
  · simp only [PqxdhRecordLiftSeed.sendOne, pendingRun, bind_tc_ok,
      RawCtxSourceSend.resumeSend_exact, SendSeal.finish_returns_interpreter_result,
      RawCtxMaterialInterpretation.rust_map_ok, selected, ready]

/-- The actual Server gate and both actual KDF continuations produce the whole existing post-sequence-one seed kernel, including counters and every cache cell. -/
theorem server_seed (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : agreement.ServerAgreement) (application : Slice Std.U8)
    (initial : registration.ServerInitialKdf)
    (actual : BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission control current availability agreement application initial)
    (left right : PqxdhSecretInputKdf.RootOutput) (output : PqxdhFullSecretInputKdf.FullOutput) :
    ∃ (next : registration.ServerInitialSeal) (selected : registration.ServerRecordAead),
      initial.resume (.Some (RawCtxSelectedInitialConstructor.response64 (left ++ right))) = .ok (.Ok next) ∧
      next.resume (.Some (RawCtxKdfRequestTable.fullResponse output)) = .ok (.Ok selected) ∧
      PqxdhRecordLiftSeed.serverKernel (PqxdhOrderedChainHybrids.nextChain output, right) =
        .ok selected.pending.seal.advanced := by
  obtain ⟨kernel, next, selected, context, kernelRun, initialRun, nextRun, sent⟩ :=
    source_send initial (RawCtxSelectedInitialConstructor.response64 (left ++ right))
      (RawCtxKdfRequestTable.fullResponse output)
  have supplied : PqxdhInitialReplyErasure.kernelOf false
      (RawCtxSelectedInitialConstructor.response64 (left ++ right)) = .ok kernel := by
    rw [server_pending control current availability agreement application initial actual] at kernelRun
    exact kernelRun
  have seed := PqxdhRecordLiftSeed.server_source left right output context (.None : core.option.Option Unit)
  rw [supplied, bind_tc_ok, sent] at seed
  obtain ⟨expected, expectedRun⟩ :=
    PqxdhRecordLiftSeed.serverKernel_total (PqxdhOrderedChainHybrids.nextChain output, right)
  rw [expectedRun, RawCtxMaterialInterpretation.rust_map_ok] at seed
  have equal : selected.pending.seal.advanced = expected := by
    simpa only [RustM.ok.injEq, Option.some.injEq, Prod.mk.injEq, and_true] using seed
  exact ⟨next, selected, initialRun, nextRun, expectedRun.trans (congrArg RustM.ok equal.symm)⟩

theorem server_seed_parts (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : agreement.ServerAgreement) (application : Slice Std.U8)
    (initial : registration.ServerInitialKdf)
    (actual : BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission control current availability agreement application initial)
    (left key : PqxdhSecretInputKdf.RootOutput) (seed : PqxdhRecordLiftSeed.Seed)
    (nonce : PqxdhFullSecretInputKdf.NonceOutput) :
    ∃ (next : registration.ServerInitialSeal) (selected : registration.ServerRecordAead),
      initial.resume (.Some (RawCtxSelectedInitialConstructor.response64 (left ++ seed.2))) = .ok (.Ok next) ∧
      next.resume (.Some (RawCtxKdfRequestTable.fullResponse (RawCtxKdfRequestTable.assemble (key, seed.1, nonce)))) =
        .ok (.Ok selected) ∧ PqxdhRecordLiftSeed.serverKernel seed = .ok selected.pending.seal.advanced := by
  simpa only [PqxdhRecordLiftSeed.assembled_next] using server_seed control current availability agreement application
    initial actual left seed.2 (RawCtxKdfRequestTable.assemble (key, seed.1, nonce))

end BeaconcryptCore.Computational.RegistrationSeedKernel

/-- info: 'BeaconcryptCore.Computational.RegistrationSeedKernel.server_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSeedKernel.server_pending
/-- info: 'BeaconcryptCore.Computational.RegistrationSeedKernel.source_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSeedKernel.source_send
/-- info: 'BeaconcryptCore.Computational.RegistrationSeedKernel.server_seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSeedKernel.server_seed
/-- info: 'BeaconcryptCore.Computational.RegistrationSeedKernel.server_seed_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSeedKernel.server_seed_parts
