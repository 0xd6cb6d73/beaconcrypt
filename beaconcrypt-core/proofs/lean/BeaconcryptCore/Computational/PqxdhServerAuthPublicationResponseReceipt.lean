import BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter

/-! Ordered successful inner-send and outer-response writer receipts from the actual builder. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseReceipt
open PqxdhJointKdfGame
open PqxdhServerAuthExperiment (Codec Checks)
open PqxdhServerAuthPublicationTrace (Compiler Event Trace)
open PqxdhServerAuthCtxCalls (Kernel Residual)
variable {Reader WireResponse Metadata PeerMetadata Consumed : Type}

/-- An actual successful first-send result has one newly appended sealer observation with the same complete encrypted value and source context. -/
theorem send_success (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (kernel advanced : Kernel)
    (context : RawCtxSourceSend.SealContext) (encrypted : RawCtxSourceSend.Encrypted)
    (before after : PqxdhServerAuthPublicationTrace.State)
    (supported : (some (advanced, some encrypted), after) ∈ support
      (((PqxdhServerAuthPublicationWriter.calls source codec checks rest).send kernel context).run.run before)) :
    ∃ pending : PqxdhServerAuthCtxSend.Pending,
      pending.context = context ∧ pending.advanced = advanced ∧
      after.1 = before.1 ++ [context] ∧
      after.2 = before.2 ++ [.seal pending (some (some encrypted))] := by
  unfold PqxdhServerAuthPublicationWriter.calls PqxdhServerAuthCtxBuildSettlement.calls
    RawCtxChainSend.execute at supported
  cases begun : RawCtxChainSend.normalBegin kernel context with
  | exhausted previous actual =>
      simp only [begun, RawCtxChainSend.program, simulateQ_pure, OptionT.run_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
  | requested pending =>
      simp only [begun, RawCtxChainSend.program, simulateQ_bind, simulateQ_spec_query,
        PqxdhServerAuthCtxBuildSettlement.labels, pure_bind,
        bind_pure_comp, simulateQ_map, OptionT.run_map, StateT.run_map] at supported
      rw [PqxdhServerAuthPublicationTrace.seal_run, Functor.map_map, support_map] at supported
      obtain ⟨reply, _, same⟩ := supported
      cases reply with
      | none => cases same
      | some value =>
          cases value with
          | none => cases same
          | some sealed =>
              simp only [Option.map_some, Prod.mk.injEq, Option.some.injEq] at same
              rcases same with ⟨⟨advancedSame, rfl⟩, rfl⟩
              have contextSame := PqxdhServerAuthBuildReceipt.requested_context kernel context pending begun
              exact ⟨RawCtxChainSend.ready pending (PqxdhServerAuthCtxCalls.step source rest pending.request),
                contextSame, advancedSame, by simp only [RawCtxChainSend.ready, contextSame], rfl⟩

/-- Successful response publication uses the precise encrypted value from the immediately preceding successful sealer; both actual observations remain in chronological order. -/
theorem after_success (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (candidate : pqxdh.ServerRegistrationCandidate)
    (authenticated : Pqxdh.Bytes) (kernel : Kernel) (metadata : PeerMetadata)
    (state published : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed)
    (before after : PqxdhServerAuthPublicationTrace.State)
    (response : PqxdhServerRegistrationPublication.Response)
    (supported : (some (some response, published), after) ∈ support
      ((PqxdhInitialGenericPublication.afterInitialization
        (PqxdhServerAuthPublicationWriter.calls source codec checks rest)
        (PqxdhServerAuthPublicationWriter.aux source codec checks)
        candidate authenticated kernel metadata state).run.run before)) :
    ∃ (pending : PqxdhServerAuthCtxSend.Pending) (encrypted : RawCtxSourceSend.Encrypted),
      pending.context = PqxdhServerRegistrationPublication.firstContext candidate authenticated ∧
      after.1 = before.1 ++ [pending.context] ∧
      after.2 = before.2 ++ [.seal pending (some (some encrypted)),
        .write (PqxdhServerRegistrationPublication.responseFields candidate encrypted)
          (some (some response.serialized))] ∧
      codec.write2 (PqxdhServerRegistrationPublication.responseFields candidate encrypted) = some response.serialized ∧
      response.keyId = candidate.key_id ∧
      published = PqxdhInitialGenericPublication.publish state candidate pending.advanced metadata := by
  rw [PqxdhServerAuthPublicationWriter.after_run, mem_support_bind_iff] at supported
  obtain ⟨⟨sent, afterSend⟩, reached, supported⟩ := supported
  cases sent with
  | none =>
      simp only [support_pure, Set.mem_singleton_iff] at supported
      cases supported
  | some sent =>
      rcases sent with ⟨advanced, encrypted⟩
      cases encrypted with
      | none =>
          simp only [support_pure, Set.mem_singleton_iff] at supported
          cases supported
      | some encrypted =>
          cases written : codec.write2 (PqxdhServerRegistrationPublication.responseFields candidate encrypted) with
          | none =>
              simp only [written, Option.map_none, Option.isSome_none, Bool.false_eq_true, ite_false,
                support_pure, Set.mem_singleton_iff] at supported
              cases supported
          | some bytes =>
              simp only [written, Option.map_some, Option.isSome_some, ite_true,
                support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at supported
              rcases supported with ⟨⟨rfl, rfl⟩, rfl⟩
              obtain ⟨pending, contextSame, advancedSame, logSame, traceSame⟩ :=
                send_success source codec checks rest kernel advanced
                  (PqxdhServerRegistrationPublication.firstContext candidate authenticated)
                  encrypted before afterSend reached
              exact ⟨pending, encrypted, contextSame, by simpa only [contextSame] using logSame,
                by simp only [traceSame, List.append_assoc, List.singleton_append], written, rfl,
                by rw [advancedSame]⟩

/-- A successful candidate result supplies the original successful initializer and literal key-ID binding, with the complete reached first-send tail. -/
theorem candidate_tail (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (initial : RustM Kernel)
    (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state published : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed)
    (before after : PqxdhServerAuthPublicationTrace.State)
    (response : PqxdhServerRegistrationPublication.Response)
    (supported : (some (.ok (some response, published)), after) ∈ support
      ((PqxdhInitialGenericBuilder.candidate
        (PqxdhServerAuthPublicationWriter.calls source codec checks rest)
        (PqxdhServerAuthPublicationWriter.aux source codec checks)
        initial candidate data metadata state).run.run before)) :
    ∃ (kernel : Kernel) (binding : pqxdh.RegistrationKeyIdBinding),
      initial = .ok kernel ∧ candidate.key_id_binding = .ok binding ∧
      (some (some response, published), after) ∈ support
        ((PqxdhInitialGenericPublication.afterInitialization
          (PqxdhServerAuthPublicationWriter.calls source codec checks rest)
          (PqxdhServerAuthPublicationWriter.aux source codec checks) candidate
          (absBytes binding.bytes ++ data.getD PqxdhServerRegistrationPublication.registrationWitness)
          kernel metadata state).run.run before) := by
  simp only [PqxdhInitialGenericBuilder.candidate] at supported
  rw [PqxdhServerAuthPublicationWriter.aux_quiet source codec checks (.checkIdentity _) (by intros; simp)] at supported
  simp only [PqxdhServerAuthPublicationWriter.auxValue, pure_bind] at supported
  cases identity : checks.beaconIdentity candidate.beacon_identity_public_key
  · simp only [identity, Bool.not_false, ite_true, OptionT.run_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    cases supported

  · simp only [identity, Bool.not_true, Bool.false_eq_true, ite_false] at supported
    rw [PqxdhServerAuthPublicationWriter.aux_quiet source codec checks .reservePeer (by intros; simp)] at supported
    simp only [PqxdhServerAuthPublicationWriter.auxValue, pure_bind] at supported
    cases reserved : checks.reservePeer
    · simp only [reserved, Bool.not_false, ite_true, OptionT.run_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported

    · simp only [reserved, Bool.not_true, Bool.false_eq_true, ite_false] at supported
      cases initial with
      | fail error =>
          simp only [PqxdhInitialGenericBuilder.continueRust, OptionT.run_pure,
            StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          cases supported

      | div =>
          simp only [PqxdhInitialGenericBuilder.continueRust, OptionT.run_pure,
            StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          cases supported

      | ok kernel =>
          simp only [PqxdhInitialGenericBuilder.continueRust] at supported
          by_cases empty : (data.getD PqxdhServerRegistrationPublication.registrationWitness).isEmpty = true
          · simp only [empty, ite_true, OptionT.run_pure, StateT.run_pure,
              support_pure, Set.mem_singleton_iff] at supported
            cases supported

          · simp only [empty, Bool.false_eq_true, ite_false] at supported
            by_cases fits : 8 + (data.getD PqxdhServerRegistrationPublication.registrationWitness).length ≤ Usize.max
            · simp only [fits, ite_true] at supported
              rw [PqxdhServerAuthPublicationWriter.aux_quiet source codec checks (.reservePlaintext _) (by intros; simp)] at supported
              simp only [PqxdhServerAuthPublicationWriter.auxValue, pure_bind] at supported
              cases allocated : checks.reservePlaintext (8 + (data.getD PqxdhServerRegistrationPublication.registrationWitness).length)
              · simp only [allocated, Bool.not_false, ite_true, OptionT.run_pure,
                  StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
                cases supported

              · simp only [allocated, Bool.not_true, Bool.false_eq_true, ite_false] at supported
                cases bindingReply : candidate.key_id_binding with
                | fail error =>
                    simp only [bindingReply, OptionT.run_pure, StateT.run_pure,
                      support_pure, Set.mem_singleton_iff] at supported
                    cases supported

                | div =>
                    simp only [bindingReply, OptionT.run_pure, StateT.run_pure,
                      support_pure, Set.mem_singleton_iff] at supported
                    cases supported

                | ok binding =>
                    simp only [bindingReply, OptionT.run_map, StateT.run_map, support_map] at supported
                    obtain ⟨⟨reply, stateAfter⟩, reached, same⟩ := supported
                    cases reply with
                    | none => cases same
                    | some value =>
                        simp only [Option.map_some, Prod.mk.injEq, Option.some.injEq, RustM.ok.injEq] at same
                        rcases same with ⟨rfl, rfl⟩
                        exact ⟨kernel, binding, rfl, rfl, reached⟩
            · simp only [fits, ite_false, OptionT.run_pure, StateT.run_pure,
                support_pure, Set.mem_singleton_iff] at supported
              cases supported


/-- Full builder success comes from its actual checked next ID and pending-token Server-binding candidate, followed by the literal candidate execution. -/
theorem build_tail (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (initial : RustM Kernel)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state published : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed)
    (before after : PqxdhServerAuthPublicationTrace.State)
    (response : PqxdhServerRegistrationPublication.Response)
    (supported : (some (.ok (some response, published)), after) ∈ support
      ((PqxdhServerAuthSendFactor.genericBuild
        (PqxdhServerAuthPublicationWriter.calls source codec checks rest)
        (PqxdhServerAuthPublicationWriter.aux source codec checks)
        initial pending data metadata state).run.run before)) :
    ∃ (key : Std.U64) (candidate : pqxdh.ServerRegistrationCandidate),
      pqxdh.server_next_key_id state.control = .ok (.Ok key) ∧
      pqxdh.server_prepare_commit state.control pending ⟨state.server.identity, state.identityKeyId⟩
        (if (state.server.peers key).isSome then .Occupied else .Available) = .ok (.Ok candidate) ∧
      (some (.ok (some response, published)), after) ∈ support
        ((PqxdhInitialGenericBuilder.candidate
          (PqxdhServerAuthPublicationWriter.calls source codec checks rest)
          (PqxdhServerAuthPublicationWriter.aux source codec checks)
          initial candidate data metadata state).run.run before) := by
  unfold PqxdhServerAuthSendFactor.genericBuild at supported
  cases next : pqxdh.server_next_key_id state.control with
  | fail error =>
      simp only [next, PqxdhInitialGenericBuilder.continueRust, OptionT.run_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported

  | div =>
      simp only [next, PqxdhInitialGenericBuilder.continueRust, OptionT.run_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported

  | ok value =>
      cases value with
      | Err error =>
          simp only [next, PqxdhInitialGenericBuilder.continueRust, OptionT.run_pure,
            StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          cases supported

      | Ok key =>
          simp only [next, PqxdhInitialGenericBuilder.continueRust] at supported
          cases prepared : pqxdh.server_prepare_commit state.control pending
            ⟨state.server.identity, state.identityKeyId⟩
            (if (state.server.peers key).isSome then .Occupied else .Available) with
          | fail error =>
              simp only [prepared, OptionT.run_pure, StateT.run_pure,
                support_pure, Set.mem_singleton_iff] at supported
              cases supported

          | div =>
              simp only [prepared, OptionT.run_pure, StateT.run_pure,
                support_pure, Set.mem_singleton_iff] at supported
              cases supported

          | ok value =>
              cases value with
              | Err error =>
                  simp only [prepared, OptionT.run_pure, StateT.run_pure,
                    support_pure, Set.mem_singleton_iff] at supported
                  cases supported

              | Ok candidate =>
                  simp only [prepared] at supported
                  exact ⟨key, candidate, rfl, prepared, supported⟩

/-- The full native result projection retains the original successful material builder and its exact private trace; only the proved kernel representation is projected. -/
theorem compiled_tail (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state published : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)
    (before after : PqxdhServerAuthPublicationTrace.State)
    (response : PqxdhServerRegistrationPublication.Response)
    (supported : (some (.ok (some response, published)), after) ∈ support
      ((PqxdhServerAuthPublicationTrace.compiled source codec checks rest pending data metadata state).run.run before)) :
    ∃ originalPublished : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed,
      PqxdhInitialGenericPublication.native PqxdhServerAuthCtxBuildSettlement.resolve originalPublished = published ∧
      (some (.ok (some response, originalPublished)), after) ∈ support
        ((PqxdhServerAuthSendFactor.genericBuild
          (PqxdhServerAuthPublicationWriter.calls source codec checks rest)
          (PqxdhServerAuthPublicationWriter.aux source codec checks)
          (PqxdhServerAuthCtxCalls.initial false rest.2.2) pending data metadata
          (PqxdhServerAuthCtxBuildSettlement.embed state)).run.run before) := by
  have handler : PqxdhServerAuthPublicationTrace.compiler source codec checks =
      PqxdhServerAuthBuildProgram.impl
        (fun pending => PqxdhServerAuthPublicationTrace.compiler source codec checks (.inl pending))
        (PqxdhServerAuthPublicationWriter.aux source codec checks) := by
    funext query
    cases query <;> rfl
  rw [PqxdhServerAuthPublicationTrace.compiled, handler,
    PqxdhServerAuthBuildProgram.program_interpret] at supported
  simp only [OptionT.run_map, StateT.run_map, support_map] at supported
  obtain ⟨⟨original, originalAfter⟩, reached, same⟩ := supported
  cases original with
  | none => cases same
  | some original =>
      cases original with
      | fail error => cases same
      | div => cases same
      | ok value =>
          rcases value with ⟨reply, originalPublished⟩
          simp only [Option.map_some, RawCtxMaterialInterpretation.rust_map_ok, Prod.map,
            id_eq, Option.some.injEq, RustM.ok.injEq, Prod.mk.injEq] at same
          rcases same with ⟨⟨rfl, projection⟩, rfl⟩
          exact ⟨originalPublished, projection, reached⟩

/-- A complete native successful response carries its actual source candidate, bound plaintext, ordered inner/outer writer arguments and installed advanced kernel. No decoding or codec law is used. -/
theorem compiled_receipt (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state published : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)
    (before after : PqxdhServerAuthPublicationTrace.State)
    (response : PqxdhServerRegistrationPublication.Response)
    (supported : (some (.ok (some response, published)), after) ∈ support
      ((PqxdhServerAuthPublicationTrace.compiled source codec checks rest pending data metadata state).run.run before)) :
    ∃ (key : Std.U64) (candidate : pqxdh.ServerRegistrationCandidate)
      (binding : pqxdh.RegistrationKeyIdBinding) (sealed : PqxdhServerAuthCtxSend.Pending)
      (encrypted : RawCtxSourceSend.Encrypted),
      pqxdh.server_next_key_id state.control = .ok (.Ok key) ∧
      pqxdh.server_prepare_commit state.control pending ⟨state.server.identity, state.identityKeyId⟩
        (if (state.server.peers key).isSome then .Occupied else .Available) = .ok (.Ok candidate) ∧
      candidate.key_id_binding = .ok binding ∧
      sealed.context = PqxdhServerRegistrationPublication.firstContext candidate
        (absBytes binding.bytes ++ data.getD PqxdhServerRegistrationPublication.registrationWitness) ∧
      after.1 = before.1 ++ [sealed.context] ∧
      after.2 = before.2 ++ [.seal sealed (some (some encrypted)),
        .write (PqxdhServerRegistrationPublication.responseFields candidate encrypted)
          (some (some response.serialized))] ∧
      codec.write2 (PqxdhServerRegistrationPublication.responseFields candidate encrypted) = some response.serialized ∧
      response.keyId = candidate.key_id ∧
      published = PqxdhServerRegistrationPublication.publish state candidate
        (PqxdhServerAuthCtxBuildSettlement.resolve sealed.advanced) metadata := by
  obtain ⟨originalPublished, projection, reached⟩ :=
    compiled_tail source codec checks rest pending data metadata state published before after response supported
  obtain ⟨key, candidate, next, prepared, reached⟩ :=
    build_tail source codec checks rest (PqxdhServerAuthCtxCalls.initial false rest.2.2)
      pending data metadata (PqxdhServerAuthCtxBuildSettlement.embed state)
      originalPublished before after response reached
  obtain ⟨kernel, binding, _, bindingReply, reached⟩ :=
    candidate_tail source codec checks rest (PqxdhServerAuthCtxCalls.initial false rest.2.2)
      candidate data metadata (PqxdhServerAuthCtxBuildSettlement.embed state)
      originalPublished before after response reached
  obtain ⟨sealed, encrypted, contextSame, logSame, traceSame, written, keySame, publishedSame⟩ :=
    after_success source codec checks rest candidate _ kernel metadata
      (PqxdhServerAuthCtxBuildSettlement.embed state) originalPublished before after response reached
  refine ⟨key, candidate, binding, sealed, encrypted, next, ?_, bindingReply,
    contextSame, logSame, traceSame, written, keySame, ?_⟩
  · simpa only [PqxdhServerAuthCtxBuildSettlement.embed, Option.isSome_map] using prepared
  · have collapse : PqxdhInitialGenericPublication.native PqxdhServerAuthCtxBuildSettlement.resolve
          (PqxdhServerAuthCtxBuildSettlement.embed state) = state :=
        PqxdhServerAuthCtxBuildSettlement.native_embed _ state
    rw [← projection, publishedSame, PqxdhInitialGenericPublication.publish_native, collapse]

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseReceipt

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseReceipt.send_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseReceipt.send_success
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseReceipt.after_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseReceipt.after_success
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseReceipt.candidate_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseReceipt.candidate_tail
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseReceipt.build_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseReceipt.build_tail
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseReceipt.compiled_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseReceipt.compiled_tail
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseReceipt.compiled_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseReceipt.compiled_receipt
