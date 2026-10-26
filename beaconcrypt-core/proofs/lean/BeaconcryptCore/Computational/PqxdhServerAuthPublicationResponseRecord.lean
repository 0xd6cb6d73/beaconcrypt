import BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseReceipt
import BeaconcryptCore.Computational.PqxdhServerAuthDecodedOrigin

/-! The selected component's actual records are attached to the same observed builder callbacks. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseRecord
open PqxdhJointKdfGame PqxdhFullSecretInputKdf CtxRomAuth
open PqxdhServerAuthExperiment (Codec Checks)
open PqxdhServerAuthPublicationTrace (Event Trace)
open RawCtxSelectedAuthenticationObserver (monitor)
open RawCtxSelectedMessageSealing (selectedInput)
variable {Reader WireResponse Result : Type}

/-- A produced selected record and the actual optional native sealing reply belong to one recorded callback. -/
def Origin (writer : RawCtxMixedShared.Writer) (trace : Trace) (entry : CtxSuccessfulSeal) : Prop :=
  ∃ (pending : PqxdhServerAuthCtxSend.Pending) (reply : Option (Option RawCtxSourceSend.Encrypted))
    (nonce : NonceOutput) (width : pending.context.associatedData.length = 281) (record : CtxRomRecord),
    Event.seal pending reply ∈ trace ∧ pending.material = .hidden nonce ∧
    entry = ⟨selectedInput nonce pending.sequence pending.context width, record⟩ ∧
    reply = some ((writer ⟨pending.sequence, pending.context.senderId, record.encode⟩).map
      (RawCtxInterpretedArguments.encrypted
        (RawCtxInterpretedArguments.sealArguments (PqxdhServerAuthCtxSend.sealing pending))))

/-- A later trace extension retains the exact earlier callback occurrence and reply. -/
theorem Origin.mono (writer : RawCtxMixedShared.Writer) (before after : Trace)
    (retained : before.IsPrefix after) (entry : CtxSuccessfulSeal) (origin : Origin writer before entry) :
    Origin writer after entry := by
  obtain ⟨pending, reply, nonce, width, record, found, hidden, equal, returned⟩ := origin
  exact ⟨pending, reply, nonce, width, record, retained.subset found, hidden, equal, returned⟩

/-- The complete actual sealer records its real reply after its component work; old records remain separate from this invocation. -/
theorem seal_receipt (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (pending : PqxdhServerAuthCtxSend.Pending)
    (beforeTrace afterTrace : PqxdhServerAuthPublicationTrace.State)
    (before after : RawCtxSelectedAuthenticationObserver.State)
    (reply : Option (Option RawCtxSourceSend.Encrypted))
    (supported : ((reply, afterTrace), after) ∈ support
      (monitor ((PqxdhServerAuthPublicationTrace.compiler source codec checks (.inl pending)).run.run beforeTrace) before)) :
    beforeTrace.2.IsPrefix afterTrace.2 ∧
      ∀ entry ∈ after.seals, entry ∈ before.seals ∨ Origin codec.frameWrite afterTrace.2 entry := by
  rw [PqxdhServerAuthPublicationTrace.seal_run, RawCtxSelectedAcceptedRecord.monitor_map, support_map] at supported
  obtain ⟨⟨value, observed⟩, reached, equal⟩ := supported
  cases equal
  refine ⟨⟨[.seal pending value], rfl⟩, ?_⟩
  intro entry found
  rcases RawCtxSelectedSealReceipt.sealing_provenance source.crypto codec.frameWrite
    (PqxdhServerAuthCtxSend.sealing pending) before observed value reached entry found with
    old | ⟨nonce, width, record, hidden, entrySame, completed, _⟩
  · exact Or.inl old
  · exact Or.inr ⟨pending, value, nonce, width, record, by simp, hidden, entrySame, completed⟩

/-- Each concrete builder callback preserves the trace prefix and assigns every new selected record to its own actual sealer observation. -/
theorem compiler_receipts (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (query : PqxdhServerAuthBuildProgram.Spec.Domain)
    (beforeTrace afterTrace : PqxdhServerAuthPublicationTrace.State)
    (before after : RawCtxSelectedAuthenticationObserver.State)
    (reply : Option (PqxdhServerAuthBuildProgram.Spec.Range query))
    (supported : ((reply, afterTrace), after) ∈ support
      (monitor ((PqxdhServerAuthPublicationTrace.compiler source codec checks query).run.run beforeTrace) before)) :
    beforeTrace.2.IsPrefix afterTrace.2 ∧
      ∀ entry ∈ after.seals, entry ∈ before.seals ∨ Origin codec.frameWrite afterTrace.2 entry := by
  cases query with
  | inl pending => exact seal_receipt source codec checks pending beforeTrace afterTrace before after reply supported
  | inr auxiliary =>
      change ((reply, afterTrace), after) ∈ support
        (monitor ((PqxdhServerAuthPublicationWriter.aux source codec checks auxiliary).run.run beforeTrace) before) at supported
      rw [PqxdhServerAuthPublicationWriter.aux_run] at supported
      simp only [monitor, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact ⟨⟨_, rfl⟩, fun _ found => Or.inl found⟩

private theorem monitor_bind {X Y : Type} (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec X)
    (next : X → OracleComp AdaptiveCtxDynamicKnownKeys.Spec Y)
    (state : RawCtxSelectedAuthenticationObserver.State) :
    monitor (work >>= next) state =
      (do let result ← monitor work state; monitor (next result.1) result.2) := by
  simp only [monitor, simulateQ_bind, StateT.run_bind]

/-- Full adaptive builder syntax retains the exact callback association through all optional replies; earlier component records remain an explicit alternative. -/
theorem program_receipts (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (work : OracleComp PqxdhServerAuthBuildProgram.Spec Result)
    (beforeTrace afterTrace : PqxdhServerAuthPublicationTrace.State)
    (before after : RawCtxSelectedAuthenticationObserver.State) (reply : Option Result)
    (supported : ((reply, afterTrace), after) ∈ support
      (monitor ((simulateQ (PqxdhServerAuthPublicationTrace.compiler source codec checks) work).run.run beforeTrace) before)) :
    beforeTrace.2.IsPrefix afterTrace.2 ∧
      ∀ entry ∈ after.seals, entry ∈ before.seals ∨ Origin codec.frameWrite afterTrace.2 entry := by
  induction work using OracleComp.inductionOn generalizing beforeTrace afterTrace before after reply with
  | pure value =>
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, monitor,
        simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact ⟨List.prefix_rfl, fun _ found => Or.inl found⟩
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind] at supported
      rw [monitor_bind] at supported
      simp only [mem_support_bind_iff] at supported
      obtain ⟨⟨⟨value, middleTrace⟩, middle⟩, reached, continued⟩ := supported
      have step := compiler_receipts source codec checks query beforeTrace middleTrace before middle value reached
      cases value with
      | none =>
          simp only [Option.elim_none, StateT.run_pure, monitor, simulateQ_pure,
            StateT.run_pure, mem_support_pure_iff] at continued
          cases continued
          exact step
      | some value =>
          have tail := ih value middleTrace afterTrace middle after reply continued
          refine ⟨step.1.trans tail.1, ?_⟩
          intro entry found
          rcases tail.2 entry found with old | origin
          · rcases step.2 entry old with earlier | produced
            · exact Or.inl earlier
            · exact Or.inr (Origin.mono codec.frameWrite _ _ tail.1 entry produced)
          · exact Or.inr origin

/-- In the actual successful two-callback trace, a selected record's origin is the unique sealer observation, and that record's frame serialization is the returned inner ciphertext. -/
theorem Origin.single_success (writer : RawCtxMixedShared.Writer)
    (pending : PqxdhServerAuthCtxSend.Pending) (encrypted : RawCtxSourceSend.Encrypted)
    (fields : PqxdhServerRegistrationPublication.ResponseFields) (bytes : Pqxdh.Bytes)
    (entry : CtxSuccessfulSeal)
    (origin : Origin writer [.seal pending (some (some encrypted)), .write fields (some (some bytes))] entry) :
    ∃ (nonce : NonceOutput) (width : pending.context.associatedData.length = 281),
      pending.material = .hidden nonce ∧
      entry.input = selectedInput nonce pending.sequence pending.context width ∧
      writer ⟨pending.sequence, pending.context.senderId, entry.record.encode⟩ = some encrypted.ciphertext := by
  obtain ⟨actual, reply, nonce, width, record, found, hidden, entrySame, returned⟩ := origin
  simp only [List.mem_cons, List.not_mem_nil, Event.seal.injEq, reduceCtorEq, or_false] at found
  rcases found with ⟨samePending, sameReply⟩
  subst actual
  subst reply
  cases written : writer ⟨pending.sequence, pending.context.senderId, record.encode⟩ with
  | none => simp only [written, Option.map_none, Option.some.injEq, reduceCtorEq] at returned
  | some encoded =>
      simp only [written, Option.map_some, Option.some.injEq] at returned
      have ciphertext := congrArg RawCtxSourceSend.Encrypted.ciphertext returned
      refine ⟨nonce, width, hidden, ?_, ?_⟩
      · rw [entrySame]
      · rw [entrySame]
        simpa only [ciphertext, RawCtxInterpretedArguments.encrypted] using written

variable {Metadata PeerMetadata Consumed : Type}

/-- Every new selected component record in a successful complete builder is the actual inner frame of that same response. Candidate, pending binding and full publication remain attached to the exact source execution. -/
theorem compiled_records (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : PqxdhServerAuthCtxCalls.Residual) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state published : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)
    (beforeLog : PqxdhServerAuthBuildProgram.Log) (afterTrace : PqxdhServerAuthPublicationTrace.State)
    (before after : RawCtxSelectedAuthenticationObserver.State)
    (response : PqxdhServerRegistrationPublication.Response)
    (supported : ((some (.ok (some response, published)), afterTrace), after) ∈ support
      (monitor ((PqxdhServerAuthPublicationTrace.compiled source codec checks rest pending data metadata state).run.run
        (beforeLog, [])) before)) :
    ∃ (key : Std.U64) (candidate : pqxdh.ServerRegistrationCandidate)
      (binding : pqxdh.RegistrationKeyIdBinding) (sealed : PqxdhServerAuthCtxSend.Pending)
      (encrypted : RawCtxSourceSend.Encrypted),
      pqxdh.server_next_key_id state.control = .ok (.Ok key) ∧
      pqxdh.server_prepare_commit state.control pending ⟨state.server.identity, state.identityKeyId⟩
        (if (state.server.peers key).isSome then .Occupied else .Available) = .ok (.Ok candidate) ∧
      candidate.key_id_binding = .ok binding ∧
      sealed.context = PqxdhServerRegistrationPublication.firstContext candidate
        (absBytes binding.bytes ++ data.getD PqxdhServerRegistrationPublication.registrationWitness) ∧
      codec.write2 (PqxdhServerRegistrationPublication.responseFields candidate encrypted) = some response.serialized ∧
      response.keyId = candidate.key_id ∧
      published = PqxdhServerRegistrationPublication.publish state candidate
        (PqxdhServerAuthCtxBuildSettlement.resolve sealed.advanced) metadata ∧
      ∀ entry ∈ after.seals, entry ∈ before.seals ∨
        ∃ (nonce : NonceOutput) (width : sealed.context.associatedData.length = 281),
          sealed.material = .hidden nonce ∧
          entry.input = selectedInput nonce sealed.sequence sealed.context width ∧
          codec.frameWrite ⟨sealed.sequence, sealed.context.senderId, entry.record.encode⟩ = some encrypted.ciphertext := by
  have rawSupport : (some (.ok (some response, published)), afterTrace) ∈ support
      ((PqxdhServerAuthPublicationTrace.compiled source codec checks rest pending data metadata state).run.run
        (beforeLog, [])) := by
    rw [← RawCtxSelectedAuthenticationObserver.monitor_erase
      ((PqxdhServerAuthPublicationTrace.compiled source codec checks rest pending data metadata state).run.run
        (beforeLog, [])) before, support_map]
    exact ⟨((some (.ok (some response, published)), afterTrace), after), supported, rfl⟩
  obtain ⟨key, candidate, binding, sealed, encrypted, next, prepared, bound,
      contextSame, _, traceSame, written, keySame, publishedSame⟩ :=
    PqxdhServerAuthPublicationResponseReceipt.compiled_receipt source codec checks rest pending data metadata
      state published (beforeLog, []) afterTrace response rawSupport
  refine ⟨key, candidate, binding, sealed, encrypted, next, prepared, bound,
    contextSame, written, keySame, publishedSame, ?_⟩
  have origins := (program_receipts source codec checks
    (PqxdhServerAuthBuildProgram.program source rest pending data metadata state)
    (beforeLog, []) afterTrace before after _ supported).2
  intro entry found
  rcases origins entry found with old | origin
  · exact Or.inl old
  · rw [traceSame, List.nil_append] at origin
    exact Or.inr (Origin.single_success codec.frameWrite sealed encrypted _ response.serialized entry origin)

/-- An accepted matched target decodes to the exact frame supplied to the same actual inner writer. This transports decoded fields only, without any equality of wire encodings. -/
theorem matched_frame (read : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (candidate : pqxdh.BeaconRegistrationCandidate) (opened : RawCtxWholeOwner.Decrypted)
    (target : CtxUnclaimedAcceptance.Target)
    (delivery : PqxdhPhase2LocalMatching.LocalTarget read raw candidate opened target)
    (entry : CtxSuccessfulSeal) (same : target.toLegacy.sameFullTupleAsSuccessfulSeal entry)
    (pending : PqxdhServerAuthCtxSend.Pending) (nonce : NonceOutput)
    (width : pending.context.associatedData.length = 281)
    (input : entry.input = selectedInput nonce pending.sequence pending.context width) :
    read raw = some ⟨pending.sequence, pending.context.senderId, entry.record.encode⟩ := by
  have decoded := PqxdhServerAuthDecodedOrigin.matched_frame read raw candidate opened target delivery entry same
  have ad := same.2.1.symm.trans
    (PqxdhPhase2LocalMatching.localTarget_context read raw candidate opened target delivery).1
  rw [input] at ad
  have sequence : pending.sequence = opened.sequence :=
    UScalar.eq_of_val_eq (congrArg (fun value => value.seq) ad)
  have sender : pending.context.senderId = opened.keyId :=
    UScalar.eq_of_val_eq (congrArg (fun value => value.sid) ad)
  simpa only [sequence, sender] using decoded

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseRecord

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseRecord.Origin.mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseRecord.Origin.mono
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseRecord.seal_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseRecord.seal_receipt
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseRecord.compiler_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseRecord.compiler_receipts
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseRecord.program_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseRecord.program_receipts
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseRecord.Origin.single_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseRecord.Origin.single_success
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseRecord.compiled_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseRecord.compiled_records
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseRecord.matched_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseRecord.matched_frame
