-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMonotone

/-! Actual shared-ROM commitment witnesses for caller-known record paths. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- Every actual shared hash reply is retained at its exact input address. -/
theorem hash_cached (query : CtxRO.Domain) (before : CtxRO.QueryCache)
    (result : CtxDigest × CtxRO.QueryCache)
    (supported : result ∈ support ((ctxRandomOracle query).run before)) :
    result.2 query = some result.1 :=
  QueryImpl.withCaching_run_caches uniformSampleImpl query before result supported

/-- Shared ROM sampling only extends the same cache; hits preserve their old digest. -/
theorem hash_grows (query : CtxRO.Domain) (before : CtxRO.QueryCache)
    (result : CtxDigest × CtxRO.QueryCache)
    (supported : result ∈ support ((ctxRandomOracle query).run before)) : before ≤ result.2 :=
  QueryImpl.withCaching_cache_le uniformSampleImpl query before result supported

/-- The actual counted native hash callback returns a digest installed in its final shared cache. -/
theorem native_hash_cached (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (bytes : Pqxdh.Bytes)
    (before : PqxdhRecordLiftWorld.Primitive)
    (result : Option Pqxdh.Bytes × PqxdhRecordLiftWorld.Primitive)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.primitives setup codec
      (.inr (.inr (.inr (.inl bytes))))).run before)) :
    ∃ digest, result.1 = some digest.toList ∧ result.2.2 ((), bytes) = some digest := by
  simp only [PqxdhRecordLiftWorld.primitives, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  have source := PqxdhRecordLiftFlat.support_run_fst _ _ _ inner reached
  change inner.1 ∈ support (((RawCtxMixedShared.sharedImpl setup.source.crypto codec.frameWrite
    (RawCtxSourceHkdf.kdfImpl setup.source)) (.inr (.inr (.inr (.inl bytes))))).run ((), before.2)) at source
  rw [RawCtxMixedShared.shared_hash, bind_pure_comp, support_map] at source
  obtain ⟨hashed, queried, equal⟩ := source
  exact ⟨hashed.1, (congrArg Prod.fst equal).symm, (congrArg (fun value => value.2.2) equal).symm ▸ hash_cached ((), bytes) before.2 hashed queried⟩

/-- Every actual mixed record primitive preserves all previous shared-ROM responses. -/
theorem deployment_cache_grows (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (query : RawCtxMixedOwner.NativeSpec.Domain)
    (before : RawCtxSharedPrimitive.SharedState Unit)
    (result : RawCtxMixedOwner.NativeSpec.Range query × RawCtxSharedPrimitive.SharedState Unit)
    (supported : result ∈ support ((PqxdhDeploymentNative.primitives setup codec query).run before)) :
    before.2 ≤ result.2.2 := by
  rcases query with request | (sealing | (opening | (bytes | frame)))
  all_goals simp only [PqxdhDeploymentNative.primitives, RawCtxMixedShared.sharedImpl,
    QueryImpl.compose, RawCtxMixedShared.sharedAdapter, simulateQ_pure, simulateQ_spec_query,
    RawCtxSharedPrimitive.nativeImpl, RawCtxSharedPrimitive.openingImpl, RawCtxSourceHkdf.kdfImpl,
    StateT.run, support_pure, Set.mem_singleton_iff, bind_pure_comp, support_map] at supported
  all_goals first | change result ∈ support (pure (_, before) : ProbComp _) at supported | skip
  case inr.inr.inr.inl =>
    obtain ⟨hashed, reached, rfl⟩ := supported
    exact hash_grows ((), bytes) before.2 hashed reached
  all_goals simpa only [support_pure, Set.mem_singleton_iff] using supported ▸ (le_refl before.2)

/-- Native call and uniform instrumentation retain every already cached digest. -/
theorem native_cache_grows (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (query : RawCtxMixedOwner.NativeSpec.Domain)
    (before : PqxdhRecordLiftWorld.Primitive)
    (result : RawCtxMixedOwner.NativeSpec.Range query × PqxdhRecordLiftWorld.Primitive)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.primitives setup codec query).run before)) :
    before.2 ≤ result.2.2 := by
  simp only [PqxdhRecordLiftWorld.primitives, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact deployment_cache_grows setup codec query ((), before.2) inner.1
    (PqxdhRecordLiftFlat.support_run_fst _ _ _ inner reached)

/-- Every adaptive native primitive continuation retains the original shared cache. -/
theorem native_program_cache_grows {Result : Type} (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (program : OracleComp RawCtxMixedOwner.NativeSpec Result)
    (before : PqxdhRecordLiftWorld.Primitive) (result : Result × PqxdhRecordLiftWorld.Primitive)
    (supported : result ∈ support ((simulateQ (PqxdhRecordLiftWorld.primitives setup codec) program).run before)) :
    before.2 ≤ result.2.2 :=
  PqxdhRecordLiftFlat.support_keep_oracle (PqxdhRecordLiftWorld.primitives setup codec) (fun state => before.2 ≤ state.2)
    (fun query state prior output reached => prior.trans (native_cache_grows setup codec query state output reached))
    program before le_rfl result supported

/-- The actual frame logger preserves shared-cache witnesses even on writer refusal. -/
theorem record_cache_grows (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (query : RawCtxMixedOwner.NativeSpec.Domain)
    (before : PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames)
    (result : RawCtxMixedOwner.NativeSpec.Range query ×
      (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (supported : result ∈ support ((PqxdhRecordLiftProtocol.recordNative setup codec query).run before)) :
    before.1.2 ≤ result.2.1.2 := by
  simp only [PqxdhRecordLiftProtocol.recordNative, PqxdhRecordLiftLoggedAdapters.loggedNative,
    StateT.run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact native_program_cache_grows setup codec _ before.1 inner reached

/-- The actual frame logger leaves its buffer unchanged at a commitment hash callback. -/
theorem record_hash_run (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (bytes : Pqxdh.Bytes)
    (primitive : PqxdhRecordLiftWorld.Primitive) (frames : PqxdhRecordLiftLoggedAdapters.Frames) :
    (PqxdhRecordLiftProtocol.recordNative setup codec (.inr (.inr (.inr (.inl bytes))))).run (primitive, frames) =
      (fun reply => (reply.1, (reply.2, frames))) <$>
        (PqxdhRecordLiftWorld.primitives setup codec (.inr (.inr (.inr (.inl bytes))))).run primitive := by
  change PqxdhRecordLiftLoggedAdapters.swapResult <$> (simulateQ (PqxdhRecordLiftWorld.primitives setup codec)
    ((PqxdhDeploymentNative.frameLog (.inr (.inr (.inr (.inl bytes))))).run frames)).run primitive = _
  simp only [PqxdhDeploymentNative.frameLog, StateT.run_lift, bind_pure_comp, simulateQ_map,
    simulateQ_spec_query, StateT.run_map, Functor.map_map, PqxdhRecordLiftLoggedAdapters.swapResult]

/-- The frame logger forwards the actual commitment bytes and cache entry unchanged. -/
theorem record_hash_cached (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (bytes : Pqxdh.Bytes)
    (before : PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames)
    (result : Option Pqxdh.Bytes × (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (supported : result ∈ support ((PqxdhRecordLiftProtocol.recordNative setup codec
      (.inr (.inr (.inr (.inl bytes))))).run before)) :
    ∃ digest, result.1 = some digest.toList ∧ result.2.1.2 ((), bytes) = some digest := by
  rw [record_hash_run setup codec bytes before.1 before.2, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact native_hash_cached setup codec bytes before.1 inner reached

/-- The counted native writer returns exactly its functional codec result. -/
theorem native_writer_reply (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (frame : PqxdhDeploymentNative.Frame)
    (before : PqxdhRecordLiftWorld.Primitive) (result : Option Pqxdh.Bytes × PqxdhRecordLiftWorld.Primitive)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.primitives setup codec
      (.inr (.inr (.inr (.inr frame))))).run before)) : result.1 = codec.frameWrite frame := by
  simp only [PqxdhRecordLiftWorld.primitives, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  have source := PqxdhRecordLiftFlat.support_run_fst _ _ _ inner reached
  change inner.1 ∈ support (((RawCtxMixedShared.sharedImpl setup.source.crypto codec.frameWrite
    (RawCtxSourceHkdf.kdfImpl setup.source)) (.inr (.inr (.inr (.inr frame))))).run ((), before.2)) at source
  rw [RawCtxMixedShared.shared_writing, support_pure, Set.mem_singleton_iff] at source
  exact congrArg Prod.fst source

/-- The real writer log records the submitted frame and forwards only its actual codec reply. -/
theorem record_writer_reply (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (frame : PqxdhDeploymentNative.Frame)
    (before : PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames)
    (result : Option Pqxdh.Bytes × (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (supported : result ∈ support ((PqxdhRecordLiftProtocol.recordNative setup codec
      (.inr (.inr (.inr (.inr frame))))).run before)) : result.1 = codec.frameWrite frame := by
  rw [PqxdhRecordLiftProtocol.recordNative, PqxdhRecordLiftLoggedAdapters.logged_writer
    (PqxdhRecordLiftWorld.primitives setup codec) frame before.1 before.2, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact native_writer_reply setup codec frame before.1 inner reached

/-- A frame's commitment bytes are one digest already stored in the actual shared ROM. -/
def SharedCommit (frame : PqxdhDeploymentNative.Frame) (cache : CtxRO.QueryCache) : Prop :=
  ∃ (record : Pqxdh.RecordCipher) (digest : CtxDigest) (bytes : Pqxdh.Bytes), Pqxdh.decodeRecord frame.payload = some record ∧
    record.commit = digest.toList ∧ cache ((), bytes) = some digest

/-- Successful caller-known sealing returns a frame whose actual commitment remains in the shared ROM. -/
theorem source_send_cached (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (readBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (kernel : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext)
    (before : PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames)
    (result : (ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) ×
      (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (supported : result ∈ support ((simulateQ
      (PqxdhRecordLiftWorldCompiler.sendNative (PqxdhRecordLiftProtocol.recordNative setup codec))
      (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send kernel context))).run before))
    (message : RawCtxSourceSend.Encrypted) (accepted : result.1.2 = some message) :
    ∃ frame, codec.frameRead message.ciphertext = some frame ∧ SharedCommit frame result.2.1.2 := by
  obtain ⟨pending, response, afterKdf, entry, contextEq, inputEq, info, kdf, advanced,
    body, tag, afterAead, commitment, afterHash, messageEq, aead, width, tagWidth, hashed, written⟩ :=
    RawCtxSourceSeal.send_success_primitives
      (PqxdhRecordLiftProtocol.recordNative setup codec ∘ₛ RawCtxMixedOwner.sendLift)
      kernel context before result
      (by simpa only [PqxdhRecordLiftWorldCompiler.sendNative, RawCtxMixedOwner.sendAdapter,
        QueryImpl.simulateQ_compose] using supported) message accepted
  simp only [QueryImpl.apply_compose, RawCtxMixedOwner.sendLift, simulateQ_spec_query] at hashed written
  obtain ⟨digest, digestEq, cached⟩ := record_hash_cached setup codec _ afterAead (some commitment, afterHash) hashed
  refine ⟨_, (readBack _ _ (record_writer_reply setup codec _ afterHash
    (some message.ciphertext, result.2) written).symm).2, ?_⟩
  exact ⟨⟨body, tag, commitment⟩, digest, _,
    RawCtxSourceSeal.frame_record _ body tag commitment tagWidth
      (by simpa only [Option.some.inj digestEq] using ctxDigest_toList_length digest),
    Option.some.inj digestEq, record_cache_grows setup codec
      (.inr (.inr (.inr (.inr (RawCtxSourceSeal.frame
        (RawCtxSourceSend.arguments (RawCtxSourceSend.resumeSend pending response)) body tag commitment))))) afterHash
      (some message.ciphertext, result.2) written cached⟩

/-- The actual caller-known send service retains its source commitment in the final shared cache. -/
theorem known_send_cached (modes : PqxdhRecordLiftWorldCompiler.Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (readBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (kernel : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext) (before : CtxPrivate n)
    (result : (ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) × CtxPrivate n)
    (supported : result ∈ support ((ctxInterpreter modes replace setup codec (.knownSend kernel context)).run before))
    (message : RawCtxSourceSend.Encrypted) (accepted : result.1.2 = some message) :
    ∃ frame, codec.frameRead message.ciphertext = some frame ∧ SharedCommit frame result.2.base.primitive.2 := by
  simp only [ctxInterpreter, onBase, PqxdhRecordLiftProtocol.interpreter,
    PqxdhRecordLiftProtocol.withRecord, PqxdhRecordLiftProtocol.primitiveWork, StateT.run,
    bind_pure_comp, Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact source_send_cached setup codec readBack kernel context _ inner reached message accepted

/-- Successful caller-known receiving identifies the actual accepted frame commitment in the final shared ROM. -/
theorem source_receive_cached (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (kernel : ConcreteRatchetKernel) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (before : PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames)
    (result : (ConcreteRatchetKernel × core.option.Option RawCtxWholeOwner.Decrypted) ×
      (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (supported : result ∈ support ((simulateQ
      (PqxdhRecordLiftWorldCompiler.receiveNative (PqxdhRecordLiftProtocol.recordNative setup codec))
      (simulateQ RawCtxWholeOwner.adapter (RawCtxOwnerOracle.receive kernel target context))).run before))
    (message : RawCtxWholeOwner.Decrypted) (accepted : result.1.2 = .Some message) :
    SharedCommit context.frame result.2.1.2 := by
  obtain ⟨pending, input, plaintext, beforeOpen, arguments, material, sequence, contextEq, messageEq, opened⟩ :=
    RawCtxOwnerProvenance.receive_adapter_success
      (PqxdhRecordLiftWorldCompiler.receiveNative (PqxdhRecordLiftProtocol.recordNative setup codec))
      before kernel target context result
      (by simpa only [QueryImpl.simulateQ_compose] using supported) message accepted
  obtain ⟨slices, afterHash, parsed, width, hashed, aead⟩ :=
    RawCtxSourceOpen.openInput_success
      (PqxdhRecordLiftProtocol.recordNative setup codec ∘ₛ RawCtxMixedOwner.receiveLift ∘ₛ RawCtxSourceOpen.openLift)
      input beforeOpen result.2 plaintext
      (by simpa only [PqxdhRecordLiftWorldCompiler.receiveNative, RawCtxMixedOwner.receiveAdapter,
        QueryImpl.apply_compose, RawCtxSourceOpen.nativeAdapter, QueryImpl.simulateQ_compose] using opened)
  simp only [QueryImpl.apply_compose, RawCtxSourceOpen.openLift, RawCtxMixedOwner.receiveLift, simulateQ_spec_query] at hashed aead
  obtain ⟨digest, digestEq, cached⟩ := record_hash_cached setup codec _ beforeOpen (some slices.commitment, afterHash) hashed
  obtain ⟨record, decoded, body, tag, commitment, rest⟩ := RawCtxFrameDecoding.fromPayload_record _ slices parsed
  exact ⟨record, digest, _, by simpa only [contextEq] using decoded,
    commitment.symm.trans (Option.some.inj digestEq),
    record_cache_grows setup codec (.inr (.inr (.inl (RawCtxSourceOpen.baseInput input slices))))
      afterHash (some plaintext, result.2) aead cached⟩


/-- The actual caller-known receive service retains the accepted commitment in the final shared cache. -/
theorem known_receive_cached (modes : PqxdhRecordLiftWorldCompiler.Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (kernel : ConcreteRatchetKernel) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (before : CtxPrivate n)
    (result : (ConcreteRatchetKernel × core.option.Option RawCtxWholeOwner.Decrypted) × CtxPrivate n)
    (supported : result ∈ support ((ctxInterpreter modes replace setup codec (.knownReceive kernel target context)).run before))
    (message : RawCtxWholeOwner.Decrypted) (accepted : result.1.2 = .Some message) :
    SharedCommit context.frame result.2.base.primitive.2 := by
  simp only [ctxInterpreter, onBase, PqxdhRecordLiftProtocol.interpreter,
    PqxdhRecordLiftProtocol.withRecord, PqxdhRecordLiftProtocol.primitiveWork, StateT.run,
    bind_pure_comp, Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact source_receive_cached setup codec kernel target context _ inner reached message accepted

/-- Extending the actual shared cache preserves a frame's observed commitment witness. -/
theorem SharedCommit.grows (frame : PqxdhDeploymentNative.Frame) (before after : CtxRO.QueryCache)
    (grows : before ≤ after) (witness : SharedCommit frame before) : SharedCommit frame after := by
  obtain ⟨record, digest, bytes, decoded, commitment, cached⟩ := witness
  exact ⟨record, digest, bytes, decoded, commitment, grows cached⟩

/-- Every shared-hash callback preserves old answers, including intervening finite coins. -/
theorem hashImpl_grows (query : AdaptiveCtxSharedHash.HashSpec.Domain) (before : CtxRO.QueryCache)
    (result : AdaptiveCtxSharedHash.HashSpec.Range query × CtxRO.QueryCache)
    (supported : result ∈ support ((AdaptiveCtxSharedHash.hashImpl query).run before)) :
    before ≤ result.2 := by
  cases query with
  | inl coin =>
      change result ∈ support ((fun reply => (reply, before)) <$> (unifSpec.query coin : ProbComp _)) at supported
      rw [support_map] at supported
      obtain ⟨reply, reached, rfl⟩ := supported
      exact le_rfl
  | inr query => exact hash_grows query before result supported

/-- A complete adaptive shared-hash program retains every earlier cached digest. -/
theorem hash_program_grows {X : Type} (program : OracleComp AdaptiveCtxSharedHash.HashSpec X)
    (before : CtxRO.QueryCache) (result : X × CtxRO.QueryCache)
    (supported : result ∈ support ((simulateQ AdaptiveCtxSharedHash.hashImpl program).run before)) :
    before ≤ result.2 :=
  PqxdhRecordLiftFlat.support_keep_oracle AdaptiveCtxSharedHash.hashImpl (fun cache => before ≤ cache)
    (fun query state previous output reached => previous.trans (hashImpl_grows query state output reached))
    program before le_rfl result supported

/-- Every counted keyed CTX call retains shared-cache witnesses in every mode. -/
theorem keyed_cache_grows (modes : PqxdhRecordLiftWorldCompiler.Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto) (query : (KeyedSpec n).Domain)
    (before : CtxPrivate n) (result : (KeyedSpec n).Range query × CtxPrivate n)
    (supported : result ∈ support ((keyed modes decode crypto query).run before)) :
    before.base.primitive.2 ≤ result.2.base.primitive.2 := by
  simp only [keyed, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨sampled, reached, rfl⟩ := supported
  simp only [PqxdhRecordLiftProtocol.sampled, StateT.run, bind_pure_comp, support_map] at reached
  obtain ⟨counted, countedSupport, rfl⟩ := reached
  exact hash_program_grows _ before.base.primitive.2 counted.1
    (PqxdhRecordLiftFlat.support_run_fst PqxdhRecordLiftWorld.countCoin _ before.base.primitive.1.uniform counted countedSupport)

/-- Complete hidden opening and sealing continuations retain earlier shared-ROM observations. -/
theorem keyed_program_cache_grows {X : Type} (modes : PqxdhRecordLiftWorldCompiler.Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto) (program : OracleComp (KeyedSpec n) X)
    (before : CtxPrivate n) (result : X × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (keyed modes decode crypto) program).run before)) :
    before.base.primitive.2 ≤ result.2.base.primitive.2 :=
  PqxdhRecordLiftFlat.support_keep_oracle (keyed modes decode crypto)
    (fun state => before.base.primitive.2 ≤ state.base.primitive.2)
    (fun query state previous output reached => previous.trans (keyed_cache_grows modes decode crypto query state output reached))
    program before le_rfl result supported

/-- Every complete caller-known record program retains its previously observed commitment digests. -/
theorem record_program_cache_grows {X : Type} (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (program : OracleComp RawCtxMixedOwner.NativeSpec X)
    (before : PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames)
    (result : X × (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (supported : result ∈ support ((simulateQ (PqxdhRecordLiftProtocol.recordNative setup codec) program).run before)) :
    before.1.2 ≤ result.2.1.2 :=
  PqxdhRecordLiftFlat.support_keep_oracle (PqxdhRecordLiftProtocol.recordNative setup codec)
    (fun state => before.1.2 ≤ state.1.2)
    (fun query state previous output reached => previous.trans (record_cache_grows setup codec query state output reached))
    program before le_rfl result supported

/-- All actual private services retain the shared ROM, including rejected attempts and lookup work. -/
theorem service_cache_grows (modes : PqxdhRecordLiftWorldCompiler.Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : PqxdhRecordLiftProtocol.Service n) (before : CtxPrivate n)
    (result : (PqxdhRecordLiftProtocol.ServiceSpec n).Range query × CtxPrivate n)
    (supported : result ∈ support ((ctxInterpreter modes replace setup codec query).run before)) :
    before.base.primitive.2 ≤ result.2.base.primitive.2 := by
  cases query
  case opening pending => exact keyed_program_cache_grows modes _ _ _ before result supported
  case sealing pending =>
    simp only [ctxInterpreter, StateT.run, bind_pure_comp, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact keyed_program_cache_grows modes _ _ _ before inner reached
  case lookup coordinate =>
    rw [show ctxInterpreter modes replace setup codec (.lookup coordinate) =
      PqxdhRecordLiftCtxLink.ctxInterpreterWith PqxdhRecordLiftCtxLink.tableKey modes replace setup codec (.lookup coordinate) from rfl,
      PqxdhRecordLiftCtxAvailability.lookup_factor, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    cases found : before.base.chain coordinate with
    | some output =>
        rw [PqxdhRecordLiftChainOracle.lookup_hit _ _ _ _ _ rfl output found, support_pure,
          Set.mem_singleton_iff] at reached
        exact reached ▸ le_rfl
    | none =>
        rw [PqxdhRecordLiftChainOracle.lookup_miss _ _ _ _ _ rfl found, support_map] at reached
        obtain ⟨output, _, rfl⟩ := reached
        exact le_rfl
  case knownSend kernel context =>
    simp only [ctxInterpreter, onBase, PqxdhRecordLiftProtocol.interpreter,
      PqxdhRecordLiftProtocol.withRecord, PqxdhRecordLiftProtocol.primitiveWork, StateT.run,
      bind_pure_comp, Functor.map_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact record_program_cache_grows setup codec _ _ inner
      (by simpa only [PqxdhRecordLiftWorldCompiler.sendNative, RawCtxMixedOwner.sendAdapter,
        QueryImpl.simulateQ_compose, StateT.run] using reached)
  case knownReceive kernel target context =>
    simp only [ctxInterpreter, onBase, PqxdhRecordLiftProtocol.interpreter,
      PqxdhRecordLiftProtocol.withRecord, PqxdhRecordLiftProtocol.primitiveWork, StateT.run,
      bind_pure_comp, Functor.map_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact record_program_cache_grows setup codec _ _ inner
      (by simpa only [PqxdhRecordLiftWorldCompiler.receiveNative, RawCtxMixedOwner.receiveAdapter,
        QueryImpl.simulateQ_compose, StateT.run] using reached)
  case hash bytes =>
    simp only [ctxInterpreter, onBase, PqxdhRecordLiftProtocol.interpreter,
      PqxdhRecordLiftProtocol.sampled, StateT.run, bind_pure_comp, Functor.map_map,
      support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact hash_grows ((), bytes) before.base.primitive.2 inner.1
      (PqxdhRecordLiftFlat.support_run_fst PqxdhRecordLiftWorld.countCoin _ before.base.primitive.1.uniform inner reached)
  all_goals
    simp only [ctxInterpreter, onBase, PqxdhRecordLiftProtocol.interpreter,
      PqxdhRecordLiftProtocol.sampled, StateT.run, bind_pure_comp, Functor.map_map,
      support_map, map_pure, support_pure, Set.mem_singleton_iff] at supported
    first
    | exact supported ▸ le_rfl
    | obtain ⟨inner, reached, rfl⟩ := supported; exact le_rfl

/-- Arbitrary adaptive private-service continuations preserve shared-cache witnesses. -/
theorem program_cache_grows (modes : PqxdhRecordLiftWorldCompiler.Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (program : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) X) (before : CtxPrivate n)
    (result : X × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec) program).run before)) :
    before.base.primitive.2 ≤ result.2.base.primitive.2 :=
  PqxdhRecordLiftFlat.support_keep_oracle (ctxInterpreter modes replace setup codec)
    (fun state => before.base.primitive.2 ≤ state.base.primitive.2)
    (fun query state previous output reached => previous.trans (service_cache_grows modes replace setup codec query state output reached))
    program before le_rfl result supported

/-- Every actual native command preserves shared-cache evidence, including environment commands. -/
theorem native_query_cache_grows (modes : PqxdhRecordLiftWorldCompiler.Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : PqxdhRecordLiftInterface.Environment n E) (query : PqxdhDeploymentInterface.Spec.Domain)
    (before : PqxdhRecordLiftFlat.NativeState n E)
    (result : PqxdhDeploymentInterface.Spec.Range query × PqxdhRecordLiftFlat.NativeState n E)
    (supported : result ∈ support ((PqxdhRecordLiftFlat.nativeImpl modes replace setup codec route env query).run before)) :
    before.2.base.primitive.2 ≤ result.2.2.base.primitive.2 := by
  rw [PqxdhRecordLiftFlat.nativeImpl_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact program_cache_grows modes replace setup codec _ before.2 inner reached

/-- Arbitrary native scheduling retains all existing shared-ROM commitment witnesses. -/
theorem native_schedule_cache_grows (modes : PqxdhRecordLiftWorldCompiler.Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : PqxdhRecordLiftInterface.Environment n E) (program : OracleComp PqxdhDeploymentInterface.Spec X)
    (before : PqxdhRecordLiftFlat.NativeState n E) (result : X × PqxdhRecordLiftFlat.NativeState n E)
    (supported : result ∈ support ((simulateQ (PqxdhRecordLiftFlat.nativeImpl modes replace setup codec route env) program).run before)) :
    before.2.base.primitive.2 ≤ result.2.2.base.primitive.2 :=
  PqxdhRecordLiftFlat.support_keep_oracle (PqxdhRecordLiftFlat.nativeImpl modes replace setup codec route env)
    (fun state => before.2.base.primitive.2 ≤ state.2.base.primitive.2)
    (fun query state previous output reached => previous.trans (native_query_cache_grows modes replace setup codec route env query state output reached))
    program before le_rfl result supported

/-- Every full ledger command retains shared-ROM evidence through all forwarded native work. -/
theorem full_cache_grows (modes : PqxdhRecordLiftWorldCompiler.Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : PqxdhRecordLiftInterface.Environment n E) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (query : PqxdhDeploymentInterface.FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × PqxdhRecordLiftFlat.NativeState n E)
    (result : PqxdhDeploymentInterface.FullSpec.Range query ×
      (PqxdhDeploymentSecrecy.Ledger × PqxdhRecordLiftFlat.NativeState n E))
    (supported : result ∈ support ((PqxdhRecordLiftFlat.fullImpl modes replace setup codec route env serverKid bounds query).run before)) :
    before.2.2.base.primitive.2 ≤ result.2.2.2.base.primitive.2 := by
  rw [PqxdhRecordLiftFlat.fullImpl_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact native_schedule_cache_grows modes replace setup codec route env _ before.2 inner reached

/-- Adaptive raw receives, sends, reveals, tests and stopping preserve every earlier shared-cache commitment witness. -/
theorem full_program_cache_grows (modes : PqxdhRecordLiftWorldCompiler.Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : PqxdhRecordLiftInterface.Environment n E) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (program : OracleComp PqxdhDeploymentInterface.FullSpec X)
    (before : PqxdhDeploymentSecrecy.Ledger × PqxdhRecordLiftFlat.NativeState n E)
    (result : X × (PqxdhDeploymentSecrecy.Ledger × PqxdhRecordLiftFlat.NativeState n E))
    (supported : result ∈ support ((simulateQ
      (PqxdhRecordLiftFlat.fullImpl modes replace setup codec route env serverKid bounds) program).run before)) :
    before.2.2.base.primitive.2 ≤ result.2.2.2.base.primitive.2 :=
  PqxdhRecordLiftFlat.support_keep_oracle (PqxdhRecordLiftFlat.fullImpl modes replace setup codec route env serverKid bounds)
    (fun state => before.2.2.base.primitive.2 ≤ state.2.2.base.primitive.2)
    (fun query state previous output reached => previous.trans
      (full_cache_grows modes replace setup codec route env serverKid bounds query state output reached))
    program before le_rfl result supported

end BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.hash_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.hash_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.hash_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.hash_grows

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.native_hash_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.native_hash_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.deployment_cache_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.deployment_cache_grows

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.native_cache_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.native_cache_grows

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.native_program_cache_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.native_program_cache_grows

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.record_cache_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.record_cache_grows

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.record_hash_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.record_hash_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.record_hash_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.record_hash_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.native_writer_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.native_writer_reply

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.record_writer_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.record_writer_reply

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.source_send_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.source_send_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.known_send_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.known_send_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.source_receive_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.source_receive_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.known_receive_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.known_receive_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.SharedCommit.grows' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.SharedCommit.grows

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.hashImpl_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.hashImpl_grows

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.hash_program_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.hash_program_grows

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.keyed_cache_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.keyed_cache_grows

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.keyed_program_cache_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.keyed_program_cache_grows

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.record_program_cache_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.record_program_cache_grows

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.service_cache_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.service_cache_grows

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.program_cache_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.program_cache_grows

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.native_query_cache_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.native_query_cache_grows

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.native_schedule_cache_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.native_schedule_cache_grows

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.full_cache_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.full_cache_grows

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.full_program_cache_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence.full_program_cache_grows
