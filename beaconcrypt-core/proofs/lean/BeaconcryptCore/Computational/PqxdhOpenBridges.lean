import BeaconcryptCore.Computational.PqxdhHeadlineBridges

/-!
# Record-opening bridges for HB-111 and HB-112

The headline experiments HB-111 (`PqxdhAuthenticatedRootBudgets.authenticated_native_root_bound`) and HB-112 (`PqxdhAuthenticatedEvolvingSecrecy.bound`) open a protected record with hand-written Lean programs. In HB-111 the receive driver `RawCtxOwnerOracle.program` hands the source opening capability to the whole-owner adapter `RawCtxWholeOwner.adapter`, and HB-112's symbolic receive driver issues the same adapter callback on the native view of its capability; the adapter's opening query is expanded by `RawCtxSourceOpen.nativeAdapter` into `RawCtxSourceOpen.openInput` (payload split, commitment hash query, comparison, AEAD query) and embedded into the experiments' primitive interface by `RawCtxMixedOwner.receiveAdapter`. Production instead runs the extracted phases `record.begin_open`, `record.OpenCommitment.impl.transcript`, `record.OpenCommitment.transcript_mut`, `record.OpenCommitment.supplied_commitment`, `record.OpenCommitment.resume`, `record.OpenAead.request` and `record.OpenAead.finish`, composed by the adapter function `execute_open` in `beaconcrypt/src/ratchet.rs`, which is not extracted. This module adds new statements; it changes no existing theorem.

`executeOpen` is a hand-written Lean transcription of `execute_open`. It calls the extracted phase functions and the extracted `commitment.CommitmentTranscript.as_bytes` and `as_mut_bytes` in production order and threads their `RustM` results. The commitment hash and the AEAD opening are queries of the stand-in's own primitive interface `RawCtxSourceOpen.OpenSpec`: the hash query receives the bytes of the transcript returned by the extracted phases, the comparison is length-checked byte equality, which is what `libsodium_rs::utils::memcmp` computes (a length check followed by libsodium's `sodium_memcmp`, primitive law PL-11), and the AEAD query receives the key, nonce, associated data and combined ciphertext of the extracted `record.AeadRequest`. The transcript erasure writes an arbitrary array `erased` through the extracted mutable borrows (production writes zeros), and every statement holds for every such array. The composition, the two primitive queries, the comparison `compareDigest` and the erasure are hand-written Lean. No Lean statement relates `executeOpen` to the Rust `execute_open`: that it follows `execute_open`, including the phase order, the mapping of `crypto_generichash::generichash(…, None, COMMITMENT_SIZE).ok()` and `crypto_aead::chacha20poly1305_ietf::decrypt(…).ok()` onto the two `RawCtxSourceOpen.OpenSpec` queries and the conversion to `Decrypted`, is adapter-level trust checked only by review of `beaconcrypt/src/ratchet.rs`; the comparison also relies on primitive law PL-11, and its constant-time behaviour is not modelled. B12 relates this transcription to the experiments' opening step; it does not verify the Rust adapter.

B12 (`OpenBridge`) quantifies over every source opening capability whose payload and associated data are represented by a byte slice and a 153-byte array; its last conjunct shows that every payload of at most `Std.Usize.max` bytes and every 153-byte associated data is represented, the same width conditions as B6 and B8. The extracted payload admission `record.OpenFrameContext.from_frame` always returns normally. If it rejects, the payload has at most 80 bytes (so the experiments' frame validity check rejects it before any receive), and the experiments' opening step makes no hash or AEAD query and returns the entry kernel without plaintext. If it admits a frame context, the experiments' complete opening step, callback and kernel publication, equals `executeOpen` on the capability with the same ratchet entry and prepared receive and the admitted context, wrapped in `ok`, as programs over the experiments' hash and AEAD queries. The equality therefore holds for a capability without material and for every primitive reply, including hash failure, commitment mismatch, AEAD failure and success, and the extracted phases never fail or diverge there. A second equality states the same for the opening callback alone.

The headline restatements conjoin the statements of `PqxdhHeadlineBridges.authenticated_native_root_bound_bridged_full`, `PqxdhHeadlineBridges.authenticated_extracted_root_bound`, `PqxdhHeadlineBridges.evolving_bound_bridged_full` and `PqxdhHeadlineBridges.evolving_extracted_bound` with B12 at the same parameters and under the same hypotheses. B12 itself has no premises besides its representation conditions. The experiments still execute the hand-written opening programs; B12 states their equality with `executeOpen`, the hand-written Lean transcription of the unextracted `execute_open` that composes the extracted phases, not with the Rust function itself.

Not bridged here: `record.finish_frame_read`, whose only logic is the check that decoding consumed the whole input; that check is part of frame decoding, which is outside the proof: messages are arbitrary byte strings that each side knows how to decode, so the experiments keep the frame decoder as a free parameter. The opening capability carries the decoded frame and associated data (`RawCtxWholeOwner.OpenContext`) in the experiments and the admitted `record.OpenFrameContext` in production; B12 relates capabilities with equal ratchet entry and prepared receive. It does not prove that the extracted receive driver (`begin_receive` and `ReceiveKdf.resume`, which are generic in the context type and by inspection only move it) yields such a pair for the two context types, and it does not transcribe the unextracted adapter loop `decrypt_message_with_ratchet` (prechecks, kernel take and put, and the `ratchet_hkdf` interpretation of each KDF request) that produces production's capability. HB-112 publishes the kernel after the opening callback through the symbolic `RawCtxChainReceive.normalFinish`, which the existing `RawCtxChainRealization.receive_native` relates to the native driver `RawCtxOwnerOracle.receive`; for HB-112, the callback equality of B12 is the part that concerns the opening.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhOpenBridges
open PqxdhRefinement BeaconcryptCore.Refinement.RepresentationBridge
open RawCtxInterpretedOpening (bindResult)
open BeaconcryptCore.Refinement.ProtocolComposition (concreteByte absByte_concreteByte)

/-! ## Hand-written transcription of production's composition of the extracted opening phases -/

/-- The same opening capability (ratchet entry and prepared receive) with its context replaced; production's capability carries the admitted frame context where the experiments' capability carries the decoded frame. -/
def withContext {Context Other : Type} (pending : ReceiveOpen Context) (context : Other) :
    ReceiveOpen Other :=
  ⟨pending.entry, context, pending.prepared⟩

/-- The byte view of the extracted AEAD request, as a query of the stand-in's AEAD interface: key, nonce, associated data and the combined ciphertext (body and tag) that production passes to `chacha20poly1305_ietf::decrypt`. -/
def aeadQuery (request : record.AeadRequest) : RawCtxSourceOpen.BaseInput :=
  ⟨absBytes request.key, absBytes request.nonce, absBytes request.associated_data,
    RawCtxNativeFramePrelude.sliceBytes request.ciphertext⟩

/-- Hand-written transcription of production's conversion of the extracted opened record into the API result: plaintext, sender key identifier and sequence. -/
def decryptedOf (opened : record.OpenedRecord Pqxdh.Bytes) : RawCtxWholeOwner.Decrypted :=
  ⟨opened.plaintext, opened.key_id, opened.seq⟩

/-- Hand-written model of production's commitment comparison: a failed hash compares as false; otherwise the digest is compared with the supplied commitment returned by the extracted `record.OpenCommitment.supplied_commitment` by length-checked byte equality, which is what `libsodium_rs::utils::memcmp` computes (its length check, then primitive law PL-11); constant-time behaviour is not modelled. -/
def compareDigest (digest : Option Pqxdh.Bytes) (pending : record.OpenCommitment) : RustM Bool :=
  match digest with
  | none => ok false
  | some digest => do
      let supplied ← record.OpenCommitment.supplied_commitment pending
      ok (decide (digest = absBytes supplied))

/-- Hand-written Lean transcription of production's `execute_open` (`beaconcrypt/src/ratchet.rs`). It calls the extracted `record.begin_open`, `record.OpenCommitment.impl.transcript`, `commitment.CommitmentTranscript.as_bytes`, `record.OpenCommitment.transcript_mut`, `commitment.CommitmentTranscript.as_mut_bytes`, `record.OpenCommitment.supplied_commitment`, `record.OpenCommitment.resume`, `record.OpenAead.request` and `record.OpenAead.finish` in production order; the commitment hash and the AEAD opening are queries of `RawCtxSourceOpen.OpenSpec`, and the transcript erasure writes `erased`. A `RustM` failure or divergence of an extracted phase is returned unchanged. -/
def executeOpen (erased : Std.Array Std.U8 229#usize) (opening : ReceiveOpen record.OpenFrameContext) :
    OracleComp RawCtxSourceOpen.OpenSpec
      (RustM (ConcreteRatchetKernel × core.option.Option RawCtxWholeOwner.Decrypted)) :=
  bindResult (record.begin_open opening) fun start =>
    match start with
    | .OpenRejected kernel => pure (ok (kernel, .None))
    | .OpenCommitmentRequested pending =>
      bindResult (record.OpenCommitment.impl.transcript pending) fun transcript =>
      bindResult (commitment.CommitmentTranscript.as_bytes transcript) fun bytes => do
        let digest ← RawCtxSourceOpen.OpenSpec.query (.inl (absBytes bytes))
        bindResult (record.OpenCommitment.transcript_mut pending) fun borrowed =>
        bindResult (commitment.CommitmentTranscript.as_mut_bytes borrowed.1) fun bytesBorrowed =>
        bindResult (compareDigest digest (borrowed.2 (bytesBorrowed.2 erased))) fun matched =>
        bindResult (record.OpenCommitment.resume (borrowed.2 (bytesBorrowed.2 erased)) matched) fun next =>
          match next with
          | .OpenCommitmentRejected kernel => pure (ok (kernel, .None))
          | .OpenAeadRequested opening =>
            bindResult (record.OpenAead.request opening) fun request => do
              let plaintext ← match request with
                | .None => pure core.option.Option.None
                | .Some request => RawCtxSourceOpen.OpenSpec.query (.inr (aeadQuery request))
              bindResult (record.OpenAead.finish opening plaintext) fun result =>
                pure (ok (result.1, RawCtxOwnerResult.mapReply decryptedOf result.2))

/-- The embedding of `RawCtxSourceOpen.OpenSpec` into the experiments' primitive interface used by `RawCtxMixedOwner.receiveAdapter`: hash queries go to its hash oracle and AEAD queries to its opening AEAD oracle. -/
def mixedOpen : QueryImpl RawCtxSourceOpen.OpenSpec (OracleComp RawCtxMixedOwner.NativeSpec) :=
  RawCtxMixedOwner.receiveLift ∘ₛ RawCtxSourceOpen.openLift

/-! ## The experiments' hand-written opening step -/

/-- The hand-written opening step of the experiments over `RawCtxSourceOpen.OpenSpec`: missing source material rejects without a query; otherwise `RawCtxSourceOpen.openInput` runs on the source arguments, its optional plaintext is wrapped by `RawCtxWholeOwner.decrypted`, and `RawCtxOwnerOracle.finish` publishes the kernel. -/
noncomputable def sourceOpen (pending : ReceiveOpen RawCtxWholeOwner.OpenContext) :
    OracleComp RawCtxSourceOpen.OpenSpec
      (ConcreteRatchetKernel × core.option.Option RawCtxWholeOwner.Decrypted) := do
  let reply ← match RawCtxWholeOwner.arguments pending with
    | none => pure .None
    | some input => RawCtxOwnerResult.mapReply (RawCtxWholeOwner.decrypted input) <$>
        RawCtxSourceOpen.openInput input
  pure (RawCtxOwnerOracle.finish pending reply)

/-- The experiments' opening step at the native primitive interface: the receive driver `RawCtxOwnerOracle.program` at an opening effect, interpreted by `RawCtxWholeOwner.adapter` and `RawCtxSourceOpen.nativeAdapter`. -/
noncomputable def standInOpen (pending : ReceiveOpen RawCtxWholeOwner.OpenContext) :
    OracleComp RawCtxSourceOpen.NativeSpec
      (ConcreteRatchetKernel × core.option.Option RawCtxWholeOwner.Decrypted) :=
  simulateQ (RawCtxSourceOpen.nativeAdapter ∘ₛ RawCtxWholeOwner.adapter)
    (RawCtxOwnerOracle.program (Plaintext := RawCtxWholeOwner.Decrypted) (.ReceiveOpenRequested pending))

/-- The experiments' opening step is the hand-written `sourceOpen` embedded into the native primitive interface. -/
theorem standInOpen_source (pending : ReceiveOpen RawCtxWholeOwner.OpenContext) :
    standInOpen pending = simulateQ RawCtxSourceOpen.openLift (sourceOpen pending) := by
  unfold standInOpen sourceOpen
  rw [RawCtxOwnerOracle.program.eq_2]
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, QueryImpl.apply_compose]
  cases h : RawCtxWholeOwner.arguments pending with
  | none => simp [RawCtxWholeOwner.adapter, h]
  | some input =>
    simp [RawCtxWholeOwner.adapter, h, RawCtxSourceOpen.nativeAdapter, simulateQ_map]

/-- The experiments' opening step publishes the kernel with `RawCtxOwnerOracle.finish` after the opening callback of the whole-owner adapter. -/
theorem standInOpen_callback (pending : ReceiveOpen RawCtxWholeOwner.OpenContext) :
    standInOpen pending = (fun reply => RawCtxOwnerOracle.finish pending reply) <$>
      simulateQ RawCtxSourceOpen.nativeAdapter (RawCtxWholeOwner.adapter (.inr pending)) := by
  unfold standInOpen
  rw [RawCtxOwnerOracle.program.eq_2]
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, QueryImpl.apply_compose, map_eq_bind_pure_comp]
  rfl

/-- If the hand-written payload splitter rejects the payload, the hand-written opening step makes no query and returns the entry kernel without plaintext. -/
theorem sourceOpen_rejected (pending : ReceiveOpen RawCtxWholeOwner.OpenContext)
    (hslices : RawCtxFrameDecoding.fromPayload pending.context.frame.payload = none) :
    sourceOpen pending = pure (pending.entry, .None) := by
  cases h : RawCtxWholeOwner.arguments pending with
  | none => simp only [sourceOpen, h, pure_bind, RawCtxOwnerOracle.finish_none]
  | some input =>
    have hcontext := (RawCtxWholeOwner.arguments_some pending input h).2.2
    simp only [sourceOpen, h, RawCtxSourceOpen.openInput, hcontext, hslices, map_pure, pure_bind,
      RawCtxOwnerResult.mapReply, RawCtxOwnerOracle.finish_none]

/-- The opening step of the experiments at their primitive interface, as composed by `RawCtxMixedOwner.receiveAdapter`, is `standInOpen` embedded by `RawCtxMixedOwner.receiveLift`. -/
theorem mixed_step (pending : ReceiveOpen RawCtxWholeOwner.OpenContext) :
    simulateQ (RawCtxMixedOwner.receiveAdapter ∘ₛ RawCtxWholeOwner.adapter)
        (RawCtxOwnerOracle.program (Plaintext := RawCtxWholeOwner.Decrypted) (.ReceiveOpenRequested pending)) =
      simulateQ RawCtxMixedOwner.receiveLift (standInOpen pending) := by
  simp only [standInOpen, RawCtxMixedOwner.receiveAdapter, QueryImpl.simulateQ_compose]

/-- The opening callback at the experiments' primitive interface is the native callback embedded by `RawCtxMixedOwner.receiveLift`. -/
theorem mixed_callback (pending : ReceiveOpen RawCtxWholeOwner.OpenContext) :
    simulateQ RawCtxMixedOwner.receiveAdapter (RawCtxWholeOwner.adapter (.inr pending)) =
      simulateQ RawCtxMixedOwner.receiveLift
        (simulateQ RawCtxSourceOpen.nativeAdapter (RawCtxWholeOwner.adapter (.inr pending))) := by
  simp only [RawCtxMixedOwner.receiveAdapter, QueryImpl.simulateQ_compose]

/-! ## B12: the extracted opening phases equal the experiments' opening step -/

/-- Binding a normal `RustM` result continues with its value. -/
theorem bindResult_ok {m : Type → Type} [Pure m] {Input Output : Type} (value : Input)
    (next : Input → m (RustM Output)) : bindResult (ok value) next = next value := rfl

/-- The extracted material getter does not read the context. -/
theorem material_withContext {Context Other : Type} (pending : ReceiveOpen Context) (context : Other) :
    ReceiveOpen.material (withContext pending context) = ReceiveOpen.material pending := rfl

/-- The extracted sequence getter does not read the context. -/
theorem sequence_withContext {Context Other : Type} (pending : ReceiveOpen Context) (context : Other) :
    ReceiveOpen.sequence (withContext pending context) = ReceiveOpen.sequence pending := rfl

/-- Replacing the context installs exactly the given context. -/
@[simp]
theorem context_withContext {Context Other : Type} (pending : ReceiveOpen Context) (context : Other) :
    (withContext pending context).context = context := rfl

/-- Replacing the context keeps the ratchet entry kernel. -/
@[simp]
theorem entry_withContext {Context Other : Type} (pending : ReceiveOpen Context) (context : Other) :
    (withContext pending context).entry = pending.entry := rfl

/-- The extracted finish publishes the same kernel for any context and any successful plaintext value; only the returned plaintext differs. -/
theorem finish_withContext {Context Other A B : Type} (pending : ReceiveOpen Context) (context : Other)
    (x : A) (y : B) :
    ReceiveOpen.finish (withContext pending context) (.Some x) =
      (fun result => (result.1, core.option.Option.Some x)) <$> ReceiveOpen.finish pending (.Some y) := by
  rcases pending with ⟨entry, context', prepared⟩
  cases prepared with
  | PreparedReceiveCachedCase p =>
    simp only [withContext, ReceiveOpen.finish]
    generalize ratchet.refined.publish_cached_receive entry.refined p = r
    cases r <;> rfl
  | PreparedReceiveFutureCase p =>
    simp only [withContext, ReceiveOpen.finish]
    generalize ratchet.refined.publish_future_receive entry.refined p = r
    cases r <;> rfl

/-- Core bridge: whenever the extracted payload admission admits a frame context from a slice and array representing the capability's payload and associated data, the transcription of `execute_open` on the capability with that context equals the hand-written opening step `sourceOpen`, wrapped in `ok`, as programs over the same hash and AEAD queries. -/
theorem executeOpen_source (erased : Std.Array Std.U8 229#usize)
    (pending : ReceiveOpen RawCtxWholeOwner.OpenContext)
    (payload : Slice Std.U8) (ad : Std.Array Std.U8 153#usize) (context : record.OpenFrameContext)
    (hpayload : RawCtxNativeFramePrelude.sliceBytes payload = pending.context.frame.payload)
    (had : absBytes ad = pending.context.associatedData)
    (hframe : record.OpenFrameContext.from_frame payload ad pending.context.frame.sender =
      ok (.Some context)) :
    executeOpen erased (withContext pending context) = (fun result => ok result) <$> sourceOpen pending := by
  obtain ⟨result, execution, fields⟩ :=
    BeaconcryptCore.Refinement.NativeRecordWrapper.payload_views payload ad pending.context.frame.sender
  rw [hframe] at execution
  cases execution
  obtain ⟨_, _, _, _, hctxAd, hctxSender⟩ := fields
  have hslices : RawCtxFrameDecoding.fromPayload pending.context.frame.payload =
      some (RawCtxNativeFramePrelude.contextSlices context) := by
    have exact := RawCtxNativeFramePrelude.payload_exact payload ad pending.context.frame.sender
    rw [hframe, hpayload] at exact
    exact (RustM.ok.inj exact).symm
  have hadLength : pending.context.associatedData.length = 153 := by
    rw [← had]; simp [absBytes_length]
  have hsequence := pending.sequence_total.choose_spec
  cases hm : pending.material_total.choose with
  | none =>
    have hmaterial : pending.material = ok .None := by
      have spec := pending.material_total.choose_spec
      rw [hm] at spec; exact spec
    have hargs : RawCtxWholeOwner.arguments pending = none := RawCtxWholeOwner.arguments_none pending hmaterial
    have hbegin := BeaconcryptCore.Refinement.NativeRecordWrapper.begin_missing (withContext pending context)
      (by rw [material_withContext]; exact hmaterial)
    simp only [executeOpen, sourceOpen, hbegin, bindResult_ok, hargs, pure_bind, map_pure,
      RawCtxOwnerOracle.finish_none]
    rfl
  | some material =>
    have hmaterial : pending.material = ok (.Some material) := by
      have spec := pending.material_total.choose_spec
      rw [hm] at spec; exact spec
    have hargs : RawCtxWholeOwner.arguments pending =
        some ⟨material, pending.sequence_total.choose, pending.context⟩ := by
      simp only [RawCtxWholeOwner.arguments, hm]
    generalize pending.sequence_total.choose = sequence at hsequence hargs
    obtain ⟨transcript, htranscript, htabs⟩ := build_commitment_transcript_abs material.key.bytes
      material.nonce.bytes context.associated_data context.tag sequence context.sender_kid
    have hbegin : record.begin_open (withContext pending context) =
        ok (.OpenCommitmentRequested ⟨withContext pending context, transcript⟩) := by
      rw [record.begin_open, material_withContext, hmaterial]
      simp only [bind_tc_ok, sequence_withContext, hsequence, ReceiveOpen.impl.context, context_withContext,
        RatchetMaterial.impl.key, RatchetMaterial.impl.nonce, RatchetKey.as_bytes, RatchetNonce.as_bytes,
        htranscript]
    have hhash : absBytes transcript.bytes = RawCtxSourceOpen.hashInput ⟨material, sequence, pending.context⟩
        (RawCtxNativeFramePrelude.contextSlices context) := by
      simp only [RawCtxSourceOpen.hashInput, absMaterial, RawCtxNativeFramePrelude.contextSlices, htabs, hctxAd,
        had, hctxSender]
    simp only [executeOpen, hbegin, bindResult_ok, record.OpenCommitment.impl.transcript,
      commitment.CommitmentTranscript.as_bytes, sourceOpen, hargs, RawCtxSourceOpen.openInput, hslices,
      hadLength, ite_true, RawCtxSourceOpen.openSlices, map_bind, bind_assoc, bind_map_left]
    rw [hhash]
    refine bind_congr fun digest => ?_
    simp only [record.OpenCommitment.transcript_mut, commitment.CommitmentTranscript.as_mut_bytes, bindResult_ok]
    cases digest with
    | none =>
      simp only [compareDigest, bindResult_ok, BeaconcryptCore.Refinement.NativeRecordWrapper.resume_exact,
        Bool.false_eq_true, ite_false, pure_bind, map_pure, RawCtxOwnerResult.mapReply,
        RawCtxOwnerOracle.finish_none, entry_withContext]
    | some digest =>
      simp only [compareDigest, record.OpenCommitment.supplied_commitment, ReceiveOpen.impl.context, bind_tc_ok,
        bindResult_ok, BeaconcryptCore.Refinement.NativeRecordWrapper.resume_exact, context_withContext]
      by_cases hd : digest = absBytes context.commitment
      · have hrequest := BeaconcryptCore.Refinement.NativeRecordWrapper.request_selected
          ⟨withContext pending context⟩ material (by rw [material_withContext]; exact hmaterial)
        have haead : aeadQuery ⟨material.key.bytes, material.nonce.bytes,
            (withContext pending context).context.base_ciphertext,
            (withContext pending context).context.associated_data⟩ =
            RawCtxSourceOpen.baseInput ⟨material, sequence, pending.context⟩
              (RawCtxNativeFramePrelude.contextSlices context) := by
          simp only [aeadQuery, RawCtxSourceOpen.baseInput, absMaterial, context_withContext, hctxAd, had,
            RawCtxNativeFramePrelude.contextSlices]
        have hd' : digest = (RawCtxNativeFramePrelude.contextSlices context).commitment := hd
        simp only [decide_eq_true hd, ite_true, hrequest, bindResult_ok, map_pure]
        simp only [hd', ite_true]
        rw [haead]
        refine bind_congr fun plaintext => ?_
        rw [BeaconcryptCore.Refinement.NativeRecordWrapper.finish_selected _ sequence
          (by rw [sequence_withContext]; exact hsequence)]
        cases plaintext with
        | none =>
          simp only [RawCtxOwnerResult.mapReply, RawCtxOwnerOracle.finish_none]
          rfl
        | some plaintext =>
          obtain ⟨kernel, hkernel⟩ := pending.finish_result_exact
            (core.option.Option.Some (RawCtxWholeOwner.decrypted ⟨material, sequence, pending.context⟩ plaintext))
          have hwith := finish_withContext pending context
            (⟨plaintext, context.sender_kid, sequence⟩ : record.OpenedRecord Pqxdh.Bytes)
            (RawCtxWholeOwner.decrypted ⟨material, sequence, pending.context⟩ plaintext)
          rw [hkernel] at hwith
          have hfinish := RawCtxOwnerOracle.finish_exact pending
            (core.option.Option.Some (RawCtxWholeOwner.decrypted ⟨material, sequence, pending.context⟩ plaintext))
          rw [hkernel] at hfinish
          rw [hctxSender, RawCtxMaterialInterpretation.rust_map_ok] at hwith
          simp only [RawCtxOwnerResult.mapReply, context_withContext, hctxSender, hwith, bindResult_ok,
            ← RustM.ok.inj hfinish]
          rfl
      · simp only [hd, decide_false, Bool.false_eq_true, ite_false, RawCtxNativeFramePrelude.contextSlices,
          pure_bind, map_pure, RawCtxOwnerResult.mapReply, RawCtxOwnerOracle.finish_none, entry_withContext]

/-- B12 (record opening): for every erasure value, every source opening capability and every slice and 153-byte array representing its payload and associated data, the extracted payload admission returns normally and either rejects a payload of at most 80 bytes while the experiments' opening step returns the entry kernel without any query, or admits a frame context for which the experiments' opening step (at the interface of `RawCtxMixedOwner.receiveAdapter`) and its opening callback equal the transcription `executeOpen` of production's composition of the extracted opening phases, wrapped in `ok`. Every payload of at most `Std.Usize.max` bytes and every 153-byte associated data is represented. -/
def OpenBridge : Prop :=
  (∀ (erased : Std.Array Std.U8 229#usize) (pending : ReceiveOpen RawCtxWholeOwner.OpenContext)
      (payload : Slice Std.U8) (ad : Std.Array Std.U8 153#usize),
    RawCtxNativeFramePrelude.sliceBytes payload = pending.context.frame.payload →
    absBytes ad = pending.context.associatedData →
    (record.OpenFrameContext.from_frame payload ad pending.context.frame.sender = ok .None ∧
      pending.context.frame.payload.length ≤ 80 ∧
      simulateQ (RawCtxMixedOwner.receiveAdapter ∘ₛ RawCtxWholeOwner.adapter)
        (RawCtxOwnerOracle.program (Plaintext := RawCtxWholeOwner.Decrypted) (.ReceiveOpenRequested pending)) =
        pure (pending.entry, .None)) ∨
    (∃ context, record.OpenFrameContext.from_frame payload ad pending.context.frame.sender = ok (.Some context) ∧
      simulateQ mixedOpen (executeOpen erased (withContext pending context)) =
        (fun result => ok result) <$> simulateQ (RawCtxMixedOwner.receiveAdapter ∘ₛ RawCtxWholeOwner.adapter)
          (RawCtxOwnerOracle.program (Plaintext := RawCtxWholeOwner.Decrypted) (.ReceiveOpenRequested pending)) ∧
      (fun result => (fun opened => opened.2) <$> result) <$>
          simulateQ mixedOpen (executeOpen erased (withContext pending context)) =
        (fun reply => ok reply) <$>
          simulateQ RawCtxMixedOwner.receiveAdapter (RawCtxWholeOwner.adapter (.inr pending)))) ∧
  (∀ context : RawCtxWholeOwner.OpenContext, context.frame.payload.length ≤ Std.Usize.max →
    context.associatedData.length = 153 →
    ∃ (payload : Slice Std.U8) (ad : Std.Array Std.U8 153#usize),
      RawCtxNativeFramePrelude.sliceBytes payload = context.frame.payload ∧ absBytes ad = context.associatedData)

/-- B12 holds. -/
theorem open_bridge : OpenBridge := by
  refine ⟨fun erased pending payload ad hpayload had => ?_, fun context hpayload had => ?_⟩
  · obtain ⟨result, execution, fields⟩ :=
      BeaconcryptCore.Refinement.NativeRecordWrapper.payload_views payload ad pending.context.frame.sender
    have split := RawCtxNativeFramePrelude.payload_exact payload ad pending.context.frame.sender
    rw [execution, hpayload] at split
    cases result with
    | none =>
      have hslices : RawCtxFrameDecoding.fromPayload pending.context.frame.payload = none :=
        (RustM.ok.inj split).symm
      refine Or.inl ⟨execution, ?_, ?_⟩
      · rw [← hpayload]
        simpa [RawCtxNativeFramePrelude.sliceBytes] using fields
      · rw [mixed_step, standInOpen_source, sourceOpen_rejected pending hslices]
        simp
    | some context =>
      have step := executeOpen_source erased pending payload ad context hpayload had execution
      have full : simulateQ mixedOpen (executeOpen erased (withContext pending context)) =
          (fun result => ok result) <$> simulateQ (RawCtxMixedOwner.receiveAdapter ∘ₛ RawCtxWholeOwner.adapter)
            (RawCtxOwnerOracle.program (Plaintext := RawCtxWholeOwner.Decrypted) (.ReceiveOpenRequested pending)) := by
        rw [mixed_step, standInOpen_source, mixedOpen, QueryImpl.simulateQ_compose, step, simulateQ_map,
          simulateQ_map]
      refine Or.inr ⟨context, execution, full, ?_⟩
      rw [full, mixed_step, standInOpen_callback, mixed_callback, simulateQ_map, Functor.map_map, Functor.map_map]
      rfl
  · obtain ⟨array, harray⟩ := PqxdhHeadlineBridges.array_of_bytes 153#usize context.associatedData (by simpa using had)
    exact ⟨⟨context.frame.payload.map concreteByte, by simpa using hpayload⟩, array, by
      simp [RawCtxNativeFramePrelude.sliceBytes, List.map_map, Function.comp_def, absByte_concreteByte], harray⟩

/-! ## Headline statements with the record-opening bridge -/

section Headlines
open PqxdhHeadlineBridges
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhPhase2GeneratedDriver PqxdhAuthenticatedRootExperiment PqxdhPrivateAcceptedRoot
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhChallengeSecretRouting PqxdhJointKdfGame
open PqxdhChallengeSecretQueryBounds PqxdhAuthenticatedRootPrepareBounds
open PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid PqxdhSecretInputKdf
open ENNReal
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post)

/-- HB-111 with bridges B1-B10 and B12 in the statement: the statement of `PqxdhHeadlineBridges.authenticated_native_root_bound_bridged_full` (HB-111's bound and reached Server representation, bridges B1-B10, same hypotheses) together with the record-opening bridge B12, which relates the experiments' opening step to `executeOpen`, a hand-written Lean transcription of the unextracted adapter function `execute_open` that calls the extracted opening phases. -/
theorem authenticated_native_root_bound_bridged_open
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (sourceCorrect : SourceRootCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (secretIdentity : M → Pqxdh.Bytes)
    (initialMatch : PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity
      env.senderId env.index env.server env.initial) :
    let p := protocol env kem attachedVerify primitives program post
    ((actual env baseImpl kem attachedVerify primitives program post).boolDistAdvantage
      (uniformGame (rootReduction env.source baseImpl kem p)) ≤
      (PqxdhJointIdentity.advantage primitives
        (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup
          (driver env.toDriverEnvironment program) fallback ordinaryFallback)).toReal +
      Pr[= true | simulateQ (kemAmbientImpl baseImpl) (PqxdhKemCorrectnessError.errorExperiment kem)].toReal +
      kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (PqxdhChallengeSecretRouting.reduction env.source kem p).toINDCCA +
      PqxdhCorrelatedExtractFamily.advantage hmac
        (PqxdhCorrelatedExtractFamily.reduction env.source hmac baseImpl kem p) +
      ∑ index ∈ Finset.range c.qRoot,
        (hmacPrfRealGame hmac (indexedReduction hmac (rootReduction env.source baseImpl kem p) index)).boolDistAdvantage
          (hmacPrfRandomGame (indexedReduction hmac (rootReduction env.source baseImpl kem p) index))) ∧
    (∀ result ∈ support (PqxdhPrivateSourceCoins.privateRun attachedVerify primitives 1
      (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup (driver env.toDriverEnvironment program))),
      ∃ output, result.1.map PqxdhPrivateRootSource.eraseOutput = some output ∧
        PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity env.senderId env.index
          env.server output.context.selection.2) ∧
    PrepareBridge ∧ CommitBridge ∧ BeaconStartBridge ∧ BeaconCommitBridge ∧ RegistrationIdBridge ∧
    CommitmentTranscriptBridge ∧ SendFinishBridge ∧ FramePayloadBridge ∧
    AcceptBridge env baseImpl kem attachedVerify primitives program post secretIdentity ∧
    ValidateInitBridge ∧
    OpenBridge := by
  intro p
  obtain ⟨bound, reached, prepare, commit, start, established, rid, transcript, send, frame, accept, validate⟩ :=
    authenticated_native_root_bound_bridged_full env baseImpl kem attachedVerify primitives program post c
      compatible adapter functional hmac sourceCorrect fallback ordinaryFallback secretIdentity initialMatch
  exact ⟨bound, reached, prepare, commit, start, established, rid, transcript, send, frame, accept, validate,
    open_bridge⟩

/-- HB-111 for the experiment that executes the extracted acceptance on its accepted branch: the statement of `PqxdhHeadlineBridges.authenticated_extracted_root_bound` (same hypotheses) together with the record-opening bridge B12. The experiment still runs the hand-written opening programs; B12 relates them to `executeOpen`, a hand-written Lean transcription of the unextracted adapter function `execute_open` that calls the extracted opening phases. -/
theorem authenticated_extracted_root_bound_open
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (sourceCorrect : SourceRootCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (secretIdentity : M → Pqxdh.Bytes)
    (initialMatch : PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity
      env.senderId env.index env.server env.initial) :
    let p := protocol env kem attachedVerify primitives program post
    ((extractedActual env baseImpl kem attachedVerify primitives program post secretIdentity).boolDistAdvantage
      (uniformGame (rootReduction env.source baseImpl kem p)) ≤
      (PqxdhJointIdentity.advantage primitives
        (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup
          (driver env.toDriverEnvironment program) fallback ordinaryFallback)).toReal +
      Pr[= true | simulateQ (kemAmbientImpl baseImpl) (PqxdhKemCorrectnessError.errorExperiment kem)].toReal +
      kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (PqxdhChallengeSecretRouting.reduction env.source kem p).toINDCCA +
      PqxdhCorrelatedExtractFamily.advantage hmac
        (PqxdhCorrelatedExtractFamily.reduction env.source hmac baseImpl kem p) +
      ∑ index ∈ Finset.range c.qRoot,
        (hmacPrfRealGame hmac (indexedReduction hmac (rootReduction env.source baseImpl kem p) index)).boolDistAdvantage
          (hmacPrfRandomGame (indexedReduction hmac (rootReduction env.source baseImpl kem p) index))) ∧
    (∀ result ∈ support (PqxdhPrivateSourceCoins.privateRun attachedVerify primitives 1
      (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup (driver env.toDriverEnvironment program))),
      ∃ output, result.1.map PqxdhPrivateRootSource.eraseOutput = some output ∧
        PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity env.senderId env.index
          env.server output.context.selection.2) ∧
    PrepareBridge ∧ CommitBridge ∧ BeaconStartBridge ∧ BeaconCommitBridge ∧ RegistrationIdBridge ∧
    CommitmentTranscriptBridge ∧ SendFinishBridge ∧ FramePayloadBridge ∧ ValidateInitBridge ∧
    OpenBridge := by
  intro p
  obtain ⟨bound, reached, prepare, commit, start, established, rid, transcript, send, frame, validate⟩ :=
    authenticated_extracted_root_bound env baseImpl kem attachedVerify primitives program post c
      compatible adapter functional hmac sourceCorrect fallback ordinaryFallback secretIdentity initialMatch
  exact ⟨bound, reached, prepare, commit, start, established, rid, transcript, send, frame, validate,
    open_bridge⟩

variable (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64)
    (ancestors disclosed : List RatchetChain)

/-- HB-112 with bridges B1-B8, B10, B11 and B12 in the statement: the statement of `PqxdhHeadlineBridges.evolving_bound_bridged_full` (HB-112's bound, bridges B1-B8, B10 and B11, same hypotheses including HB-111's representation premises for B11) together with the record-opening bridge B12, which relates the experiments' opening step to `executeOpen`, a hand-written Lean transcription of the unextracted adapter function `execute_open` that calls the extracted opening phases. For HB-112 only B12's callback equality concerns the opening; the kernel publication after the callback stays the symbolic `RawCtxChainReceive.normalFinish`. -/
theorem evolving_bound_bridged_open (positive : 0 < number.val)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (correct : PqxdhFullSecretInputKdf.SourceFullCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (secretIdentity : M → Pqxdh.Bytes)
    (initialMatch : PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity
      env.senderId env.index env.server env.initial) :
    (PqxdhInitialRootEventSecrecy.actual env baseImpl kem attachedVerify primitives program post selected number
        ancestors disclosed).boolDistAdvantage
      (PqxdhAuthenticatedEvolvingSecrecy.ideal env baseImpl kem attachedVerify primitives program post selected
        number ancestors disclosed) ≤
      PqxdhAuthenticatedEvolvingSecrecy.loss env baseImpl kem attachedVerify primitives program post selected
        number ancestors disclosed c hmac fallback ordinaryFallback ∧
    PrepareBridge ∧ CommitBridge ∧ BeaconStartBridge ∧ BeaconCommitBridge ∧ RegistrationIdBridge ∧
    CommitmentTranscriptBridge ∧ SendFinishBridge ∧ FramePayloadBridge ∧ ValidateInitBridge ∧
    EvolvingAcceptBridge env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed
      secretIdentity ∧
    OpenBridge := by
  obtain ⟨bound, prepare, commit, start, established, rid, transcript, send, frame, validate, accept⟩ :=
    evolving_bound_bridged_full env baseImpl kem attachedVerify primitives program post c selected number
      ancestors disclosed positive compatible adapter functional hmac correct fallback ordinaryFallback
      secretIdentity initialMatch
  exact ⟨bound, prepare, commit, start, established, rid, transcript, send, frame, validate, accept, open_bridge⟩

/-- HB-112 for the experiment that executes the extracted acceptance on its accepted branch: the statement of `PqxdhHeadlineBridges.evolving_extracted_bound` (same hypotheses) together with the record-opening bridge B12. The experiment still runs the hand-written opening programs; B12 relates them to `executeOpen`, a hand-written Lean transcription of the unextracted adapter function `execute_open` that calls the extracted opening phases. For HB-112 only B12's callback equality concerns the opening; the kernel publication after the callback stays the symbolic `RawCtxChainReceive.normalFinish`. -/
theorem evolving_extracted_bound_open (positive : 0 < number.val)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (correct : PqxdhFullSecretInputKdf.SourceFullCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (secretIdentity : M → Pqxdh.Bytes)
    (initialMatch : PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity
      env.senderId env.index env.server env.initial) :
    (extractedEvolvingActual env baseImpl kem attachedVerify primitives program post selected number ancestors
        disclosed secretIdentity).boolDistAdvantage
      (PqxdhAuthenticatedEvolvingSecrecy.ideal env baseImpl kem attachedVerify primitives program post selected
        number ancestors disclosed) ≤
      PqxdhAuthenticatedEvolvingSecrecy.loss env baseImpl kem attachedVerify primitives program post selected
        number ancestors disclosed c hmac fallback ordinaryFallback ∧
    PrepareBridge ∧ CommitBridge ∧ BeaconStartBridge ∧ BeaconCommitBridge ∧ RegistrationIdBridge ∧
    CommitmentTranscriptBridge ∧ SendFinishBridge ∧ FramePayloadBridge ∧ ValidateInitBridge ∧
    OpenBridge := by
  obtain ⟨bound, prepare, commit, start, established, rid, transcript, send, frame, validate⟩ :=
    evolving_extracted_bound env baseImpl kem attachedVerify primitives program post c selected number
      ancestors disclosed positive compatible adapter functional hmac correct fallback ordinaryFallback
      secretIdentity initialMatch
  exact ⟨bound, prepare, commit, start, established, rid, transcript, send, frame, validate, open_bridge⟩

end Headlines

end BeaconcryptCore.Computational.PqxdhOpenBridges

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenBridges.standInOpen_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenBridges.standInOpen_source

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenBridges.standInOpen_callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenBridges.standInOpen_callback

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenBridges.sourceOpen_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenBridges.sourceOpen_rejected

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenBridges.mixed_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenBridges.mixed_step

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenBridges.mixed_callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenBridges.mixed_callback

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenBridges.bindResult_ok' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenBridges.bindResult_ok

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenBridges.material_withContext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenBridges.material_withContext

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenBridges.sequence_withContext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenBridges.sequence_withContext

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenBridges.context_withContext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenBridges.context_withContext

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenBridges.entry_withContext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenBridges.entry_withContext

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenBridges.finish_withContext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenBridges.finish_withContext

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenBridges.executeOpen_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenBridges.executeOpen_source

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenBridges.open_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenBridges.open_bridge

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenBridges.authenticated_native_root_bound_bridged_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenBridges.authenticated_native_root_bound_bridged_open

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenBridges.authenticated_extracted_root_bound_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenBridges.authenticated_extracted_root_bound_open

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenBridges.evolving_bound_bridged_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenBridges.evolving_bound_bridged_open

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenBridges.evolving_extracted_bound_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenBridges.evolving_extracted_bound_open
