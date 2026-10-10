-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish
import BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels
import BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap
import BeaconcryptCore.Computational.PqxdhPhase2InputBytes

/-!
# CE-12 D-ct: the witness steps on the split game

The final split game of a target (`PqxdhDeploymentBackend.gameWith … splitInit (PqxdhDeploymentIdealDefer.idealSplit t p)`) keeps one extended state: the R1 table `r1` (the shared Extract table of the native state), the BLAKE2b cache `ctxCache`, and the lazily drawn slot material of the backend (`slotKey`: the key part of slot 0's material). `CommitAt codec cache bytes key`: the frame that the public Phase 2 reading of `bytes` gives carries a commitment digest that the cache holds at an input whose first 32 bytes are `key` (`commitAt_mono`: it survives cache growth).

- `finish_root` (design-v2 section 8's case split, stated on `finishStepC`'s actual guard, design amendment A3): every successful finish of the split handler on an input that is not `ChallengeRead` leaves an R1 entry `v` and its input committed under `seqKey setup v`. `finishStepC_root` is the slot-program form: the real branch (the guard fails; this includes `c = k*` active but not `InitSent`) is the native schedule's finish (`realRegAt_support`, `onNative_native`, `scheduleFinish_keyed`); the hidden branch (owner k active in `InitSent`) is owner k's challenge finish, whose challenge marker is excluded (`finishChallenge_keyed`). `slotRunX_support` runs a slot step through the allocator and `beaconInstall_keeps` shows that the hidden Beacon install changes only an owner's kernel.
- The marked build's seal (Rust `server.rs`, `build_registration_response`: the sequence-one record is sealed under the initial ratchet's first message key and its commitment `BLAKE2b-512(K ‖ N ‖ AD ‖ T ‖ LE64(seq) ‖ LE64(kid))` is put in the frame). `tailSeal_keyed`: a seal of the Server's logging tail writes a codec frame whose commitment the final cache holds at an input keyed by the seal's material key (`sealHash_take`). `firstSend_keyed`: the first labelled send on the hidden initial kernel (`PqxdhDeploymentHiddenKernels.initial_send_requested`) seals with the material of the decoded challenge response. `afterInit_keyed`, `candidate_keyed`, `genericBuild_keyed`, `hiddenBuild_keyed` and `buildHidden_keyed` lift it through the generic Server build (as `PqxdhDeploymentIdealBeaconFacts.genericBuild_written` does for the written fields) to the marked build of the native state with the erased hidden services: a published response is the Phase 2 writing of fields whose application ciphertext is that frame. `join_key`: the material key of a joined output's ratchet response is the material's key part. `written_frame`: under `Phase2ReadBack` and `FrameReadBack`, the public reading of such a response is that frame.
- `markedBuild_commit`: a successful build of the marked session on the split state either found the allocator full with the marked coordinates holding no slot, or leaves the marked coordinates at a slot whose cached material `m` keys the commitment of the response's frame (`lazyRead`: the read through the allocator in front of the lazy service; `serverInstall_keeps`: the hidden Server install keeps the reply, both tables and the slots). `buildStepC_pending` (with `realBuild_pending`, `nativeBuild_pending`): a successful build answers only from a pending token of its session.
- The challenge-marker exclusion (design amendment A1): `ciphertextOf_of_challengeRead` (the needed direction, from `ciphertext_roundtrip`) and `not_challengeRead`.

Support facts only; no assumption is used (`markedBuild_commit` and `written_frame` take the approved codec contracts `Phase2ReadBack` and `FrameReadBack` as premises).
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentBackend (XState)
open PqxdhDeploymentIdealSteps (SplitBk IdealCore)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhSecretInputKdf (HmacBlock HmacOracle)
open PqxdhDeploymentHeadlineDctReceive (KeyedCommit seqKey)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-! ### Views of the split state -/

/-- The shared R1 (Extract) table. -/
def r1 (x : XState KemSK SplitBk 2) : HmacOracle.QueryCache := x.base.native.shared.1.cache

/-- The key part of slot 0's cached material (`key32_0`). -/
def slotKey (x : XState KemSK SplitBk 2) : Option RawCtxKdfRequestTable.KeyPart := (x.backend.1 0).map Prod.fst

/-- The shared BLAKE2b cache. -/
def ctxCache (x : XState KemSK SplitBk 2) : CtxRomAuth.CtxRO.QueryCache := x.base.native.shared.2.ctx

/-- The frame of the public Phase 2 reading of `bytes` carries a commitment digest that the cache holds at an input whose first 32 bytes are `key`. -/
def CommitAt (codec : Codec Reader Response) (cache : CtxRomAuth.CtxRO.QueryCache) (bytes : Pqxdh.Bytes)
    (key : List UInt8) : Prop :=
  ∃ frame, PqxdhServerAuthRecordPublicationEvent.frame codec bytes = some frame ∧ KeyedCommit frame cache key

/-- A commitment survives the growth of the cache. -/
theorem commitAt_mono (codec : Codec Reader Response) (before after : CtxRomAuth.CtxRO.QueryCache) (bytes : Pqxdh.Bytes)
    (key : List UInt8) (held : CommitAt codec before bytes key)
    (grows : ∀ input digest, before input = some digest → after input = some digest) : CommitAt codec after bytes key := by
  obtain ⟨frame, framed, keyed⟩ := held
  exact ⟨frame, framed, PqxdhDeploymentHeadlineDctReceive.keyedCommit_mono frame before after key keyed grows⟩

/-! ### The finish -/

section Finish
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (route : RawCtxServerRouting.SenderDecoder) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- The hidden Beacon install keeps the native state's shared part and the reply. -/
theorem beaconInstall_keeps (owner : ℕ)
    (mid : (Option Pqxdh.Bytes × Option PqxdhDeploymentIdealSlots.Coord) × XState KemSK SplitBk 2)
    (installed : (Option Pqxdh.Bytes × Option PqxdhDeploymentIdealSlots.Coord) × XState KemSK SplitBk 2)
    (member : installed ∈ support (PqxdhDeploymentIdealDefer.beaconInstall owner mid)) :
    installed.1.1 = mid.1.1 ∧ installed.2.base.native.shared = mid.2.base.native.shared := by
  unfold PqxdhDeploymentIdealDefer.beaconInstall PqxdhDeploymentIdealDefer.xInstall at member
  split at member
  · rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, rfl⟩
  · split at member
    · rw [support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨rfl, rfl⟩
    · split at member
      · rw [support_map] at member
        obtain ⟨_, _, rfl⟩ := member
        exact ⟨rfl, rfl⟩
      · rw [support_pure, Set.mem_singleton_iff] at member
        subst member
        exact ⟨rfl, rfl⟩

/-- A slot step run by `slotRunX` against the allocator and a slot service answers as the slot step on the detached state, with the same deployment state. -/
theorem slotRunX_support {β : Type}
    (svc : PqxdhDeploymentSeedSplit.SlotService
      (PqxdhDeploymentIdealKernel.MatCache 2 × PqxdhDeploymentIdealKernel.SeedCache 2) 2)
    (step : StateT (XState KemSK IdealCore 2) (OracleComp PqxdhDeploymentIdealSlots.SlotSpec) β)
    (x : XState KemSK SplitBk 2) (result : β × XState KemSK SplitBk 2)
    (member : result ∈ support ((PqxdhDeploymentIdealKernel.slotRunX svc step).run x)) :
    ∃ inner, inner ∈ support (step.run (PqxdhDeploymentIdealKeys.detachX x)) ∧ result.1 = inner.1 ∧
      result.2.base = inner.2.base := by
  change result ∈ support ((fun r => (r.1, PqxdhDeploymentIdealKeys.attachX r.2.1 r.2.2.1 r.2.2.2)) <$>
    (PqxdhDeploymentIdealErase.onPair svc step).run
      (PqxdhDeploymentIdealKeys.detachX x, (x.backend.2.1, (x.backend.1, x.seeds)))) at member
  rw [support_map] at member
  obtain ⟨paired, pairedMember, rfl⟩ := member
  rw [PqxdhDeploymentIdealErase.onPair_run, support_map] at pairedMember
  obtain ⟨simulated, simulatedMember, rfl⟩ := pairedMember
  refine ⟨simulated.1, ?_, rfl, rfl⟩
  apply OracleComp.support_simulateQ_run'_subset (PqxdhRegistrationJointKemSecondEntry.slotImpl svc)
    (step.run (PqxdhDeploymentIdealKeys.detachX x)) (x.backend.2.1, (x.backend.1, x.seeds))
  rw [StateT.run'_eq, support_map]
  exact ⟨simulated, simulatedMember, rfl⟩

/-- The finish step of the split core (`finishStepC`), on the slot program's state: a successful finish on an input that is not `ChallengeRead` leaves an R1 entry `v` and the input committed under the sequence-one key of `v`. Real branch (the guard fails, including `c = k*` active but not `InitSent`): the native schedule's finish (`realRegAt_support`, `onNative_native`, `scheduleFinish_keyed`). Hidden branch: owner k's challenge finish (`finishChallenge_keyed`), whose challenge marker is excluded. -/
theorem finishStepC_root
    (hidden : PqxdhServerAuthKeySchedule.Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (owner : ℕ) (raw : Pqxdh.Bytes) (y : XState KemSK IdealCore 2)
    (result : (Option Pqxdh.Bytes × Option PqxdhDeploymentIdealSlots.Coord) × XState KemSK IdealCore 2)
    (member : result ∈ support ((PqxdhDeploymentIdealKernel.finishStepC setup codec checks route t p hidden created
      owner raw).run y))
    (reply : Pqxdh.Bytes) (replied : result.1.1 = some reply)
    (other : ¬ PqxdhDeploymentIdealBeacon.ChallengeRead codec p.challenge raw) :
    ∃ u v, result.2.base.native.shared.1.cache u = some v ∧
      CommitAt codec result.2.base.native.shared.2.ctx raw (seqKey setup v).toList := by
  change result ∈ support (PqxdhDeploymentIdealKernel.finishStepC setup codec checks route t p hidden created
    owner raw y) at member
  unfold PqxdhDeploymentIdealKernel.finishStepC at member
  split_ifs at member with guard
  · change result ∈ support ((fun r => ((r.1, r.2.2), PqxdhDeploymentIdealKernel.assembleF y owner r.2)) <$>
      (PqxdhDeploymentIdealSteps.finishChallenge setup codec hidden p.challenge owner raw).run
        (y.base.native, none)) at member
    rw [support_map] at member
    obtain ⟨r, rMember, rfl⟩ := member
    obtain ⟨u, v, frame, cached, framed, keyed⟩ := PqxdhDeploymentHeadlineDctFinish.finishChallenge_keyed setup codec
      hidden p.challenge owner raw y.base.native none r rMember reply replied other
    exact ⟨u, v, cached, frame, framed, keyed⟩
  · change result ∈ support ((fun r => ((r.1, none), r.2)) <$> OracleComp.liftComp
      ((PqxdhDeploymentIdealSteps.realRegAt setup codec route checks created ⟨.finish owner raw, trivial⟩).run y)
        PqxdhDeploymentIdealSlots.SlotSpec) at member
    rw [support_map, OracleComp.support_liftComp] at member
    obtain ⟨r, rMember, rfl⟩ := member
    obtain ⟨nativeMember, -⟩ := PqxdhDeploymentIdealKeymatch.realRegAt_support setup codec route checks created _ y r
      rMember
    have scheduleMember := PqxdhDeploymentIdealKeymatch.onNative_native
      (PqxdhRegistrationSchedule.finish setup codec owner raw) y.base r.1 r.2.base nativeMember
    obtain ⟨u, v, frame, cached, framed, keyed⟩ := PqxdhDeploymentHeadlineDctFinish.scheduleFinish_keyed setup codec
      owner raw y.base.native (r.1, r.2.base.native) scheduleMember reply replied
    exact ⟨u, v, cached, frame, framed, keyed⟩

/-- `finish_root`: a successful finish of the split handler on an input that is not `ChallengeRead` leaves an R1 entry `v` and its input committed under the sequence-one key of `v`. -/
theorem finish_root (owner : ℕ) (raw : Pqxdh.Bytes) (x : XState KemSK SplitBk 2)
    (result : Option Pqxdh.Bytes × XState KemSK SplitBk 2)
    (supported : result ∈ support ((PqxdhDeploymentBackend.handlerWith setup codec route
      (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created) (.inr (.finish owner raw))).run x))
    (reply : Pqxdh.Bytes) (replied : result.1 = some reply)
    (other : ¬ PqxdhDeploymentIdealBeacon.ChallengeRead codec p.challenge raw) :
    ∃ u v, r1 result.2 u = some v ∧ CommitAt codec (ctxCache result.2) raw (seqKey setup v).toList := by
  change result ∈ support ((fun r => (r.1.1, r.2)) <$> ((PqxdhDeploymentIdealKernel.slotRunX
    PqxdhDeploymentIdealKernel.lazyDummy (PqxdhDeploymentIdealKernel.finishStepC setup codec checks route t p
      (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks) created owner raw)).run x >>=
        PqxdhDeploymentIdealDefer.beaconInstall owner)) at supported
  rw [support_map] at supported
  obtain ⟨installed, installedMember, rfl⟩ := supported
  rw [mem_support_bind_iff] at installedMember
  obtain ⟨mid, midMember, installMember⟩ := installedMember
  obtain ⟨replyEq, sharedEq⟩ := beaconInstall_keeps owner mid installed installMember
  obtain ⟨inner, innerMember, innerReply, baseEq⟩ := slotRunX_support _ _ x mid midMember
  have innerReplied : inner.1.1 = some reply := by
    rw [← innerReply, ← replyEq]
    exact replied
  obtain ⟨u, v, cached, committed⟩ := finishStepC_root setup codec checks route t p created _ owner raw _ inner
    innerMember reply innerReplied other
  refine ⟨u, v, ?_, ?_⟩
  · simp only [r1, sharedEq, baseEq]
    exact cached
  · simp only [ctxCache, sharedEq, baseEq]
    exact committed

end Finish

/-! ### The marked build's seal -/

section Seal
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- The first 32 bytes of a seal's commitment input are the material key. -/
theorem sealHash_take (input : RawCtxSourceSend.SealInput) (tag : Pqxdh.Bytes) :
    (RawCtxSourceSeal.hashInput input tag).take 32 = PqxdhRefinement.absBytes input.material.key.bytes := by
  have length : (PqxdhRefinement.absBytes input.material.key.bytes).length = 32 := by
    simp [PqxdhRefinement.absBytes_length]
  simp only [RawCtxSourceSeal.hashInput, Pqxdh.ctxPreimage, BeaconcryptCore.Refinement.RepresentationBridge.absMaterial,
    List.append_assoc]
  rw [List.take_append_of_le_length (by rw [length]), List.take_of_length_le (by rw [length])]

/-- A successful seal of the Server's logging tail writes, with the codec's frame writer, a frame whose commitment the final cache holds at an input keyed by the seal's material key. -/
theorem tailSeal_keyed (input : RawCtxSourceSend.SealInput)
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (result : Option Pqxdh.Bytes × RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (supported : result ∈ support ((PqxdhServerAuthExperiment.tailImpl setup codec checks (.inl (.inr input))).run
      state))
    (ciphertext : Pqxdh.Bytes) (present : result.1 = some ciphertext) :
    ∃ frame, codec.frameWrite frame = some ciphertext ∧
      KeyedCommit frame result.2.2 (PqxdhRefinement.absBytes input.material.key.bytes) := by
  simp only [PqxdhServerAuthExperiment.tailImpl, PqxdhServerAuthExperiment.nativeTail, QueryImpl.apply_compose,
    PqxdhServerRegistrationPublication.nativeAdapter, RawCtxSourceSeal.nativeAdapter, StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨sealed, sealedRun, rest⟩ := supported
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose] at sealedRun
  change sealed ∈ support ((simulateQ (PqxdhServerAuthNegativeControl.sealHandler setup codec checks)
    (RawCtxSourceSeal.sealInput input)).run state) at sealedRun
  rcases sealed with ⟨_ | sealedBytes, afterSeal⟩
  · simp only [Option.isSome_none, Bool.false_eq_true, ite_false, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at rest
    rw [rest] at present
    cases present
  simp only [Option.isSome_some, ite_true, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
    support_pure, Set.mem_singleton_iff] at rest
  subst rest
  simp only [Option.some.injEq] at present
  subst present
  obtain ⟨body, tag, afterAead, commitment, afterHash, _, _, tagWidth, hashRun, frameRun⟩ :=
    RawCtxSourceSeal.sealInput_success (PqxdhServerAuthNegativeControl.sealHandler setup codec checks) input state
      afterSeal sealedBytes sealedRun
  rw [PqxdhServerAuthNegativeControl.sealHandler_hash, mem_support_bind_iff] at hashRun
  obtain ⟨answer, answerRun, hashEq⟩ := hashRun
  rw [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hashEq
  obtain ⟨rfl, rfl⟩ := hashEq
  rw [PqxdhServerAuthNegativeControl.sealHandler_frame, support_pure, Set.mem_singleton_iff, Prod.mk.injEq]
    at frameRun
  obtain ⟨frameEq, rfl⟩ := frameRun
  refine ⟨RawCtxSourceSeal.frame input body tag answer.1.toList, frameEq.symm, ⟨body, tag, answer.1.toList⟩,
    answer.1, RawCtxSourceSeal.hashInput input tag, RawCtxSourceSeal.frame_record input body tag _ tagWidth
      (CtxRomAuth.ctxDigest_toList_length answer.1), rfl, ?_, sealHash_take input tag⟩
  exact PqxdhRecordFactsBindingEvidence.hash_cached _ _ answer answerRun

/-- The first labelled Server send on the hidden initial kernel (`PqxdhDeploymentHiddenKernels.serverInitial`), with the logging tail: a produced record carries a frame written by the codec whose commitment the final cache holds keyed by the material key of the decoded challenge response. -/
theorem firstSend_keyed (challenge : beaconcrypt_core.ratchet.RatchetKdfResponse) (right : PqxdhSecretInputKdf.RootOutput)
    (receive : PqxdhServerAuthSendFactor.Kernel → Std.U64 → RawCtxWholeOwner.OpenContext →
      PqxdhServerAuthLoggedSendFactor.Logged (PqxdhServerAuthSendFactor.Kernel ×
        core.option.Option RawCtxWholeOwner.Decrypted))
    (context : RawCtxSourceSend.SealContext)
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (sent : (PqxdhServerAuthSendFactor.Kernel × Option RawCtxSourceSend.Encrypted) ×
      RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (supported : sent ∈ support (((PqxdhServerAuthLoggedSendFactor.calls receive
      (PqxdhServerAuthLoggedSendFactor.loggedPrim setup codec checks) setup.source challenge).send
        (PqxdhDeploymentHiddenKernels.serverInitial right) context).run state))
    (encrypted : RawCtxSourceSend.Encrypted) (present : sent.1.2 = some encrypted) :
    ∃ frame, codec.frameWrite frame = some encrypted.ciphertext ∧
      KeyedCommit frame sent.2.2
        (PqxdhRefinement.absBytes (RawCtxInterpretedReceive.decodeResponse challenge).2.key.bytes) := by
  obtain ⟨pending, begun, request⟩ := PqxdhDeploymentHiddenKernels.initial_send_requested right context
  simp only [PqxdhServerAuthLoggedSendFactor.calls, RawCtxChainSend.execute, begun, RawCtxChainSend.program,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure] at supported
  rw [request] at supported
  simp only [PqxdhServerAuthSendFactor.primLabels, pure_bind, QueryImpl.apply_compose, RawCtxSourceSend.adapter,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨_, ⟨sealed, sealRun, rfl⟩, rfl⟩ := supported
  cases produced : sealed.1 with
  | none =>
      simp only [produced, Option.map_none] at present
      cases present
  | some ciphertext =>
      simp only [produced, Option.map_some, Option.some.injEq] at present
      subst present
      exact tailSeal_keyed setup codec checks _ state sealed sealRun ciphertext produced

/-- The generic first send and Phase 2 writing on the hidden initial kernel, with the logging tail: a published response is the codec's Phase 2 writing of fields whose application ciphertext is a codec frame whose commitment the final cache holds keyed by the challenge's material key. -/
theorem afterInit_keyed {Metadata PeerMetadata Consumed : Type} (challenge : beaconcrypt_core.ratchet.RatchetKdfResponse)
    (right : PqxdhSecretInputKdf.RootOutput)
    (receive : PqxdhServerAuthSendFactor.Kernel → Std.U64 → RawCtxWholeOwner.OpenContext →
      PqxdhServerAuthLoggedSendFactor.Logged (PqxdhServerAuthSendFactor.Kernel ×
        core.option.Option RawCtxWholeOwner.Decrypted))
    (candidate : beaconcrypt_core.pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (metadata : PeerMetadata)
    (generic : PqxdhInitialGenericPublication.State PqxdhServerAuthSendFactor.Kernel Metadata PeerMetadata Consumed)
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (result : (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhInitialGenericPublication.State PqxdhServerAuthSendFactor.Kernel Metadata PeerMetadata Consumed) ×
        RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (supported : result ∈ support ((PqxdhInitialGenericPublication.afterInitialization
      (PqxdhServerAuthLoggedSendFactor.calls receive (PqxdhServerAuthLoggedSendFactor.loggedPrim setup codec checks)
        setup.source challenge) (PqxdhServerAuthLoggedSendFactor.loggedAux setup codec checks) candidate authenticated
      (PqxdhDeploymentHiddenKernels.serverInitial right) metadata generic).run state))
    (response : PqxdhServerRegistrationPublication.Response) (published : result.1.1 = some response) :
    ∃ fields frame, codec.write2 fields = some response.serialized ∧ codec.frameWrite frame = some fields.appCiphertext ∧
      KeyedCommit frame result.2.2
        (PqxdhRefinement.absBytes (RawCtxInterpretedReceive.decodeResponse challenge).2.key.bytes) := by
  unfold PqxdhInitialGenericPublication.afterInitialization at supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨sent, sendRun, rest⟩ := supported
  simp only [PqxdhServerAuthLoggedSendFactor.loggedAux] at rest
  obtain ⟨erased, erasedRun, rest⟩ := rest
  rw [PqxdhServerAuthNegativeControl.tailImpl_aux] at erasedRun
  simp only [PqxdhServerAuthExperiment.tailAux, StateT.run_pure, support_pure, Set.mem_singleton_iff] at erasedRun
  subst erasedRun
  rcases sent with ⟨⟨advanced, _ | encrypted⟩, afterSend⟩
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at rest
    subst rest
    cases published
  simp only [StateT.run_bind, mem_support_bind_iff] at rest
  obtain ⟨written, writtenRun, rest⟩ := rest
  rw [PqxdhServerAuthNegativeControl.tailImpl_aux] at writtenRun
  simp only [PqxdhServerAuthExperiment.tailAux, StateT.run_pure, support_pure, Set.mem_singleton_iff] at writtenRun
  subst writtenRun
  cases writeEq : codec.write2 (PqxdhServerRegistrationPublication.responseFields candidate encrypted) with
  | none =>
      simp only [writeEq, StateT.run_pure, support_pure, Set.mem_singleton_iff] at rest
      subst rest
      cases published
  | some serialized =>
      simp only [writeEq, StateT.run_pure, support_pure, Set.mem_singleton_iff] at rest
      subst rest
      simp only [Option.some.injEq] at published
      subst published
      obtain ⟨frame, framed, keyed⟩ := firstSend_keyed setup codec checks challenge right receive _ state _ sendRun
        encrypted rfl
      exact ⟨_, frame, writeEq, framed, keyed⟩

/-- The generic candidate admission and first send on the hidden initial kernel, with the logging tail: a published response is as in `afterInit_keyed`. -/
theorem candidate_keyed {Metadata PeerMetadata Consumed : Type}
    (challenge : beaconcrypt_core.ratchet.RatchetKdfResponse) (right : PqxdhSecretInputKdf.RootOutput)
    (receive : PqxdhServerAuthSendFactor.Kernel → Std.U64 → RawCtxWholeOwner.OpenContext →
      PqxdhServerAuthLoggedSendFactor.Logged (PqxdhServerAuthSendFactor.Kernel ×
        core.option.Option RawCtxWholeOwner.Decrypted))
    (candidate : beaconcrypt_core.pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata)
    (generic : PqxdhInitialGenericPublication.State PqxdhServerAuthSendFactor.Kernel Metadata PeerMetadata Consumed)
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhInitialGenericPublication.State PqxdhServerAuthSendFactor.Kernel Metadata PeerMetadata Consumed) ×
        RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (supported : result ∈ support ((PqxdhInitialGenericBuilder.candidate
      (PqxdhServerAuthLoggedSendFactor.calls receive (PqxdhServerAuthLoggedSendFactor.loggedPrim setup codec checks)
        setup.source challenge) (PqxdhServerAuthLoggedSendFactor.loggedAux setup codec checks)
      (RawCtxSelectedInitialConstructor.initial false right) candidate data metadata generic).run state))
    (response : PqxdhServerRegistrationPublication.Response) (after)
    (published : result.1 = .ok (some response, after)) :
    ∃ fields frame, codec.write2 fields = some response.serialized ∧ codec.frameWrite frame = some fields.appCiphertext ∧
      KeyedCommit frame result.2.2
        (PqxdhRefinement.absBytes (RawCtxInterpretedReceive.decodeResponse challenge).2.key.bytes) := by
  unfold PqxdhInitialGenericBuilder.candidate at supported
  simp only [PqxdhServerAuthLoggedSendFactor.loggedAux, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨valid, validRun, supported⟩ := supported
  rw [PqxdhServerAuthNegativeControl.tailImpl_aux] at validRun
  simp only [PqxdhServerAuthExperiment.tailAux, StateT.run_pure, support_pure, Set.mem_singleton_iff] at validRun
  subst validRun
  cases hvalid : checks.beaconIdentity candidate.beacon_identity_public_key
  · simp only [hvalid, Bool.not_false, ite_true, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    cases published
  simp only [hvalid, Bool.not_true, Bool.false_eq_true, ite_false, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨reserved, reservedRun, supported⟩ := supported
  rw [PqxdhServerAuthNegativeControl.tailImpl_aux] at reservedRun
  simp only [PqxdhServerAuthExperiment.tailAux, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reservedRun
  subst reservedRun
  cases hreserved : checks.reservePeer
  · simp only [hreserved, Bool.not_false, ite_true, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    cases published
  simp only [hreserved, Bool.not_true, Bool.false_eq_true, ite_false, PqxdhDeploymentHiddenKernels.serverInitial_exact,
    PqxdhInitialGenericBuilder.continueRust] at supported
  by_cases empty : (data.getD PqxdhServerRegistrationPublication.registrationWitness).isEmpty = true
  · simp only [empty, ite_true, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    cases published
  simp only [empty, Bool.false_eq_true, ite_false] at supported
  split_ifs at supported with fits
  · simp only [StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨allocated, allocatedRun, supported⟩ := supported
    rw [PqxdhServerAuthNegativeControl.tailImpl_aux] at allocatedRun
    simp only [PqxdhServerAuthExperiment.tailAux, StateT.run_pure, support_pure, Set.mem_singleton_iff] at allocatedRun
    subst allocatedRun
    cases hallocated : checks.reservePlaintext (8 + (data.getD PqxdhServerRegistrationPublication.registrationWitness).length)
    · simp only [hallocated, Bool.not_false, ite_true, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      cases published
    simp only [hallocated, Bool.not_true, Bool.false_eq_true, ite_false] at supported
    cases binding : candidate.key_id_binding with
    | ok value =>
        simp only [binding, StateT.run_map, support_map] at supported
        obtain ⟨inner, innerRun, rfl⟩ := supported
        simp only [RustM.ok.injEq] at published
        exact afterInit_keyed setup codec checks challenge right receive candidate _ metadata generic _ inner innerRun
          response (by rw [published])
    | fail error =>
        simp only [binding, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst supported
        cases published
    | div =>
        simp only [binding, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst supported
        cases published
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    cases published

/-- The generic Server build on the hidden initial kernel, with the logging tail: a published response is as in `afterInit_keyed`. -/
theorem genericBuild_keyed {Metadata PeerMetadata Consumed : Type}
    (challenge : beaconcrypt_core.ratchet.RatchetKdfResponse) (right : PqxdhSecretInputKdf.RootOutput)
    (receive : PqxdhServerAuthSendFactor.Kernel → Std.U64 → RawCtxWholeOwner.OpenContext →
      PqxdhServerAuthLoggedSendFactor.Logged (PqxdhServerAuthSendFactor.Kernel ×
        core.option.Option RawCtxWholeOwner.Decrypted))
    (pending : beaconcrypt_core.pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (generic : PqxdhInitialGenericPublication.State PqxdhServerAuthSendFactor.Kernel Metadata PeerMetadata Consumed)
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhInitialGenericPublication.State PqxdhServerAuthSendFactor.Kernel Metadata PeerMetadata Consumed) ×
        RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (supported : result ∈ support ((PqxdhServerAuthSendFactor.genericBuild
      (PqxdhServerAuthLoggedSendFactor.calls receive (PqxdhServerAuthLoggedSendFactor.loggedPrim setup codec checks)
        setup.source challenge) (PqxdhServerAuthLoggedSendFactor.loggedAux setup codec checks)
      (RawCtxSelectedInitialConstructor.initial false right) pending data metadata generic).run state))
    (response : PqxdhServerRegistrationPublication.Response) (after)
    (published : result.1 = .ok (some response, after)) :
    ∃ fields frame, codec.write2 fields = some response.serialized ∧ codec.frameWrite frame = some fields.appCiphertext ∧
      KeyedCommit frame result.2.2
        (PqxdhRefinement.absBytes (RawCtxInterpretedReceive.decodeResponse challenge).2.key.bytes) := by
  unfold PqxdhServerAuthSendFactor.genericBuild PqxdhInitialGenericBuilder.continueRust at supported
  cases next : beaconcrypt_core.pqxdh.server_next_key_id generic.control with
  | ok value =>
      rw [next] at supported
      rcases value with key | error
      · dsimp only at supported
        cases prepared : beaconcrypt_core.pqxdh.server_prepare_commit generic.control pending
            ⟨generic.server.identity, generic.identityKeyId⟩
            (if (generic.server.peers key).isSome then beaconcrypt_core.pqxdh.KeyIdAvailability.Occupied
              else .Available) with
        | ok value =>
            rw [prepared] at supported
            rcases value with candidate | error
            · exact candidate_keyed setup codec checks challenge right receive candidate data metadata generic state result
                supported response after published
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              cases published
        | fail error =>
            rw [prepared] at supported
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
            subst supported
            cases published
        | div =>
            rw [prepared] at supported
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
            subst supported
            cases published
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst supported
        cases published
  | fail error =>
      rw [next] at supported
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      cases published
  | div =>
      rw [next] at supported
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      cases published

/-- The factored hidden build at a 108-byte value (`PqxdhRegistrationJointKemEntryFactor.factoredHidden`), with the logging tail: a published response is the codec's Phase 2 writing of fields whose application ciphertext is a codec frame whose commitment the final cache holds keyed by the material key of the value's ratchet response. -/
theorem hiddenBuild_keyed (value : PqxdhServerAuthKeySchedule.Output) (token : PqxdhServerRelatedRootConsumer.Returned)
    (payload : Option Pqxdh.Bytes) (server : PqxdhServerAuthEntryFactor.ServerState)
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (result : RustM (Option PqxdhServerRegistrationPublication.Response × PqxdhServerAuthEntryFactor.ServerState) ×
      RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (supported : result ∈ support
      (((PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks value).hiddenBuild token payload
        server).run state))
    (response : PqxdhServerRegistrationPublication.Response)
    (published : (PqxdhServerAuthExperiment.settle server result.1).1 = some response) :
    ∃ fields frame, codec.write2 fields = some response.serialized ∧ codec.frameWrite frame = some fields.appCiphertext ∧
      KeyedCommit frame result.2.2 (PqxdhRefinement.absBytes (RawCtxInterpretedReceive.decodeResponse
        (PqxdhServerAuthCtxMaterial.factor value).1).2.key.bytes) := by
  change result ∈ support ((Functor.map (Prod.map id (PqxdhInitialGenericPublication.native
    PqxdhServerAuthSendFactor.resolve)) <$> PqxdhServerAuthSendFactor.genericBuild
      (PqxdhServerAuthLoggedSendFactor.calls (fun entry _ _ => pure (entry, .None))
        (PqxdhServerAuthLoggedSendFactor.loggedPrim setup codec checks) setup.source
        (PqxdhServerAuthCtxMaterial.factor value).1) (PqxdhServerAuthLoggedSendFactor.loggedAux setup codec checks)
      (RawCtxSelectedInitialConstructor.initial false (PqxdhServerAuthCtxMaterial.factor value).2) token.pending
      payload () (PqxdhServerAuthSendFactor.embed server)).run state) at supported
  rw [StateT.run_map, support_map] at supported
  obtain ⟨inner, innerRun, rfl⟩ := supported
  rcases inner with ⟨⟨_ | built, after⟩ | error | _, final⟩
  · cases published
  · have same : some built = some response := published
    cases same
    exact genericBuild_keyed setup codec checks _ _ _ token.pending payload () _ state _ innerRun response after rfl
  · cases published
  · cases published

/-- The material key of the ratchet response of a joined output is the material's key part. -/
theorem join_key (m : PqxdhDeploymentHiddenLayout.Material) (seed : PqxdhRecordLiftSeed.Seed) :
    PqxdhRefinement.absBytes (RawCtxInterpretedReceive.decodeResponse
      (PqxdhServerAuthCtxMaterial.factor (PqxdhDeploymentHiddenLayout.joinOutput m seed)).1).2.key.bytes =
        m.1.toList := by
  rw [PqxdhDeploymentHiddenLayout.factor_join]
  change PqxdhRefinement.absBytes (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse
    (RawCtxKdfRequestTable.assemble (m.1, seed.1, m.2)))).2.key.bytes = _
  rw [RawCtxFreshChainCut.decoded_parts, PqxdhDeploymentHiddenSplit.material_assemble]
  simp [RawCtxFreshChainCut.concreteMaterial, PqxdhRefinement.absBytes, List.map_map, Function.comp_def,
    BeaconcryptCore.Refinement.ProtocolComposition.absByte_concreteByte]

/-- The marked build of the native state with the erased hidden services at a value: a published response is the codec's Phase 2 writing of fields whose application ciphertext is a codec frame whose commitment the final CTX cache holds keyed by the material key of the value's ratchet response. -/
theorem buildHidden_keyed (value : PqxdhServerAuthKeySchedule.Output) (session : ℕ) (payload : Option Pqxdh.Bytes)
    (shared : PqxdhServerAuthNative.NativeState KemSK)
    (r : Option PqxdhServerRegistrationPublication.Response × PqxdhServerAuthNative.NativeState KemSK)
    (member : r ∈ support ((PqxdhDeploymentIdealSteps.buildHidden (PqxdhDeploymentIdealSteps.erasedHidden setup codec
      checks value) session payload).run shared))
    (response : PqxdhServerRegistrationPublication.Response) (replied : r.1 = some response) :
    ∃ fields frame, codec.write2 fields = some response.serialized ∧ codec.frameWrite frame = some fields.appCiphertext ∧
      KeyedCommit frame r.2.2.ctx (PqxdhRefinement.absBytes (RawCtxInterpretedReceive.decodeResponse
        (PqxdhServerAuthCtxMaterial.factor value).1).2.key.bytes) := by
  unfold PqxdhDeploymentIdealSteps.buildHidden at member
  rw [PqxdhDeploymentBackend.nativeGet_bind] at member
  split at member
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    cases replied
  · rename_i token _
    rw [PqxdhDeploymentBackend.nativeCoins_bind, mem_support_bind_iff] at member
    obtain ⟨built, builtMember, member⟩ := member
    simp only [PqxdhServerAuthNative.nativeSet, StateT.run] at member
    subst member
    exact hiddenBuild_keyed setup codec checks value token payload shared.2.server ([], shared.2.ctx) built builtMember
      response replied

/-- Under the approved Phase 2 and frame read-back contracts, the public Phase 2 reading of a Phase 2 writing whose application ciphertext is a frame writing is that frame. -/
theorem written_frame (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (fields : PqxdhServerRegistrationPublication.ResponseFields) (frame : RawCtxReceive.DecodedFrame)
    (bytes : Pqxdh.Bytes) (written : codec.write2 fields = some bytes)
    (framed : codec.frameWrite frame = some fields.appCiphertext) :
    PqxdhServerAuthRecordPublicationEvent.frame codec bytes = some frame := by
  obtain ⟨read, readEq, -, -, -, -, application⟩ := phase2 fields bytes written
  obtain ⟨-, back⟩ := frameBack frame fields.appCiphertext framed
  simp only [PqxdhServerAuthRecordPublicationEvent.frame, readEq, application, back, Option.bind_eq_bind,
    Option.bind_some]

end Seal

/-! ### The marked build on the split state -/

section MarkedBuild
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (route : RawCtxServerRouting.SenderDecoder) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- The hidden Server install keeps the reply, the R1 table, the CTX cache, the allocator and the material cache. -/
theorem serverInstall_keeps
    (mid installed : (Option PqxdhServerRegistrationPublication.Response × Option PqxdhDeploymentIdealSlots.Coord) ×
      XState KemSK SplitBk 2)
    (member : installed ∈ support (PqxdhDeploymentIdealDefer.serverInstall mid)) :
    installed.1.1 = mid.1.1 ∧ installed.2.base.native.shared.1 = mid.2.base.native.shared.1 ∧
      installed.2.base.native.shared.2.ctx = mid.2.base.native.shared.2.ctx ∧
      installed.2.backend.2.1 = mid.2.backend.2.1 ∧ installed.2.backend.1 = mid.2.backend.1 := by
  obtain ⟨allocEq, matEq, -⟩ := PqxdhDeploymentIdealDefer.xInstall_support _ _ _ mid installed member
  refine ⟨?_, ?_, ?_, allocEq, matEq⟩ <;>
  · unfold PqxdhDeploymentIdealDefer.serverInstall PqxdhDeploymentIdealDefer.xInstall at member
    split at member
    · rw [support_pure, Set.mem_singleton_iff] at member
      subst member
      rfl
    · split at member
      · rw [support_pure, Set.mem_singleton_iff] at member
        subst member
        rfl
      · split at member
        · rw [support_map] at member
          obtain ⟨_, _, rfl⟩ := member
          simp only [PqxdhDeploymentIdealKernel.buildApply, PqxdhDeploymentIdealKeys.attachX,
            PqxdhDeploymentIdealKeys.detachX, PqxdhDeploymentIdealKernel.peerFix]
          all_goals (split <;> rfl)
        · rw [support_pure, Set.mem_singleton_iff] at member
          subst member
          rfl

/-- A read through the allocator in front of the lazy service: the coordinates hold a slot whose cached material `m` gives the value `joinOutput m dummySeed`, or the allocator was full, the coordinates hold no slot, and the allocator and service state are kept. -/
theorem lazyRead (c : PqxdhDeploymentIdealSlots.Coord)
    (state : PqxdhRegistrationJointKemSecondEntry.Alloc PqxdhDeploymentIdealSlots.Coord 2 ×
      (PqxdhDeploymentIdealKernel.MatCache 2 × PqxdhDeploymentIdealKernel.SeedCache 2))
    (r : PqxdhServerAuthKeySchedule.Output × (PqxdhRegistrationJointKemSecondEntry.Alloc PqxdhDeploymentIdealSlots.Coord 2 ×
      (PqxdhDeploymentIdealKernel.MatCache 2 × PqxdhDeploymentIdealKernel.SeedCache 2)))
    (member : r ∈ support ((PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentIdealKernel.lazyDummy
      (.inr c)).run state)) :
    (∃ j m, r.2.1.1 c = some j ∧ r.2.2.1 j = some m ∧
      r.1 = PqxdhDeploymentHiddenLayout.joinOutput m PqxdhDeploymentHiddenSplit.dummySeed) ∨
    (r.2 = state ∧ state.1.1 c = none ∧ 2 ≤ state.1.2) := by
  rcases found : state.1.1 c with _ | slot
  · by_cases room : state.1.2 < 2
    · rw [PqxdhDeploymentIdealDefer.slotImpl_lazy_new c state found room, support_map] at member
      obtain ⟨inner, innerMember, rfl⟩ := member
      exact Or.inl ⟨⟨state.1.2, room⟩, inner.1, by simp,
        PqxdhDeploymentIdealKernel.query_support _ _ inner innerMember, rfl⟩
    · simp only [PqxdhRegistrationJointKemSecondEntry.slotImpl, QueryImpl.add_apply_inr, StateT.run_mk, found, room,
        _root_.dite_false, support_map] at member
      obtain ⟨answer, -, rfl⟩ := member
      exact Or.inr ⟨rfl, rfl, by omega⟩
  · rw [PqxdhDeploymentIdealDefer.slotImpl_lazy_found c state slot found, support_map] at member
    obtain ⟨inner, innerMember, rfl⟩ := member
    exact Or.inl ⟨slot, inner.1, found, PqxdhDeploymentIdealKernel.query_support _ _ inner innerMember, rfl⟩

/-- The native build of a session answers a response only from a pending token of that session. -/
theorem nativeBuild_pending (session : ℕ) (payload : Option Pqxdh.Bytes)
    (shared : PqxdhServerAuthNative.NativeState KemSK)
    (r : Option PqxdhServerRegistrationPublication.Response × PqxdhServerAuthNative.NativeState KemSK)
    (member : r ∈ support ((PqxdhServerAuthNative.nativeBuild setup codec checks session payload).run shared))
    (response : PqxdhServerRegistrationPublication.Response) (replied : r.1 = some response) :
    (shared.2.pending session).isSome = true := by
  unfold PqxdhServerAuthNative.nativeBuild at member
  rw [PqxdhDeploymentBackend.nativeGet_bind] at member
  split at member
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    cases replied
  · rename_i token found
    rw [found]
    rfl

/-- The real build of the slot program answers a response only from a pending token of its session. -/
theorem realBuild_pending (session : ℕ) (payload : Option Pqxdh.Bytes) (y : XState KemSK IdealCore 2)
    (r : (Option PqxdhServerRegistrationPublication.Response × Option PqxdhDeploymentIdealSlots.Coord) ×
      XState KemSK IdealCore 2)
    (member : r ∈ support ((fun r => ((r.1, none), r.2)) <$> OracleComp.liftComp
      ((PqxdhDeploymentIdealSteps.realRegAt setup codec route checks created ⟨.build session payload, trivial⟩).run y)
        PqxdhDeploymentIdealSlots.SlotSpec))
    (response : PqxdhServerRegistrationPublication.Response) (replied : r.1.1 = some response) :
    (y.base.native.shared.2.pending session).isSome = true := by
  rw [support_map, OracleComp.support_liftComp] at member
  obtain ⟨q, qMember, rfl⟩ := member
  obtain ⟨nativeMember, -⟩ := PqxdhDeploymentIdealKeymatch.realRegAt_support setup codec route checks created _ y q
    qMember
  have scheduleMember := PqxdhDeploymentIdealKeymatch.onNative_native
    (PqxdhRegistrationSchedule.onShared (PqxdhServerAuthNative.nativeBuild setup codec checks session payload))
    y.base q.1 q.2.base nativeMember
  change (q.1, q.2.base.native) ∈ support ((fun result => (result.1, { y.base.native with shared := result.2 })) <$>
    (PqxdhServerAuthNative.nativeBuild setup codec checks session payload).run y.base.native.shared) at scheduleMember
  rw [support_map] at scheduleMember
  obtain ⟨built, builtMember, same⟩ := scheduleMember
  have replyEq : built.1 = q.1 := congrArg Prod.fst same
  exact nativeBuild_pending setup codec checks session payload _ built builtMember response (replyEq.trans replied)

/-- The build step of the split core answers a response only from a pending token of its session. -/
theorem buildStepC_pending
    (hidden : PqxdhServerAuthKeySchedule.Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (session : ℕ) (payload : Option Pqxdh.Bytes) (y : XState KemSK IdealCore 2)
    (r : (Option PqxdhServerRegistrationPublication.Response × Option PqxdhDeploymentIdealSlots.Coord) ×
      XState KemSK IdealCore 2)
    (member : r ∈ support ((PqxdhDeploymentIdealKernel.buildStepC setup codec checks route hidden created session
      payload).run y))
    (response : PqxdhServerRegistrationPublication.Response) (replied : r.1.1 = some response) :
    (y.base.native.shared.2.pending session).isSome = true := by
  change r ∈ support (match y.backend.marks with
    | some (index, coords) =>
        if index = session ∧ (y.base.native.shared.2.pending session).isSome then
          (PqxdhDeploymentIdealKernel.buildHiddenC hidden session payload coords).run y
        else (fun r : Option PqxdhServerRegistrationPublication.Response × XState KemSK IdealCore 2 =>
          ((r.1, none), r.2)) <$> PqxdhDeploymentIdealSteps.onSlots
          (PqxdhDeploymentIdealSteps.realRegAt setup codec route checks created ⟨.build session payload, trivial⟩) y
    | none => (fun r : Option PqxdhServerRegistrationPublication.Response × XState KemSK IdealCore 2 =>
        ((r.1, none), r.2)) <$> PqxdhDeploymentIdealSteps.onSlots
        (PqxdhDeploymentIdealSteps.realRegAt setup codec route checks created ⟨.build session payload, trivial⟩) y)
    at member
  split at member
  · split_ifs at member with guard
    · exact guard.2
    · exact realBuild_pending setup codec checks route created session payload y r member response replied
  · exact realBuild_pending setup codec checks route created session payload y r member response replied

/-- `markedBuild_commit`: a successful build of the marked session on the split state either found the allocator full with the marked coordinates holding no slot, or leaves the marked coordinates at a slot whose cached material `m` keys the commitment of the frame that the public Phase 2 reading of the response gives (under the approved Phase 2 and frame read-back contracts). -/
theorem markedBuild_commit (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec) (session : ℕ) (payload : Option Pqxdh.Bytes)
    (x : XState KemSK SplitBk 2) (c : PqxdhDeploymentIdealSlots.Coord) (marked : x.backend.2.2.marks = some (session, c))
    (result : Option PqxdhServerRegistrationPublication.Response × XState KemSK SplitBk 2)
    (supported : result ∈ support ((PqxdhDeploymentBackend.handlerWith setup codec route
      (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created) (.inr (.build session payload))).run x))
    (response : PqxdhServerRegistrationPublication.Response) (replied : result.1 = some response) :
    (result.2.backend.2.1.1 c = none ∧ 2 ≤ result.2.backend.2.1.2) ∨
      ∃ j m, result.2.backend.2.1.1 c = some j ∧ result.2.backend.1 j = some m ∧
        CommitAt codec (ctxCache result.2) response.serialized m.1.toList := by
  change result ∈ support ((fun r => (r.1.1, r.2)) <$> ((PqxdhDeploymentIdealKernel.slotRunX
    PqxdhDeploymentIdealKernel.lazyDummy (PqxdhDeploymentIdealKernel.buildStepC setup codec checks route
      (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks) created session payload)).run x >>=
        PqxdhDeploymentIdealDefer.serverInstall)) at supported
  rw [support_map] at supported
  obtain ⟨installed, installedMember, rfl⟩ := supported
  rw [mem_support_bind_iff] at installedMember
  obtain ⟨mid, midMember, installMember⟩ := installedMember
  obtain ⟨replyEq, -, ctxEq, allocEq, matEq⟩ := serverInstall_keeps mid installed installMember
  have midReplied : mid.1.1 = some response := replyEq.symm.trans replied
  simp only [ctxCache, ctxEq, allocEq, matEq]
  change mid ∈ support ((fun r => (r.1, PqxdhDeploymentIdealKeys.attachX r.2.1 r.2.2.1 r.2.2.2)) <$>
    (PqxdhDeploymentIdealErase.onPair PqxdhDeploymentIdealKernel.lazyDummy (PqxdhDeploymentIdealKernel.buildStepC
      setup codec checks route (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks) created session payload)).run
        (PqxdhDeploymentIdealKeys.detachX x, (x.backend.2.1, (x.backend.1, x.seeds)))) at midMember
  rw [support_map] at midMember
  obtain ⟨paired, pairedMember, rfl⟩ := midMember
  rw [PqxdhDeploymentIdealErase.onPair_run, support_map] at pairedMember
  obtain ⟨simulated, simulatedMember, rfl⟩ := pairedMember
  have stepMember : simulated.1 ∈ support ((PqxdhDeploymentIdealKernel.buildStepC setup codec checks route
      (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks) created session payload).run
        (PqxdhDeploymentIdealKeys.detachX x)) := by
    apply OracleComp.support_simulateQ_run'_subset
      (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentIdealKernel.lazyDummy) _
      (x.backend.2.1, (x.backend.1, x.seeds))
    rw [StateT.run'_eq, support_map]
    exact ⟨simulated, simulatedMember, rfl⟩
  have pendingSome := buildStepC_pending setup codec checks route created _ session payload _ simulated.1 stepMember
    response midReplied
  obtain ⟨token, pendingEq⟩ := Option.isSome_iff_exists.mp pendingSome
  replace pendingEq : x.base.native.shared.2.pending session = some token := pendingEq
  have hiddenStep : (PqxdhDeploymentIdealKernel.buildStepC setup codec checks route
      (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks) created session payload).run
        (PqxdhDeploymentIdealKeys.detachX x) =
      (PqxdhDeploymentIdealKernel.buildHiddenC (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks)
        session payload c).run (PqxdhDeploymentIdealKeys.detachX x) := by
    change (match x.backend.2.2.marks with
      | some (index, coords) => if index = session ∧ (x.base.native.shared.2.pending session).isSome then _ else _
      | none => _) = _
    rw [marked]
    simp only [pendingEq, Option.isSome_some, and_self, ↓reduceIte]
  rw [hiddenStep] at simulatedMember
  unfold PqxdhDeploymentIdealKernel.buildHiddenC at simulatedMember
  rw [PqxdhDeploymentIdealErase.readAt_bind_run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    mem_support_bind_iff] at simulatedMember
  obtain ⟨read, readMember, rest⟩ := simulatedMember
  change simulated ∈ support ((simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl
    PqxdhDeploymentIdealKernel.lazyDummy) (PqxdhDeploymentIdealSteps.liftS
      (((fun r => (r, some c)) <$> PqxdhDeploymentIdealErase.buildFocus (PqxdhDeploymentIdealSteps.erasedHidden setup codec
        checks read.1) session payload c).run (PqxdhDeploymentIdealKeys.detachX x)))).run read.2) at rest
  rw [PqxdhDeploymentIdealEnvFacts.slot_liftS, support_map] at rest
  obtain ⟨a, aMember, rfl⟩ := rest
  rcases lazyRead c _ read readMember with ⟨j, m, slotted, cached, valueEq⟩ | ⟨kept, unslotted, full⟩
  · right
    refine ⟨j, m, slotted, cached, ?_⟩
    rw [StateT.run_map, support_map] at aMember
    obtain ⟨b, bMember, rfl⟩ := aMember
    unfold PqxdhDeploymentIdealErase.buildFocus at bMember
    simp only [StateT.run] at bMember
    rw [support_map] at bMember
    obtain ⟨h, hMember, rfl⟩ := bMember
    rw [valueEq] at hMember
    obtain ⟨fields, frame, written, framed, keyed⟩ := buildHidden_keyed setup codec checks _ session payload _ h hMember
      response midReplied
    rw [join_key] at keyed
    exact ⟨frame, written_frame codec phase2 frameBack fields frame _ written framed, keyed⟩
  · left
    rw [kept]
    exact ⟨unslotted, full⟩

end MarkedBuild

/-! ### The challenge-marker exclusion -/

section Challenge

/-- A finish input that the Phase 2 reader reads as the challenge ciphertext carries the challenge ciphertext's array (`ciphertext_roundtrip`'s first conjunct; design amendment A1). -/
theorem ciphertextOf_of_challengeRead (codec : Codec Reader Response) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (raw : Pqxdh.Bytes) (read : PqxdhDeploymentIdealBeacon.ChallengeRead codec challenge raw) :
    PqxdhDeploymentHeadlineGap.ciphertextOf codec (some raw) =
      some (PqxdhAcceptedRegistration.ciphertextArray challenge) := by
  obtain ⟨ct, found, bytes⟩ := read
  have back := (PqxdhPhase2InputBytes.ciphertext_roundtrip ct challenge).1
  rw [bytes] at back
  show (codec.read2 raw).bind codec.ciphertext = _
  rw [found, back]

/-- A finish input whose ciphertext differs from that of a build carrying the challenge ciphertext is not `ChallengeRead`. -/
theorem not_challengeRead (codec : Codec Reader Response) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (raw : Pqxdh.Bytes) (built : Option Pqxdh.Bytes)
    (carries : PqxdhDeploymentHeadlineGap.ciphertextOf codec built =
      some (PqxdhAcceptedRegistration.ciphertextArray challenge))
    (differ : PqxdhDeploymentHeadlineGap.ciphertextOf codec (some raw) ≠
      PqxdhDeploymentHeadlineGap.ciphertextOf codec built) :
    ¬ PqxdhDeploymentIdealBeacon.ChallengeRead codec challenge raw := fun read =>
  differ ((ciphertextOf_of_challengeRead codec challenge raw read).trans carries.symm)

end Challenge

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.commitAt_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.commitAt_mono

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.beaconInstall_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.beaconInstall_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.slotRunX_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.slotRunX_support

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.finishStepC_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.finishStepC_root

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.finish_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.finish_root

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.sealHash_take' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.sealHash_take

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.tailSeal_keyed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.tailSeal_keyed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.firstSend_keyed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.firstSend_keyed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.afterInit_keyed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.afterInit_keyed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.candidate_keyed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.candidate_keyed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.genericBuild_keyed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.genericBuild_keyed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.hiddenBuild_keyed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.hiddenBuild_keyed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.join_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.join_key

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.buildHidden_keyed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.buildHidden_keyed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.written_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.written_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.serverInstall_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.serverInstall_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.lazyRead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.lazyRead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.nativeBuild_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.nativeBuild_pending

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.realBuild_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.realBuild_pending

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.buildStepC_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.buildStepC_pending

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.markedBuild_commit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.markedBuild_commit

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.ciphertextOf_of_challengeRead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.ciphertextOf_of_challengeRead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.not_challengeRead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit.not_challengeRead
