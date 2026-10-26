-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctReceive
import BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels
import BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationEvent
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeletonNative
import BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon

/-!
# CE-12 D-ct: the Beacon finish reads an R1 value and commits under its sequence-one key

A successful Beacon finish (`beaconcrypt/src/beacon.rs`, `finish_registration`) derives its root from the R1 table (route R1: the zero-salt Extract of the root key input as a lazily sampled table), starts the initial ratchet from the root alone and opens the registration record at sequence one. This module shows, on the native source schedule, that a successful finish tail leaves an R1 entry `v` and the frame's commitment cached at an input keyed by `seqKey setup v` (`PqxdhDeploymentHeadlineDctReceive`).

- R1 growth. `R1Grows before after`: every R1 entry of `before` is in `after`. Every native callback of the Beacon finish keeps or extends the R1 table (`callbacks_grows`, with `sourceRoot_read`: the root callback reads the table at the root key input and returns the root of the value read).
- The real finish. `tail_keyed`: on the source schedule's Beacon tail (`PqxdhBeaconPhase2Publication.tail` under `PqxdhRegistrationSchedule.callbacks`), a successful tail leaves the R1 entry of its root key input and the frame of its application input committed under the sequence-one key of that entry (`tail_supported`, `afterRoot_supported`, `afterOpening_success`, `PqxdhDeploymentRecordKernels.finish_receive`, `whole_keyed`, `factor_key`). `owner_keyed` lifts it to the native owner (`owner_success`, `prepare_origin`, `collect_inputs`: the prepared response is the Phase 2 reading of the input bytes) and `scheduleFinish_keyed` to the schedule's finish (`finish_source`): the frame is the one that `PqxdhServerAuthRecordPublicationEvent.frame` reads from the finish input.
- The known-root branch of owner k's challenge finish. `consumer_keyed`: the related-root consumer's tail on the actual Beacon tail interpreter (`PqxdhServerAuthBeaconFactor.beacon_afterRoot_run` to the factored tail, `PqxdhPhase2LocalMatching.consumer_opening` and `raw_success` for sequence one, `factored_keyed`). `groupNative_keyed`: item 2's native grouped answer `groupNativeN` reads the R1 table through the private root interpreter `markedRoot` (the source root callback on the same table) and runs that tail (`afterRoot_embed`). `prepareCE_facts`: with the challenge handle, a prepared finish carries the Phase 2 reading of its input, and carries the challenge marker only when its ciphertext is the challenge ciphertext (`preparationCE`'s `if`; amendment A1/A3 of the design). `finishChallenge_keyed`: owner k's challenge finish on an input that is not `ChallengeRead` is answered by the known-root branch (`groupCE_known`), with the same conclusion as the real finish (`keepLift_run` for the state-keeping preparation).

Support facts only; no assumption is used.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhServerAuthNative (NativeState NativeGame)
open PqxdhDeploymentHeadlineDctReceive (KeyedCommit seqKey)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-! ### The R1 table only grows -/

/-- Every R1 entry of `before` is an R1 entry of `after`. -/
def R1Grows (before after : NativeState KemSK) : Prop :=
  ∀ u v, before.1.cache u = some v → after.1.cache u = some v

theorem r1Grows_trans {first second third : NativeState KemSK} (one : R1Grows first second)
    (two : R1Grows second third) : R1Grows first third :=
  fun u v found => two u v (one u v found)

/-- A computation on the shared CTX state keeps the R1 table. -/
theorem nativeCtx_keeps {α : Type} (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp α)
    (state : NativeState KemSK) (result : α × NativeState KemSK)
    (supported : result ∈ support ((PqxdhServerAuthNative.nativeCtx work).run state)) :
    result.2.1 = state.1 := by
  change result ∈ support ((fun r => (r.1, (state.1, { state.2 with ctx := r.2.2 }))) <$>
    work.run ((), state.2.ctx)) at supported
  rw [support_map] at supported
  obtain ⟨_, _, rfl⟩ := supported
  rfl

/-- The source root callback reads the R1 table at the root key input and returns the root of the value read; the CTX state is kept. -/
theorem sourceRoot_read (hmac : PqxdhSecretInputKdf.HmacSha512) (input : beaconcrypt_core.pqxdh.RootKeyInput)
    (state : NativeState KemSK) (result : Option PqxdhBeaconPhase2Preparation.Word32 × NativeState KemSK)
    (supported : result ∈ support ((PqxdhServerAuthNative.sourceRoot hmac input).run state)) :
    R1Grows state result.2 ∧ result.2.2 = state.2 ∧ ∃ v, result.1 =
      some (PqxdhRootTableInitialization.rootArray (PqxdhSecretInputKdf.expandRoot hmac v)) ∧
      result.2.1.cache (PqxdhRefinement.absBytes input.bytes) = some v := by
  change result ∈ support ((fun r => (some (PqxdhRootTableInitialization.rootArray
    (PqxdhSecretInputKdf.expandRoot hmac r.1)), ({ state.1 with cache := r.2 }, state.2))) <$>
      (PqxdhSecretInputKdf.HmacOracle.randomOracle (PqxdhRefinement.absBytes input.bytes)).run state.1.cache)
    at supported
  rw [support_map] at supported
  obtain ⟨⟨v, cache⟩, read, rfl⟩ := supported
  refine ⟨fun u w found => ?_, rfl, v, rfl, ?_⟩
  · exact QueryImpl.withCaching_cache_le _ _ _ _ read found
  · cases old : state.1.cache (PqxdhRefinement.absBytes input.bytes) with
    | none =>
        rw [QueryImpl.withCaching_run_none _ old, support_map] at read
        obtain ⟨w, _, same⟩ := read
        cases same
        exact QueryCache.cacheQuery_self _ _ _
    | some w =>
        rw [QueryImpl.withCaching_run_some _ old, support_pure, Set.mem_singleton_iff] at read
        cases read
        exact old

/-- Every native callback of the Beacon finish keeps or extends the R1 table. -/
theorem callbacks_grows (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : (PqxdhBeaconPhase2Publication.NativeSpec PqxdhJointIdentity.IdentitySeed PqxdhJointGapDh.ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) PqxdhJointIdentity.IdentitySeed Response).Domain)
    (state : NativeState KemSK) (result : _ × NativeState KemSK)
    (supported : result ∈ support ((PqxdhRegistrationSchedule.callbacks setup codec query).run state)) :
    R1Grows state result.2 := by
  rcases query with query | query
  · change result ∈ support ((fun value => (value, state)) <$> _) at supported
    rw [support_map] at supported
    obtain ⟨_, _, rfl⟩ := supported
    exact fun _ _ found => found
  · rcases query with query | (input | request | response)
    · intro u v found
      rw [nativeCtx_keeps _ state result supported]
      exact found
    · exact (sourceRoot_read setup.hmac input state result supported).1
    · intro u v found
      rw [nativeCtx_keeps _ state result supported]
      exact found
    · intro u v found
      rw [nativeCtx_keeps _ state result supported]
      exact found

/-- A whole program run on the native callbacks of the Beacon finish keeps or extends the R1 table. -/
theorem run_callbacks_grows {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (program : OracleComp (PqxdhBeaconPhase2Publication.NativeSpec PqxdhJointIdentity.IdentitySeed
      PqxdhJointGapDh.ScalarBytes (PqxdhKemIndCca.MlKem768PublicKey × KemSK) PqxdhJointIdentity.IdentitySeed
      Response) α)
    (state : NativeState KemSK) (result : α × NativeState KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhRegistrationSchedule.callbacks setup codec) program).run state)) :
    R1Grows state result.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query (PqxdhRegistrationSchedule.callbacks setup codec)
    (fun after => R1Grows state after)
    (fun query middle grown next member => r1Grows_trans grown (callbacks_grows setup codec query middle next member))
    program state (fun _ _ found => found) result supported

/-! ### The real Beacon tail -/

/-- The source schedule's Beacon tail: a successful tail leaves the R1 entry `v` of its root key input and the frame of its application input committed in the final CTX cache under the sequence-one key of `v`. -/
theorem tail_keyed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (prepared : PqxdhBeaconPhase2Preparation.Prepared Response) (state final : NativeState KemSK)
    (staged : PqxdhBeaconPhase2Publication.Staged)
    (supported : (some staged, final) ∈ support ((simulateQ (fun query =>
      (PqxdhRegistrationSchedule.callbacks setup codec ∘ₛ PqxdhBeaconPhase2Publication.nativeAdapter) (.inr query))
      (PqxdhBeaconPhase2Publication.tail codec.frameRead prepared)).run state)) :
    ∃ v raw frame, final.1.cache (PqxdhRefinement.absBytes prepared.candidate.root_key_input.bytes) = some v ∧
      codec.application prepared.response = some raw ∧ codec.frameRead raw = some frame ∧
      KeyedCommit frame final.2.ctx (seqKey setup v).toList := by
  obtain ⟨root, intermediate, rootMember, after⟩ :=
    PqxdhBeaconPhase2Publication.tail_supported _ codec.frameRead prepared state final staged supported
  simp only [QueryImpl.apply_compose, PqxdhBeaconPhase2Publication.nativeAdapter,
    PqxdhBeaconPhase2Publication.nativeTailAdapter, PqxdhBeaconPhase2Publication.nativeTailLift,
    simulateQ_spec_query] at rootMember
  change (some root, intermediate) ∈ support ((PqxdhServerAuthNative.sourceRoot setup.hmac
    prepared.candidate.root_key_input).run state) at rootMember
  obtain ⟨_, _, v, rootEq, cached⟩ := sourceRoot_read setup.hmac _ state _ rootMember
  simp only [Option.some.injEq] at rootEq
  subst rootEq
  have grows : R1Grows intermediate final := by
    have composed : (fun query => (PqxdhRegistrationSchedule.callbacks setup codec ∘ₛ
        PqxdhBeaconPhase2Publication.nativeAdapter) (.inr query)) =
        PqxdhRegistrationSchedule.callbacks setup codec ∘ₛ
          (fun query => PqxdhBeaconPhase2Publication.nativeAdapter (.inr query)) := rfl
    rw [composed, QueryImpl.simulateQ_compose] at after
    exact run_callbacks_grows setup codec _ intermediate _ after
  obtain ⟨initial, initialState, raw, appState, received, initialMember, appMember, rawMember, finalEq, opening⟩ :=
    PqxdhBeaconPhase2Publication.afterRoot_supported _ codec.frameRead prepared _ intermediate final staged after
  obtain ⟨openedReply, sequenceOne, _, _⟩ := PqxdhBeaconPhase2Publication.afterOpening_success _ _ _ staged opening
  have value : initial = RawCtxSourceHkdf.initialResponse setup.source.crypto
      (PqxdhInitialRatchetComplementarity.beaconPending
        (PqxdhRootTableInitialization.rootArray (PqxdhSecretInputKdf.expandRoot setup.hmac v))).request := by
    simp only [QueryImpl.apply_compose, PqxdhBeaconPhase2Publication.nativeAdapter,
      PqxdhBeaconPhase2Publication.nativeTailAdapter, PqxdhBeaconPhase2Publication.nativeTailLift,
      simulateQ_spec_query] at initialMember
    change (initial, initialState) ∈ support (PqxdhServerAuthNative.nativeCtx (pure (RawCtxSourceHkdf.initialResponse
      setup.source.crypto (PqxdhInitialRatchetComplementarity.beaconPending
        (PqxdhRootTableInitialization.rootArray (PqxdhSecretInputKdf.expandRoot setup.hmac v))).request))
      intermediate) at initialMember
    simp only [PqxdhServerAuthNative.nativeCtx, StateT.run_pure, map_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at initialMember
    exact initialMember.1
  subst value
  have application : codec.application prepared.response = some raw := by
    simp only [QueryImpl.apply_compose, PqxdhBeaconPhase2Publication.nativeAdapter,
      PqxdhBeaconPhase2Publication.nativeTailAdapter, PqxdhBeaconPhase2Publication.nativeTailLift,
      simulateQ_spec_query] at appMember
    change (some raw, appState) ∈ support (PqxdhServerAuthNative.nativeCtx (pure (codec.application prepared.response))
      initialState) at appMember
    simp only [PqxdhServerAuthNative.nativeCtx, StateT.run_pure, map_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at appMember
    exact appMember.1.symm
  have projected := PqxdhDeploymentRecordKernels.finish_receive setup codec ((RawCtxWholeOwner.rawReceive codec.frameRead
    raw).run (PqxdhBeaconPhase2Publication.localOwner (PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate)
      (PqxdhBeaconPhase2Publication.normalInitial (PqxdhInitialRatchetComplementarity.beaconPending
        (PqxdhRootTableInitialization.rootArray (PqxdhSecretInputKdf.expandRoot setup.hmac v)))
        (RawCtxSourceHkdf.initialResponse setup.source.crypto (PqxdhInitialRatchetComplementarity.beaconPending
          (PqxdhRootTableInitialization.rootArray (PqxdhSecretInputKdf.expandRoot setup.hmac v))).request))))
    appState
  have member : (received.1, PqxdhDeploymentRecordKernels.cacheOf received.2) ∈ support (RawCtxWholeOwner.rawGame
      (RawCtxReceiveConsumption.receiveNative setup.source) codec.frameRead raw
      (PqxdhBeaconPhase2Publication.localOwner (PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate)
        (PqxdhBeaconPhase2Publication.normalInitial (PqxdhInitialRatchetComplementarity.beaconPending
          (PqxdhRootTableInitialization.rootArray (PqxdhSecretInputKdf.expandRoot setup.hmac v)))
          (RawCtxSourceHkdf.initialResponse setup.source.crypto (PqxdhInitialRatchetComplementarity.beaconPending
            (PqxdhRootTableInitialization.rootArray (PqxdhSecretInputKdf.expandRoot setup.hmac v))).request)))
      (PqxdhDeploymentRecordKernels.cacheOf appState)) := by
    unfold RawCtxWholeOwner.rawGame
    rw [← projected, support_map]
    exact ⟨received, rawMember, rfl⟩
  obtain ⟨frame, decoded, keyed⟩ := PqxdhDeploymentHeadlineDctReceive.whole_keyed setup codec codec.frameRead raw _
    (PqxdhSecretInputKdf.expandRoot setup.hmac v) _ _ member staged.opened openedReply sequenceOne
  rw [PqxdhDeploymentHeadlineDctReceive.factor_key] at keyed
  refine ⟨v, raw, frame, grows _ _ cached, application, decoded, ?_⟩
  rw [← finalEq]
  exact keyed

/-- The source native Beacon owner: a successful finish on bytes `raw` leaves an R1 entry `v` and the frame that the public Phase 2 reading of `raw` gives committed in the final CTX cache under the sequence-one key of `v`. -/
theorem owner_keyed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (raw : Pqxdh.Bytes)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (shared : NativeState KemSK)
    (result : (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) × NativeState KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhRegistrationSchedule.callbacks setup codec)
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)).run shared))
    (plaintext : Pqxdh.Bytes) (replied : result.1.1 = some plaintext) :
    ∃ u v frame, result.2.1.cache u = some v ∧ PqxdhServerAuthRecordPublicationEvent.frame codec raw = some frame ∧
      KeyedCommit frame result.2.2.ctx (seqKey setup v).toList := by
  rcases result with ⟨⟨reply, next⟩, final⟩
  simp only at replied
  subst replied
  rw [PqxdhBeaconPhase2Publication.nativeOwner, ← QueryImpl.simulateQ_compose] at supported
  obtain ⟨control, prekey, oneTime, kem, prepared, intermediate, staged, _, prepareSupport, tailSupport,
    _, _, _, _⟩ := PqxdhBeaconPhase2Publication.owner_success _ codec.frameRead raw plaintext owner next
      shared final supported
  have handlerEq : (fun query => (PqxdhRegistrationSchedule.callbacks setup codec ∘ₛ
      PqxdhBeaconPhase2Publication.nativeAdapter) (.inl query)) =
        PqxdhDeploymentCompileFootprint.preparationHandler setup codec := by
    funext query
    simp only [QueryImpl.compose, PqxdhBeaconPhase2Publication.nativeAdapter, simulateQ_spec_query]
    rfl
  rw [handlerEq] at prepareSupport
  obtain ⟨inputs, middle, collected, _, _, responseEq, _, _⟩ :=
    PqxdhBeaconPhase2Preparation.prepare_origin _ control owner.beacon.identity prekey oneTime kem raw shared
      intermediate prepared prepareSupport
  obtain ⟨decoded, _⟩ := PqxdhDeploymentCompileFootprint.collect_inputs setup codec owner.beacon.identity prekey
    oneTime kem raw shared inputs middle collected
  obtain ⟨v, raw', frame, cached, application, frameDecoded, keyed⟩ :=
    tail_keyed setup codec prepared intermediate final staged tailSupport
  refine ⟨_, v, frame, cached, ?_, keyed⟩
  simp only [PqxdhServerAuthRecordPublicationEvent.frame, decoded, ← responseEq, application, frameDecoded,
    Option.bind_eq_bind, Option.bind_some]

/-- The source schedule's finish: a successful finish of an owner on bytes `raw` leaves an R1 entry `v` and the frame that the public Phase 2 reading of `raw` gives committed in the final CTX cache under the sequence-one key of `v`. -/
theorem scheduleFinish_keyed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : ℕ)
    (raw : Pqxdh.Bytes) (state : PqxdhRegistrationSchedule.State KemSK)
    (result : Option Pqxdh.Bytes × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationSchedule.finish setup codec index raw).run state))
    (plaintext : Pqxdh.Bytes) (replied : result.1 = some plaintext) :
    ∃ u v frame, result.2.shared.1.cache u = some v ∧
      PqxdhServerAuthRecordPublicationEvent.frame codec raw = some frame ∧
      KeyedCommit frame result.2.shared.2.ctx (seqKey setup v).toList := by
  cases found : state.owners[index]? with
  | none =>
      rw [PqxdhRegistrationSchedule.finish_missing setup codec index raw state found, support_pure,
        Set.mem_singleton_iff] at supported
      subst supported
      cases replied
  | some owner =>
      change result ∈ support (PqxdhRegistrationSchedule.finish setup codec index raw state) at supported
      rw [PqxdhRegistrationSchedule.finish_source setup codec index raw state owner found, support_map] at supported
      obtain ⟨reached, member, rfl⟩ := supported
      exact owner_keyed setup codec raw owner state.shared reached member plaintext replied

/-! ### The related-root consumer's tail (the known-root branch) -/

/-- The related-root consumer's post-root tail on the actual Beacon tail interpreter: a successful tail decodes the frame of its application input and the final CTX cache holds that frame's commitment keyed by the key of the root's factor. -/
theorem consumer_keyed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) (root : PqxdhSecretInputKdf.RootOutput)
    (state final : RawCtxSharedPrimitive.SharedState Unit) (staged : PqxdhBeaconPhase2Publication.Staged)
    (supported : (some staged, final) ∈ support ((simulateQ (PqxdhServerAuthExperiment.beaconNative setup codec)
      (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead pending (PqxdhRootTableInitialization.rootArray root))).run
        state)) :
    ∃ raw frame, codec.application (PqxdhPhase2DhRootConsumer.cleared pending).response = some raw ∧
      codec.frameRead raw = some frame ∧ KeyedCommit frame final.2
        (PqxdhRefinement.absBytes (RawCtxInterpretedReceive.decodeResponse
          (PqxdhServerAuthSendFactor.factor setup.source root).1).2.key.bytes) := by
  have ordinary : PqxdhPhase2LocalMatching.OrdinaryOpen setup.source.crypto
      (fun query => PqxdhServerAuthExperiment.beaconNative setup codec (.inl query)) :=
    PqxdhPhase2LocalMatching.native_ordinary setup.source.crypto (RawCtxSourceHkdf.kdfImpl setup.source)
  obtain ⟨initial, initialState, raw, application, received, input, slices, parsed, width, _, appMember,
    rawMember, _, reply, staging, _⟩ := PqxdhPhase2LocalMatching.consumer_opening setup.source.crypto _ ordinary
      codec.frameRead pending _ state final staged supported
  have rawEq : codec.application (PqxdhPhase2DhRootConsumer.cleared pending).response = some raw := by
    change (some raw, application) ∈ support ((pure (codec.application (PqxdhPhase2DhRootConsumer.cleared
      pending).response) : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp _).run initialState) at appMember
    rw [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at appMember
    exact appMember.1.symm
  obtain ⟨_, sequenceOne, _, _⟩ := PqxdhBeaconPhase2Publication.afterOpening_success _ _ _ staged staging
  obtain ⟨frame, _, input', plaintext, _, decoded, _, _, _, sequence, _, messageEq, _⟩ :=
    RawCtxOwnerProvenance.raw_success _ codec.frameRead raw _ application received rawMember staged.opened reply
  have frameOne : frame.sequence = 1#u64 := by
    rw [← sequence, ← sequenceOne, messageEq]
    rfl
  rw [PqxdhServerAuthBeaconFactor.beacon_afterRoot_run setup codec (fun kernel _ => pure (kernel, none))] at supported
  exact ⟨raw, frame, rawEq, decoded, PqxdhDeploymentHeadlineDctReceive.factored_keyed setup codec _ _ _ state final
    staged supported raw frame rawEq decoded frameOne⟩

/-- The native grouped answer of a known decapsulation result (item 2's `groupNativeN`, the CE known-root branch): a successful answer reads an R1 entry `v` through the private root interpreter and leaves the frame of the prepared response's application input committed in the final CTX cache under the sequence-one key of `v`. -/
theorem groupNative_keyed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (pending : PqxdhRegistrationJointKemPostSkeleton.Pending Response)
    (state final : NativeState KemSK) (staged : PqxdhBeaconPhase2Publication.Staged)
    (supported : (some staged, final) ∈ support
      ((PqxdhRegistrationJointKemPostSkeleton.groupNativeN setup codec candidate pending).run state)) :
    ∃ u v raw frame, final.1.cache u = some v ∧ codec.application pending.response = some raw ∧
      codec.frameRead raw = some frame ∧ KeyedCommit frame final.2.ctx (seqKey setup v).toList := by
  simp only [PqxdhRegistrationJointKemPostSkeleton.groupNativeN, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨root, middle⟩, rootMember, rest⟩ := supported
  unfold PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot at rootMember
  split at rootMember
  · rename_i input _
    obtain ⟨grows, _, v, rootEq, cached⟩ := sourceRoot_read setup.hmac input state _ rootMember
    simp only at rootEq
    subst rootEq
    simp only at rest
    change (some staged, final) ∈ support ((fun r => (r.1, (middle.1, { middle.2 with ctx := r.2.2 }))) <$>
      (simulateQ (PqxdhRegistrationJointKemPostSkeleton.tailNative setup codec)
        (PqxdhBeaconPhase2Shared.afterRoot codec.frameRead pending _)).run ((), middle.2.ctx)) at rest
    rw [support_map] at rest
    obtain ⟨inner, innerMember, same⟩ := rest
    rw [PqxdhRegistrationJointKemPostSkeleton.afterRoot_embed] at innerMember
    have stagedEq : inner.1 = some staged := congrArg Prod.fst same
    have finalEq : final = (middle.1, { middle.2 with ctx := inner.2.2 }) := (congrArg Prod.snd same).symm
    obtain ⟨raw, frame, application, decoded, keyed⟩ := consumer_keyed setup codec
      (PqxdhRegistrationJointKemPostSkeleton.embed pending) (PqxdhSecretInputKdf.expandRoot setup.hmac v) _ inner.2
      staged (by rw [← stagedEq]; exact innerMember)
    rw [PqxdhDeploymentHeadlineDctReceive.factor_key] at keyed
    refine ⟨PqxdhRefinement.absBytes input.bytes, v, raw, frame, ?_, application, decoded, ?_⟩
    · rw [finalEq]
      exact cached
    · rw [finalEq]
      exact keyed
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at rootMember
    rw [rootMember] at rest
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at rest

/-! ### Owner k's preparation with the challenge handle -/

/-- Owner k's preparation with the challenge handle (`preparationCE`): a prepared finish carries the response that the Phase 2 reader gives on the input bytes, and it carries the challenge marker only when that response's ciphertext is the challenge ciphertext (`ChallengeRead`): the marker is answered only on the challenge ciphertext, every other ciphertext gives a known decapsulation result. -/
theorem prepareCE_facts (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (control : beaconcrypt_core.pqxdh.BeaconInitSent) (identity : PqxdhJointIdentity.IdentitySeed)
    (prekey oneTime : PqxdhJointGapDh.ScalarBytes) (kem : PqxdhKemIndCca.MlKem768PublicKey × KemSK)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (raw : Pqxdh.Bytes)
    (pending : PqxdhRegistrationJointKemPostSkeleton.Pending Response)
    (member : some pending ∈ support (simulateQ (PqxdhDeploymentIdealSteps.preparationCE (Response := Response) setup
      codec challenge) (PqxdhBeaconPhase2Shared.prepare control identity prekey oneTime kem raw))) :
    codec.read2 raw = some pending.response ∧
      (pending.root.shared = .challenge → PqxdhDeploymentIdealBeacon.ChallengeRead codec challenge raw) := by
  simp only [PqxdhBeaconPhase2Shared.prepare, simulateQ_bind, mem_support_bind_iff] at member
  obtain ⟨inputs, inputsMember, member⟩ := member
  rcases inputs with _ | inputs
  · simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff, reduceCtorEq] at member
  obtain ⟨responseMember, ciphertextMember, sharedMember⟩ :=
    PqxdhDeploymentIdealBeaconFacts.collect_answers _ identity prekey oneTime kem raw inputs inputsMember
  simp only [PqxdhDeploymentIdealSteps.preparationCE, support_pure, Set.mem_singleton_iff] at responseMember
  simp only [PqxdhDeploymentIdealSteps.preparationCE, support_pure, Set.mem_singleton_iff] at ciphertextMember
  simp only [PqxdhBeaconPhase2Shared.afterInputs, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
  obtain ⟨_, -, found⟩ := member
  obtain ⟨metadata, -, rfl⟩ := Option.map_eq_some_iff.mp found.symm
  refine ⟨responseMember.symm, fun marked => ⟨inputs.ciphertext, ?_, ?_⟩⟩
  · rw [← responseMember, Option.bind_some, ← ciphertextMember]
  · change inputs.secrets.shared = .challenge at marked
    rw [marked] at sharedMember
    by_contra other
    simp only [PqxdhDeploymentIdealSteps.preparationCE, other, ↓reduceIte, support_map, Set.mem_image] at sharedMember
    obtain ⟨_, _, wrong⟩ := sharedMember
    cases ‹Option _› <;> simp at wrong

/-- The state-keeping lift of a probabilistic interpreter to the slot interface. -/
noncomputable def keepLift {κ σ : Type} {spec : OracleSpec κ} (impl : QueryImpl spec ProbComp) :
    QueryImpl spec (StateT σ (OracleComp PqxdhDeploymentIdealSlots.SlotSpec)) :=
  fun query current => (fun reply => (reply, current)) <$> PqxdhDeploymentIdealSteps.liftS (impl query)

/-- A program simulated by a state-keeping lift keeps the state and returns a value of the plain simulation. -/
theorem keepLift_run {κ σ α : Type} {spec : OracleSpec κ} (impl : QueryImpl spec ProbComp) (program : OracleComp spec α)
    (state : σ) (result : α × σ)
    (member : result ∈ support ((simulateQ (keepLift (σ := σ) impl) program).run state)) :
    result.2 = state ∧ result.1 ∈ support (simulateQ impl program) := by
  induction program using OracleComp.inductionOn generalizing result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨rfl, by simp⟩
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at member
      obtain ⟨⟨reply, middle⟩, first, rest⟩ := member
      change (reply, middle) ∈ support ((fun reply => (reply, state)) <$> PqxdhDeploymentIdealSteps.liftS (impl query))
        at first
      rw [support_map] at first
      obtain ⟨reply', replied, same⟩ := first
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      obtain ⟨stateEq, inner⟩ := ih reply' result rest
      refine ⟨stateEq, ?_⟩
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        mem_support_bind_iff]
      exact ⟨reply', OracleComp.mem_support_of_mem_support_liftComp _ _ _ replied, inner⟩

/-- Owner k's challenge finish (`finishChallenge`) on an input that is not `ChallengeRead`: a successful finish leaves an R1 entry `v` and the frame of the Phase 2 reading of the input committed in the final CTX cache under the sequence-one key of `v`. Only the challenge ciphertext gets the challenge marker (`prepareCE_facts`), so the grouped request is answered by the known-root branch (`groupCE_known`, `groupNative_keyed`). -/
theorem finishChallenge_keyed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (hidden : PqxdhServerAuthKeySchedule.Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (index : ℕ) (raw : Pqxdh.Bytes)
    (state : PqxdhRegistrationSchedule.State KemSK) (recorded : Option PqxdhDeploymentIdealSlots.Coord)
    (result : Option Pqxdh.Bytes × (PqxdhRegistrationSchedule.State KemSK × Option PqxdhDeploymentIdealSlots.Coord))
    (supported : result ∈ support ((PqxdhDeploymentIdealSteps.finishChallenge setup codec hidden challenge index raw).run
      (state, recorded)))
    (reply : Pqxdh.Bytes) (replied : result.1 = some reply)
    (other : ¬ PqxdhDeploymentIdealBeacon.ChallengeRead codec challenge raw) :
    ∃ u v frame, result.2.1.shared.1.cache u = some v ∧
      PqxdhServerAuthRecordPublicationEvent.frame codec raw = some frame ∧
      KeyedCommit frame result.2.1.shared.2.ctx (seqKey setup v).toList := by
  change result ∈ support (match state.owners[index]? with
    | none => pure (none, (state, recorded))
    | some owner => do
        let result ← (simulateQ (PqxdhDeploymentIdealSteps.ownerImplCE setup codec hidden challenge)
          (PqxdhDeploymentIdealSteps.groupedOwnerCE (Response := Response) raw owner)).run (state.shared, recorded)
        pure (result.1.1, (({ shared := result.2.1, owners := state.owners.set index result.1.2 } :
          PqxdhRegistrationSchedule.State KemSK), result.2.2))) at supported
  cases found : state.owners[index]? with
  | none =>
      rw [found] at supported
      simp only [support_pure, Set.mem_singleton_iff] at supported
      subst supported
      cases replied
  | some owner =>
      rw [found] at supported
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨ownerResult, ownerMember, rfl⟩ := supported
      simp only at replied
      unfold PqxdhDeploymentIdealSteps.groupedOwnerCE at ownerMember
      split at ownerMember
      · rename_i control prekey oneTime kem _
        simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at ownerMember
        obtain ⟨⟨prepared, afterPrep⟩, prepMember, ownerMember⟩ := ownerMember
        rw [← QueryImpl.simulateQ_compose] at prepMember
        have liftEq : (PqxdhDeploymentIdealSteps.ownerImplCE setup codec hidden challenge ∘ₛ
            (fun query => ((PqxdhDeploymentIdealSteps.OwnerSpecCE KemSK Response).query (.inl query) :
              OracleComp (PqxdhDeploymentIdealSteps.OwnerSpecCE KemSK Response) _))) =
            keepLift (PqxdhDeploymentIdealSteps.preparationCE setup codec challenge) := by
          funext query
          simp only [QueryImpl.apply_compose, simulateQ_spec_query, PqxdhDeploymentIdealSteps.ownerImplCE]
          rfl
        rw [liftEq] at prepMember
        obtain ⟨stateEq, prepSupport⟩ := keepLift_run _ _ _ _ prepMember
        simp only at stateEq prepSupport ownerMember
        subst stateEq
        cases prepared with
        | none =>
            simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at ownerMember
            rw [ownerMember, PqxdhDeploymentIdealBeaconFacts.finish_none] at replied
            cases replied
        | some pending =>
            obtain ⟨readEq, marker⟩ := prepareCE_facts challenge control owner.beacon.identity prekey oneTime kem setup
              codec raw pending prepSupport
            simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
              mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at ownerMember
            obtain ⟨⟨staged, afterGroup⟩, groupMember, rfl⟩ := ownerMember
            cases staged with
            | none =>
                rw [PqxdhDeploymentIdealBeaconFacts.finish_none] at replied
                cases replied
            | some staged =>
                cases shared : pending.root.shared with
                | challenge => exact absurd (marker shared) other
                | known secret =>
                    change (some staged, afterGroup) ∈ support ((PqxdhDeploymentIdealSteps.groupCE setup codec hidden
                      pending).run (state.shared, recorded)) at groupMember
                    rw [PqxdhDeploymentIdealSteps.groupCE_known setup codec hidden pending secret shared, support_map]
                      at groupMember
                    obtain ⟨native, nativeMember, same⟩ := groupMember
                    have nativeMember' := OracleComp.mem_support_of_mem_support_liftComp _ _ _ nativeMember
                    have stagedEq : native.1 = some staged := congrArg Prod.fst same
                    have afterEq : afterGroup = (native.2, recorded) := (congrArg Prod.snd same).symm
                    obtain ⟨u, v, raw', frame, cached, application, decoded, keyed⟩ :=
                      groupNative_keyed setup codec _ pending state.shared native.2 staged
                        (by rw [← stagedEq]; exact nativeMember')
                    refine ⟨u, v, frame, ?_, ?_, ?_⟩
                    · rw [afterEq]
                      exact cached
                    · simp only [PqxdhServerAuthRecordPublicationEvent.frame, readEq, application, decoded,
                        Option.bind_eq_bind, Option.bind_some]
                    · rw [afterEq]
                      exact keyed
      · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at ownerMember
        rw [ownerMember] at replied
        cases replied

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish.r1Grows_trans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish.r1Grows_trans

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish.nativeCtx_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish.nativeCtx_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish.sourceRoot_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish.sourceRoot_read

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish.callbacks_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish.callbacks_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish.run_callbacks_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish.run_callbacks_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish.tail_keyed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish.tail_keyed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish.owner_keyed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish.owner_keyed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish.scheduleFinish_keyed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish.scheduleFinish_keyed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish.consumer_keyed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish.consumer_keyed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish.groupNative_keyed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish.groupNative_keyed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish.prepareCE_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish.prepareCE_facts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish.keepLift_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish.keepLift_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish.finishChallenge_keyed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctFinish.finishChallenge_keyed
