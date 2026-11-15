-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhServerAuthNative
import BeaconcryptCore.Computational.PqxdhServerAuthRootObserved
import BeaconcryptCore.Computational.PqxdhCtxBirthdayPotential

/-!
# The transcript-hash collision term of the Server-authentication game

Both honest roles of the generic Server-authentication game `PqxdhServerAuthExperiment.gameState` compute their record associated data as `context87 ‖ BLAKE2b-512(T)` of the 2638-byte registration transcript `T`, with the same lazily sampled oracle `CtxRomAuth.ctxRandomOracle` that answers the adversary's `.hash` queries and every CTX commitment (design §4.3). Equal associated data then forces equal transcripts unless the final BLAKE2b cache holds two distinct inputs with one digest (VCVio's `CacheHasCollision`). This module bounds that event by an explicit birthday term.

- `reads Q qHash = qHash + 2·Q + 2` counts the BLAKE2b reads of one run: at most `qHash` adversary queries (`AuthBudget.hash`), at most two honest reads per Server build that consumes a pending token (the transcript hash and the one commitment of the first seal, `PqxdhServerRegistrationPublication.build_bound … .seal`, `RawCtxSourceSeal.sealInput_bound … .hash`), at most `Q` tokens (`AuthBudget.accept`), and at most two reads in the Beacon's single finish (the transcript hash and the one opening commitment, `RawCtxSourceOpen.raw_primitive_bounds`). Accept, HMAC, reveal and coin queries read nothing.
- `term Q qHash = C(reads Q qHash, 2)/2^512`.
- `gameState_bound`: on the final cache of the experiment the collision probability is at most `C(reads Q qHash, 2)/2^512`. The proof is the stopped birthday potential `PqxdhDeploymentHeadlineDctHash.drawPotential` over the native view `PqxdhServerAuthNative.nativeHandler` (`actual_state`), with the remaining reads `h + 2a + 2·pending + 2·initSent` reserved for `h` hash and `a` accept queries left, the pending tokens and the InitSent Beacon (`PqxdhCtxBirthdayPotential.expected_run_bounded_pair`). The potential is gated by the experiment's operational invariant `GameInv`, which every native step keeps (`handler_native`, `authHandler_step`).
- `collision`, `game_bound`, `game_collision_bound`: the same bound on the annotated R1 source game `PqxdhServerAuthRootExecution.game … false …`, transferred by `PqxdhServerAuthRootExecution.game_erase` (no loss), and its real-valued form on the Boolean observation `collision`.
- `ordered_bound`: the real-valued bound in production observation order, on `PqxdhServerAuthRootObserved.orderedGame … false …`, transferred by `PqxdhServerAuthRootObserved.observation_order` (an equality of output distributions).

The only hypothesis is the ordinary query budget `AuthBudget`. No assumption is used: BLAKE2b is the existing lazy random oracle and the bound follows from uniform sampling.
-/

open OracleComp OracleSpec ENNReal
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision
open OracleComp.ProgramLogic (wp)
open PqxdhDeploymentHeadlineDctHash (CtxColl drawPotential draw_step size_empty)
open PqxdhCtxBirthdayPotential
open PqxdhJointIdentity PqxdhJointGapDh
open PqxdhServerAuthExperiment PqxdhServerAuthNative

/-! ## The count and the term -/

/-- The BLAKE2b reads of one run: `qHash` adversary queries, two per consumed Server token (at most `Q`) and two for the Beacon's single finish. -/
def reads (Q qHash : Nat) : Nat := qHash + 2 * Q + 2

/-- The explicit birthday term of the transcript-hash collision. -/
noncomputable def term (Q qHash : Nat) : ℝ := ((reads Q qHash).choose 2 : ℝ) / 2 ^ 512

/-! ## One read of the shared oracle -/

/-- One read of the lazily sampled BLAKE2b oracle spends one reserved read of the stopped potential in expectation. -/
theorem oracle_read (H : ℕ) (cache : CtxRomAuth.CtxRO.QueryCache) (query : CtxRomAuth.CtxRO.Domain) :
    wp ((CtxRomAuth.ctxRandomOracle query).run cache) (fun result => drawPotential H 0 result.2) ≤
      drawPotential (H + 1) 0 cache := by
  have step := draw_step (H + 1) 0 cache query
  simp only [drawPotential_shift] at step
  exact step

/-- A step whose every outcome keeps the BLAKE2b cache leaves the potential unchanged. -/
theorem wp_keep {σ α : Type} (run : ProbComp (α × σ)) (view : σ → CtxRomAuth.CtxRO.QueryCache) (H : ℕ)
    (start : CtxRomAuth.CtxRO.QueryCache) (keep : ∀ result ∈ support run, view result.2 = start) :
    wp run (fun result => drawPotential H 0 (view result.2)) ≤ drawPotential H 0 start :=
  OracleComp.ProgramLogic.wp_le_const_of_support _ fun result supported => by rw [keep result supported]

/-- A returned value of a state computation is evaluated at its state. -/
theorem wp_statePure {σ α : Type} (value : α) (state : σ) (post : α × σ → ℝ≥0∞) :
    wp ((pure value : StateT σ ProbComp α) state) post = post (value, state) :=
  OracleComp.ProgramLogic.wp_pure _ _

/-- The native commitment/opening hash service is one read of the shared oracle. -/
theorem opening_read {A : Type} (c : Pqxdh.Crypto)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (bytes : Pqxdh.Bytes) (state : RawCtxSharedPrimitive.SharedState A) (H : ℕ) :
    wp ((RawCtxSharedPrimitive.nativeImpl c kdf (.inr (.inl bytes))).run state)
      (fun result => drawPotential H 0 result.2.2) ≤ drawPotential (H + 1) 0 state.2 := by
  change wp ((RawCtxSharedPrimitive.openingImpl c (.inl bytes)).run state) _ ≤ _
  simp only [RawCtxSharedPrimitive.openingImpl, StateT.run, OracleComp.ProgramLogic.wp_bind,
    OracleComp.ProgramLogic.wp_pure]
  exact oracle_read H state.2 ((), bytes)

/-! ## The Server's response tail -/

section Server
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- One sealing callback of the Server's tail makes at most one commitment read (`sealInput_bound`); AEAD and the frame writer are functional. -/
theorem seal_reads (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (input : RawCtxSourceSend.SealInput)
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) (H : ℕ) :
    wp ((nativeTail setup codec checks (.inl (.inr input))).run state) (fun result => drawPotential H 0 result.2.2) ≤
      drawPotential (H + 1) 0 state.2 := by
  simp only [nativeTail, QueryImpl.apply_compose, PqxdhServerRegistrationPublication.nativeAdapter,
    RawCtxSourceSeal.nativeAdapter]
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  refine PqxdhDeploymentHeadlineDctTools.expected_run_bounded _ (fun query => RawCtxSourceSeal.callKind query = .hash)
    (fun b state => drawPotential (H + b) 0 state.2) (fun b state => drawPotential_mono_cap (Nat.le_succ _) 0 state.2)
    ?_ ?_ (RawCtxSourceSeal.sealInput input) 1 (RawCtxSourceSeal.sealInput_bound input .hash) state
  · intro query state b hash
    rcases query with x | (bytes | frame)
    · simp [RawCtxSourceSeal.callKind] at hash
    · simp [QueryImpl.apply_compose, RawCtxSourceSeal.sealLift, PqxdhRegistrationProtocolState.registrationImpl,
        RawCtxMixedShared.sharedImpl, RawCtxMixedOwner.sendLift, RawCtxMixedShared.sharedAdapter]
      exact opening_read _ _ bytes state (H + b)
    · simp [RawCtxSourceSeal.callKind] at hash
  · intro query state b notHash
    rcases query with x | (bytes | frame)
    · simp [QueryImpl.apply_compose, RawCtxSourceSeal.sealLift, PqxdhRegistrationProtocolState.registrationImpl,
        RawCtxMixedShared.sharedImpl, RawCtxMixedOwner.sendLift, RawCtxMixedShared.sharedAdapter]
    · simp [RawCtxSourceSeal.callKind] at notHash
    · simp [QueryImpl.apply_compose, RawCtxSourceSeal.sealLift, PqxdhRegistrationProtocolState.registrationImpl,
        RawCtxMixedShared.sharedImpl, RawCtxMixedOwner.sendLift, RawCtxMixedShared.sharedAdapter]

/-- Any Server tail program with at most `n` sealing callbacks makes at most `n` BLAKE2b reads. -/
theorem tail_reads {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (work : OracleComp PqxdhServerRegistrationPublication.TailSpec α) (n : ℕ)
    (bounded : work.IsQueryBoundP (fun query => PqxdhServerRegistrationPublication.callKind query = .seal) n)
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) (H : ℕ) :
    wp ((simulateQ (tailImpl setup codec checks) work).run state) (fun result => drawPotential H 0 result.2.2) ≤
      drawPotential (H + n) 0 state.2 := by
  refine PqxdhDeploymentHeadlineDctTools.expected_run_bounded _ _
    (fun b state => drawPotential (H + b) 0 state.2) (fun b state => drawPotential_mono_cap (Nat.le_succ _) 0 state.2)
    ?_ ?_ work n bounded state
  · intro query state b sealing
    rcases query with (request | input) | request
    · simp [PqxdhServerRegistrationPublication.callKind] at sealing
    · simp only [tailImpl, StateT.run_bind, OracleComp.ProgramLogic.wp_bind]
      refine le_trans (OracleComp.ProgramLogic.wp_mono _ fun sealed => ?_) (seal_reads setup codec checks input state (H + b))
      by_cases present : sealed.1.isSome
      · simp [present]
      · simp [present]
    · cases request <;> simp [PqxdhServerRegistrationPublication.callKind, PqxdhServerRegistrationPublication.auxKind] at sealing
  · intro query state b notSeal
    rcases query with (request | input) | request
    · simp [tailImpl, nativeTail, QueryImpl.apply_compose, PqxdhServerRegistrationPublication.nativeAdapter,
        RawCtxSourceSeal.nativeAdapter, PqxdhRegistrationProtocolState.registrationImpl, RawCtxMixedShared.sharedImpl,
        RawCtxMixedOwner.sendLift, RawCtxMixedShared.sharedAdapter]
      change wp ((RawCtxSourceHkdf.kdfImpl setup.source request).run state) _ ≤ _
      rw [RawCtxSourceHkdf.kdf_step, OracleComp.ProgramLogic.wp_pure]
    · simp [PqxdhServerRegistrationPublication.callKind] at notSeal
    · cases request <;> simp [tailImpl, nativeTail, QueryImpl.apply_compose, PqxdhServerRegistrationPublication.nativeAdapter,
        PqxdhRegistrationProtocolState.registrationImpl, tailAux]

end Server

/-! ## The Beacon's opening tail -/

section Beacon
open PqxdhBeaconPhase2Publication (NativeTailSpec nativeTailAdapter)

/-- The opening-commitment reads of the Beacon's native tail: the hash service of the opening interface. -/
def isOpenHash {Resp : Type} : (NativeTailSpec Resp).Domain → Bool
  | .inl query => RawCtxSourceOpen.openingPredicate Sum.isLeft query
  | .inr _ => false

/-- After its root, the Beacon's tail (initial KDF, application getter, one raw receive) issues at most one opening commitment (`RawCtxSourceOpen.raw_primitive_bounds`). -/
theorem afterRoot_hash {Resp : Type} (decode : RawCtxReceive.FrameDecoder)
    (prepared : PqxdhBeaconPhase2Preparation.Prepared Resp) (root : PqxdhBeaconPhase2Preparation.Word32) :
    (simulateQ nativeTailAdapter (PqxdhBeaconPhase2Publication.afterRoot decode prepared root)).IsQueryBoundP
      (fun query => isOpenHash query = true) 1 := by
  unfold PqxdhBeaconPhase2Publication.afterRoot PqxdhBeaconPhase2Publication.initialRun
  simp only [bind_assoc, pure_bind, simulateQ_bind, simulateQ_spec_query, nativeTailAdapter]
  change (show OracleComp (NativeTailSpec Resp) (Option PqxdhBeaconPhase2Publication.Staged) from do
    let response ← (NativeTailSpec Resp).query
      (.inr (.initial (PqxdhInitialRatchetComplementarity.beaconPending root).request))
    let reply ← (NativeTailSpec Resp).query (.inr (.application prepared.response))
    simulateQ nativeTailAdapter (match reply with
      | none => pure none
      | some raw => do
        let result ← simulateQ PqxdhBeaconPhase2Publication.rawLift ((RawCtxWholeOwner.rawReceive decode raw).run
          (PqxdhBeaconPhase2Publication.localOwner (PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate)
            prepared.binding.associated_data (PqxdhBeaconPhase2Publication.normalInitial
              (PqxdhInitialRatchetComplementarity.beaconPending root) response)))
        pure (PqxdhBeaconPhase2Publication.afterOpening (PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate)
          prepared.binding.associated_data result.2.owner.kernel result.1))).IsQueryBoundP
      (fun query => isOpenHash query = true) 1
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr Nat.one_pos, fun response => ?_⟩
  simp only [isOpenHash, Bool.false_eq_true, ↓reduceIte]
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr Nat.one_pos, fun reply => ?_⟩
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases reply with
  | none => simp only [simulateQ_pure]; exact isQueryBoundP_pure _ _ _
  | some raw =>
      simp only [bind_pure_comp, simulateQ_map, PqxdhBeaconPhase2Bounds.native_raw_lift, isQueryBoundP_map_iff]
      apply RawCtxSourceOpen.simulate_bound PqxdhBeaconPhase2Publication.nativeRawLift
        (fun query => RawCtxSourceOpen.openingPredicate Sum.isLeft query = true) _ _ 1
        (RawCtxSourceOpen.raw_primitive_bounds decode raw _).1
      intro query
      exact (isQueryBoundP_query_iff (spec := NativeTailSpec Resp)
        (p := fun query => isOpenHash query = true) (.inl query) _).2 (fun hit => by simp only [isOpenHash] at hit; simp [hit])

/-- The whole Beacon tail, root request included, issues at most one opening commitment. -/
theorem tail_hash {Resp : Type} (decode : RawCtxReceive.FrameDecoder)
    (prepared : PqxdhBeaconPhase2Preparation.Prepared Resp) :
    (simulateQ nativeTailAdapter (PqxdhBeaconPhase2Publication.tail decode prepared)).IsQueryBoundP
      (fun query => isOpenHash query = true) 1 := by
  unfold PqxdhBeaconPhase2Publication.tail
  simp only [simulateQ_bind, simulateQ_spec_query, nativeTailAdapter]
  change (show OracleComp (NativeTailSpec Resp) (Option PqxdhBeaconPhase2Publication.Staged) from do
    let reply ← (NativeTailSpec Resp).query (.inr (.root prepared.candidate.root_key_input))
    simulateQ nativeTailAdapter (match reply with
      | none => pure none
      | some root => PqxdhBeaconPhase2Publication.afterRoot decode prepared root)).IsQueryBoundP
      (fun query => isOpenHash query = true) 1
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr Nat.one_pos, fun reply => ?_⟩
  simp only [isOpenHash, Bool.false_eq_true, ↓reduceIte]
  cases reply with
  | none => simp only [simulateQ_pure]; exact isQueryBoundP_pure _ _ _
  | some root => exact afterRoot_hash decode prepared root

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- A shared-cache callback whose every outcome keeps the cache leaves the native potential unchanged. -/
theorem nativeCtx_keep {Result : Type} (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp Result)
    (state : NativeState KemSK) (H : ℕ)
    (keep : ∀ result ∈ support (work.run ((), state.2.ctx)), result.2.2 = state.2.ctx) :
    wp ((nativeCtx work).run state) (fun result => drawPotential H 0 result.2.2.ctx) ≤ drawPotential H 0 state.2.ctx := by
  change wp ((fun result => (result.1, (state.1, { state.2 with ctx := result.2.2 }))) <$> work.run ((), state.2.ctx)) _ ≤ _
  rw [OracleComp.ProgramLogic.wp_map]
  exact wp_keep _ (fun shared : RawCtxSharedPrimitive.SharedState Unit => shared.2) H _ keep

/-- The Beacon's native tail makes at most one BLAKE2b read (its opening commitment); its root request reads the Extract table only. -/
theorem beaconTail_reads (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (publicValue : PublicChallenge)
    (original : PqxdhBeaconPhase2Preparation.Prepared Response) (state : NativeState KemSK) (H : ℕ) :
    wp ((nativeBeaconTail setup codec publicValue original).run state)
      (fun result => drawPotential H 0 result.2.2.ctx) ≤ drawPotential (H + 1) 0 state.2.ctx := by
  unfold nativeBeaconTail
  refine PqxdhDeploymentHeadlineDctTools.expected_run_bounded _ (fun query => isOpenHash query = true)
    (fun b state => drawPotential (H + b) 0 state.2.ctx) (fun b state => drawPotential_mono_cap (Nat.le_succ _) 0 _)
    ?_ ?_ _ 1 (tail_hash _ _) state
  · intro query state b hash
    rcases query with (request | (bytes | input)) | request
    · simp [isOpenHash, RawCtxSourceOpen.openingPredicate] at hash
    · change wp ((nativeCtx (beaconNative setup codec (.inl (.inr (.inl bytes))))).run state) _ ≤ _
      change wp ((fun result => (result.1, (state.1, { state.2 with ctx := result.2.2 }))) <$>
        (RawCtxSharedPrimitive.nativeImpl setup.source.crypto (RawCtxSourceHkdf.kdfImpl setup.source)
          (.inr (.inl bytes))).run ((), state.2.ctx)) _ ≤ _
      rw [OracleComp.ProgramLogic.wp_map]
      exact opening_read _ _ bytes ((), state.2.ctx) (H + b)
    · simp [isOpenHash, RawCtxSourceOpen.openingPredicate] at hash
    · simp [isOpenHash] at hash
  · intro query state b notHash
    rcases query with (request | (bytes | input)) | request
    · change wp ((nativeCtx (beaconNative setup codec (.inl (.inl request)))).run state) _ ≤ _
      refine nativeCtx_keep _ state _ fun result supported => ?_
      change result ∈ support ((RawCtxSourceHkdf.kdfImpl setup.source request).run ((), state.2.ctx)) at supported
      rw [RawCtxSourceHkdf.kdf_step, support_pure, Set.mem_singleton_iff] at supported
      rw [supported]
    · simp [isOpenHash, RawCtxSourceOpen.openingPredicate] at notHash
    · change wp ((nativeCtx (beaconNative setup codec (.inl (.inr (.inr input))))).run state) _ ≤ _
      refine nativeCtx_keep _ state _ fun result supported => ?_
      change result ∈ support ((RawCtxSharedPrimitive.openingImpl setup.source.crypto (.inr input)).run
        ((), state.2.ctx)) at supported
      simp only [RawCtxSharedPrimitive.openingImpl, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      rw [supported]
    · cases request with
      | root input =>
          change wp ((nativeBeaconRoot setup.hmac publicValue original input).run state) _ ≤ _
          refine wp_keep _ (fun native : NativeState KemSK => native.2.ctx) _ _ fun result supported => ?_
          simp only [nativeBeaconRoot, StateT.run_bind, mem_support_bind_iff] at supported
          obtain ⟨touched, logged, supported⟩ := supported
          simp only [nativeTouch, localState, StateT.run, support_pure, Set.mem_singleton_iff] at logged
          subst logged
          simp only [romRootReply, StateT.run_map, support_map, Set.mem_image] at supported
          obtain ⟨rooted, reached, rfl⟩ := supported
          simp only [StateT.run, romRootBytes, support_map, Set.mem_image] at reached
          obtain ⟨_, _, rfl⟩ := reached
          rfl
      | initial request =>
          change wp ((nativeCtx (beaconNative setup codec (.inr (.initial request)))).run state) _ ≤ _
          refine nativeCtx_keep _ state _ fun result supported => ?_
          simp only [beaconNative, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          rw [supported]
      | application response =>
          change wp ((nativeCtx (beaconNative setup codec (.inr (.application response)))).run state) _ ≤ _
          refine nativeCtx_keep _ state _ fun result supported => ?_
          simp only [beaconNative, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          rw [supported]

/-- The Beacon's native stage: a stateless preparation, then at most one BLAKE2b read in its tail. -/
theorem stage_reads (completedBinding : beaconcrypt_core.session.CompletedRegistrationBinding)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (seed : IdentitySeed) (scalar : ScalarBytes)
    (beaconSeed : IdentitySeed) (control : pqxdh.BeaconInitSent) (identity : Unit) (oneTime : Unit ⊕ ScalarBytes)
    (kem : KemSK) (raw : Pqxdh.Bytes) (state : NativeState KemSK) (H : ℕ) :
    wp ((nativeBeaconStage completedBinding setup codec seed scalar beaconSeed control identity oneTime kem raw).run state)
      (fun result => drawPotential H 0 result.2.2.ctx) ≤ drawPotential (H + 1) 0 state.2.ctx := by
  simp only [StateT.run]
  unfold nativeBeaconStage
  rw [nativeCoins_bind, OracleComp.ProgramLogic.wp_bind]
  refine OracleComp.ProgramLogic.wp_le_const_of_support _ fun prepared _ => ?_
  cases prepared with
  | none =>
      change wp (pure (none, state) : ProbComp _) _ ≤ _
      rw [OracleComp.ProgramLogic.wp_pure]
      exact drawPotential_mono_cap (Nat.le_succ H) 0 _
  | some original => exact beaconTail_reads setup codec _ original state H

end Beacon

/-! ## The Server's build and the Beacon's finish on the native state -/

section Steps
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- A build that consumes a pending token makes at most two BLAKE2b reads: the transcript hash and the one commitment of its tail (`build_bound … .seal`). -/
theorem build_reads (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (session : Nat) (payload : Option Pqxdh.Bytes) (state : NativeState KemSK) (H : ℕ) :
    wp ((nativeBuild setup codec checks session payload).run state)
      (fun result => drawPotential H 0 result.2.2.ctx) ≤ drawPotential (H + 2) 0 state.2.ctx := by
  simp only [StateT.run]
  unfold nativeBuild
  rw [nativeGet_bind]
  cases present : state.2.pending session with
  | none =>
      simp only
      rw [wp_statePure]
      exact drawPotential_mono_cap (by omega) 0 _
  | some token =>
      simp only
      cases guard : PqxdhServerRegistrationPublication.prehash state.2.server token.pending payload with
      | none =>
          simp only
          rw [nativeSet_bind, wp_statePure]
          exact drawPotential_mono_cap (by omega) 0 _
      | some candidate =>
          simp only
          rw [native_bind_run, OracleComp.ProgramLogic.wp_bind]
          change wp ((fun result => (result.1, (state.1, { state.2 with ctx := result.2 }))) <$>
            (CtxRomAuth.ctxRandomOracle ((), PqxdhTranscriptAd.transcript (PqxdhTranscriptAd.initOf token.init)
              (PqxdhTranscriptAd.serverResponse candidate))).run state.2.ctx) _ ≤ _
          rw [OracleComp.ProgramLogic.wp_map]
          have read := oracle_read (H + 1) state.2.ctx ((), PqxdhTranscriptAd.transcript
            (PqxdhTranscriptAd.initOf token.init) (PqxdhTranscriptAd.serverResponse candidate))
          refine le_trans (OracleComp.ProgramLogic.wp_mono _ fun hashed => ?_) read
          simp only [Function.comp, nativeGet_bind, nativeCoins_bind, OracleComp.ProgramLogic.wp_bind]
          refine le_trans (OracleComp.ProgramLogic.wp_mono _ fun tail => ?_) (tail_reads setup codec checks _ 1
            (PqxdhServerRegistrationPublication.build_bound _ _ _ _ _ _ _
              PqxdhServerRegistrationPublication.CallKind.seal) _ H)
          simp only [nativeSet_bind, wp_statePure, le_refl]

/-- The Beacon's finish makes at most two BLAKE2b reads: the transcript hash and the one opening commitment of its stage. -/
theorem finish_reads (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (seed : IdentitySeed)
    (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (raw : Pqxdh.Bytes) (state : NativeState KemSK) (H : ℕ) :
    wp ((nativeFinish setup codec seed scalar beaconSeed raw).run state)
      (fun result => drawPotential H 0 result.2.2.ctx) ≤ drawPotential (H + 2) 0 state.2.ctx := by
  simp only [StateT.run]
  unfold nativeFinish
  rw [nativeGet_bind]
  cases phase : state.2.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only
      cases retained : state.2.beaconInit with
      | none =>
          simp only
          rw [nativeSet_bind, wp_statePure]
          exact drawPotential_mono_cap (by omega) 0 _
      | some init =>
          cases decoded : responseOf codec raw with
          | none =>
              simp only
              rw [nativeSet_bind, wp_statePure]
              exact drawPotential_mono_cap (by omega) 0 _
          | some response =>
              simp only
              rw [native_bind_run, OracleComp.ProgramLogic.wp_bind]
              change wp ((fun result => (result.1, (state.1, { state.2 with ctx := result.2 }))) <$>
                (CtxRomAuth.ctxRandomOracle ((), PqxdhTranscriptAd.transcript (PqxdhTranscriptAd.initOf init)
                  response)).run state.2.ctx) _ ≤ _
              rw [OracleComp.ProgramLogic.wp_map]
              have read := oracle_read (H + 1) state.2.ctx ((), PqxdhTranscriptAd.transcript
                (PqxdhTranscriptAd.initOf init) response)
              refine le_trans (OracleComp.ProgramLogic.wp_mono _ fun hashed => ?_) read
              simp only [Function.comp, nativeGet_bind]
              rw [native_bind_run, OracleComp.ProgramLogic.wp_bind]
              refine le_trans (OracleComp.ProgramLogic.wp_mono _ fun staged => ?_)
                (stage_reads _ setup codec seed scalar beaconSeed control _ oneTime kem raw _ H)
              simp only [nativeGet_bind, nativeSet_bind, wp_statePure, le_refl]
  | _ =>
      simp only
      rw [wp_statePure]
      exact drawPotential_mono_cap (by omega) 0 _

end Steps

/-! ## Reserved reads -/

section Counts
variable {KemSK : Type}

/-- Weight of one pending-token slot. -/
def slotWeight {α : Type} : Option α → Nat
  | none => 0
  | some _ => 1

/-- Number of present slots below `limit`. -/
def pendingSlots {α : Type} (limit : Nat) (slots : Nat → Option α) : Nat :=
  ∑ index ∈ Finset.range limit, slotWeight (slots index)

/-- The pending Server tokens of the allocated sessions; each reserves two reads for its build. -/
def pendingTokens (state : GameState KemSK) : Nat := pendingSlots state.sessions state.pending

/-- Whether the Beacon is in the InitSent phase, which reserves two reads for its finish. -/
def initSentFlag (state : GameState KemSK) : Nat :=
  match state.beacon.beacon.phase with
  | .initSent _ _ _ _ => 1
  | _ => 0

/-- A new slot at the allocation index adds its own weight. -/
theorem pending_new {α : Type} (limit : Nat) (slots : Nat → Option α) (value : Option α) :
    pendingSlots (limit + 1) (Function.update slots limit value) = pendingSlots limit slots + slotWeight value := by
  unfold pendingSlots
  rw [Finset.sum_range_succ, Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro index member
  rw [Function.update_of_ne (Nat.ne_of_lt (Finset.mem_range.mp member))]

/-- A slot weighs at most one. -/
theorem slotWeight_le {α : Type} (value : Option α) : slotWeight value ≤ 1 := by
  cases value <;> simp [slotWeight]

/-- Clearing an allocated slot removes exactly its weight. -/
theorem pending_clear {α : Type} (limit : Nat) (slots : Nat → Option α) (index : Nat) (inside : index < limit) :
    pendingSlots limit (Function.update slots index none) + slotWeight (slots index) = pendingSlots limit slots := by
  unfold pendingSlots
  simp only [Function.apply_update (fun _ value => slotWeight value) slots index none,
    Finset.sum_update_of_mem (Finset.mem_range.mpr inside)]
  have split : (∑ i ∈ Finset.range limit, slotWeight (slots i)) = slotWeight (slots index) +
      ∑ i ∈ Finset.range limit \ {index}, slotWeight (slots i) := by
    simpa only [Function.update_eq_self] using Finset.sum_update_of_mem
      (Finset.mem_range.mpr inside) (fun i => slotWeight (slots i)) (slotWeight (slots index))
  rw [split]
  simp only [slotWeight, Nat.zero_add, Nat.add_comm]

/-- Exposing the next index adds at most that slot's weight. -/
theorem pending_extend {α : Type} (limit : Nat) (slots : Nat → Option α) :
    pendingSlots (limit + 1) slots = pendingSlots limit slots + slotWeight (slots limit) :=
  Finset.sum_range_succ _ _

/-- Outside the InitSent phase the flag is zero. -/
theorem initSentFlag_zero (state : GameState KemSK) (inactive : ¬ InitSent state) : initSentFlag state = 0 := by
  unfold initSentFlag
  split
  · rename_i control prekey oneTime kem phase
    exact absurd ⟨control, prekey, oneTime, kem, phase⟩ inactive
  · rfl

/-- The flag is at most one. -/
theorem initSentFlag_le (state : GameState KemSK) : initSentFlag state ≤ 1 := by
  unfold initSentFlag
  split <;> omega

/-- The stopped birthday potential with the reads reserved for `h` hash and `a` accept queries left, the pending tokens and the InitSent Beacon. -/
noncomputable def reserved (h a : Nat) (state : GameState KemSK) : ℝ≥0∞ :=
  drawPotential (h + 2 * a + 2 * pendingTokens state + 2 * initSentFlag state) 0 state.ctx

end Counts

/-! ## Support facts of the experiment's oracles -/

section Shapes
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- An accept allocates one index, keeps the BLAKE2b cache and the Beacon, and adds at most its own token. -/
theorem accept_shape (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (raw : Pqxdh.Bytes) (state : GameState KemSK)
    (result : Option Nat × GameState KemSK)
    (supported : result ∈ support ((acceptOracle setup codec checks publicValue raw).run state)) :
    result.2.sessions = state.sessions + 1 ∧ result.2.ctx = state.ctx ∧ result.2.beacon = state.beacon ∧
      (result.2.pending = state.pending ∨ ∃ token,
        result.2.pending = Function.update state.pending state.sessions (some token)) := by
  simp only [acceptOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  obtain ⟨collected, lifted, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
  obtain ⟨_, same⟩ := liftCoins_mem _ _ _ lifted
  simp only [StateT.run_set, pure_bind, same] at supported
  cases hc : collected.1.1 with
  | none =>
      simp only [hc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨rfl, rfl, rfl, Or.inl rfl⟩
  | some input =>
      simp only [hc, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨returned, derived, supported⟩ := supported
      obtain ⟨consumed, extra, eq, _, _⟩ := client_run state.sessions (binding setup publicValue) input _ returned derived
      have sessionsEq : returned.2.sessions = state.sessions + 1 := by rw [eq]
      have pendingEq : returned.2.pending = state.pending := by rw [eq]
      have ctxEq : returned.2.ctx = state.ctx := by rw [eq]
      have beaconEq : returned.2.beacon = state.beacon := by rw [eq]
      rcases returned with ⟨outcome, after⟩
      dsimp only at sessionsEq pendingEq ctxEq beaconEq
      rcases outcome with (_ | token) | error | _
      all_goals simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at supported
      all_goals subst supported
      · exact ⟨sessionsEq, ctxEq, beaconEq, Or.inl pendingEq⟩
      · exact ⟨sessionsEq, ctxEq, beaconEq, Or.inr ⟨token, by simp only [pendingEq]⟩⟩
      · exact ⟨sessionsEq, ctxEq, beaconEq, Or.inl pendingEq⟩
      · exact ⟨sessionsEq, ctxEq, beaconEq, Or.inl pendingEq⟩

/-- A build keeps the session counter and the Beacon and disposes of exactly the requested token. -/
theorem build_shape (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (session : Nat) (payload : Option Pqxdh.Bytes) (state : GameState KemSK)
    (result : Option PqxdhServerRegistrationPublication.Response × GameState KemSK)
    (supported : result ∈ support ((buildOracle setup codec checks session payload).run state)) :
    result.2.sessions = state.sessions ∧ result.2.pending = Function.update state.pending session none ∧
      result.2.beacon = state.beacon := by
  simp only [buildOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases hp : state.pending session with
  | none =>
      simp only [hp, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨rfl, by rw [← hp, Function.update_eq_self], rfl⟩
  | some token =>
      simp only [hp] at supported
      cases hpre : PqxdhServerRegistrationPublication.prehash state.server token.pending payload with
      | none =>
          simp only [hpre, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at supported
          subst supported
          exact ⟨rfl, rfl, rfl⟩
      | some candidate =>
          simp only [hpre, StateT.run_bind, mem_support_bind_iff] at supported
          obtain ⟨hashed, hashRun, supported⟩ := supported
          obtain ⟨hashEq, _, _⟩ := hashOracle_grows _ state hashed hashRun
          simp only [StateT.run_get] at supported
          obtain ⟨current, currentRun, supported⟩ := supported
          rw [support_pure, Set.mem_singleton_iff] at currentRun
          subst currentRun
          obtain ⟨tail, lifted, supported⟩ := supported
          obtain ⟨_, same⟩ := liftCoins_mem _ _ _ lifted
          simp only [same, StateT.run_set, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          obtain ⟨_, rfl, rfl⟩ := supported
          rw [hashEq]
          exact ⟨rfl, rfl, rfl⟩

/-- The Beacon's finish keeps the session counter and every pending Server token. -/
theorem finish_shape (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (raw : Pqxdh.Bytes)
    (state : GameState KemSK) (result : Option Pqxdh.Bytes × GameState KemSK)
    (supported : result ∈ support ((finishOracle setup codec publicValue beaconSeed raw).run state)) :
    result.2.sessions = state.sessions ∧ result.2.pending = state.pending := by
  simp only [finishOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases hphase : state.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [hphase] at supported
      rcases hinit : state.beaconInit with _ | init <;> rcases hresp : responseOf codec raw with _ | response
      all_goals simp only [hinit, hresp] at supported
      rotate_left 3
      · simp only [StateT.run_bind, mem_support_bind_iff] at supported
        obtain ⟨hashed, hashRun, supported⟩ := supported
        obtain ⟨hashEq, _, _⟩ := hashOracle_grows _ state hashed hashRun
        simp only [StateT.run_get] at supported
        obtain ⟨current, currentRun, supported⟩ := supported
        rw [support_pure, Set.mem_singleton_iff] at currentRun
        subst currentRun
        obtain ⟨staged, stageRun, supported⟩ := supported
        simp only [StateT.run_set, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at supported
        obtain ⟨_, rfl, _, rfl, rfl⟩ := supported
        rw [hashEq] at stageRun
        obtain ⟨cache, extra, stagedEq, _⟩ := stage_run _ setup codec beaconSeed publicValue control _ oneTime kem raw _
          staged stageRun
        rw [stagedEq]
        exact ⟨rfl, rfl⟩
      all_goals
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
          Set.mem_singleton_iff] at supported
        subst supported
        exact ⟨rfl, rfl⟩
  | _ =>
      simp only [hphase, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨rfl, rfl⟩

/-- Coins, public HMAC and reveal keep the BLAKE2b cache, the pending tokens, the session counter and the Beacon. -/
theorem quiet_shape (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (query : ServerAuthSpec.Domain)
    (notHash : ¬ IsHashQuery query) (notAccept : ¬ IsAcceptQuery query)
    (notBuild : ∀ index payload, query ≠ .inr (.build index payload)) (notFinish : ∀ raw, query ≠ .inr (.finish raw))
    (state : GameState KemSK) (result : ServerAuthSpec.Range query × GameState KemSK)
    (supported : result ∈ support ((authHandler setup codec checks publicValue beaconSeed query).run state)) :
    result.2.ctx = state.ctx ∧ result.2.pending = state.pending ∧ result.2.sessions = state.sessions ∧
      result.2.beacon = state.beacon := by
  rcases query with coin | query
  · rw [forward_support _ _ _ supported]
    exact ⟨rfl, rfl, rfl, rfl⟩
  cases query with
  | accept raw => exact (notAccept trivial).elim
  | build index payload => exact (notBuild index payload rfl).elim
  | finish raw => exact (notFinish raw rfl).elim
  | hmac key message =>
      change result ∈ support ((hmacOracle key message).run state) at supported
      simp only [hmacOracle] at supported
      split_ifs at supported
      · obtain ⟨middle, first, rest⟩ := run_bind_support _ _ _ _ supported
        rw [record_run, support_pure, Set.mem_singleton_iff] at first
        subst first
        rw [forward_support _ _ _ rest]
        exact ⟨rfl, rfl, rfl, rfl⟩
      · rw [forward_support _ _ _ supported]
        exact ⟨rfl, rfl, rfl, rfl⟩
  | hash bytes => exact (notHash trivial).elim
  | reveal keyId =>
      change result ∈ support (pure _ : OracleComp PqxdhJointDhExtractRoot.RootSpec _) at supported
      rw [support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨rfl, rfl, rfl, rfl⟩

end Shapes

/-! ## The gated potential on the native view -/

section Gate
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

open Classical in
/-- The reserved-read potential on states that satisfy the experiment's invariant, and `⊤` elsewhere (unreachable). -/
noncomputable def potential (Reader Response : Type) (setup : Setup baseSpec KemSK) (publicValue : PublicChallenge)
    (h a : Nat) (state : NativeState KemSK) : ℝ≥0∞ :=
  if GameInv Reader Response setup publicValue state.2 then reserved h a state.2 else ⊤

/-- The potential is monotone in the remaining hash budget. -/
theorem potential_mono_hash (Reader Response : Type) (setup : Setup baseSpec KemSK) (publicValue : PublicChallenge)
    (h a : Nat) (state : NativeState KemSK) :
    potential Reader Response setup publicValue h a state ≤ potential Reader Response setup publicValue (h + 1) a state := by
  unfold potential reserved
  split_ifs
  · exact drawPotential_mono_cap (by omega) 0 _
  · exact le_rfl

/-- The potential is monotone in the remaining accept budget. -/
theorem potential_mono_accept (Reader Response : Type) (setup : Setup baseSpec KemSK) (publicValue : PublicChallenge)
    (h a : Nat) (state : NativeState KemSK) :
    potential Reader Response setup publicValue h a state ≤ potential Reader Response setup publicValue h (a + 1) state := by
  unfold potential reserved
  split_ifs
  · exact drawPotential_mono_cap (by omega) 0 _
  · exact le_rfl

end Gate

section Native
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed)

/-- On a reached state, a native outcome is an outcome of the original handler (`handler_native`, `evaluate_support`). -/
theorem native_support (query : ServerAuthSpec.Domain) (state : NativeState KemSK)
    (invariant : GameInv Reader Response setup (challenge setup.joint setup.dh seed scalar) state.2)
    (result : ServerAuthSpec.Range query × NativeState KemSK)
    (supported : result ∈ support ((nativeHandler setup codec checks seed scalar beaconSeed query).run state)) :
    (result.1, result.2.2) ∈ support
      ((authHandler setup codec checks (challenge setup.joint setup.dh seed scalar) beaconSeed query).run state.2) := by
  change result ∈ support (nativeHandler setup codec checks seed scalar beaconSeed query state) at supported
  rw [← handler_native setup codec checks seed scalar beaconSeed query state invariant] at supported
  exact evaluate_support setup seed scalar _ state result supported

/-- On a reached state the gate is open after every native step. -/
theorem gate (query : ServerAuthSpec.Domain) (state : NativeState KemSK)
    (invariant : GameInv Reader Response setup (challenge setup.joint setup.dh seed scalar) state.2) (h a : Nat) :
    wp ((nativeHandler setup codec checks seed scalar beaconSeed query).run state)
        (fun result => potential Reader Response setup (challenge setup.joint setup.dh seed scalar) h a result.2) ≤
      wp ((nativeHandler setup codec checks seed scalar beaconSeed query).run state)
        (fun result => reserved h a result.2.2) := by
  refine OracleComp.ProgramLogic.wp_mono_of_support _ fun result supported => ?_
  have kept := (authHandler_step codec checks beaconSeed query state.2 _
    (native_support setup codec checks seed scalar beaconSeed query state invariant result supported)).1 invariant
  simp only [potential, kept, ↓reduceIte, le_refl]

/-- A hash query spends one reserved read. -/
theorem hash_step (bytes : Pqxdh.Bytes) (state : NativeState KemSK) (h a : Nat) :
    wp ((nativeHandler setup codec checks seed scalar beaconSeed (.inr (.hash bytes))).run state)
        (fun result => potential Reader Response setup (challenge setup.joint setup.dh seed scalar) h a result.2) ≤
      potential Reader Response setup (challenge setup.joint setup.dh seed scalar) (h + 1) a state := by
  by_cases invariant : GameInv Reader Response setup (challenge setup.joint setup.dh seed scalar) state.2
  · refine le_trans (gate setup codec checks seed scalar beaconSeed _ state invariant h a) ?_
    simp only [potential, invariant, ↓reduceIte]
    change wp ((fun result => (result.1, (state.1, { state.2 with ctx := result.2 }))) <$>
      (CtxRomAuth.ctxRandomOracle ((), bytes)).run state.2.ctx) _ ≤ _
    rw [OracleComp.ProgramLogic.wp_map]
    have read := oracle_read (h + 2 * a + 2 * pendingTokens state.2 + 2 * initSentFlag state.2) state.2.ctx ((), bytes)
    unfold reserved
    rw [show h + 1 + 2 * a + 2 * pendingTokens state.2 + 2 * initSentFlag state.2 =
      h + 2 * a + 2 * pendingTokens state.2 + 2 * initSentFlag state.2 + 1 by omega]
    exact read
  · simp only [potential, invariant, ↓reduceIte]
    exact le_top

/-- An accept reads nothing and moves two reserved reads from the accept budget to its pending token. -/
theorem accept_step (raw : Pqxdh.Bytes) (state : NativeState KemSK) (h a : Nat) :
    wp ((nativeHandler setup codec checks seed scalar beaconSeed (.inr (.accept raw))).run state)
        (fun result => potential Reader Response setup (challenge setup.joint setup.dh seed scalar) h a result.2) ≤
      potential Reader Response setup (challenge setup.joint setup.dh seed scalar) h (a + 1) state := by
  by_cases invariant : GameInv Reader Response setup (challenge setup.joint setup.dh seed scalar) state.2
  · refine le_trans (gate setup codec checks seed scalar beaconSeed _ state invariant h a) ?_
    simp only [potential, invariant, ↓reduceIte]
    refine OracleComp.ProgramLogic.wp_le_const_of_support _ fun result supported => ?_
    obtain ⟨sessionsEq, ctxEq, beaconEq, pendingEq⟩ := accept_shape setup codec checks _ raw state.2 (result.1, result.2.2)
      (native_support setup codec checks seed scalar beaconSeed _ state invariant result supported)
    dsimp only at sessionsEq ctxEq beaconEq pendingEq
    have tokens : pendingTokens result.2.2 ≤ pendingTokens state.2 + 1 := by
      rcases pendingEq with old | ⟨token, installed⟩
      · simp only [pendingTokens, sessionsEq, old, pending_extend]
        exact Nat.add_le_add_left (slotWeight_le _) _
      · simp only [pendingTokens, sessionsEq, installed, pending_new, slotWeight, le_refl]
    have flag : initSentFlag result.2.2 = initSentFlag state.2 := by
      unfold initSentFlag
      rw [beaconEq]
    unfold reserved
    rw [ctxEq, flag]
    exact drawPotential_mono_cap (by omega) 0 _
  · simp only [potential, invariant, ↓reduceIte]
    exact le_top

/-- A build spends the two reads reserved by the token it consumes; without a token it changes nothing. -/
theorem build_step (session : Nat) (payload : Option Pqxdh.Bytes) (state : NativeState KemSK) (h a : Nat) :
    wp ((nativeHandler setup codec checks seed scalar beaconSeed (.inr (.build session payload))).run state)
        (fun result => potential Reader Response setup (challenge setup.joint setup.dh seed scalar) h a result.2) ≤
      potential Reader Response setup (challenge setup.joint setup.dh seed scalar) h a state := by
  by_cases invariant : GameInv Reader Response setup (challenge setup.joint setup.dh seed scalar) state.2
  · refine le_trans (gate setup codec checks seed scalar beaconSeed _ state invariant h a) ?_
    simp only [potential, invariant, ↓reduceIte]
    change wp ((nativeBuild setup codec checks session payload).run state) (fun result => reserved h a result.2.2) ≤ _
    cases present : state.2.pending session with
    | none =>
        change wp (nativeBuild setup codec checks session payload state) _ ≤ _
        unfold nativeBuild
        rw [nativeGet_bind]
        simp only [present]
        rw [wp_statePure]
    | some token =>
        have tokens := pending_clear state.2.sessions state.2.pending session
          (invariant.pendingBelow session token present)
        rw [present] at tokens
        simp only [slotWeight] at tokens
        refine le_trans (le_trans (OracleComp.ProgramLogic.wp_mono_of_support _ fun result supported => ?_)
          (build_reads setup codec checks session payload state
            (h + 2 * a + 2 * (pendingTokens state.2 - 1) + 2 * initSentFlag state.2))) ?_
        · obtain ⟨sessionsEq, pendingEq, beaconEq⟩ := build_shape setup codec checks session payload state.2
            (result.1, result.2.2) (native_support setup codec checks seed scalar beaconSeed (.inr (.build session payload))
              state invariant result supported)
          dsimp only at sessionsEq pendingEq beaconEq
          have flag : initSentFlag result.2.2 = initSentFlag state.2 := by
            unfold initSentFlag
            rw [beaconEq]
          have count : pendingTokens result.2.2 = pendingTokens state.2 - 1 := by
            simp only [pendingTokens, sessionsEq, pendingEq]
            omega
          simp only [reserved, flag, count, le_refl]
        · have positive : 1 ≤ pendingTokens state.2 := by
            simp only [pendingTokens]
            omega
          unfold reserved
          rw [show h + 2 * a + 2 * (pendingTokens state.2 - 1) + 2 * initSentFlag state.2 + 2 =
            h + 2 * a + 2 * pendingTokens state.2 + 2 * initSentFlag state.2 by omega]
  · simp only [potential, invariant, ↓reduceIte]
    exact le_top

/-- The Beacon's finish spends the two reads reserved by the InitSent phase; outside it, it changes nothing. -/
theorem finish_step (raw : Pqxdh.Bytes) (state : NativeState KemSK) (h a : Nat) :
    wp ((nativeHandler setup codec checks seed scalar beaconSeed (.inr (.finish raw))).run state)
        (fun result => potential Reader Response setup (challenge setup.joint setup.dh seed scalar) h a result.2) ≤
      potential Reader Response setup (challenge setup.joint setup.dh seed scalar) h a state := by
  by_cases invariant : GameInv Reader Response setup (challenge setup.joint setup.dh seed scalar) state.2
  · refine le_trans (gate setup codec checks seed scalar beaconSeed _ state invariant h a) ?_
    simp only [potential, invariant, ↓reduceIte]
    change wp ((nativeFinish setup codec seed scalar beaconSeed raw).run state) (fun result => reserved h a result.2.2) ≤ _
    by_cases active : InitSent state.2
    · have flag : initSentFlag state.2 = 1 := by
        obtain ⟨control, prekey, oneTime, kem, phase⟩ := active
        unfold initSentFlag
        rw [phase]
      refine le_trans (le_trans (OracleComp.ProgramLogic.wp_mono_of_support _ fun result supported => ?_)
        (finish_reads setup codec seed scalar beaconSeed raw state (h + 2 * a + 2 * pendingTokens state.2))) ?_
      · have gameSupported := native_support setup codec checks seed scalar beaconSeed (.inr (.finish raw)) state
          invariant result supported
        obtain ⟨sessionsEq, pendingEq⟩ := finish_shape setup codec _ beaconSeed raw state.2 _ gameSupported
        obtain ⟨_, _, _, inactive, _⟩ := PqxdhServerAuthExperiment.finish_step codec beaconSeed raw state.2 _
          gameSupported
        dsimp only at sessionsEq pendingEq inactive
        have count : pendingTokens result.2.2 = pendingTokens state.2 := by
          simp only [pendingTokens, sessionsEq, pendingEq]
        simp only [reserved, count, initSentFlag_zero _ inactive, Nat.mul_zero, Nat.add_zero, le_refl]
      · simp only [reserved, flag, Nat.mul_one, le_refl]
    · refine OracleComp.ProgramLogic.wp_le_const_of_support _ fun result supported => ?_
      obtain ⟨_, _, _, _, same⟩ := PqxdhServerAuthExperiment.finish_step codec beaconSeed raw state.2 _
        (native_support setup codec checks seed scalar beaconSeed (.inr (.finish raw)) state invariant result supported)
      have unchanged := same active
      dsimp only at unchanged
      rw [unchanged]
  · simp only [potential, invariant, ↓reduceIte]
    exact le_top

/-- Coins, public HMAC and reveal read nothing and keep every reserved read. -/
theorem quiet_step (query : ServerAuthSpec.Domain) (notHash : ¬ IsHashQuery query) (notAccept : ¬ IsAcceptQuery query)
    (notBuild : ∀ index payload, query ≠ .inr (.build index payload)) (notFinish : ∀ raw, query ≠ .inr (.finish raw))
    (state : NativeState KemSK) (h a : Nat) :
    wp ((nativeHandler setup codec checks seed scalar beaconSeed query).run state)
        (fun result => potential Reader Response setup (challenge setup.joint setup.dh seed scalar) h a result.2) ≤
      potential Reader Response setup (challenge setup.joint setup.dh seed scalar) h a state := by
  by_cases invariant : GameInv Reader Response setup (challenge setup.joint setup.dh seed scalar) state.2
  · refine le_trans (gate setup codec checks seed scalar beaconSeed _ state invariant h a) ?_
    simp only [potential, invariant, ↓reduceIte]
    refine OracleComp.ProgramLogic.wp_le_const_of_support _ fun result supported => ?_
    obtain ⟨ctxEq, pendingEq, sessionsEq, beaconEq⟩ := quiet_shape setup codec checks _ beaconSeed query notHash
      notAccept notBuild notFinish state.2 _
      (native_support setup codec checks seed scalar beaconSeed _ state invariant result supported)
    dsimp only at ctxEq pendingEq sessionsEq beaconEq
    have flag : initSentFlag result.2.2 = initSentFlag state.2 := by
      unfold initSentFlag
      rw [beaconEq]
    simp only [reserved, pendingTokens, ctxEq, pendingEq, sessionsEq, flag, le_refl]
  · simp only [potential, invariant, ↓reduceIte]
    exact le_top

end Native

/-! ## The bound on the final cache -/

section Bound
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The transcript-hash collision on the final BLAKE2b cache of the Server-authentication experiment has probability at most `C(qHash + 2Q + 2, 2)/2^512`, under the ordinary query budget only. -/
theorem gameState_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) (Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash) :
    Pr{let result ← PqxdhServerAuthExperiment.gameState setup codec checks revealSeed adversary}[
        CacheHasCollision result.2.2.1.ctx] ≤
      ((reads Q qHash).choose 2 : ℝ≥0∞) / 2 ^ 512 := by
  classical
  rw [← actual_state, OracleComp.ProgramLogic.prEvent_eq_wp_indicator]
  simp only [actualState, nativeBody, OracleComp.ProgramLogic.wp_bind, OracleComp.ProgramLogic.wp_pure,
    OracleComp.ProgramLogic.wp_map]
  refine OracleComp.ProgramLogic.wp_le_const_of_support _ fun seed _ => ?_
  refine OracleComp.ProgramLogic.wp_le_const_of_support _ fun scalar _ => ?_
  refine OracleComp.ProgramLogic.wp_le_const_of_support _ fun beaconSeed _ => ?_
  refine OracleComp.ProgramLogic.wp_le_const_of_support _ fun oneTime _ => ?_
  refine OracleComp.ProgramLogic.wp_le_const_of_support _ fun keys _ => ?_
  refine OracleComp.ProgramLogic.wp_le_const_of_support _ fun published supported => ?_
  have invariant := inv_initial setup codec beaconSeed (challenge setup.joint setup.dh seed scalar) oneTime keys.1 keys.2
    published supported
  refine le_trans (OracleComp.ProgramLogic.wp_mono _ fun result => ?_) (le_trans
    (expected_run_bounded_pair (nativeHandler setup codec checks seed scalar beaconSeed) IsHashQuery IsAcceptQuery
      (potential Reader Response setup (challenge setup.joint setup.dh seed scalar))
      (potential_mono_hash Reader Response setup _) (potential_mono_accept Reader Response setup _) ?_ ?_ ?_ _ qHash Q
      (budget.hash _) (budget.accept _) _) ?_)
  · simp only [Function.comp]
    split_ifs with collision
    · unfold potential
      split_ifs
      · unfold reserved drawPotential
        simp only [Nat.zero_le, ↓reduceIte, (cacheHasCollision_iff_ctxColl _).1 collision]
        exact le_self_add
      · exact le_top
    · exact zero_le
  · intro query state h a hash
    rcases query with coin | query
    · exact hash.elim
    cases query with
    | hash bytes => exact hash_step setup codec checks seed scalar beaconSeed bytes state h a
    | _ => exact hash.elim
  · intro query state h a notHash accept
    rcases query with coin | query
    · exact accept.elim
    cases query with
    | accept raw => exact accept_step setup codec checks seed scalar beaconSeed raw state h a
    | _ => exact accept.elim
  · intro query state h a notHash notAccept
    rcases query with coin | query
    · exact quiet_step setup codec checks seed scalar beaconSeed _ notHash notAccept
        (fun _ _ same => by cases same) (fun _ same => by cases same) state h a
    cases query with
    | accept raw => exact (notAccept trivial).elim
    | build session payload => exact build_step setup codec checks seed scalar beaconSeed session payload state h a
    | finish raw => exact finish_step setup codec checks seed scalar beaconSeed raw state h a
    | hmac key message =>
        exact quiet_step setup codec checks seed scalar beaconSeed _ notHash notAccept
          (fun _ _ same => by cases same) (fun _ same => by cases same) state h a
    | hash bytes => exact (notHash trivial).elim
    | reveal keyId =>
        exact quiet_step setup codec checks seed scalar beaconSeed _ notHash notAccept
          (fun _ _ same => by cases same) (fun _ same => by cases same) state h a
  · have empty : pendingTokens (initialGameState setup (challenge setup.joint setup.dh seed scalar) published.1.2
        published.2) = 0 := by
      simp [pendingTokens, pendingSlots, initialGameState]
    have flag := initSentFlag_le (initialGameState setup (challenge setup.joint setup.dh seed scalar) published.1.2
      published.2)
    have notColl : ¬ CtxColl (∅ : CtxRomAuth.CtxRO.QueryCache) := by
      rintro ⟨y, z, d, -, found, -⟩
      cases found
    simp only [potential, invariant, ↓reduceIte, reserved, empty]
    refine le_trans (drawPotential_mono_cap (H' := reads Q qHash) (by unfold reads; omega) 0 _) (le_of_eq ?_)
    change drawPotential _ 0 ∅ = _
    simp only [drawPotential, Nat.zero_le, ↓reduceIte, notColl, Nat.sub_zero, size_empty, zero_mul, zero_add,
      ENNReal.div_eq_inv_mul, mul_comm]

end Bound

/-! ## Transfer to the annotated R1 source game -/

section Source
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The transcript-hash collision of one annotated source outcome: its final shared BLAKE2b cache holds two distinct inputs with one digest. -/
noncomputable def collision (result : PqxdhServerAuthRootExecution.Outcome KemSK) : Bool :=
  @decide (CacheHasCollision result.state.1.ctx) (Classical.propDecidable _)

/-- The collision bound on the annotated R1 source game: the annotations erase to the experiment (`PqxdhServerAuthRootExecution.game_erase`), whose final cache is bounded by `gameState_bound`. -/
theorem game_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash) :
    Pr{let result ← PqxdhServerAuthRootExecution.game setup codec checks false adversary}[
        CacheHasCollision result.state.1.ctx] ≤
      ((reads Q qHash).choose 2 : ℝ≥0∞) / 2 ^ 512 := by
  have bound := gameState_bound setup codec checks false adversary Q qH qHash budget
  rw [← PqxdhServerAuthRootExecution.game_erase, prEvent_map] at bound
  exact bound

/-- The real-valued form of `game_bound` on the Boolean observation `collision` of the annotated source game. -/
theorem game_collision_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash) :
    (𝒟[collision <$> PqxdhServerAuthRootExecution.game setup codec checks false adversary] {true}).toReal ≤
      term Q qHash := by
  have finite : ((reads Q qHash).choose 2 : ℝ≥0∞) / 2 ^ 512 ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (pow_ne_zero _ two_ne_zero)
  have real := ENNReal.toReal_mono finite (game_bound setup codec checks adversary Q qH qHash budget)
  rw [← prEvent_eq_evalDist_singleton _ true, prEvent_map]
  simpa only [Function.comp_def, collision, decide_eq_true_eq, term, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat] using real

/-- The transcript-hash collision bound in production observation order (`PqxdhServerAuthRootObserved.observation_order`). -/
theorem ordered_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash) :
    (𝒟[collision <$> PqxdhServerAuthRootObserved.orderedGame setup codec checks false adversary] {true}).toReal ≤
      term Q qHash := by
  rw [← PqxdhServerAuthRootObserved.observation_order setup codec checks false adversary collision]
  exact game_collision_bound setup codec checks adversary Q qH qHash budget

end Source

end BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision

-- Axiom guards (generated from kernel output)
/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.reads' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.reads

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.term' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.term

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.oracle_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.oracle_read

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.wp_keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.wp_keep

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.wp_statePure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.wp_statePure

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.opening_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.opening_read

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.seal_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.seal_reads

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.tail_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.tail_reads

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.isOpenHash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.isOpenHash

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.afterRoot_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.afterRoot_hash

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.tail_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.tail_hash

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.nativeCtx_keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.nativeCtx_keep

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.beaconTail_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.beaconTail_reads

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.stage_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.stage_reads

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.build_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.build_reads

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.finish_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.finish_reads

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.slotWeight' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.slotWeight

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.pendingSlots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.pendingSlots

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.pendingTokens' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.pendingTokens

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.initSentFlag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.initSentFlag

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.pending_new' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.pending_new

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.slotWeight_le' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.slotWeight_le

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.pending_clear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.pending_clear

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.pending_extend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.pending_extend

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.initSentFlag_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.initSentFlag_zero

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.initSentFlag_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.initSentFlag_le

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.reserved

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.accept_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.accept_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.build_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.build_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.finish_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.finish_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.quiet_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.quiet_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.potential' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.potential

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.potential_mono_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.potential_mono_hash

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.potential_mono_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.potential_mono_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.native_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.native_support

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.gate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.gate

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.hash_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.hash_step

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.accept_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.accept_step

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.build_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.build_step

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.finish_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.finish_step

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.quiet_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.quiet_step

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.gameState_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.gameState_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.collision

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.game_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.game_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.game_collision_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.game_collision_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.ordered_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision.ordered_bound
