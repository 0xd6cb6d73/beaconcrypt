import BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged
import BeaconcryptCore.Refinement.RatchetControlSurface
import BeaconcryptCore.Refinement.RatchetStructuralFuture

/-!
# First-record integrity with replay rejection

Audit finding F7 (records) observed that the probabilistic multi-key integrity games let the ideal receiver accept exact replays of honest records, that replay rejection was only a functional property of the extracted receive driver (`RawCtxReceive.rawReceive_success_replay`), and that no statement combined it with the bounds. This module closes that gap for the first Beacon record: `first_beacon_record_integrity_replay` bounds a larger event than `PqxdhFirstRecordStopTagged.first_beacon_record_integrity_stop`, namely a canonical first-record forgery or a reacceptance at the registered Server peer, by exactly the same right side and under exactly the same premises.

Event. `replayPost` logs the post like `PqxdhFirstBeaconRecordCanonical.canonicalPost` and outputs the adversary's bit together with `PqxdhFirstBeaconRecordCanonical.ReplyCanonicalForged` or `ReplyReaccepted`. `Reaccepted` holds when some Server raw receive at `env.index`, routed to the key identifier of the registration reply, accepted bytes whose decoded frame has the sequence of a frame accepted earlier at the same peer (`AcceptedSequence`). A second accepted sequence-one record is a reacceptance (`second_first_reaccepted`), and so is every accepted exact replay of an accepted record (`replay_reaccepted`). The reacceptance event uses the sequence of the frame returned by the environment's decoder, which is the target that the Server wrapper passes to the receive driver; the `RawCtxWholeOwner.Decrypted.sequence` field of the reply is not used. Logging adds no request, so the query certificate transfers unchanged (`replay_query_bound`, `replayCertificate`).

Code path. In the HB-112 actual game the accepted continuation runs the post only in the pending branch (`PqxdhFirstRecordTarget.pendingActual`, through `PqxdhInitialRootEventAccepted.client`); the constant-`false` continuation is subtracted on the left side, as in the canonical theorem. There the post is answered by `PqxdhInitialOriginPost.compiler` after the first Server builder `PqxdhInitialPendingBuilder.build`. A Server raw receive goes through `RawCtxPendingFamilyLiveQueries.compiler`, `RawCtxGenericFamilyFrontend.impl`, `RawCtxGenericServer.rawServer` (routing by `env.route` into the peer map of the Server state) and `RawCtxChainOwner.rawReceive` (decoding by `env.decode` and frame validation) to the extracted chain-generic receive program (`RawCtxChainReceive.normalBegin`, `RawCtxChainReceive.normalResume` and `RawCtxChainReceive.normalFinish`, run by `RawCtxPendingReceiveQueries.program`) on the peer kernel held in the threaded Server state. Only its key-derivation replies and its opening reply are oracle answers; admission, the skipped-key cache and publication are the extracted code. Routing and decoding only select the peer and the frame, acceptance is decided by the extracted driver and the opening reply, and no post operation installs, restores or removes a Server peer: sends and raw receives only replace the peer's kernel by the driver's result.

Driver facts. They hold for every oracle reply. `Consumed` says that a sequence is at or below the receive counter and absent from the skipped-key cache. On a kernel whose control is valid, a consumed target is rejected at admission with the unchanged kernel (`begin_consumed`). Every reachable result of a receive call on a kernel whose control satisfies the structural invariant `ratchet.control.ValidControl` is either a rejection that returns the kernel, or an acceptance of a target that was not consumed, returning a kernel whose control is valid, has consumed the target and keeps every consumed sequence consumed (`receive_result`, from `begin_admitted`, `resume_admitted`, `finish_some` and `program_result`; the future path is tracked through the skipped-key window `Window`). Sends keep the receive counter and the cache (`send_result`). The initial kernel of the builder is valid (`initial_valid`), and a successful registration installs the peer with a first-send move of it (`ready_installed`), so the invariant holds after the builder (`build_tracks`).

Composition. `Tracks` states that the registered peer is present with a valid control that consumed every sequence accepted in the transcript, and that the transcript has no reacceptance. Every post request keeps it (`compiler_tracks`), so it holds at every reachable end of the logged run (`logged_invariant`); `no_reacceptance` states the resulting gate-free fact that no reachable transcript of the pending branch has a reacceptance, for every post and whatever the adversary's bit. Hence two logged proxies of the same post whose bits agree on transcripts without a reacceptance give the same source client as oracle computations (`client_congr`). For the replay and canonical proxies this makes the accepted continuations and the pending branches equal (`accepted_replay`, `pending_replay`), so the HB-112 difference of the replay proxy equals that of the canonical proxy (`replay_canonical`), and the final theorem follows from `PqxdhFirstRecordStopTagged.first_beacon_record_integrity_stop`. For the proxy whose bit is the adversary's bit and a reacceptance only, the pending branch never outputs `true` (`pending_reaccept`), so its HB-112 difference is zero (`reaccepted_zero`).

Premises and limits. No premise is added: the invariant is proved for arbitrary routing, decoder, writer and oracle replies. Messages are byte strings that the environment's decoder reads, and no property of a serialization library is used. The right side is literally that of `PqxdhFirstRecordStopTagged.first_beacon_record_integrity_stop`: advantages of reductions constructed from the canonical proxy of `post0`, `2^-256` twice and the explicit stop term. Only the Server peer registered by the first builder at `env.index` is covered, and only runs of the pending branch, which the HB-112 gate restricts to runs in which Beacon `b` published its first record from the selected root and the selected chain stayed undisclosed; the constant-`false` continuation of the difference is not bounded here. Snapshots, persistence and restoration are excluded, as in the imported modules. The post interface has no Server registration, snapshot or restore query after the first builder, so a re-installation at the registered key identifier cannot happen in this game by construction, not by a property proved about the Server implementation.
-/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhFirstRecordReplay

section Control
open ratchet.control ratchet.refined

/-- Sequence `n` is consumed by a receive control state: it is at or below the receive counter and absent from the skipped-key cache. -/
def Consumed (control : RatchetState) (n : Nat) : Prop :=
  n ≤ control.receive_sequence.val ∧ n ∉ cacheSeqs control.receive_cache

/-- The receive plan either rejects or names the requested target, with no derivation exactly for past targets. -/
theorem plan_cases (state : RatchetState) (target : Std.U64) (plan : ReceivePlan)
    (planned : plan_receive_until state target = ok plan) :
    plan.sequence = .None ∨ (plan.sequence = .Some target ∧ (plan.derivations = 0#u64 ↔ target.val ≤ state.receive_sequence.val)) := by
  unfold plan_receive_until at planned
  by_cases past : target ≤ state.receive_sequence
  · rw [ite_eq_left past] at planned
    cases RustM.ok.inj planned
    exact Or.inr ⟨rfl, by simp only [true_iff]; scalar_tac⟩
  · rw [ite_eq_right past] at planned
    obtain ⟨gap, gapEq, gapVal⟩ := uscalar_sub_eq_ok target state.receive_sequence (by scalar_tac)
    obtain ⟨skip, skipEq, _⟩ := uscalar_sub_eq_ok gap 1#u64 (by scalar_tac)
    simp only [gapEq, skipEq, bind_tc_ok, lift] at planned
    have future : ¬ target.val ≤ state.receive_sequence.val := by scalar_tac
    have nonzero : gap ≠ 0#u64 := by scalar_tac
    by_cases wide : skip > RATCHET_MAX_GAP
    · rw [ite_eq_left wide] at planned
      cases RustM.ok.inj planned
      exact Or.inl rfl
    · rw [ite_eq_right wide] at planned
      obtain ⟨room, roomEq, _⟩ := uscalar_sub_eq_ok RATCHET_MAX_GAP skip (by scalar_tac)
      simp only [roomEq, bind_tc_ok] at planned
      split at planned
      · cases RustM.ok.inj planned
        exact Or.inl rfl
      · cases RustM.ok.inj planned
        exact Or.inr ⟨rfl, by simp only [nonzero, future]⟩

/-- The skipped-key window of a future receive: `working` is `entry` advanced past `count` skipped keys, each appended to the cache. -/
structure Window (entry : RatchetState) (count : Nat) (working : RatchetState) : Prop where
  sequence : working.receive_sequence.val = entry.receive_sequence.val + count
  capacity : working.Wf
  cache : cacheSeqs working.receive_cache =
    cacheSeqs entry.receive_cache ++ (List.range count).map (fun j => entry.receive_sequence.val + j + 1)

variable {Send Receive Material Context : Type}

/-- Facts of a prepared opening of `kernel` for `target`: a checked cached slot, or a future window ending at `target`. -/
def Prepared (kernel : RefinedRatchet Send Receive Material) (target : Std.U64) :
    PreparedReceive Receive Material → Prop
  | .PreparedReceiveCachedCase prepared => CachedPreparationFacts kernel target prepared
  | .PreparedReceiveFutureCase pending => kernel.control.receive_sequence.val < target.val ∧
      pending.first_slot = kernel.control.receive_cache.len ∧ pending.committed_control.receive_sequence = target ∧
      target.val = kernel.control.receive_sequence.val + pending.skipped.val + 1 ∧ pending.committed_control.Wf ∧
      cacheSeqs pending.committed_control.receive_cache = cacheSeqs kernel.control.receive_cache ++
        (List.range pending.skipped.val).map (fun j => kernel.control.receive_sequence.val + j + 1)

/-- Facts of a receive effect started on `kernel` for `target`: rejection keeps `kernel`, a pending derivation works on a window of `kernel`, and an opening is prepared for `target`. -/
def Admitted (kernel : RefinedRatchet Send Receive Material) (target : Std.U64) :
    RawCtxChainReceive.Effect Send Receive Material Context → Prop
  | .rejected entry _ => entry = kernel
  | .kdfRequested pending => pending.entry = kernel ∧ pending.target = target ∧
      kernel.control.receive_sequence.val < target.val ∧ pending.first_slot = kernel.control.receive_cache.len ∧
      Window kernel.control pending.skipped.val pending.working_control
  | .openRequested opening => opening.entry = kernel ∧ Prepared kernel target opening.prepared

/-- Admission of any target on a kernel with a bounded cache has the admission facts. -/
theorem begin_admitted (kernel : RefinedRatchet Send Receive Material) (target : Std.U64) (context : Context)
    (capacity : kernel.control.Wf) :
    Admitted kernel target (RawCtxChainReceive.normalBegin kernel target context) := by
  have exact := RawCtxChainReceive.normalBegin_exact kernel target context
  generalize RawCtxChainReceive.normalBegin kernel target context = effect at exact ⊢
  unfold RawCtxChainReceive.beginReceive at exact
  cases planned : plan_receive_until kernel.control target with
  | fail error => simp only [planned, bind_tc_fail, reduceCtorEq] at exact
  | div => simp only [planned, bind_tc_div, reduceCtorEq] at exact
  | ok plan =>
    simp only [planned, bind_tc_ok] at exact
    rcases plan_cases kernel.control target plan planned with none | ⟨some, derivations⟩
    · simp only [none, RawCtxChainReceive.rejected, RustM.ok.injEq] at exact
      subst exact
      rfl
    · simp only [some] at exact
      by_cases zero : plan.derivations = 0#u64
      · rw [ite_eq_left zero] at exact
        cases prepared : prepare_cached_receive kernel target with
        | fail error => simp only [prepared, bind_tc_fail, reduceCtorEq] at exact
        | div => simp only [prepared, bind_tc_div, reduceCtorEq] at exact
        | ok found =>
          simp only [prepared, bind_tc_ok] at exact
          cases found with
          | none =>
            simp only [RawCtxChainReceive.rejected, RustM.ok.injEq] at exact
            subst exact
            rfl
          | some cached =>
            simp only [RustM.ok.injEq] at exact
            subst exact
            exact ⟨rfl, prepare_cached_receive_success_inv kernel target cached prepared⟩
      · rw [ite_eq_right zero] at exact
        have future : kernel.control.receive_sequence.val < target.val := by
          have := (not_congr derivations).mp zero
          omega
        have window : Window kernel.control 0 kernel.control := ⟨rfl, capacity, by simp⟩
        obtain ⟨skipped, skippedEq, _⟩ := uscalar_sub_eq_ok plan.derivations 1#u64 (by scalar_tac)
        simp only [skippedEq, bind_tc_ok, RawCtxChainReceive.rejected, RatchetState.receive_cache_len, lift] at exact
        repeat' split at exact
        all_goals first
          | (simp only [RustM.ok.injEq] at exact; subst exact; rfl)
          | skip
        cases emptied : refined_receive_slots_are_empty kernel kernel.control.receive_cache.len
            (UScalar.cast UScalarTy.U8 skipped) with
        | fail error => simp only [emptied, bind_tc_fail, reduceCtorEq] at exact
        | div => simp only [emptied, bind_tc_div, reduceCtorEq] at exact
        | ok flag =>
          simp only [emptied, bind_tc_ok] at exact
          cases flag
          · simp only [Bool.false_eq_true, ite_false, RustM.ok.injEq] at exact
            subst exact
            rfl
          · cases slots : empty_material_slots Material with
            | fail error => simp only [slots, ite_true, bind_tc_fail, reduceCtorEq] at exact
            | div => simp only [slots, ite_true, bind_tc_div, reduceCtorEq] at exact
            | ok staged =>
              simp only [slots, ite_true, bind_tc_ok, RustM.ok.injEq] at exact
              subst exact
              exact ⟨rfl, rfl, future, rfl, window⟩

/-- On a kernel whose control is valid, a consumed target is rejected at admission with the unchanged kernel. -/
theorem begin_consumed (kernel : RefinedRatchet Send Receive Material) (target : Std.U64) (context : Context)
    (valid : ValidControl kernel.control) (consumed : Consumed kernel.control target.val) :
    RawCtxChainReceive.normalBegin kernel target context = .rejected kernel context := by
  apply RustM.ok.inj
  rw [← RawCtxChainReceive.normalBegin_exact]
  have missing := lookup_receive_key_of_not_mem kernel.control target valid.capacity consumed.2
  simp only [RawCtxChainReceive.beginReceive, plan_receive_until_replay kernel.control target consumed.1, bind_tc_ok,
    ite_true, prepare_cached_receive, missing, RawCtxChainReceive.rejected]

/-- A key derivation that yields a sequence number extends the skipped-key window by that sequence number. -/
theorem advance_window (entry working : RatchetState) (count : Nat) (window : Window entry count working)
    (advanced : ReceiveAdvance) (step : advance_receive working = ok advanced) (sequence : Std.U64)
    (yielded : advanced.sequence = .Some sequence) :
    Window entry (count + 1) advanced.state ∧ sequence.val = entry.receive_sequence.val + count + 1 := by
  by_cases top : working.receive_sequence = core.num.U64.MAX
  · rw [advance_receive_max working top] at step
    cases RustM.ok.inj step
    cases yielded
  by_cases full : 50 ≤ working.receive_cache.len.val
  · rw [advance_receive_full working full] at step
    cases RustM.ok.inj step
    cases yielded
  obtain ⟨next, nextEq, nextSequence, _, _, nextYield, nextCache⟩ :=
    advance_receive_cacheSeqs working top (by omega)
  cases RustM.ok.inj (nextEq.symm.trans step)
  rw [nextYield] at yielded
  cases yielded
  refine ⟨⟨by rw [nextSequence, window.sequence]; omega, advance_receive_wf working window.capacity _ nextEq, ?_⟩,
    by rw [nextSequence, window.sequence]⟩
  rw [nextCache, window.cache, List.range_succ, List.map_append, List.append_assoc, window.sequence]
  simp only [List.map_cons, List.map_nil]

/-- A successful `RustM` bind succeeded on its first computation. -/
theorem rust_bind_ok {α β : Type} {x : RustM α} {f : α → RustM β} {y : β} (h : (x >>= f) = ok y) :
    ∃ v, x = ok v ∧ f v = ok y := by
  cases x with
  | ok v => exact ⟨v, rfl, h⟩
  | fail e => cases h
  | div => cases h

/-- Every resumed derivation keeps the admission facts of its entry kernel and target. -/
theorem resume_admitted (kernel : RefinedRatchet Send Receive Material) (target : Std.U64)
    (pending : RawCtxChainReceive.Kdf Send Receive Material Context) (reply : Receive × Material)
    (admitted : Admitted kernel target (.kdfRequested pending)) :
    Admitted kernel target (RawCtxChainReceive.normalResume pending reply) := by
  obtain ⟨entry, aimed, future, first, window⟩ := admitted
  have exact := RawCtxChainReceive.normalResume_exact pending reply
  generalize RawCtxChainReceive.normalResume pending reply = effect at exact ⊢
  unfold RawCtxChainReceive.resume at exact
  have rejectedCase : ∀ (context : Context), RawCtxChainReceive.rejected pending.entry context = ok effect →
      Admitted kernel target effect := by
    intro context same
    simp only [RawCtxChainReceive.rejected, RustM.ok.injEq] at same
    subst same
    exact entry
  by_cases zero : pending.remaining = 0#u8
  · rw [ite_eq_left zero] at exact
    exact rejectedCase _ exact
  rw [ite_eq_right zero] at exact
  by_cases last : pending.remaining = 1#u8
  · rw [ite_eq_left last] at exact
    by_cases top : pending.working_control.receive_sequence = core.num.U64.MAX
    · rw [advance_receive_target_max _ top] at exact
      simp only [bind_tc_ok] at exact
      exact rejectedCase _ exact
    obtain ⟨advanced, advancedEq, advancedSequence, _, advancedCache, advancedYield⟩ := advance_receive_target_ok _ top
    simp only [advancedEq, bind_tc_ok, advancedYield] at exact
    by_cases hit : advanced.state.receive_sequence = pending.target
    · rw [ite_eq_left hit] at exact
      obtain ⟨valid, _, exact⟩ := rust_bind_ok exact
      split at exact
      · simp only [RustM.ok.injEq] at exact
        subst exact
        refine ⟨entry, future, first, hit.trans aimed, ?_, ?_, ?_⟩
        · rw [← aimed, ← hit, advancedSequence, window.sequence]
        · simpa only [RatchetState.Wf, advancedCache] using window.capacity
        · rw [advancedCache, window.cache]
      · exact rejectedCase _ exact
    · rw [ite_eq_right hit] at exact
      exact rejectedCase _ exact
  rw [ite_eq_right last] at exact
  obtain ⟨advanced, advancedEq, exact⟩ := rust_bind_ok exact
  cases yielded : advanced.sequence with
  | none =>
    simp only [yielded] at exact
    exact rejectedCase _ exact
  | some sequence =>
    simp only [yielded] at exact
    obtain ⟨extended, _⟩ := advance_window _ _ _ window advanced advancedEq sequence yielded
    have bump : ∀ next : Std.U8, pending.skipped + 1#u8 = ok next → Window kernel.control next.val advanced.state := by
      intro next nextEq
      have := UScalar.add_equiv pending.skipped 1#u8
      rw [nextEq] at this
      have value : next.val = pending.skipped.val + 1 := by scalar_tac
      rw [value]
      exact extended
    cases slotted : advanced.slot with
    | none =>
      simp only [slotted] at exact
      exact rejectedCase _ exact
    | some slot =>
      simp only [slotted] at exact
      repeat' (first | (obtain ⟨_, _, exact⟩ := rust_bind_ok exact) | split at exact)
      all_goals first
        | exact rejectedCase _ exact
        | (simp only [RustM.ok.injEq] at exact
           subst exact
           exact ⟨entry, aimed, future, first, bump _ ‹_›⟩)

/-- Publication after a rejected opening returns the opening's entry kernel. -/
theorem finish_none {Plaintext : Type} (opening : RawCtxInterpretedOpening.Opening Send Receive Material Context) :
    RawCtxChainReceive.normalFinish opening (.None : core.option.Option Plaintext) = (opening.entry, .None) := by
  have exact := RawCtxChainReceive.normalFinish_exact opening (.None : core.option.Option Plaintext)
  simp only [RawCtxInterpretedOpening.finish] at exact
  exact (RustM.ok.inj exact).symm

/-- Publication of a prepared opening of a valid kernel for `target` keeps the control valid, consumes `target` and keeps every consumed sequence consumed; the reply is returned unchanged. -/
theorem finish_some {Plaintext : Type} (kernel : RefinedRatchet Send Receive Material) (target : Std.U64)
    (opening : RawCtxInterpretedOpening.Opening Send Receive Material Context) (reply : Plaintext)
    (entry : opening.entry = kernel) (prepared : Prepared kernel target opening.prepared) (valid : ValidControl kernel.control) :
    (RawCtxChainReceive.normalFinish opening (.Some reply)).2 = .Some reply ∧
      ValidControl (RawCtxChainReceive.normalFinish opening (.Some reply)).1.control ∧
      Consumed (RawCtxChainReceive.normalFinish opening (.Some reply)).1.control target.val ∧
      ∀ n, Consumed kernel.control n → Consumed (RawCtxChainReceive.normalFinish opening (.Some reply)).1.control n := by
  have exact := RawCtxChainReceive.normalFinish_exact opening (.Some reply)
  generalize RawCtxChainReceive.normalFinish opening (.Some reply) = result at exact ⊢
  subst entry
  unfold Prepared at prepared
  cases shape : opening.prepared with
  | PreparedReceiveCachedCase cached =>
    rw [shape] at prepared
    obtain ⟨published, publishedEq, publishedControl, _, _, _⟩ :=
      publish_cached_receive_exact opening.entry cached prepared.target_bound prepared.last_bound
    simp only [RawCtxInterpretedOpening.finish, shape, publishedEq, bind_tc_ok, RustM.ok.injEq] at exact
    subst exact
    obtain ⟨finished, finishedEq, _, finishedValid, finishedPerm⟩ :=
      valid.finish_receive_exact target cached.target_slot prepared.target_live prepared.entry
    obtain ⟨consumed, consumedEq, _, _, _, consumedSequence, _, _⟩ :=
      finish_receive_consumed opening.entry.control target cached.target_slot valid.capacity prepared.target_live prepared.entry
    have sameFinished := RustM.ok.inj (finishedEq.symm.trans prepared.finish)
    have sameConsumed := RustM.ok.inj (consumedEq.symm.trans prepared.finish)
    subst sameFinished
    subst sameConsumed
    simp only at finishedValid finishedPerm consumedSequence
    have member : target.val ∈ cacheSeqs opening.entry.control.receive_cache :=
      (mem_cacheSeqs_iff _ _).mpr ⟨cached.target_slot.val, prepared.target_live, congrArg UScalar.val prepared.entry⟩
    refine ⟨rfl, publishedControl ▸ finishedValid, ⟨?_, ?_⟩, fun n old => ⟨?_, ?_⟩⟩
    · rw [publishedControl, consumedSequence]
      exact valid.past _ member
    · rw [publishedControl, finishedPerm.mem_iff]
      exact valid.unique.not_mem_erase
    · rw [publishedControl, consumedSequence]
      exact old.1
    · rw [publishedControl, finishedPerm.mem_iff]
      exact fun inErase => old.2 (List.mem_of_mem_erase inErase)
  | PreparedReceiveFutureCase pending =>
    rw [shape] at prepared
    obtain ⟨future, first, committedSequence, targetValue, committedCapacity, committedCache⟩ := prepared
    have length := congrArg List.length committedCache
    simp only [cacheSeqs_length, List.length_append, List.length_map, List.length_range] at length
    have bound : pending.first_slot.val + pending.skipped.val ≤ 50 := by
      have := committedCapacity
      simp only [RatchetState.Wf, SequenceCache.Wf] at this
      rw [first]
      omega
    obtain ⟨published, publishedEq, publishedControl, _, _, _⟩ := publish_future_receive_exact opening.entry pending bound
    simp only [RawCtxInterpretedOpening.finish, shape, publishedEq, bind_tc_ok, RustM.ok.injEq] at exact
    subst exact
    have fresh : ∀ n ∈ cacheSeqs pending.committed_control.receive_cache,
        n ∈ cacheSeqs opening.entry.control.receive_cache ∨ opening.entry.control.receive_sequence.val < n := by
      intro n member
      rw [committedCache, List.mem_append, List.mem_map] at member
      rcases member with old | ⟨j, _, rfl⟩
      · exact Or.inl old
      · exact Or.inr (by omega)
    refine ⟨rfl, ?_, ⟨?_, ?_⟩, fun n old => ⟨?_, ?_⟩⟩
    · rw [publishedControl]
      exact valid.extend pending.skipped.val committedCapacity (by rw [committedSequence]; omega) committedCache
    · rw [publishedControl, committedSequence]
    · rw [publishedControl]
      intro member
      rw [committedCache, List.mem_append, List.mem_map] at member
      rcases member with old | ⟨j, range, same⟩
      · have := valid.past _ old
        omega
      · have := List.mem_range.mp range
        omega
    · rw [publishedControl, committedSequence]
      have := old.1
      omega
    · rw [publishedControl]
      intro member
      rcases fresh n member with inOld | above
      · exact old.2 inOld
      · have := old.1
        omega

/-- Every reachable result of the pending receive program started from admission facts of a valid kernel for `target`: a rejection returns the kernel, and an acceptance returns a valid kernel that consumed `target` and keeps every consumed sequence consumed. -/
theorem program_result {Plaintext : Type} (kernel : RefinedRatchet Send Receive Material) (target : Std.U64)
    (valid : ValidControl kernel.control) (effect : RawCtxChainReceive.Effect Send Receive Material Context)
    (admitted : Admitted kernel target effect)
    (result : RefinedRatchet Send Receive Material × core.option.Option Plaintext)
    (supported : result ∈ support (RawCtxPendingReceiveQueries.program effect)) :
    (result.2 = .None → result.1 = kernel) ∧
      ∀ value, result.2 = .Some value → ValidControl result.1.control ∧ Consumed result.1.control target.val ∧
        ∀ n, Consumed kernel.control n → Consumed result.1.control n := by
  generalize hdepth : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect result with
  | h depth ih =>
    cases effect with
    | rejected entry context =>
      rw [RawCtxPendingReceiveQueries.program] at supported
      simp only [support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨fun _ => admitted, fun value same => by cases same⟩
    | openRequested opening =>
      rw [RawCtxPendingReceiveQueries.program] at supported
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨reply, _, rfl⟩ := supported
      obtain ⟨entry, prepared⟩ := admitted
      cases reply with
      | none =>
        rw [finish_none]
        exact ⟨fun _ => entry, fun value same => by cases same⟩
      | some value =>
        obtain ⟨same, rest⟩ := finish_some kernel target opening value entry prepared valid
        refine ⟨fun none => (by rw [same] at none; cases none), fun other _ => rest⟩
    | kdfRequested pending =>
      rw [RawCtxPendingReceiveQueries.program] at supported
      simp only [mem_support_bind_iff] at supported
      obtain ⟨reply, _, supported⟩ := supported
      exact ih _ (hdepth ▸ RawCtxChainReceive.normalResume_rank pending reply) _
        (resume_admitted kernel target pending reply admitted) result supported rfl

end Control
section Calls
open ratchet.control ratchet.refined

/-- Interpreting the queries of a free oracle computation by other free oracle computations can only reach results of the original computation. -/
theorem support_simulate {ι κ : Type} {spec : OracleSpec ι} {target : OracleSpec κ} {α : Type}
    (impl : QueryImpl spec (OracleComp target)) (work : OracleComp spec α) :
    support (simulateQ impl work) ⊆ support work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]; exact le_refl _
  | query_bind query next ih =>
    intro result reached
    simp only [simulateQ_query_bind, mem_support_bind_iff] at reached
    obtain ⟨reply, _, reached⟩ := reached
    simp only [mem_support_bind_iff]
    exact ⟨reply, mem_support_query query reply, ih reply reached⟩

variable {Chain : Type}

/-- Every reachable result of one pending receive call on a valid kernel for `target`: a rejection returns the kernel; an accepted target was not consumed before, and the call returns a valid kernel that consumed `target`, and keeps every consumed sequence consumed. -/
theorem receive_result (kernel : RawCtxPendingOwnerQueries.Kernel Chain) (target : Std.U64)
    (context : RawCtxWholeOwner.OpenContext) (valid : ValidControl kernel.control)
    (result : RawCtxPendingOwnerQueries.Kernel Chain × core.option.Option RawCtxWholeOwner.Decrypted)
    (supported : result ∈ support (RawCtxPendingOwnerQueries.calls.receive kernel target context)) :
    (result.2 = .None → result.1 = kernel) ∧
      ∀ value, result.2 = .Some value → ¬Consumed kernel.control target.val ∧ ValidControl result.1.control ∧
        Consumed result.1.control target.val ∧ ∀ n, Consumed kernel.control n → Consumed result.1.control n := by
  have reached := support_simulate _ _ supported
  have facts := program_result kernel target valid _ (begin_admitted kernel target context valid.capacity) result reached
  refine ⟨facts.1, fun value accepted => ⟨fun consumed => ?_, facts.2 value accepted⟩⟩
  rw [begin_consumed kernel target context valid consumed, RawCtxPendingReceiveQueries.program] at reached
  simp only [support_pure, Set.mem_singleton_iff] at reached
  rw [reached] at accepted
  cases accepted

/-- Send admission keeps the entry kernel and commits a control with the entry's receive counter and cache. -/
theorem send_begin_control {Send Receive Material Context : Type} (kernel : RefinedRatchet Send Receive Material)
    (context : Context) :
    (∃ other, RawCtxChainSend.normalBegin kernel context = .exhausted kernel other) ∨
      ∃ pending, RawCtxChainSend.normalBegin kernel context = .requested pending ∧ pending.entry = kernel ∧
        pending.committed_control.receive_sequence = kernel.control.receive_sequence ∧
        pending.committed_control.receive_cache = kernel.control.receive_cache := by
  have begun := RawCtxChainSend.normalBegin_exact kernel context
  generalize RawCtxChainSend.normalBegin kernel context = start at begun ⊢
  unfold RawCtxChainSend.beginSend advance_send at begun
  by_cases top : kernel.control.send_sequence = core.num.U64.MAX
  · rw [ite_eq_left top] at begun
    simp only [SendKey.unavailable, bind_tc_ok, RustM.ok.injEq] at begun
    subst begun
    exact Or.inl ⟨_, rfl⟩
  · rw [ite_eq_right top] at begun
    obtain ⟨next, nextEq, _⟩ := uscalar_add_eq_ok kernel.control.send_sequence 1#u64 (by
      have := kernel.control.send_sequence.hBounds
      simp only [core.num.U64.MAX, U64.rMax] at top
      scalar_tac)
    simp only [nextEq, bind_tc_ok] at begun
    repeat' (first | (obtain ⟨_, _, begun⟩ := rust_bind_ok begun) | split at begun)
    all_goals simp only [RustM.ok.injEq] at begun
    all_goals subst begun
    all_goals first
      | exact Or.inl ⟨_, rfl⟩
      | exact Or.inr ⟨_, rfl, rfl, rfl, rfl⟩

/-- Every reachable result of one pending send call keeps the kernel's receive counter and skipped-key cache. -/
theorem send_result (kernel : RawCtxPendingOwnerQueries.Kernel Chain) (context : RawCtxSourceSend.SealContext)
    (result : RawCtxPendingOwnerQueries.Kernel Chain × Option RawCtxSourceSend.Encrypted)
    (supported : result ∈ support (RawCtxPendingOwnerQueries.calls.send kernel context)) :
    result.1.control.receive_sequence = kernel.control.receive_sequence ∧
      result.1.control.receive_cache = kernel.control.receive_cache := by
  have reached := support_simulate _ _ supported
  rcases send_begin_control kernel context with ⟨other, exhausted⟩ | ⟨pending, requested, entry, sequence, cache⟩
  · rw [exhausted, RawCtxPendingOwnerQueries.sendProgram] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst reached
    exact ⟨rfl, rfl⟩
  · rw [requested, RawCtxPendingOwnerQueries.sendProgram] at reached
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
    obtain ⟨_, _, _, _, rfl⟩ := reached
    exact ⟨sequence, cache⟩

end Calls
section Server
open ratchet.control RawCtxGenericRoleStorage
variable {Chain M P : Type}

/-- Every reachable result of one owner raw receive on a valid kernel: a rejection keeps the kernel; an acceptance decoded a frame whose sequence was not consumed before, and it leaves a valid kernel that consumed that sequence and keeps every consumed sequence consumed. -/
theorem owner_result (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State (RawCtxPendingOwnerQueries.Kernel Chain) P) (valid : ValidControl owner.kernel.control)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × RawCtxChainOwner.State (RawCtxPendingOwnerQueries.Kernel Chain) P)
    (supported : result ∈ support ((RawCtxChainOwner.rawReceive RawCtxPendingOwnerQueries.calls decode raw).run owner)) :
    (result.1 = .None → result.2.kernel = owner.kernel) ∧
      ∀ decrypted, result.1 = .Some decrypted → ∃ frame, decode raw = some frame ∧
        ¬Consumed owner.kernel.control frame.sequence.val ∧ ValidControl result.2.kernel.control ∧
        Consumed result.2.kernel.control frame.sequence.val ∧
        ∀ n, Consumed owner.kernel.control n → Consumed result.2.kernel.control n := by
  unfold RawCtxChainOwner.rawReceive StateT.run at supported
  split at supported
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact ⟨fun _ => rfl, fun _ accepted => by cases accepted⟩
  cases decoded : decode raw with
  | none =>
    simp only [decoded, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact ⟨fun _ => rfl, fun _ accepted => by cases accepted⟩
  | some frame =>
    simp only [decoded] at supported
    split at supported
    · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨received, reached, rfl⟩ := supported
      obtain ⟨rejected, accepted⟩ := receive_result owner.kernel frame.sequence _ valid received reached
      refine ⟨rejected, fun decrypted same => ?_⟩
      obtain ⟨fresh, validAfter, consumed, kept⟩ := accepted decrypted same
      exact ⟨frame, rfl, fresh, validAfter, consumed, kept⟩
    · simp only [support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨fun _ => rfl, fun _ accepted => by cases accepted⟩

/-- The Server peer `kid` is installed with a valid control that consumed every sequence satisfying `accepted`. -/
def PeerTracks (accepted : Nat → Prop) (kid : Std.U64)
    (server : Server (RawCtxPendingOwnerQueries.Kernel Chain) M P) : Prop :=
  ∃ peer, server.peers kid = some peer ∧ ValidControl peer.kernel.control ∧ ∀ n, accepted n → Consumed peer.kernel.control n

/-- Tracking a weaker set of accepted sequences follows from tracking a stronger one. -/
theorem tracks_mono (accepted weaker : Nat → Prop) (kid : Std.U64) (server : Server (RawCtxPendingOwnerQueries.Kernel Chain) M P)
    (implied : ∀ n, weaker n → accepted n) (tracks : PeerTracks accepted kid server) : PeerTracks weaker kid server := by
  obtain ⟨peer, found, valid, consumed⟩ := tracks
  exact ⟨peer, found, valid, fun n holds => consumed n (implied n holds)⟩

/-- Replacing the kernel of another peer keeps the tracked peer. -/
theorem tracks_put_other (accepted : Nat → Prop) (kid other : Std.U64) (server : Server (RawCtxPendingOwnerQueries.Kernel Chain) M P)
    (peer : Peer (RawCtxPendingOwnerQueries.Kernel Chain) P) (kernel : RawCtxPendingOwnerQueries.Kernel Chain)
    (different : other ≠ kid) (tracks : PeerTracks accepted kid server) :
    PeerTracks accepted kid (RawCtxGenericServer.putPeer server other peer kernel) := by
  obtain ⟨tracked, found, valid, consumed⟩ := tracks
  exact ⟨tracked, by simp only [RawCtxGenericServer.putPeer, Function.update_of_ne (Ne.symm different), found], valid, consumed⟩

/-- Replacing the kernel of the tracked peer by a valid kernel that consumed the tracked sequences keeps it tracked. -/
theorem tracks_put_same (accepted : Nat → Prop) (kid : Std.U64) (server : Server (RawCtxPendingOwnerQueries.Kernel Chain) M P)
    (peer : Peer (RawCtxPendingOwnerQueries.Kernel Chain) P) (kernel : RawCtxPendingOwnerQueries.Kernel Chain)
    (valid : ValidControl kernel.control) (consumed : ∀ n, accepted n → Consumed kernel.control n) :
    PeerTracks accepted kid (RawCtxGenericServer.putPeer server kid peer kernel) :=
  ⟨{peer with kernel := kernel}, by simp only [RawCtxGenericServer.putPeer, Function.update_self], valid, consumed⟩

/-- One Server raw receive keeps the tracked peer `kid`; when it accepts bytes routed to `kid`, their decoded sequence was not tracked before, and it is tracked afterwards. -/
theorem raw_tracks (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : ServerState (RawCtxPendingOwnerQueries.Kernel Chain) M P) (accepted : Nat → Prop) (kid : Std.U64)
    (tracks : PeerTracks accepted kid state.server)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × ServerState (RawCtxPendingOwnerQueries.Kernel Chain) M P)
    (supported : result ∈ support (RawCtxGenericServer.rawServer RawCtxPendingOwnerQueries.calls route decode raw state)) :
    (∀ decrypted frame, result.1 = .Some decrypted → route raw = some kid → decode raw = some frame →
      ¬accepted frame.sequence.val) ∧
    PeerTracks (fun n => accepted n ∨ ∃ decrypted frame, result.1 = .Some decrypted ∧ route raw = some kid ∧
      decode raw = some frame ∧ frame.sequence.val = n) kid result.2.server := by
  have rejected : result.1 = .None → result.2.server = state.server →
      (∀ decrypted frame, result.1 = .Some decrypted → route raw = some kid → decode raw = some frame →
        ¬accepted frame.sequence.val) ∧
      PeerTracks (fun n => accepted n ∨ ∃ decrypted frame, result.1 = .Some decrypted ∧ route raw = some kid ∧
        decode raw = some frame ∧ frame.sequence.val = n) kid result.2.server := by
    intro none same
    refine ⟨fun decrypted frame accepted => (by rw [none] at accepted; cases accepted), ?_⟩
    rw [same]
    refine tracks_mono accepted _ kid state.server (fun n holds => ?_) tracks
    rcases holds with old | ⟨decrypted, frame, accepted, _⟩
    · exact old
    · rw [none] at accepted
      cases accepted
  unfold RawCtxGenericServer.rawServer at supported
  split at supported
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact rejected rfl rfl
  rename_i other routed
  split at supported
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact rejected rfl rfl
  rename_i ad associated
  split at supported
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact rejected rfl rfl
  rename_i peer found
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨received, reached, rfl⟩ := supported
  by_cases same : other = kid
  · subst same
    obtain ⟨tracked, trackedFound, valid, consumed⟩ := tracks
    rw [found, Option.some.injEq] at trackedFound
    subst trackedFound
    obtain ⟨none, some⟩ := owner_result decode raw _ valid received reached
    cases reply : received.1 with
    | none =>
      have kept := none reply
      refine ⟨fun decrypted frame accepted => (by cases accepted), ?_⟩
      refine tracks_put_same _ other state.server peer received.2.kernel (by rw [kept]; exact valid) fun n holds => ?_
      rcases holds with old | ⟨decrypted, frame, accepted, _⟩
      · rw [kept]
        exact consumed n old
      · cases accepted
    | some decrypted =>
      obtain ⟨frame, decoded, fresh, validAfter, consumedNow, kept⟩ := some decrypted reply
      refine ⟨fun decrypted' frame' _ _ decoded' old => ?_, ?_⟩
      · rw [decoded, Option.some.injEq] at decoded'
        subst decoded'
        exact fresh (consumed _ old)
      refine tracks_put_same _ other state.server peer received.2.kernel validAfter fun n holds => ?_
      rcases holds with old | ⟨decrypted', frame', _, _, decoded', rfl⟩
      · exact kept n (consumed n old)
      · rw [decoded, Option.some.injEq] at decoded'
        subst decoded'
        exact consumedNow
  · refine ⟨fun decrypted frame _ routedKid => ?_, ?_⟩
    · rw [routed, Option.some.injEq] at routedKid
      exact absurd routedKid same
    refine tracks_put_other _ kid other state.server peer _ same (tracks_mono accepted _ kid state.server (fun n holds => ?_) tracks)
    rcases holds with old | ⟨decrypted, frame, _, routedKid, _⟩
    · exact old
    · rw [routed, Option.some.injEq] at routedKid
      exact absurd routedKid same

/-- One Server send keeps the tracked peer `kid`. -/
theorem send_tracks (senderId : M → Std.U64) (plaintext : Pqxdh.Bytes) (other : Std.U64)
    (state : ServerState (RawCtxPendingOwnerQueries.Kernel Chain) M P) (accepted : Nat → Prop) (kid : Std.U64)
    (tracks : PeerTracks accepted kid state.server)
    (result : Option RawCtxSourceSend.Encrypted × ServerState (RawCtxPendingOwnerQueries.Kernel Chain) M P)
    (supported : result ∈ support (RawCtxGenericServer.sendServer RawCtxPendingOwnerQueries.calls senderId plaintext other state)) :
    PeerTracks accepted kid result.2.server := by
  unfold RawCtxGenericServer.sendServer at supported
  cases associated : RawCtxGenericServer.peerAssociatedData state.server other with
  | none =>
    simp only [associated, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact tracks
  | some ad =>
    simp only [associated] at supported
    cases found : state.server.peers other with
    | none =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact tracks
    | some peer =>
      simp only [found, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨sent, reached, rfl⟩ := supported
      have keeps : sent.2.kernel.control.receive_sequence = peer.kernel.control.receive_sequence ∧
          sent.2.kernel.control.receive_cache = peer.kernel.control.receive_cache := by
        unfold RawCtxChainOwner.sendOwner StateT.run at reached
        split at reached
        · simp only [support_pure, Set.mem_singleton_iff] at reached
          subst reached
          exact ⟨rfl, rfl⟩
        · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
          obtain ⟨call, called, rfl⟩ := reached
          exact send_result _ _ call called
      by_cases same : other = kid
      · subst same
        obtain ⟨tracked, trackedFound, valid, consumed⟩ := tracks
        rw [found, Option.some.injEq] at trackedFound
        subst trackedFound
        refine tracks_put_same _ other state.server peer sent.2.kernel (valid.of_receive_eq _ keeps.1 keeps.2) fun n old => ?_
        have before := consumed n old
        exact ⟨keeps.1 ▸ before.1, keeps.2 ▸ before.2⟩
      · exact tracks_put_other _ kid other state.server peer _ same tracks

end Server
section Event
open PqxdhFirstBeaconRecordIntegrity PqxdhFirstBeaconRecordCanonical
variable {ι : Type} {baseSpec : OracleSpec ι} {S B : Nat}

/-- Some Server raw receive at `index` in `log`, routed to `kid`, accepted bytes whose decoded frame has sequence `n`. -/
def AcceptedSequence (index : Fin S) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (kid : Std.U64) (log : List (Entry baseSpec S B)) (n : Nat) : Prop :=
  ∃ entry ∈ log, ∃ raw decrypted frame, serverOpen entry = some (index, raw, .Some decrypted) ∧ route raw = some kid ∧
    decode raw = some frame ∧ frame.sequence.val = n

/-- Reacceptance: some Server raw receive at `index`, routed to `kid`, accepted bytes whose decoded frame has the sequence of a frame accepted earlier at the same peer; in particular a second accepted sequence-one record and an accepted exact replay of an accepted record. -/
def Reaccepted (index : Fin S) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (kid : Std.U64) (log : List (Entry baseSpec S B)) : Prop :=
  ∃ before entry after raw decrypted frame, log = before ++ entry :: after ∧
    serverOpen entry = some (index, raw, .Some decrypted) ∧ route raw = some kid ∧ decode raw = some frame ∧
    AcceptedSequence index route decode kid before frame.sequence.val

/-- The reacceptance event for the registration reply: its key identifier names the Server peer; an unsuccessful registration has no reacceptance. -/
def ReplyReaccepted (index : Fin S) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (reply : RustM (Option PqxdhServerRegistrationPublication.Response)) (log : List (Entry baseSpec S B)) : Prop :=
  match reply with
  | .ok (some response) => Reaccepted index route decode response.keyId log
  | _ => False

/-- The logged post bit of the replay proxy: the adversary's own bit and either a canonical first-record forgery or a reacceptance at the registered peer. -/
noncomputable def replayBit (index : Fin S) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (writer : RawCtxMixedShared.Writer) (reply : RustM (Option PqxdhServerRegistrationPublication.Response))
    (result : Bool × List (Entry baseSpec S B)) : Bool :=
  result.1 && @decide (ReplyCanonicalForged index route decode writer reply result.2 ∨
    ReplyReaccepted index route decode reply result.2) (Classical.propDecidable _)

/-- An accepted sequence of a transcript with one appended entry was accepted in the prefix or by the appended entry. -/
theorem accepted_append (index : Fin S) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (kid : Std.U64) (log : List (Entry baseSpec S B)) (last : Entry baseSpec S B) (n : Nat) :
    AcceptedSequence index route decode kid (log ++ [last]) n ↔ AcceptedSequence index route decode kid log n ∨
      ∃ raw decrypted frame, serverOpen last = some (index, raw, .Some decrypted) ∧ route raw = some kid ∧
        decode raw = some frame ∧ frame.sequence.val = n := by
  constructor
  · rintro ⟨entry, present, rest⟩
    rcases List.mem_append.mp present with old | new
    · exact Or.inl ⟨entry, old, rest⟩
    · rw [List.mem_singleton] at new
      subst new
      exact Or.inr rest
  · rintro (⟨entry, present, rest⟩ | rest)
    · exact ⟨entry, List.mem_append_left _ present, rest⟩
    · exact ⟨last, List.mem_append_right _ (List.mem_singleton_self _), rest⟩

/-- A reacceptance in a transcript with one appended entry is a reacceptance of the prefix or is witnessed by the appended entry, which accepted a sequence already accepted in the prefix. -/
theorem reaccepted_append (index : Fin S) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (kid : Std.U64) (log : List (Entry baseSpec S B)) (last : Entry baseSpec S B)
    (again : Reaccepted index route decode kid (log ++ [last])) :
    Reaccepted index route decode kid log ∨ ∃ raw decrypted frame, serverOpen last = some (index, raw, .Some decrypted) ∧
      route raw = some kid ∧ decode raw = some frame ∧ AcceptedSequence index route decode kid log frame.sequence.val := by
  obtain ⟨before, entry, after, raw, decrypted, frame, split, opened, routed, decoded, earlier⟩ := again
  rcases split_append log [last] before after entry split with ⟨middle, rfl, _⟩ | ⟨middle, single, rfl⟩
  · exact Or.inl ⟨before, entry, middle, raw, decrypted, frame, rfl, opened, routed, decoded, earlier⟩
  · cases middle with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at single
      obtain ⟨rfl, rfl⟩ := single
      exact Or.inr ⟨raw, decrypted, frame, opened, routed, decoded, by simpa only [List.append_nil] using earlier⟩
    | cons head tail =>
      simp only [List.cons_append, List.cons.injEq] at single
      exact absurd single.2.symm (by simp)

/-- Exact replays are counted: appending an accepted receive of the same bytes as an earlier accepted receive at the same peer gives a reacceptance. -/
theorem replay_reaccepted (index : Fin S) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (kid : Std.U64) (log : List (Entry baseSpec S B)) (raw : Pqxdh.Bytes) (first second : RawCtxWholeOwner.Decrypted)
    (frame : RawCtxReceive.DecodedFrame) (routed : route raw = some kid) (decoded : decode raw = some frame)
    (earlier : serverRawEntry index raw (.Some first) ∈ log) :
    Reaccepted index route decode kid (log ++ [serverRawEntry index raw (.Some second)]) :=
  ⟨log, _, [], raw, second, frame, rfl, rfl, routed, decoded, _, earlier, raw, first, frame, rfl, routed, decoded, rfl⟩

/-- A second accepted sequence-one record is counted: two accepted receives at the same peer whose frames both have sequence one give a reacceptance. -/
theorem second_first_reaccepted (index : Fin S) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (kid : Std.U64) (before middle after : List (Entry baseSpec S B))
    (firstRaw secondRaw : Pqxdh.Bytes) (first second : RawCtxWholeOwner.Decrypted) (firstFrame secondFrame : RawCtxReceive.DecodedFrame)
    (firstRouted : route firstRaw = some kid) (firstDecoded : decode firstRaw = some firstFrame) (firstOne : firstFrame.sequence.val = 1)
    (secondRouted : route secondRaw = some kid) (secondDecoded : decode secondRaw = some secondFrame)
    (secondOne : secondFrame.sequence.val = 1) :
    Reaccepted index route decode kid
      (before ++ serverRawEntry index firstRaw (.Some first) :: middle ++ serverRawEntry index secondRaw (.Some second) :: after) :=
  ⟨before ++ serverRawEntry index firstRaw (.Some first) :: middle, serverRawEntry index secondRaw (.Some second), after,
    secondRaw, second, secondFrame, by simp, rfl, secondRouted, secondDecoded, serverRawEntry index firstRaw (.Some first),
    by simp, firstRaw, first, firstFrame, rfl, firstRouted, firstDecoded, firstOne.trans secondOne.symm⟩

end Event

section ReplayPost
open PqxdhFirstBeaconRecordIntegrity PqxdhFirstBeaconRecordCanonical
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))

/-- The replay proxy: run `post0` while logging its transcript and output its bit together with a canonical first-record forgery or a reacceptance at the registered Server peer. -/
noncomputable def replayPost : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1) :=
  fun selection reply => replayBit env.index env.route env.decode env.recordWriter reply <$> logged (post0 selection reply) []

/-- The replay proxy makes exactly the requests of `post0`, so it keeps every post query budget. -/
theorem replay_query_bound (selection : program.Selection) (reply : RustM (Option PqxdhServerRegistrationPublication.Response))
    (predicate : (PostSpec baseSpec S (B + 1)).Domain → Prop) [DecidablePred predicate] (bound : Nat) :
    (replayPost env program post0 selection reply).IsQueryBoundP predicate bound ↔
      (post0 selection reply).IsQueryBoundP predicate bound := by
  simp only [replayPost, isQueryBoundP_map_iff]
  exact logged_queries predicate (post0 selection reply) [] bound

/-- The original certificate transported to the replay proxy: only the post budget refers to the post, and it is unchanged. It is provided for downstream use; the main theorem keeps the certificate of `post0`. -/
def replayCertificate (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post0) :
    PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program (replayPost env program post0) :=
  { c with
    postBound := by
      intro selection reply kind
      exact (replay_query_bound env program post0 selection reply _ _).mpr (c.postBound selection reply kind) }

end ReplayPost
section Compiler
open PqxdhFirstBeaconRecordIntegrity RawCtxGenericRoleStorage
variable {ι Chain M P I D K X Response Shared Origin : Type} {baseSpec : OracleSpec ι} {S B : Nat}

/-- Transcript invariant for the registered peer `kid` of Server `index`: the peer is installed with a valid control that consumed every sequence accepted in the transcript, and no sequence was accepted twice. -/
def Tracks (index : Fin S) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) (kid : Std.U64)
    (log : List (Entry baseSpec S B)) (front : PqxdhInitialPendingPost.Front Chain M P I D K S B) : Prop :=
  PeerTracks (AcceptedSequence index route decode kid log) kid (front.roles.1.1 index).server ∧
    ¬Reaccepted index route decode kid log

/-- Appending an entry that is not an accepted Server raw receive at `index` keeps the invariant for any tracked Server state. -/
theorem tracks_quiet (index : Fin S) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (kid : Std.U64) (log : List (Entry baseSpec S B)) (last : Entry baseSpec S B)
    (after : PqxdhInitialPendingPost.Front Chain M P I D K S B)
    (quiet : ∀ raw decrypted, serverOpen last ≠ some (index, raw, .Some decrypted))
    (peer : PeerTracks (AcceptedSequence index route decode kid log) kid (after.roles.1.1 index).server)
    (once : ¬Reaccepted index route decode kid log) : Tracks index route decode kid (log ++ [last]) after := by
  refine ⟨tracks_mono _ _ kid _ (fun n holds => ?_) peer, fun again => ?_⟩
  · rcases (accepted_append index route decode kid log last n).mp holds with old | ⟨raw, decrypted, frame, opened, _⟩
    · exact old
    · exact absurd opened (quiet raw decrypted)
  · rcases reaccepted_append index route decode kid log last again with old | ⟨raw, decrypted, frame, opened, _⟩
    · exact once old
    · exact absurd opened (quiet raw decrypted)

/-- Appending an accepted-or-rejected Server raw receive at `index` whose acceptance is tracked keeps the invariant. -/
theorem tracks_raw (index : Fin S) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (kid : Std.U64) (log : List (Entry baseSpec S B)) (raw : Pqxdh.Bytes) (reply : core.option.Option RawCtxWholeOwner.Decrypted)
    (after : PqxdhInitialPendingPost.Front Chain M P I D K S B)
    (fresh : ∀ decrypted frame, reply = .Some decrypted → route raw = some kid → decode raw = some frame →
      ¬AcceptedSequence index route decode kid log frame.sequence.val)
    (peer : PeerTracks (fun n => AcceptedSequence index route decode kid log n ∨ ∃ decrypted frame, reply = .Some decrypted ∧
      route raw = some kid ∧ decode raw = some frame ∧ frame.sequence.val = n) kid (after.roles.1.1 index).server)
    (once : ¬Reaccepted index route decode kid log) :
    Tracks index route decode kid (log ++ [serverRawEntry index raw reply]) after := by
  refine ⟨tracks_mono _ _ kid _ (fun n holds => ?_) peer, fun again => ?_⟩
  · rcases (accepted_append index route decode kid log _ n).mp holds with old | ⟨raw', decrypted, frame, opened, routed, decoded, sequence⟩
    · exact Or.inl old
    · simp only [serverRawEntry, serverOpen, Option.some.injEq, Prod.mk.injEq] at opened
      obtain ⟨_, rfl, rfl⟩ := opened
      exact Or.inr ⟨decrypted, frame, rfl, routed, decoded, sequence⟩
  · rcases reaccepted_append index route decode kid log _ again with old | ⟨raw', decrypted, frame, opened, routed, decoded, earlier⟩
    · exact once old
    · simp only [serverRawEntry, serverOpen, Option.some.injEq, Prod.mk.injEq] at opened
      obtain ⟨_, rfl, rfl⟩ := opened
      exact fresh decrypted frame rfl routed decoded earlier

/-- One post request of the actual pending-branch compiler keeps the transcript invariant of the registered peer. -/
theorem compiler_tracks (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (kid : Std.U64)
    (log : List (Entry baseSpec S B)) (query : (PostSpec baseSpec S B).Domain)
    (before : PqxdhInitialPendingPost.Front Chain M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)
    (tracks : Tracks index route decode kid log before.1)
    (result : (PostSpec baseSpec S B).Range query ×
      (PqxdhInitialPendingPost.Front Chain M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B))
    (supported : result ∈ support ((PqxdhInitialOriginPost.compiler (X := X) (Response := Response)
      (extra := PqxdhPrivateKemSource.SelectorSpec baseSpec) mark sender route decode query).run before)) :
    Tracks index route decode kid (log ++ [⟨query, result.1⟩]) result.2.1 := by
  rcases query with (((⟨i, request⟩ | (⟨b, request⟩ | request)) | reveal) | selector) | ⟨b, raw⟩
  · simp only [PqxdhInitialOriginPost.compiler, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨live, liveReached, rfl⟩ := supported
    have liveSource := support_simulate _ _ liveReached
    simp only [RawCtxPendingFamilyLiveQueries.compiler, StateT.run, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at liveSource
    obtain ⟨roles, rolesReached, rfl⟩ := liveSource
    have rolesSource := support_simulate _ _ rolesReached
    simp only [RawCtxGenericFamilyFrontend.impl, StateT.run, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at rolesSource
    obtain ⟨served, servedReached, rfl⟩ := rolesSource
    by_cases same : i = index
    · subst same
      rcases request with ⟨plaintext, other⟩ | raw
      · simp only [RawCtxGenericServer.serverImpl] at servedReached
        refine tracks_quiet i route decode kid log _ _ (fun raw decrypted opened => by cases opened) ?_ tracks.2
        simp only [Function.update_self]
        exact send_tracks sender plaintext other _ _ kid tracks.1 served servedReached
      · simp only [RawCtxGenericServer.serverImpl] at servedReached
        obtain ⟨fresh, peer⟩ := raw_tracks route decode raw _ _ kid tracks.1 served servedReached
        refine tracks_raw i route decode kid log raw served.1 _ fresh ?_ tracks.2
        simpa only [Function.update_self] using peer
    · refine tracks_quiet index route decode kid log _ _ (fun raw decrypted opened => ?_) ?_ tracks.2
      · rcases request with ⟨plaintext, other⟩ | raw'
        · cases opened
        · simp only [serverOpen, Option.some.injEq, Prod.mk.injEq] at opened
          exact same opened.1
      · simpa only [Function.update_of_ne (Ne.symm same)] using tracks.1
  · simp only [PqxdhInitialOriginPost.compiler, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨live, liveReached, rfl⟩ := supported
    have liveSource := support_simulate _ _ liveReached
    simp only [RawCtxPendingFamilyLiveQueries.compiler, StateT.run, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at liveSource
    obtain ⟨roles, rolesReached, rfl⟩ := liveSource
    have rolesSource := support_simulate _ _ rolesReached
    simp only [RawCtxGenericFamilyFrontend.impl, StateT.run, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at rolesSource
    obtain ⟨served, servedReached, rfl⟩ := rolesSource
    exact tracks_quiet index route decode kid log _ _ (fun raw decrypted opened => by cases opened) tracks.1 tracks.2
  · simp only [PqxdhInitialOriginPost.compiler, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨live, liveReached, rfl⟩ := supported
    have liveSource := support_simulate _ _ liveReached
    simp only [RawCtxPendingFamilyLiveQueries.compiler, StateT.run, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at liveSource
    obtain ⟨roles, rolesReached, rfl⟩ := liveSource
    have rolesSource := support_simulate _ _ rolesReached
    simp only [RawCtxGenericFamilyFrontend.impl, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at rolesSource
    obtain ⟨served, servedReached, rfl⟩ := rolesSource
    exact tracks_quiet index route decode kid log _ _ (fun raw decrypted opened => by cases opened) tracks.1 tracks.2
  · simp only [PqxdhInitialOriginPost.compiler, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨live, liveReached, rfl⟩ := supported
    have liveSource := support_simulate _ _ liveReached
    simp only [RawCtxPendingFamilyLiveQueries.compiler, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at liveSource
    obtain ⟨reply, _, rfl⟩ := liveSource
    exact tracks_quiet index route decode kid log _ _ (fun raw decrypted opened => by cases opened) tracks.1 tracks.2
  · simp only [PqxdhInitialOriginPost.compiler, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    exact tracks_quiet index route decode kid log _ _ (fun raw decrypted opened => by cases opened) tracks.1 tracks.2
  · simp only [PqxdhInitialOriginPost.compiler, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨finished, _, rfl⟩ := supported
    exact tracks_quiet index route decode kid log _ _ (fun raw decrypted opened => by cases opened) tracks.1 tracks.2

/-- A transcript invariant preserved by every request of a stateful implementation holds at every reachable end of a logged run. -/
theorem logged_invariant {σ κ Result : Type} {target : OracleSpec κ}
    (impl : QueryImpl (PostSpec baseSpec S B) (StateT σ (OracleComp target)))
    (holds : List (Entry baseSpec S B) → σ → Prop)
    (step : ∀ log state query, holds log state → ∀ result ∈ support ((impl query).run state),
      holds (log ++ [⟨query, result.1⟩]) result.2)
    (client : OracleComp (PostSpec baseSpec S B) Result) (log : List (Entry baseSpec S B)) (state : σ)
    (start : holds log state) (result : (Result × List (Entry baseSpec S B)) × σ)
    (supported : result ∈ support ((simulateQ impl (logged client log)).run state)) : holds result.1.2 result.2 := by
  induction client using OracleComp.inductionOn generalizing log state result with
  | pure value =>
    simp only [logged, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact start
  | query_bind query next ih =>
    simp only [logged, simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
    simp only [recorder, StateT.run] at supported
    simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, mem_support_bind_iff] at supported
    obtain ⟨reply, replyReached, supported⟩ := supported
    change reply ∈ support (StateT.run (impl query >>= fun x => pure (x, log ++ [⟨query, x⟩])) state) at replyReached
    simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at replyReached
    obtain ⟨answered, answeredReached, rfl⟩ := replyReached
    exact ih answered.1 _ answered.2 (step log state query start answered answeredReached) result supported

end Compiler
section Builder
open PqxdhInitialGenericPublication
variable {Kernel Metadata PeerMetadata ConsumedIds κ : Type} {spec : OracleSpec κ}

/-- The registration first-send tail installs, at the candidate key identifier, a kernel reached by one send of `kernel`. -/
theorem after_installed (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (OracleComp spec))
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (kernel : Kernel) (metadata : PeerMetadata)
    (state : State Kernel Metadata PeerMetadata ConsumedIds)
    (result : Option PqxdhServerRegistrationPublication.Response × State Kernel Metadata PeerMetadata ConsumedIds)
    (supported : result ∈ support (afterInitialization calls aux candidate authenticated kernel metadata state))
    (response : PqxdhServerRegistrationPublication.Response) (replied : result.1 = some response) :
    ∃ found, result.2.server.peers response.keyId = some found ∧
      ∃ context, ∃ sent ∈ support (calls.send kernel context), sent.1 = found.kernel := by
  unfold afterInitialization at supported
  simp only [mem_support_bind_iff] at supported
  obtain ⟨sent, sentFound, erased, _, rest⟩ := supported
  rcases sent with ⟨advanced, encrypted⟩
  cases encrypted with
  | none =>
    simp only [support_pure, Set.mem_singleton_iff] at rest
    subst rest
    cases replied
  | some encrypted =>
    simp only [mem_support_bind_iff] at rest
    obtain ⟨serialized, _, rest⟩ := rest
    cases serialized with
    | none =>
      simp only [support_pure, Set.mem_singleton_iff] at rest
      subst rest
      cases replied
    | some serialized =>
      simp only [support_pure, Set.mem_singleton_iff] at rest
      subst rest
      obtain rfl := Option.some.inj replied
      exact ⟨⟨candidate.beacon_identity_public_key, advanced, metadata⟩, by simp only [publish, Function.update_self],
        _, _, sentFound, rfl⟩

/-- A successful registration candidate installs its key identifier with a kernel reached by one send of the initial kernel. -/
theorem candidate_installed (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (OracleComp spec))
    (initial : RustM Kernel) (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : State Kernel Metadata PeerMetadata ConsumedIds)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response × State Kernel Metadata PeerMetadata ConsumedIds))
    (supported : result ∈ support (PqxdhInitialGenericBuilder.candidate calls aux initial candidate data metadata state))
    (response : PqxdhServerRegistrationPublication.Response) (final : State Kernel Metadata PeerMetadata ConsumedIds)
    (replied : result = ok (some response, final)) :
    ∃ found, final.server.peers response.keyId = some found ∧ ∃ kernel, initial = ok kernel ∧
      ∃ context, ∃ sent ∈ support (calls.send kernel context), sent.1 = found.kernel := by
  unfold PqxdhInitialGenericBuilder.candidate at supported
  simp only [mem_support_bind_iff] at supported
  obtain ⟨valid, _, rest⟩ := supported
  have none_case : result ∈ support (pure (ok (none, state)) : OracleComp spec (RustM (Option PqxdhServerRegistrationPublication.Response ×
      State Kernel Metadata PeerMetadata ConsumedIds))) → False := by
    intro reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst reached
    simp at replied
  have stop_case : ∀ (stopped : RustM (Option PqxdhServerRegistrationPublication.Response ×
      State Kernel Metadata PeerMetadata ConsumedIds)), (∀ value, stopped ≠ ok value) →
      result ∈ support (pure stopped : OracleComp spec _) → False := by
    intro stopped notOk reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst reached
    exact notOk _ replied
  by_cases checked : (!valid) = true
  · rw [ite_eq_left checked] at rest
    exact (none_case rest).elim
  rw [ite_eq_right checked, mem_support_bind_iff] at rest
  obtain ⟨reserved, _, rest⟩ := rest
  by_cases reservedFlag : (!reserved) = true
  · rw [ite_eq_left reservedFlag] at rest
    exact (none_case rest).elim
  rw [ite_eq_right reservedFlag] at rest
  cases initial with
  | fail error => exact (stop_case _ (fun _ => by simp) rest).elim
  | div => exact (stop_case _ (fun _ => by simp) rest).elim
  | ok kernel =>
    simp only [PqxdhInitialGenericBuilder.continueRust] at rest
    by_cases empty : List.isEmpty (data.getD PqxdhServerRegistrationPublication.registrationWitness) = true
    · rw [ite_eq_left empty] at rest
      exact (none_case rest).elim
    rw [ite_eq_right empty] at rest
    by_cases bounded : 8 + List.length (data.getD PqxdhServerRegistrationPublication.registrationWitness) ≤ Usize.max
    swap
    · rw [ite_eq_right bounded] at rest
      exact (none_case rest).elim
    rw [ite_eq_left bounded, mem_support_bind_iff] at rest
    obtain ⟨allocated, _, rest⟩ := rest
    by_cases allocatedFlag : (!allocated) = true
    · rw [ite_eq_left allocatedFlag] at rest
      exact (none_case rest).elim
    rw [ite_eq_right allocatedFlag] at rest
    cases bound : candidate.key_id_binding with
    | fail error =>
      simp only [bound] at rest
      exact (stop_case _ (fun _ => by simp) rest).elim
    | div =>
      simp only [bound] at rest
      exact (stop_case _ (fun _ => by simp) rest).elim
    | ok binding =>
      simp only [bound] at rest
      rw [support_map] at rest
      obtain ⟨tail, tailFound, rfl⟩ := rest
      simp only [RustM.ok.injEq] at replied
      obtain ⟨found, peers, moves⟩ := after_installed calls aux candidate _ kernel metadata state tail tailFound response
        (by rw [replied])
      refine ⟨found, ?_, kernel, rfl, moves⟩
      rw [replied] at peers
      exact peers

/-- A successful Ready registration installs its key identifier with a kernel reached by one send of the initial kernel. -/
theorem ready_installed (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (OracleComp spec))
    (initial : RustM Kernel) (binding : pqxdh.ServerBinding) (ready : PqxdhPrivateAcceptedRoot.Ready) (metadata : PeerMetadata)
    (state : State Kernel Metadata PeerMetadata ConsumedIds)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response × State Kernel Metadata PeerMetadata ConsumedIds))
    (supported : result ∈ support (PqxdhInitialGenericBuilder.readyBuild source calls aux initial binding ready metadata state))
    (response : PqxdhServerRegistrationPublication.Response) (final : State Kernel Metadata PeerMetadata ConsumedIds)
    (replied : result = ok (some response, final)) :
    ∃ found, final.server.peers response.keyId = some found ∧ ∃ kernel, initial = ok kernel ∧
      ∃ context, ∃ sent ∈ support (calls.send kernel context), sent.1 = found.kernel := by
  have stop_case : ∀ (stopped : RustM (Option PqxdhServerRegistrationPublication.Response ×
      State Kernel Metadata PeerMetadata ConsumedIds)), (stopped ≠ ok (some response, final)) →
      result ∈ support (pure stopped : OracleComp spec _) → False := by
    intro stopped notOk reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst reached
    exact notOk replied
  unfold PqxdhInitialGenericBuilder.readyBuild PqxdhInitialGenericBuilder.usedBuild at supported
  cases following : pqxdh.server_next_key_id state.control with
  | fail error =>
    simp only [following, PqxdhInitialGenericBuilder.continueRust] at supported
    exact (stop_case _ (by simp) supported).elim
  | div =>
    simp only [following, PqxdhInitialGenericBuilder.continueRust] at supported
    exact (stop_case _ (by simp) supported).elim
  | ok next =>
    simp only [following, PqxdhInitialGenericBuilder.continueRust] at supported
    rcases next with next | error
    swap
    · exact (stop_case _ (by simp) supported).elim
    simp only at supported
    generalize PqxdhRegistrationInputs.prepare _ _ _ _ = prepared at supported
    rcases prepared with (candidate | error) | error | _
    · exact candidate_installed calls aux initial candidate _ metadata state result supported response final replied
    · exact (stop_case _ (by simp) supported).elim
    · exact (stop_case _ (by simp) supported).elim
    · exact (stop_case _ (by simp) supported).elim

end Builder
section Built
open PqxdhFirstBeaconRecordIntegrity ratchet.control
variable {ι κ Chain M P I D K X Response Shared : Type} {extra : OracleSpec κ} {baseSpec : OracleSpec ι} {S B : Nat}

/-- The initial kernel built from any initializer response has a valid control. -/
theorem initial_valid (role : Bool) (response : pqxdh.concrete.InitialRatchetKdfResponse)
    (kernel : RawCtxPendingOwnerQueries.Kernel RatchetChain)
    (built : ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf role response = ok kernel) :
    ValidControl kernel.control := by
  unfold PqxdhInitialReplyErasure.kernelOf at built
  rw [pqxdh.concrete.resume_initial_ratchet_kdf_is_core_partition] at built
  generalize pqxdh.split_initial_ratchet_kdf_output _ _ = split at built
  cases split with
  | fail error => cases built
  | div => cases built
  | ok chains =>
    obtain ⟨state, counted, valid, _⟩ := ratchet.refined.from_counters_valid (Material := RatchetMaterial) 0#u64 0#u64
      chains.send_chain chains.receive_chain
    simp only [bind_tc_ok, ConcreteRatchetKernel.new, ConcreteRatchetKernel.from_counters, counted] at built
    cases built
    exact valid.control

/-- After the first Server builder, a successful registration reply names a peer of Server `index` whose kernel has a valid control, so the transcript invariant holds for the empty transcript. -/
theorem build_tracks (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf Chain)) (initialValid : ∀ kernel, initial = ok kernel → ValidControl kernel.control)
    (sender : M → Std.U64) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (front : PqxdhInitialPendingPost.Front Chain M P I D K S B)
    (built : RustM (Option PqxdhServerRegistrationPublication.Response) × PqxdhInitialPendingPost.Front Chain M P I D K S B)
    (supported : built ∈ support ((PqxdhInitialPendingBuilder.build (extra := extra) (X := X) (Response := Response) (Shared := Shared)
      source initial sender index metadata ready).run front))
    (response : PqxdhServerRegistrationPublication.Response) (replied : built.1 = ok (some response))
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    Tracks (baseSpec := baseSpec) index route decode response.keyId [] built.2 := by
  simp only [PqxdhInitialPendingBuilder.build, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨result, reached, rfl⟩ := supported
  rcases outcome : result with value | error | _
  · rw [outcome] at reached replied
    simp only [PqxdhInitialPendingBuilder.reinstall, RustM.ok.injEq] at replied ⊢
    obtain ⟨found, peers, kernel, initialized, context, sent, sentFound, same⟩ :=
      ready_installed source _ _ initial _ ready metadata _ _ reached response value.2 (by rw [← replied])
    have kept := send_result kernel context sent (support_simulate _ _ sentFound)
    refine ⟨⟨found, ?_, ?_, fun n accepted => ?_⟩, fun again => ?_⟩
    · simp only [PqxdhInitialPendingBuilder.install, Function.update_self]
      exact peers
    · rw [← same]
      exact (initialValid kernel initialized).of_receive_eq _ kept.1 kept.2
    · obtain ⟨entry, present, _⟩ := accepted
      cases present
    · obtain ⟨before, entry, after, _, _, _, split, _⟩ := again
      simp at split
  · rw [outcome] at replied
    simp [PqxdhInitialPendingBuilder.reinstall] at replied
  · rw [outcome] at replied
    simp [PqxdhInitialPendingBuilder.reinstall] at replied

end Built
section Client
open PqxdhFirstBeaconRecordIntegrity PqxdhFirstBeaconRecordCanonical
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (program : Program baseSpec setup.Context S (B + 1))
    (post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))

/-- Without a reacceptance the replay bit is the canonical bit. -/
theorem replay_bit (index : Fin S) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (writer : RawCtxMixedShared.Writer) (reply : RustM (Option PqxdhServerRegistrationPublication.Response))
    (result : Bool × List (Entry baseSpec S B)) (once : ¬ReplyReaccepted index route decode reply result.2) :
    replayBit index route decode writer reply result = canonicalBit index route decode writer reply result := by
  unfold replayBit canonicalBit
  congr 1
  exact decide_eq_decide.mpr (or_iff_left once)

/-- In the pending branch of the actual game no reachable transcript has a reacceptance at the registered Server peer, for every post and whatever the adversary's bit, before the HB-112 gate is applied: after a successful first Server builder, every reachable final transcript of the logged post run satisfies `¬Reaccepted` at the key identifier of the registration reply. -/
theorem no_reacceptance
    (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State)
    (ready : PqxdhPrivateAcceptedRoot.Ready)
    (built : RustM (Option PqxdhServerRegistrationPublication.Response) ×
      PqxdhInitialPendingPost.Front RatchetChain M P (PqxdhGeneratedBeaconState.IdentityHandle I)
        (PqxdhGeneratedBeaconState.DhPair setup) (PqxdhGeneratedBeaconState.KemHandle K) S (B + 1))
    (reached : built ∈ support (PqxdhInitialPendingBuilder.build (extra := PqxdhPrivateKemSource.SelectorSpec (baseSpec := baseSpec))
        (X := X ⊕ PqxdhPhase2JointIdentity.Converted) (Response := Response) (Shared := PqxdhPhase2DecapsulationRouting.Shared) env.source
      (ConcreteRatchetKernel.refined <$>
        PqxdhInitialReplyErasure.kernelOf false (PqxdhInitialRootLabelService.realInitial env.source ready.root))
      env.senderId env.index env.metadata ready (PqxdhInitialRootEventAccepted.front env program prepared)))
    (response : PqxdhServerRegistrationPublication.Response) (replied : built.1 = .ok (some response)) :
    ∀ final ∈ support ((simulateQ (PqxdhInitialOriginPost.compiler (extra := PqxdhPrivateKemSource.SelectorSpec (baseSpec := baseSpec))
        (X := X ⊕ PqxdhPhase2JointIdentity.Converted) (Response := Response) (Shared := PqxdhPhase2DecapsulationRouting.Shared)
        (PqxdhInitialSelectedOrigin.mark env.source (PqxdhInitialRootEventAccepted.selectedMessage env program prepared ready))
        env.senderId env.route env.decode) (logged (post0 prepared.1.context.selection.1 built.1) [])).run
      (built.2, PqxdhInitialOriginPost.afterBuilder PqxdhInitialSourcePublication.empty built.2 env.index true built.1)),
      ¬Reaccepted env.index env.route env.decode response.keyId final.1.2 := by
  intro final finalReached
  have start : Tracks (baseSpec := baseSpec) env.index env.route env.decode response.keyId [] built.2 :=
    build_tracks env.source _ (fun kernel built => initial_valid false _ kernel built) env.senderId env.index env.metadata
      ready _ built reached response replied env.route env.decode
  have tracks := logged_invariant (PqxdhInitialOriginPost.compiler
    (PqxdhInitialSelectedOrigin.mark env.source (PqxdhInitialRootEventAccepted.selectedMessage env program prepared ready))
    env.senderId env.route env.decode)
    (fun log state => Tracks env.index env.route env.decode response.keyId log state.1)
    (fun log state query holds result reached => compiler_tracks _ env.senderId env.route env.decode env.index response.keyId
      log query state holds result reached)
    (post0 prepared.1.context.selection.1 built.1) [] _ start final finalReached
  exact tracks.2

/-- In the pending branch of the actual game, two logged proxies of `post0` whose bits agree on every transcript without a reacceptance at the registered peer give the same source client: no reachable transcript of the Server raw receives has a reacceptance. -/
theorem client_congr (first second : RustM (Option PqxdhServerRegistrationPublication.Response) →
      Bool × List (Entry baseSpec S (B + 1)) → Bool)
    (agree : ∀ reply result, ¬ReplyReaccepted env.index env.route env.decode reply result.2 → first reply result = second reply result)
    (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State)
    (ready : PqxdhPrivateAcceptedRoot.Ready) :
    PqxdhInitialRootEventAccepted.client env program (fun selection reply => first reply <$> logged (post0 selection reply) [])
        prepared ready =
      PqxdhInitialRootEventAccepted.client env program (fun selection reply => second reply <$> logged (post0 selection reply) [])
        prepared ready := by
  simp only [PqxdhInitialRootEventAccepted.client, PqxdhInitialNativeCarried.original, PqxdhInitialSourceExperiment.execution,
    PqxdhInitialOriginPost.sequence, StateT.run]
  apply bind_congr_of_forall_mem_support
  intro built reached
  simp only [simulateQ_map]
  change StateT.run (_ <$> _) _ = StateT.run (_ <$> _) _
  rw [StateT.run_map, StateT.run_map, map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  apply bind_congr_of_forall_mem_support
  intro final finalReached
  simp only [Function.comp_apply]
  congr 2
  apply agree
  rcases replied : built.1 with (_ | response) | error | _
  · exact id
  · exact no_reacceptance env program post0 prepared ready built reached response replied final finalReached
  · exact id
  · exact id

/-- In the pending branch of the actual game the replay proxy and the canonical proxy give the same source client. -/
theorem client_replay (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State)
    (ready : PqxdhPrivateAcceptedRoot.Ready) :
    PqxdhInitialRootEventAccepted.client env program (replayPost env program post0) prepared ready =
      PqxdhInitialRootEventAccepted.client env program (canonicalPost env program post0) prepared ready :=
  client_congr env program post0 _ _ (fun reply result once => replay_bit env.index env.route env.decode env.recordWriter reply result once)
    prepared ready

end Client
section Pending
open PqxdhFirstBeaconRecordIntegrity PqxdhFirstBeaconRecordCanonical
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain)

/-- The accepted source-event continuation of the replay proxy is that of the canonical proxy. -/
theorem accepted_replay :
    PqxdhInitialRootEventSecrecy.accepted env attachedVerify primitives program (replayPost env program post0)
        selected number ancestors disclosed =
      PqxdhInitialRootEventSecrecy.accepted env attachedVerify primitives program (canonicalPost env program post0)
        selected number ancestors disclosed := by
  funext prepared ready
  simp only [PqxdhInitialRootEventSecrecy.accepted, PqxdhInitialRootEventAccepted.target, client_replay]

/-- The pending-branch game of the replay proxy is the pending-branch game of the canonical proxy. -/
theorem pending_replay :
    PqxdhFirstRecordTarget.pendingActual env baseImpl kem attachedVerify primitives program (replayPost env program post0)
        (PqxdhInitialRootEventSecrecy.accepted env attachedVerify primitives program (replayPost env program post0)
          selected number ancestors disclosed) =
      PqxdhFirstRecordTarget.pendingActual env baseImpl kem attachedVerify primitives program (canonicalPost env program post0)
        (PqxdhInitialRootEventSecrecy.accepted env attachedVerify primitives program (canonicalPost env program post0)
          selected number ancestors disclosed) := by
  rw [accepted_replay]
  rfl

/-- The HB-112 actual game with any post, minus its constant-`false` continuation, is the `true` mass of its pending branch. -/
theorem actual_pending (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1)) :
    (𝒟[PqxdhInitialRootEventSecrecy.actual env baseImpl kem attachedVerify primitives program post selected number ancestors
        disclosed] {true}).toReal -
      (𝒟[PqxdhInitialRootEventExperiment.actual env baseImpl kem attachedVerify primitives program post
        (PqxdhFirstRecordTarget.rejectAll env program)] {true}).toReal =
    (𝒟[PqxdhFirstRecordTarget.pendingActual env baseImpl kem attachedVerify primitives program post
      (PqxdhInitialRootEventSecrecy.accepted env attachedVerify primitives program post selected number ancestors disclosed)]
      {true}).toReal := by
  rw [PqxdhFirstRecordTarget.target_split, ENNReal.toReal_add (PqxdhFirstRecordTarget.true_ne_top _)
    (PqxdhFirstRecordTarget.true_ne_top _), add_sub_cancel_left]

/-- The HB-112 actual game with the replay proxy, minus its constant-`false` continuation, equals the same difference for the canonical proxy: no run of the pending branch has a reacceptance. -/
theorem replay_canonical :
    (𝒟[PqxdhInitialRootEventSecrecy.actual env baseImpl kem attachedVerify primitives program (replayPost env program post0)
        selected number ancestors disclosed] {true}).toReal -
      (𝒟[PqxdhInitialRootEventExperiment.actual env baseImpl kem attachedVerify primitives program (replayPost env program post0)
        (PqxdhFirstRecordTarget.rejectAll env program)] {true}).toReal =
    (𝒟[PqxdhInitialRootEventSecrecy.actual env baseImpl kem attachedVerify primitives program (canonicalPost env program post0)
        selected number ancestors disclosed] {true}).toReal -
      (𝒟[PqxdhInitialRootEventExperiment.actual env baseImpl kem attachedVerify primitives program (canonicalPost env program post0)
        (PqxdhFirstRecordTarget.rejectAll env program)] {true}).toReal := by
  rw [actual_pending, actual_pending, pending_replay]

end Pending

section Zero
open PqxdhFirstBeaconRecordIntegrity PqxdhFirstBeaconRecordCanonical
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateRootSource PqxdhPrivateAcceptedRoot PqxdhInitializerSecrecy PqxdhSourceAuthenticatedRoot PqxdhHiddenRoot
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain)

/-- The logged post bit of the reacceptance proxy: the adversary's own bit and a reacceptance at the registered Server peer. -/
noncomputable def reacceptBit (index : Fin S) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (reply : RustM (Option PqxdhServerRegistrationPublication.Response)) (result : Bool × List (Entry baseSpec S B)) : Bool :=
  result.1 && @decide (ReplyReaccepted index route decode reply result.2) (Classical.propDecidable _)

/-- The reacceptance proxy: run `post0` while logging its transcript and output its bit together with a reacceptance at the registered Server peer. -/
noncomputable def reacceptPost : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1) :=
  fun selection reply => reacceptBit env.index env.route env.decode reply <$> logged (post0 selection reply) []

/-- A stateful simulation into free oracle computations only reaches outputs of the simulated computation. -/
theorem support_run {κ τ σ α : Type} {spec : OracleSpec κ} {target : OracleSpec τ}
    (impl : QueryImpl spec (StateT σ (OracleComp target))) (work : OracleComp spec α) (state : σ) (result : α × σ)
    (reached : result ∈ support ((simulateQ impl work).run state)) : result.1 ∈ support work := by
  induction work using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
    subst reached
    exact Set.mem_singleton _
  | query_bind query next ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at reached
    obtain ⟨reply, _, reached⟩ := reached
    simp only [mem_support_bind_iff]
    exact ⟨reply.1, mem_support_query query reply.1, ih reply.1 reply.2 result reached⟩

/-- In the pending branch of the actual game the accepted source-event continuation of the reacceptance proxy never returns `true`. -/
theorem accepted_reaccept (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (bit : Bool)
    (reached : bit ∈ support (PqxdhInitialRootEventSecrecy.accepted env attachedVerify primitives program
      (reacceptPost env program post0) selected number ancestors disclosed prepared ready)) : bit = false := by
  have silent : PqxdhInitialRootEventAccepted.client env program (reacceptPost env program post0) prepared ready =
      PqxdhInitialRootEventAccepted.client env program (fun selection reply => (fun _ => false) <$> logged (post0 selection reply) [])
        prepared ready :=
    client_congr env program post0 (reacceptBit env.index env.route env.decode) (fun _ _ => false)
      (fun reply result once => by
        unfold reacceptBit
        rw [Bool.and_eq_false_iff]
        exact Or.inr (decide_eq_false_iff_not.mpr once)) prepared ready
  unfold PqxdhInitialRootEventSecrecy.accepted PqxdhInitialRootEventAccepted.target at reached
  rw [silent, support_map] at reached
  obtain ⟨result, resultReached, rfl⟩ := reached
  have clientReached := support_run _ _ _ result resultReached
  simp only [PqxdhInitialRootEventAccepted.client, PqxdhInitialNativeCarried.original, PqxdhInitialSourceExperiment.execution,
    PqxdhInitialOriginPost.sequence, StateT.run, mem_support_bind_iff] at clientReached
  obtain ⟨built, _, clientReached⟩ := clientReached
  simp only [simulateQ_map] at clientReached
  change result.1 ∈ support (StateT.run (_ <$> _) _) at clientReached
  rw [StateT.run_map, support_map] at clientReached
  obtain ⟨final, _, same⟩ := clientReached
  unfold PqxdhInitialRootEventAccepted.decision
  rw [decide_eq_false_iff_not]
  rintro ⟨⟨gate, _⟩, _⟩
  rw [← same] at gate
  cases gate

/-- In the actual game the pending branch of the reacceptance proxy never outputs `true`. -/
theorem pending_reaccept :
    𝒟[PqxdhFirstRecordTarget.pendingActual env baseImpl kem attachedVerify primitives program (reacceptPost env program post0)
      (PqxdhInitialRootEventSecrecy.accepted env attachedVerify primitives program (reacceptPost env program post0)
        selected number ancestors disclosed)] {true} = 0 := by
  rw [← prEvent_eq_evalDist_singleton _ true]
  refine prEvent_eq_zero_of_not_mem_support _ fun reached => ?_
  simp only [PqxdhFirstRecordTarget.pendingActual, PqxdhGeneratedNativeContinuation.nativeContinued, mem_support_bind_iff] at reached
  obtain ⟨stopped, _, reached⟩ := reached
  split at reached
  · simp only [support_pure, Set.mem_singleton_iff, Bool.true_eq_false] at reached
  unfold PqxdhFirstRecordTarget.pendingNext at reached
  split at reached
  · simp only [mem_support_bind_iff] at reached
    obtain ⟨ephemeral, _, encapsulated, _, reached⟩ := reached
    unfold PqxdhFirstRecordTarget.pendingAfterEncapsulation at reached
    split at reached
    · simp only [support_pure, Set.mem_singleton_iff, Bool.true_eq_false] at reached
    split at reached
    · simp only [support_pure, Set.mem_singleton_iff, Bool.true_eq_false] at reached
    unfold PqxdhInitialRootEventExperiment.nativeAccepted at reached
    exact Bool.true_eq_false.mp (accepted_reaccept env attachedVerify primitives program post0 selected number ancestors disclosed
      _ _ true (support_simulate _ _ reached)) |>.elim
  · simp only [support_pure, Set.mem_singleton_iff, Bool.true_eq_false] at reached

/-- The HB-112 difference of the reacceptance proxy is zero: the HB-112 actual game with that proxy, minus its constant-`false` continuation, is zero, because its pending branch never returns `true`. The gate-free fact behind it is `no_reacceptance`. -/
theorem reaccepted_zero :
    (𝒟[PqxdhInitialRootEventSecrecy.actual env baseImpl kem attachedVerify primitives program (reacceptPost env program post0)
        selected number ancestors disclosed] {true}).toReal -
      (𝒟[PqxdhInitialRootEventExperiment.actual env baseImpl kem attachedVerify primitives program (reacceptPost env program post0)
        (PqxdhFirstRecordTarget.rejectAll env program)] {true}).toReal = 0 := by
  rw [actual_pending, pending_reaccept, ENNReal.toReal_zero]

end Zero

section Integrity
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity PqxdhFirstBeaconRecordCtx CtxRomAuth AdaptiveCtxSharedHash
open RawCtxSelectedAuthenticationObserver AdaptiveCtxDynamicKnownBounds AdaptiveCtxQueryBounds AdaptiveCtxReceive
open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation
open PqxdhFirstBeaconRecordCanonical (canonicalPost canonicalCertificate ReadWritable)
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅

/-- First Beacon record integrity with replay rejection: the HB-112 actual game with the replay proxy, whose event is the adversary's bit together with a canonical first-record forgery or a reacceptance at the registered Server peer (an accepted record whose decoded frame repeats the sequence of a frame accepted earlier at that peer, which includes a second accepted record whose decoded frame has sequence one and every accepted exact replay of an accepted record; the forgery disjunct reads the opening reply's sequence as in the canonical theorem, the reacceptance disjunct the decoded frame's), minus its constant-`false` continuation, has exactly the bound of `PqxdhFirstRecordStopTagged.first_beacon_record_integrity_stop`: the target and completed-branch losses, the CTX loss, `2^-256` twice and `(1 + qSend + 51 (qRaw + qFinish)) / 2^256`. The premises are exactly those of that theorem; the reacceptance adds no term because no run of the pending branch of the actual game has one. -/
theorem first_beacon_record_integrity_replay
    (post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (b : Fin (B + 1)) (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post0)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem (env0).native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem) (hmac : HmacSha512) (correct : SourceFullCorrect (env0).source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (ctxFallback : ModifiedNonceAeadForgery) (qPrelude : Nat)
    (prepareHash : PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program
      (canonicalPost env0 program post0) qPrelude)
    (small : 1 + postTotal setup env callbacks baseImpl kem program c < 2 ^ 96)
    (writable : ReadWritable env.recordWriter env.decode) :
    (𝒟[PqxdhInitialRootEventSecrecy.actual env0 baseImpl kem attachedVerify primitives program (replayPost env0 program post0)
        (.beacon b) 1#u64 [] []] {true}).toReal -
      (𝒟[PqxdhInitialRootEventExperiment.actual env0 baseImpl kem attachedVerify primitives program (replayPost env0 program post0)
        (PqxdhFirstRecordTarget.rejectAll env0 program)] {true}).toReal ≤
    PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
      (PqxdhFirstRecordTarget.unitPost program (canonicalPost env0 program post0)) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
      (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program (canonicalPost env0 program post0)
        (canonicalCertificate env0 baseImpl kem program post0 c)) hmac fallback ordinaryFallback () +
    PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0)
      hmac fallback ordinaryFallback +
    (ctxLoss setup env callbacks baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0) (firstBeacon b)
      ctxFallback (qPrelude + (1 + postTotal setup env callbacks baseImpl kem program c))
      (1 + postTotal setup env callbacks baseImpl kem program c)).toReal +
    1 / 2 ^ 256 + 1 / 2 ^ 256 +
    ((1 + c.postBudget (.inl .send) + 51 * (c.postBudget (.inl .raw) + c.postBudget (.inr 5)) : ℕ) : ℝ) / 2 ^ 256 := by
  rw [replay_canonical]
  exact PqxdhFirstRecordStopTagged.first_beacon_record_integrity_stop setup env callbacks baseImpl kem attachedVerify primitives
    program post0 b c compatible adapter functional hmac correct fallback ordinaryFallback ctxFallback qPrelude prepareHash small writable

end Integrity
end BeaconcryptCore.Computational.PqxdhFirstRecordReplay

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.plan_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.plan_cases

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.begin_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.begin_admitted

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.begin_consumed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.begin_consumed

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.advance_window' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.advance_window

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.rust_bind_ok' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.rust_bind_ok

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.resume_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.resume_admitted

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.finish_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.finish_none

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.finish_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.finish_some

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.program_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.program_result

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.support_simulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.support_simulate

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.receive_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.receive_result

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.send_begin_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.send_begin_control

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.send_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.send_result

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.owner_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.owner_result

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.tracks_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.tracks_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.tracks_put_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.tracks_put_other

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.tracks_put_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.tracks_put_same

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.raw_tracks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.raw_tracks

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.send_tracks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.send_tracks

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.accepted_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.accepted_append

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.reaccepted_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.reaccepted_append

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.replay_reaccepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.replay_reaccepted

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.second_first_reaccepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.second_first_reaccepted

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.replay_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.replay_query_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.tracks_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.tracks_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.tracks_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.tracks_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.compiler_tracks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.compiler_tracks

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.logged_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.logged_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.after_installed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.after_installed

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.candidate_installed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.candidate_installed

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.ready_installed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.ready_installed

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.initial_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.initial_valid

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.build_tracks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.build_tracks

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.replay_bit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.replay_bit

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.no_reacceptance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.no_reacceptance

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.client_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.client_congr

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.client_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.client_replay

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.accepted_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.accepted_replay

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.pending_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.pending_replay

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.actual_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.actual_pending

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.replay_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.replay_canonical

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.support_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.support_run

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.accepted_reaccept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.accepted_reaccept

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.pending_reaccept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.pending_reaccept

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.reaccepted_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.reaccepted_zero

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordReplay.first_beacon_record_integrity_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordReplay.first_beacon_record_integrity_replay
