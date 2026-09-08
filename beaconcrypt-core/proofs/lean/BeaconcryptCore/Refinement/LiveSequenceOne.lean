import BeaconcryptCore.Refinement.GeneralRegistrationAdmission
import BeaconcryptCore.Computational.RawCtxOwnerOracle
import BeaconcryptCore.Computational.RawCtxSourceSend
import BeaconcryptCore.Refinement.ProtocolComposition

/-!
# Live sequence-one source tokens

These statements preserve the complete source receive/send state, actual optional callback replies and primitive poststates through arbitrary finite live schedules. The Beacon bootstrap uses the actual supplied-root initializer, first successful sequence-one opening and the same plaintext binding. Mathematical unbounded send and explicit no-work rejection form a support overapproximation; reachable native exhaustion is retained.

The KDF interpreter is fixed and functional. Erasing its oracle prefix does not make local reconstruction free. Root/initializer, primitive and outer codec/owner routing interpretations remain explicit; LiveSequenceOneOwner supplies the per-call owner metadata relation. This is neither a source-free probability law nor an applied-pi observation, cryptographic origin or global security theorem. Snapshots, storage persistence, restoration and their consequences are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core.ratchet.control

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace beaconcrypt_core.ratchet.concrete

/-- Complete private process state; the cache is newest first and retains its actual material. -/
structure LiveToken (Context : Type) where
  context : Context
  sendSequence : Nat
  sendChain : ratchet.RatchetChain
  receiveSequence : Nat
  receiveChain : ratchet.RatchetChain
  cache : List (Nat × ratchet.RatchetMaterial)
  room : Nat

/-- The process token represents every active source field and the inactive-slot validity invariant. -/
structure LiveRepresents {Context : Type}
    (entry : ConcreteRatchetKernel) (token : LiveToken Context) : Prop where
  valid : ratchet.refined.ValidRefined entry.refined
  sendSequence : token.sendSequence = entry.refined.control.send_sequence.val
  sendChain : token.sendChain = entry.refined.send_chain
  receiveSequence : token.receiveSequence = entry.refined.control.receive_sequence.val
  receiveChain : token.receiveChain = entry.refined.receive_chain
  cache : NewestCacheRepresents entry.refined token.cache
  room : token.cache.length + token.room = 50

/-- Future derivation keeps original source sequence tags while putting new slots before the old cache. -/
def liveFutureCache {AD PT CT : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (chain : ratchet.RatchetChain) (counter skipped : Nat)
    (old : List (Nat × ratchet.RatchetMaterial)) : List (Nat × ratchet.RatchetMaterial) :=
  ((List.range skipped).map (fun j =>
    (counter + j + 1, Ratchet.msgKeyAt cr chain j))).reverse ++ old

/-- Every generated relative future branch has the exact complete source cache, including all old slots. -/
theorem RelativeFutureResult.live_cache {AD PT CT : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (entry : ConcreteRatchetKernel) (target : Std.U64)
    (published : ratchet.refined.RefinedRatchet ratchet.RatchetChain ratchet.RatchetChain ratchet.RatchetMaterial)
    (result : RelativeFutureResult cr entry target published)
    (old : List (Nat × ratchet.RatchetMaterial))
    (represented : NewestCacheRepresents entry.refined old) :
    NewestCacheRepresents published (liveFutureCache cr entry.refined.receive_chain
      entry.refined.control.receive_sequence.val
      (target.val - entry.refined.control.receive_sequence.val - 1) old) := by
  constructor
  · simp only [liveFutureCache, List.length_append, List.length_reverse,
      List.length_map, List.length_range, represented.1, result.length]
    omega
  · intro j hj
    simp only [liveFutureCache, List.length_append, List.length_reverse,
      List.length_map, List.length_range] at hj ⊢
    by_cases fresh : j < target.val - entry.refined.control.receive_sequence.val - 1
    · obtain ⟨cached, slot, sequence, material⟩ := result.staged
        (target.val - entry.refined.control.receive_sequence.val - 1 - 1 - j) (by omega)
      have address : target.val - entry.refined.control.receive_sequence.val - 1 + old.length - 1 - j =
          entry.refined.control.receive_cache.len.val +
            (target.val - entry.refined.control.receive_sequence.val - 1 - 1 - j) := by
        have := represented.1
        omega
      rw [address, slot, List.getElem?_append_left (by simpa using fresh),
        List.getElem?_reverse (by simpa using fresh)]
      simp [sequence, material, show target.val - entry.refined.control.receive_sequence.val - 1 - 1 - j <
        target.val - entry.refined.control.receive_sequence.val - 1 by omega]
    · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt fresh)]
      simp only [List.length_reverse, List.length_map, List.length_range]
      rw [result.materialPrefix _ (by have := represented.1; omega),
        represented.2 _ (by omega)]
      congr 2; omega

/-- The future worker keeps the send direction and all session fields while advancing the exact receive prefix. -/
def liveFutureToken {AD PT CT Context : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (token : LiveToken Context) (target : Nat) : LiveToken Context :=
  { token with
    receiveSequence := target
    receiveChain := Ratchet.chainAt cr token.receiveChain (target - token.receiveSequence)
    cache := liveFutureCache cr token.receiveChain token.receiveSequence
      (target - token.receiveSequence - 1) token.cache
    room := token.room - (target - token.receiveSequence - 1) }

/-- Future publication preserves the complete state relation for arbitrary current counters and cached materials. -/
theorem RelativeFutureResult.live_represents {AD PT CT Context : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (entry : ConcreteRatchetKernel) (target : Std.U64)
    (published : ratchet.refined.RefinedRatchet ratchet.RatchetChain ratchet.RatchetChain ratchet.RatchetMaterial)
    (result : RelativeFutureResult cr entry target published)
    (token : LiveToken Context) (represented : LiveRepresents entry token) :
    LiveRepresents { refined := published } (liveFutureToken cr token target.val) := by
  refine ⟨result.valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [liveFutureToken, result.sendSequence, result.sendChain,
    result.receiveSequence, result.receiveChain, represented.sendSequence,
    represented.sendChain, represented.receiveSequence, represented.receiveChain]
  · exact result.live_cache cr entry target published token.cache represented.cache
  · simp only [liveFutureCache, List.length_append, List.length_reverse,
      List.length_map, List.length_range]
    have capacity : published.control.receive_cache.len.val ≤ 50 := result.valid.control.capacity
    rw [result.length, ← represented.cache.1] at capacity
    have room := represented.room
    omega

/-- Cached success performs the source's last-slot swap and returns exactly one unit of room. -/
def liveCachedToken {Context : Type} (token : LiveToken Context)
    (index : Nat) : LiveToken Context :=
  { token with cache := registrationCacheSwap token.cache index, room := token.room + 1 }

/-- Every cached source publication preserves the full process-token relation. -/
theorem live_cached_represents {Context : Type}
    (entry : ConcreteRatchetKernel) (token : LiveToken Context)
    (represented : LiveRepresents entry token) (target : Std.U64)
    (prepared : ratchet.refined.PreparedCachedReceive)
    (ready : ratchet.refined.CachedPreparationFacts entry.refined target prepared) :
    ∃ published, ratchet.refined.publish_cached_receive entry.refined prepared = ok published ∧
      LiveRepresents { refined := published }
        (liveCachedToken token (token.cache.length - 1 - prepared.target_slot.val)) := by
  obtain ⟨published, publish, valid, sendChain, receiveChain, cache⟩ :=
    cached_publication_represents_symbolic_swap entry.refined token.cache target prepared
      represented.valid ready represented.cache
  obtain ⟨other, publication, _, control, receiveSequence, _, _, _, _⟩ :=
    ready.publication entry.refined represented.valid target prepared
  have same : other = published := RustM.ok.inj (publication.symm.trans publish)
  subst other
  obtain ⟨finished, finishedEq, _, _, sendSequence, _, _, _⟩ :=
    finish_receive_consumed entry.refined.control target prepared.target_slot
      represented.valid.control.capacity ready.target_live ready.entry
  have committed : finished.state = prepared.committed_control :=
    congrArg (fun value => value.state) (RustM.ok.inj (finishedEq.symm.trans ready.finish))
  have publicationSend : published.control.send_sequence = entry.refined.control.send_sequence :=
    (congrArg (fun state => state.send_sequence) (control.trans committed.symm)).trans sendSequence
  refine ⟨published, publish, valid, ?_, ?_, ?_, ?_, cache, ?_⟩
  all_goals simp only [liveCachedToken, publicationSend, sendChain, receiveChain,
    receiveSequence, represented.sendSequence, represented.sendChain,
    represented.receiveSequence, represented.receiveChain, registrationCacheSwap_length]
  have facts := And.intro represented.room (And.intro represented.cache.1 ready.target_live)
  omega

/-- A branch carries the actual opening material and the exact state to install only after success. -/
inductive LivePrepared {AD PT CT Context : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (token : LiveToken Context) (target : Nat) :
    ratchet.RatchetMaterial → LiveToken Context → Prop
  | cached (index : Fin 50) (material : ratchet.RatchetMaterial)
      (selected : token.cache[index.val]? = some (target, material)) :
      LivePrepared cr token target material (liveCachedToken token index.val)
  | future (skipped : Fin 51)
      (sequence : target = token.receiveSequence + skipped.val + 1)
      (available : skipped.val ≤ token.room) :
      LivePrepared cr token target (Ratchet.msgKeyAt cr token.receiveChain skipped.val)
        (liveFutureToken cr token target)

/-- The cached process branch calls the exact source getter, including its tag validation. -/
theorem live_cached_material {Context : Type}
    (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (prepared : ratchet.refined.PreparedCachedReceive)
    (ready : ratchet.refined.CachedPreparationFacts entry.refined target prepared)
    (material : ratchet.RatchetMaterial)
    (stored : entry.refined.receive_slots.val[prepared.target_slot.val]! =
      core.option.Option.Some { sequence := target, material }) :
    (ReceiveOpen.material
      { entry, context, prepared := .PreparedReceiveCachedCase prepared }) =
        ok (core.option.Option.Some material) := by
  simp only [ReceiveOpen.material, lift, bind_tc_ok, capacity_eq_ok]
  rw [if_neg (by have bound := ready.target_bound; scalar_tac)]
  simp only [BeaconcryptCore.Refinement.RatchetAccessors.material_slots_index _ _ ready.target_bound,
    stored, bind_tc_ok, core.option.Option.as_ref, ready.sequence_eq, if_true]

/-- The process opening and its publication law are fixed before the callback chooses any optional reply. -/
structure LiveOpenRefines {AD PT CT Session Context : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (entry : ConcreteRatchetKernel) (token : LiveToken Session)
    (target : Std.U64) (context : Context) (opened : ReceiveOpen Context)
    (material : ratchet.RatchetMaterial) (after : LiveToken Session) : Prop where
  entry_eq : opened.entry = entry
  context_eq : opened.context = context
  material_eq : opened.material = ok (core.option.Option.Some material)
  sequence_eq : opened.sequence = ok target
  prepared : LivePrepared cr token target.val material after
  finish : ∀ (Output : Type) (reply : core.option.Option Output),
    ∃ next, opened.finish reply = ok (next, reply) ∧
      LiveRepresents next (match reply with | .None => token | .Some _ => after)

/-- Every actual cached opening has a corresponding generated slot branch before any optional reply. -/
theorem live_cached_open {AD PT CT Session Context : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (entry : ConcreteRatchetKernel) (token : LiveToken Session)
    (represented : LiveRepresents entry token) (target : Std.U64) (context : Context)
    (prepared : ratchet.refined.PreparedCachedReceive)
    (ready : ratchet.refined.CachedPreparationFacts entry.refined target prepared) :
    ∃ material after, LiveOpenRefines cr entry token target context
      { entry, context, prepared := .PreparedReceiveCachedCase prepared } material after := by
  obtain ⟨material, stored⟩ := ready.target_material
  let index : Fin 50 := ⟨token.cache.length - 1 - prepared.target_slot.val, by
    have facts := And.intro represented.cache.1 (And.intro ready.target_live represented.room)
    omega⟩
  have back : token.cache.length - 1 - index.val = prepared.target_slot.val := by
    dsimp only [index]
    have facts := And.intro represented.cache.1 ready.target_live
    omega
  have selected : token.cache[index.val]? = some (target.val, material) := by
    simpa only [back, stored, core.option.Option.Some, _root_.Option.map_some] using
      represented.cache.2 index.val (by
        dsimp only [index]
        have facts := And.intro represented.cache.1 ready.target_live
        omega)
  obtain ⟨published, publish, nextRepresents⟩ := live_cached_represents
    entry token represented target prepared ready
  refine ⟨material, liveCachedToken token index.val, rfl, rfl,
    live_cached_material entry target context prepared ready material stored, ?_,
    .cached index material selected, ?_⟩
  · simp only [ReceiveOpen.sequence, ready.sequence_eq]
  · rintro Output (_ | value)
    · exact ⟨entry, rfl, represented⟩
    · exact ⟨{ refined := published }, by simp only [ReceiveOpen.finish, publish, bind_tc_ok], nextRepresents⟩

/-- Every actual future opening has the exact relative-distance branch and both publication outcomes before its reply. -/
theorem live_future_open {AD PT CT Session Context : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (entry : ConcreteRatchetKernel) (token : LiveToken Session)
    (represented : LiveRepresents entry token) (target : Std.U64) (context : Context)
    (opened : ReceiveOpen Context) (ready : RelativeFutureOpen cr entry context target opened) :
    ∃ material after, LiveOpenRefines cr entry token target context opened material after := by
  obtain ⟨pending, entryEq, contextEq, preparedEq, pendingFacts⟩ := ready
  let skipped : Fin 51 := ⟨target.val - entry.refined.control.receive_sequence.val - 1, by
    have capacity := pendingFacts.capacity
    omega⟩
  obtain ⟨published, publish, result, _⟩ := pendingFacts.publication cr entry target pending
  refine ⟨Ratchet.msgKeyAt cr token.receiveChain skipped.val, liveFutureToken cr token target.val,
    entryEq, contextEq, ?_, ?_, .future skipped ?_ ?_, ?_⟩
  · simp only [ReceiveOpen.material, preparedEq, pendingFacts.targetMaterial, represented.receiveChain, skipped]
  · simp only [ReceiveOpen.sequence, preparedEq, pendingFacts.targetSequence]
  · simp only [skipped, represented.receiveSequence]
    have future := pendingFacts.future
    omega
  · have facts := And.intro pendingFacts.capacity (And.intro represented.room represented.cache.1)
    dsimp only [skipped]
    omega
  · rintro Output (_ | value)
    · exact ⟨entry, by simp only [ReceiveOpen.finish, entryEq], represented⟩
    · exact ⟨{ refined := published }, by simp only [ReceiveOpen.finish, preparedEq, entryEq, publish, bind_tc_ok],
        result.live_represents cr entry target published token represented⟩

/-- Every valid source preparation is either an actual no-callback rejection or an exact process opening after its real KDF prefix. -/
theorem live_receive_prepare {AD PT CT Session Context : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (entry : ConcreteRatchetKernel)
    (token : LiveToken Session) (represented : LiveRepresents entry token)
    (target : Std.U64) (context : Context) :
    begin_receive entry target context = ok (.ReceiveRejected entry context) ∨
      ∃ effect opened count material after,
        begin_receive entry target context = ok effect ∧
        ReceiveKdfTrace execute effect (.ReceiveOpenRequested opened) count ∧
        LiveOpenRefines (withInterpreter cr execute) entry token target context opened material after := by
  by_cases future : entry.refined.control.receive_sequence.val < target.val
  · by_cases capacity : entry.refined.control.receive_cache.len.val +
        (target.val - entry.refined.control.receive_sequence.val - 1) ≤ 50
    · obtain ⟨pending, opened, began, trace, prepared⟩ :=
        relative_begin_receive_future_trace cr execute entry context target represented.valid future capacity
      obtain ⟨material, after, related⟩ := live_future_open
        (withInterpreter cr execute) entry token represented target context opened prepared
      exact Or.inr ⟨_, opened, _, material, after, began, trace, related⟩
    · exact Or.inl (begin_receive_capacity_rejected entry target context future (by omega))
  · obtain ⟨found, lookup⟩ := lookup_receive_key_total entry.refined.control target
    cases found with
    | none => exact Or.inl (begin_receive_old_missing entry target context (by omega) lookup)
    | some slot =>
      obtain ⟨prepared, began, ready⟩ := begin_receive_cached_valid
        entry target context represented.valid (by omega) slot lookup
      obtain ⟨material, after, related⟩ := live_cached_open
        (withInterpreter cr execute) entry token represented target context prepared ready
      exact Or.inr ⟨_, _, 0, material, after, began, .refl _, related⟩

open OracleComp BeaconcryptCore.Computational

/-- The source KDF is a fixed functional computation; the reached opening retains an arbitrary lawful effect. -/
def liveReceiveImpl {Context Output : Type} {m : Type → Type}
    [Monad m] (execute : KdfInterpreter)
    (opening : ReceiveOpen Context → m (core.option.Option Output)) :
    QueryImpl (RawCtxOwnerOracle.ReceiveSpec Context Output) m
  | .inl request => pure (execute request)
  | .inr opened => opening opened

/-- Interpreting the actual fixed KDF prefix preserves the entire remaining opening computation. -/
theorem ReceiveKdfTrace.live_interpretation {Context Output : Type}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (execute : KdfInterpreter) (opening : ReceiveOpen Context → m (core.option.Option Output))
    {first last : ReceiveEffect Context} {count : Nat}
    (trace : ReceiveKdfTrace execute first last count) :
    simulateQ (liveReceiveImpl execute opening) (RawCtxOwnerOracle.program first) =
      simulateQ (liveReceiveImpl execute opening) (RawCtxOwnerOracle.program last) := by
  induction trace with
  | refl => rfl
  | step pending next last count resumed tail ih =>
    rw [RawCtxOwnerOracle.program, simulateQ_bind, simulateQ_spec_query]
    simp only [liveReceiveImpl, pure_bind]
    simpa only [RustM.ok.inj ((RawCtxOwnerOracle.resume_exact pending
      (execute pending.request)).symm.trans resumed)] using ih

/-- Only the actual getter material, sequence and retained context reach the private callback; represented openings prove both getter results below. -/
def liveOpening {Context Output : Type} {m : Type → Type} [Monad m]
    (opening : ratchet.RatchetMaterial → Nat → Context → m (core.option.Option Output))
    (opened : ReceiveOpen Context) : m (core.option.Option Output) :=
  match opened.material, opened.sequence with
  | .ok (.Some material), .ok sequence => opening material sequence.val opened.context
  | _, _ => pure .None

/-- The normalized source finish retains its actual optional reply and the corresponding complete token relation. -/
theorem LiveOpenRefines.finish_represents {AD PT CT Session Context Output : Type}
    {cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT}
    {entry : ConcreteRatchetKernel} {token : LiveToken Session}
    {target : Std.U64} {context : Context} {opened : ReceiveOpen Context}
    {material : ratchet.RatchetMaterial} {after : LiveToken Session}
    (related : LiveOpenRefines cr entry token target context opened material after)
    (reply : core.option.Option Output) :
    LiveRepresents (RawCtxOwnerOracle.finish opened reply).1
      (match reply with | .None => token | .Some _ => after) := by
  obtain ⟨next, finished, represented⟩ := related.finish Output reply
  simpa only [RustM.ok.inj ((RawCtxOwnerOracle.finish_exact opened reply).symm.trans finished)] using represented

/-- Source admission fixes rejection or the exact callback and publication before any reply or primitive state is chosen. -/
theorem live_receive_interpretation {AD PT CT Session Context Output : Type}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (entry : ConcreteRatchetKernel)
    (token : LiveToken Session) (represented : LiveRepresents entry token)
    (target : Std.U64) (context : Context)
    (opening : ratchet.RatchetMaterial → Nat → Context → m (core.option.Option Output)) :
    let actual := simulateQ (liveReceiveImpl execute (liveOpening opening))
      (RawCtxOwnerOracle.receive entry target context)
    actual = pure (entry, .None) ∨
      ∃ opened material after,
        LiveOpenRefines (withInterpreter cr execute) entry token target context opened material after ∧
        actual = (do
          let reply ← opening material target.val context
          pure (RawCtxOwnerOracle.finish opened reply)) := by
  obtain rejected | ⟨effect, opened, count, material, after, began, trace, related⟩ :=
    live_receive_prepare cr execute entry token represented target context
  · exact Or.inl (by rw [RawCtxOwnerOracle.receive, RustM.ok.inj
      ((RawCtxOwnerOracle.begin_exact entry target context).symm.trans rejected),
      RawCtxOwnerOracle.program, simulateQ_pure])
  · dsimp only
    refine Or.inr ⟨opened, material, after, related, ?_⟩
    rw [RawCtxOwnerOracle.receive, RustM.ok.inj
      ((RawCtxOwnerOracle.begin_exact entry target context).symm.trans began),
      trace.live_interpretation execute (liveOpening opening),
      RawCtxOwnerOracle.program, simulateQ_bind, simulateQ_spec_query]
    simp only [liveReceiveImpl, liveOpening, related.material_eq,
      related.sequence_eq, related.context_eq, simulateQ_pure]
    rfl

/-- An allocated send step advances even when its actual optional seal fails; receive state stays intact. -/
def liveSendToken {AD PT CT Context : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (token : LiveToken Context) : LiveToken Context :=
  { token with sendSequence := token.sendSequence + 1, sendChain := cr.kdfChain token.sendChain }

/-- Nonexhausted source send selects the same material and next sequence as the live worker. -/
theorem live_send_prepare {AD PT CT Session Context : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (entry : ConcreteRatchetKernel)
    (token : LiveToken Session) (represented : LiveRepresents entry token)
    (context : Context) (active : entry.refined.control.send_sequence ≠ core.num.U64.MAX) :
    ∃ pending ready,
      RawCtxSourceSend.beginSend entry context = .SendKdfRequested pending ∧
      RawCtxSourceSend.resumeSend pending (execute pending.request) = ready ∧
      ready.material = (withInterpreter cr execute).kdfMsg token.sendChain ∧
      ready.sequence.val = token.sendSequence + 1 ∧ ready.context = context ∧
      LiveRepresents ready.advanced (liveSendToken (withInterpreter cr execute) token) := by
  obtain ⟨pending, began, entryEq, contextEq, inputEq, infoEq, sequenceEq,
      nextEq, receiveEq, cacheEq⟩ := RawCtxSourceSend.beginSend_fields entry context active
  obtain ⟨stepped, stepEq, readyEq⟩ := RawCtxSourceSend.resumeSend_fields pending (execute pending.request)
  have selected := RustM.ok.inj (stepEq.symm.trans
    (interpreter_request_refines cr execute entry.refined.send_chain pending.request inputEq infoEq))
  refine ⟨pending, _, began, readyEq, ?_, ?_, contextEq, ?_⟩
  · simp only [selected, represented.sendChain]
  · simpa only [represented.sendSequence] using nextEq
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, represented.room⟩
    all_goals simp only [liveSendToken, entryEq, selected, represented.sendSequence,
      represented.sendChain, represented.receiveSequence, represented.receiveChain,
      ← sequenceEq, nextEq, receiveEq]
    · exact represented.valid.send_update entry.refined pending.committed_control
        _ receiveEq cacheEq
    · simpa only [NewestCacheRepresents, cacheEq] using represented.cache

/-- The send callback sees only its actual selected fields; source allocation remains separate from the optional reply. -/
def liveSendImpl {Context Output : Type} {m : Type → Type} [Monad m]
    (execute : KdfInterpreter)
    (sealing : ratchet.RatchetMaterial → Nat → Context → m (Option Output)) :
    QueryImpl (RawCtxSourceSend.SendSpec Context Output) m
  | .inl request => pure (execute request)
  | .inr ready => sealing ready.material ready.sequence.val ready.context

/-- The actual send computation either stops before KDF at exhaustion or publishes its advanced kernel with every optional sealing result. -/
theorem live_send_interpretation {AD PT CT Session Context Output : Type}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (entry : ConcreteRatchetKernel)
    (token : LiveToken Session) (represented : LiveRepresents entry token)
    (context : Context)
    (sealing : ratchet.RatchetMaterial → Nat → Context → m (Option Output)) :
    let actual := simulateQ (liveSendImpl execute sealing) (RawCtxSourceSend.send entry context)
    (entry.refined.control.send_sequence = core.num.U64.MAX ∧ actual = pure (entry, none)) ∨
      ∃ next, LiveRepresents next (liveSendToken (withInterpreter cr execute) token) ∧
        actual = (do
          let reply ← sealing ((withInterpreter cr execute).kdfMsg token.sendChain)
            (token.sendSequence + 1) context
          pure (next, reply)) := by
  by_cases exhausted : entry.refined.control.send_sequence = core.num.U64.MAX
  · exact Or.inl ⟨exhausted, by rw [RawCtxSourceSend.send_exhausted entry context exhausted, simulateQ_pure]⟩
  · obtain ⟨pending, ready, began, resumed, materialEq, sequenceEq, contextEq, nextRep⟩ :=
      live_send_prepare cr execute entry token represented context exhausted
    refine Or.inr ⟨ready.advanced, nextRep, ?_⟩
    simp only [RawCtxSourceSend.send, began, RawCtxSourceSend.program,
      simulateQ_bind, simulateQ_spec_query, liveSendImpl, pure_bind,
      resumed, materialEq, sequenceEq, contextEq, simulateQ_pure]
    rfl

/-- The mixed interface retains distinct send/receive request and reply types. -/
abbrev LiveSpec (SendContext ReceiveContext SendOutput ReceiveOutput : Type) :=
  (SendContext →ₒ Option SendOutput) + ((Std.U64 × ReceiveContext) →ₒ Option ReceiveOutput)

/-- Both actual source programs use the same complete primitive state between serialized calls. -/
noncomputable def liveSourceImpl
    {SendContext ReceiveContext SendOutput ReceiveOutput PrimitiveState : Type}
    {ι : Type} {base : OracleSpec ι} (execute : KdfInterpreter)
    (sealing : ratchet.RatchetMaterial → Nat → SendContext →
      StateT PrimitiveState (OracleComp base) (Option SendOutput))
    (opening : ratchet.RatchetMaterial → Nat → ReceiveContext →
      StateT PrimitiveState (OracleComp base) (Option ReceiveOutput)) :
    QueryImpl (LiveSpec SendContext ReceiveContext SendOutput ReceiveOutput)
      (StateT (ConcreteRatchetKernel × PrimitiveState) (OracleComp base))
  | .inl context => fun state => do
      let result ← (simulateQ (liveSendImpl execute sealing)
        (RawCtxSourceSend.send state.1 context)).run state.2
      pure (result.1.2, (result.1.1, result.2))
  | .inr (target, context) => fun state => do
      let result ← (simulateQ (liveReceiveImpl execute (liveOpening opening))
        (RawCtxOwnerOracle.receive state.1 target context)).run state.2
      pure (result.1.2, (result.1.1, result.2))

/-- An operational overapproximation has explicit no-work rejection as well as actual callback branches; failed callbacks retain their poststate. -/
inductive LiveStep {AD PT CT Session SendContext ReceiveContext SendOutput ReceiveOutput PrimitiveState : Type}
    {ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (sealing : ratchet.RatchetMaterial → Nat → SendContext →
      StateT PrimitiveState (OracleComp base) (Option SendOutput))
    (opening : ratchet.RatchetMaterial → Nat → ReceiveContext →
      StateT PrimitiveState (OracleComp base) (Option ReceiveOutput)) :
    (LiveToken Session × PrimitiveState) →
      (query : (LiveSpec SendContext ReceiveContext SendOutput ReceiveOutput).Domain) →
      (LiveSpec SendContext ReceiveContext SendOutput ReceiveOutput).Range query →
      (LiveToken Session × PrimitiveState) → Prop
  | rejectSend (state : LiveToken Session × PrimitiveState) (context : SendContext) :
      LiveStep cr sealing opening state (.inl context) none state
  | rejectReceive (state : LiveToken Session × PrimitiveState) (target : Std.U64) (context : ReceiveContext) :
      LiveStep cr sealing opening state (.inr (target, context)) none state
  | send (token : LiveToken Session) (primitive : PrimitiveState) (context : SendContext)
      (reply : Option SendOutput) (after : PrimitiveState)
      (called : (reply, after) ∈ support
        ((sealing (cr.kdfMsg token.sendChain) (token.sendSequence + 1) context).run primitive)) :
      LiveStep cr sealing opening (token, primitive) (.inl context) reply
        (liveSendToken cr token, after)
  | receive (token : LiveToken Session) (primitive : PrimitiveState)
      (target : Std.U64) (context : ReceiveContext) (material : ratchet.RatchetMaterial)
      (committed : LiveToken Session) (reply : Option ReceiveOutput) (after : PrimitiveState)
      (prepared : LivePrepared cr token target.val material committed)
      (called : (reply, after) ∈ support ((opening material target.val context).run primitive)) :
      LiveStep cr sealing opening (token, primitive) (.inr (target, context)) reply
        ((match reply with | none => token | some _ => committed), after)

/-- Every supported actual mixed call has a matching process step with the identical reply and full primitive poststate. -/
theorem live_source_step
    {AD PT CT Session SendContext ReceiveContext SendOutput ReceiveOutput PrimitiveState : Type}
    {ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter)
    (sealing : ratchet.RatchetMaterial → Nat → SendContext →
      StateT PrimitiveState (OracleComp base) (Option SendOutput))
    (opening : ratchet.RatchetMaterial → Nat → ReceiveContext →
      StateT PrimitiveState (OracleComp base) (Option ReceiveOutput))
    (entry : ConcreteRatchetKernel) (token : LiveToken Session)
    (represented : LiveRepresents entry token) (primitive : PrimitiveState)
    (query : (LiveSpec SendContext ReceiveContext SendOutput ReceiveOutput).Domain)
    (result : (LiveSpec SendContext ReceiveContext SendOutput ReceiveOutput).Range query ×
      (ConcreteRatchetKernel × PrimitiveState))
    (actual : result ∈ support ((liveSourceImpl execute sealing opening query).run (entry, primitive))) :
    ∃ after, LiveRepresents result.2.1 after ∧
      LiveStep (withInterpreter cr execute) sealing opening
        (token, primitive) query result.1 (after, result.2.2) := by
  cases query with
  | inl context =>
    obtain ⟨_, rejected⟩ | ⟨next, nextRep, computed⟩ :=
      live_send_interpretation cr execute entry token represented context sealing
    · simp only [liveSourceImpl, StateT.run, rejected] at actual
      change result ∈ support (pure (none, (entry, primitive))) at actual
      simp only [support_pure] at actual
      cases actual
      exact ⟨token, represented, .rejectSend _ context⟩
    · simp only [liveSourceImpl, StateT.run, computed, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at actual
      obtain ⟨sent, actual, rfl⟩ := actual
      change sent ∈ support ((do
        let reply ← sealing ((withInterpreter cr execute).kdfMsg token.sendChain)
          (token.sendSequence + 1) context
        pure (next, reply)).run primitive) at actual
      simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at actual
      obtain ⟨⟨reply, post⟩, called, rfl⟩ := actual
      exact ⟨_, nextRep, .send token primitive context reply post called⟩
  | inr request =>
    rcases request with ⟨target, context⟩
    obtain rejected | ⟨opened, material, after, related, computed⟩ :=
      live_receive_interpretation cr execute entry token represented target context opening
    · simp only [liveSourceImpl, StateT.run, rejected] at actual
      change result ∈ support (pure (none, (entry, primitive))) at actual
      simp only [support_pure] at actual
      cases actual
      exact ⟨token, represented, .rejectReceive _ target context⟩
    · simp only [liveSourceImpl, StateT.run, computed, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at actual
      obtain ⟨received, actual, rfl⟩ := actual
      change received ∈ support ((do
        let reply ← opening material target.val context
        pure (RawCtxOwnerOracle.finish opened reply)).run primitive) at actual
      simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at actual
      obtain ⟨⟨reply, post⟩, called, rfl⟩ := actual
      refine ⟨_, related.finish_represents reply, ?_⟩
      cases reply <;> exact .receive token primitive target context material after _ post related.prepared called

/-- Private traces retain the original dependent request/reply pair for each serialized operation. -/
abbrev LiveTranscript (SendContext ReceiveContext SendOutput ReceiveOutput : Type) :=
  List ((query : (LiveSpec SendContext ReceiveContext SendOutput ReceiveOutput).Domain) ×
    (LiveSpec SendContext ReceiveContext SendOutput ReceiveOutput).Range query)

section Traces
variable {AD PT CT Session SendContext ReceiveContext SendOutput ReceiveOutput PrimitiveState : Type}
  {ι : Type} {base : OracleSpec ι}
  (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
  (execute : KdfInterpreter)
  (sealing : ratchet.RatchetMaterial → Nat → SendContext →
    StateT PrimitiveState (OracleComp base) (Option SendOutput))
  (opening : ratchet.RatchetMaterial → Nat → ReceiveContext →
    StateT PrimitiveState (OracleComp base) (Option ReceiveOutput))

/-- Each source trace step is an actual supported call, with the same complete source and primitive state passed onward. -/
inductive LiveSourceTrace : (ConcreteRatchetKernel × PrimitiveState) →
    LiveTranscript SendContext ReceiveContext SendOutput ReceiveOutput →
    (ConcreteRatchetKernel × PrimitiveState) → Prop
  | nil (state) : LiveSourceTrace state [] state
  | step {state final} (query)
      {result : (LiveSpec SendContext ReceiveContext SendOutput ReceiveOutput).Range query ×
        (ConcreteRatchetKernel × PrimitiveState)} {rest}
      (actual : result ∈ support ((liveSourceImpl execute sealing opening query).run state))
      (tail : LiveSourceTrace result.2 rest final) :
      LiveSourceTrace state (⟨query, result.1⟩ :: rest) final

/-- The process trace uses the explicit token branches, without a source-state or cryptographic-success guard. -/
inductive LiveTrace : (LiveToken Session × PrimitiveState) →
    LiveTranscript SendContext ReceiveContext SendOutput ReceiveOutput →
    (LiveToken Session × PrimitiveState) → Prop
  | nil (state) : LiveTrace state [] state
  | step {state next final} (query) (reply) {rest}
      (actual : LiveStep cr sealing opening state query reply next)
      (tail : LiveTrace next rest final) :
      LiveTrace state (⟨query, reply⟩ :: rest) final

/-- Arbitrarily long source traces embed with their exact typed transcript, complete token and identical primitive poststate. -/
theorem live_source_trace {initial final : ConcreteRatchetKernel × PrimitiveState}
    {transcript : LiveTranscript SendContext ReceiveContext SendOutput ReceiveOutput}
    (trace : LiveSourceTrace execute sealing opening initial transcript final)
    (token : LiveToken Session) (represented : LiveRepresents initial.1 token) :
    ∃ after, LiveRepresents final.1 after ∧
      LiveTrace (withInterpreter cr execute) sealing opening
        (token, initial.2) transcript (after, final.2) := by
  induction trace generalizing token with
  | nil state => exact ⟨token, represented, .nil _⟩
  | @step state final query result rest actual tail ih =>
    obtain ⟨next, nextRep, step⟩ := live_source_step cr execute sealing opening
      state.1 token represented state.2 query result actual
    obtain ⟨after, afterRep, trace⟩ := ih next nextRep
    exact ⟨after, afterRep, .step query result.1 step trace⟩

/-- An actual adaptive client constructs its source trace internally, retaining its complete returned result and state. -/
theorem live_client_trace {Result : Type}
    (client : OracleComp (LiveSpec SendContext ReceiveContext SendOutput ReceiveOutput) Result)
    (state : ConcreteRatchetKernel × PrimitiveState) (result : Result × (ConcreteRatchetKernel × PrimitiveState))
    (actual : result ∈ support ((simulateQ (liveSourceImpl execute sealing opening) client).run state)) :
    ∃ transcript, LiveSourceTrace execute sealing opening state transcript result.2 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure] at actual
    cases actual
    exact ⟨[], .nil _⟩
  | query_bind query next ih =>
    rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, mem_support_bind_iff] at actual
    obtain ⟨step, called, later⟩ := actual
    obtain ⟨rest, trace⟩ := ih step.1 step.2 result later
    exact ⟨⟨query, step.1⟩ :: rest, .step query called trace⟩

/-- Every actual adaptive mixed execution yields one matching typed token trace, without resetting any source or primitive field. -/
theorem live_supported_client {Result : Type}
    (client : OracleComp (LiveSpec SendContext ReceiveContext SendOutput ReceiveOutput) Result)
    (state : ConcreteRatchetKernel × PrimitiveState) (token : LiveToken Session)
    (represented : LiveRepresents state.1 token)
    (result : Result × (ConcreteRatchetKernel × PrimitiveState))
    (actual : result ∈ support ((simulateQ (liveSourceImpl execute sealing opening) client).run state)) :
    ∃ transcript after,
      LiveSourceTrace execute sealing opening state transcript result.2 ∧
      LiveRepresents result.2.1 after ∧
      LiveTrace (withInterpreter cr execute) sealing opening
        (token, state.2) transcript (after, result.2.2) := by
  obtain ⟨transcript, trace⟩ := live_client_trace execute sealing opening client state result actual
  obtain ⟨after, afterRep, process⟩ := live_source_trace cr execute sealing opening trace token represented
  exact ⟨transcript, after, trace, afterRep, process⟩

end Traces

/-- The pre-opening token retains the exact directional chains returned by initialization. -/
def liveInitialToken {Session : Type} (context : Session) (kernel : ConcreteRatchetKernel) :
    LiveToken Session :=
  ⟨context, 0, kernel.refined.send_chain, 0, kernel.refined.receive_chain, [], 50⟩

/-- Actual Beacon initialization supplies the complete empty token, without an assumed crypto-output equation. -/
theorem live_initialize_beacon {AD PT CT Session : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (root : Std.Array Std.U8 32#usize)
    (initial : BeaconcryptCore.Refinement.PqxdhConcreteSession.InitialKdfInterpreter)
    (context : Session) (kernel : ConcreteRatchetKernel)
    (initialized : BeaconcryptCore.Refinement.PqxdhConcreteSession.initializeBeacon root initial = ok kernel) :
    LiveRepresents kernel (liveInitialToken context kernel) := by
  obtain ⟨beaconOrigin, serverOrigin, beacon, server, returned, _, _, _, refined, _⟩ :=
    BeaconcryptCore.Refinement.PqxdhConcreteSession.initial_kernels_refine cr root initial
  cases RustM.ok.inj (returned.symm.trans initialized)
  refine ⟨refined.validRefined, refined.sendSequence.symm, rfl,
    refined.receiveControl.seq.symm, rfl, ⟨?_, by simp [liveInitialToken]⟩, rfl⟩
  have length := refined.receiveControl.cache.length_eq
  simpa only [liveInitialToken, cacheSeqs_length, List.map_nil, List.length_nil] using length.symm

/-- Successful sequence-one opening installs counter one, its actual next chain, an empty cache, and the untouched send direction. -/
def liveCommittedToken {AD PT CT Session : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (context : Session) (kernel : ConcreteRatchetKernel) : LiveToken Session :=
  ⟨context, 0, kernel.refined.send_chain, 1, cr.kdfChain kernel.refined.receive_chain, [], 50⟩

/-- The complete initial token has only the actual first-material branch at sequence one. -/
theorem live_prepared_one {AD PT CT Session : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (context : Session) (kernel : ConcreteRatchetKernel)
    (material : ratchet.RatchetMaterial) (after : LiveToken Session)
    (prepared : LivePrepared cr (liveInitialToken context kernel) 1 material after) :
    material = cr.kdfMsg kernel.refined.receive_chain ∧ after = liveCommittedToken cr context kernel := by
  cases prepared with
  | cached index material selected => simp [liveInitialToken] at selected
  | future skipped sequence available =>
    have zero : skipped.val = 0 := by simp only [liveInitialToken] at sequence; omega
    simp [liveInitialToken, liveFutureToken, liveFutureCache,
      liveCommittedToken, zero, Ratchet.msgKeyAt, Ratchet.chainAt]

/-- A real sequence-one success supplies the committed token and the same actual opening poststate; no fresh initializer is substituted afterward. -/
theorem live_sequence_one
    {AD PT CT Session SendContext ReceiveContext SendOutput ReceiveOutput PrimitiveState : Type}
    {ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter)
    (sealing : ratchet.RatchetMaterial → Nat → SendContext →
      StateT PrimitiveState (OracleComp base) (Option SendOutput))
    (opening : ratchet.RatchetMaterial → Nat → ReceiveContext →
      StateT PrimitiveState (OracleComp base) (Option ReceiveOutput))
    (root : Std.Array Std.U8 32#usize)
    (initial : BeaconcryptCore.Refinement.PqxdhConcreteSession.InitialKdfInterpreter)
    (session : Session) (context : ReceiveContext) (kernel : ConcreteRatchetKernel)
    (initialized : BeaconcryptCore.Refinement.PqxdhConcreteSession.initializeBeacon root initial = ok kernel)
    (primitive post : PrimitiveState) (next : ConcreteRatchetKernel) (plaintext : ReceiveOutput)
    (actual : (some plaintext, (next, post)) ∈ support
      ((liveSourceImpl execute sealing opening (.inr (1#u64, context))).run (kernel, primitive))) :
    LiveRepresents next (liveCommittedToken (withInterpreter cr execute) session kernel) ∧
      (some plaintext, post) ∈ support ((opening ((withInterpreter cr execute).kdfMsg kernel.refined.receive_chain)
        1 context).run primitive) := by
  obtain ⟨after, represented, step⟩ := live_source_step cr execute sealing opening kernel
    (liveInitialToken session kernel) (live_initialize_beacon cr root initial session kernel initialized)
    primitive (.inr (1#u64, context)) (some plaintext, (next, post)) actual
  cases step with
  | receive token primitive target context material committed reply post prepared called =>
    obtain ⟨materialEq, committedEq⟩ := live_prepared_one
      (withInterpreter cr execute) session kernel material committed prepared
    exact ⟨by simpa only [committedEq] using represented,
      by simpa [materialEq] using called⟩

/-- Every process step preserves the actual immutable session payload supplied by the committed owner. -/
theorem LiveStep.session {AD PT CT Session SendContext ReceiveContext SendOutput ReceiveOutput PrimitiveState : Type}
    {ι : Type} {base : OracleSpec ι}
    {cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT}
    {sealing : ratchet.RatchetMaterial → Nat → SendContext →
      StateT PrimitiveState (OracleComp base) (Option SendOutput)}
    {opening : ratchet.RatchetMaterial → Nat → ReceiveContext →
      StateT PrimitiveState (OracleComp base) (Option ReceiveOutput)}
    {state next : LiveToken Session × PrimitiveState}
    {query : (LiveSpec SendContext ReceiveContext SendOutput ReceiveOutput).Domain}
    {reply : (LiveSpec SendContext ReceiveContext SendOutput ReceiveOutput).Range query}
    (step : LiveStep cr sealing opening state query reply next) :
    next.1.context = state.1.context := by
  cases step with
  | rejectSend => rfl
  | rejectReceive => rfl
  | send => rfl
  | receive token primitive target context material committed reply post prepared called =>
    cases reply with
    | none => rfl
    | some value =>
      cases prepared <;> rfl

/-- The immutable committed session payload survives every live continuation. -/
theorem LiveTrace.session {AD PT CT Session SendContext ReceiveContext SendOutput ReceiveOutput PrimitiveState : Type}
    {ι : Type} {base : OracleSpec ι}
    {cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT}
    {sealing : ratchet.RatchetMaterial → Nat → SendContext →
      StateT PrimitiveState (OracleComp base) (Option SendOutput)}
    {opening : ratchet.RatchetMaterial → Nat → ReceiveContext →
      StateT PrimitiveState (OracleComp base) (Option ReceiveOutput)}
    {state next : LiveToken Session × PrimitiveState}
    {transcript : LiveTranscript SendContext ReceiveContext SendOutput ReceiveOutput}
    (trace : LiveTrace cr sealing opening state transcript next) :
    next.1.context = state.1.context := by
  induction trace with
  | nil => rfl
  | step query reply actual tail ih => exact ih.trans actual.session

/-- The source plaintext binding and commit retain the selected pinned Server and assigned handle. -/
theorem live_commit_binding (candidate : beaconcrypt_core.pqxdh.BeaconRegistrationCandidate)
    (sender : Std.U64) (plaintext : Pqxdh.Bytes) (established : beaconcrypt_core.pqxdh.BeaconEstablished)
    (pinned : sender = candidate.server_binding.identity_key_id)
    (committed : BeaconcryptCore.Refinement.ProtocolComposition.commitPlaintext candidate sender plaintext =
      ok (.ok established)) :
    established = ⟨candidate.server_binding, candidate.assigned_key_id⟩ ∧
      8 < plaintext.length ∧ plaintext.take 8 = Pqxdh.LE64 candidate.assigned_key_id.val := by
  rw [BeaconcryptCore.Refinement.ProtocolComposition.commitPlaintext_eq candidate sender plaintext pinned] at committed
  split at committed
  · cases committed
  · split at committed
    · cases committed
    · simp_all

/-- The actual first-opening poststate and extracted plaintext commitment seed every subsequent mixed trace with the committed binding and unchanged associated data. -/
theorem live_authenticated_client
    {AD PT CT SendContext ReceiveContext SendOutput PrimitiveState Result : Type}
    {ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter)
    (sealing : ratchet.RatchetMaterial → Nat → SendContext →
      StateT PrimitiveState (OracleComp base) (Option SendOutput))
    (opening : ratchet.RatchetMaterial → Nat → ReceiveContext →
      StateT PrimitiveState (OracleComp base) (Option Pqxdh.Bytes))
    (candidate : beaconcrypt_core.pqxdh.BeaconRegistrationCandidate) (sender : Std.U64)
    (plaintext : Pqxdh.Bytes) (established : beaconcrypt_core.pqxdh.BeaconEstablished)
    (pinned : sender = candidate.server_binding.identity_key_id)
    (committed : BeaconcryptCore.Refinement.ProtocolComposition.commitPlaintext candidate sender plaintext =
      ok (.ok established))
    (root : Std.Array Std.U8 32#usize)
    (initial : BeaconcryptCore.Refinement.PqxdhConcreteSession.InitialKdfInterpreter)
    (context : ReceiveContext) (kernel first : ConcreteRatchetKernel)
    (initialized : BeaconcryptCore.Refinement.PqxdhConcreteSession.initializeBeaconCandidate candidate root initial = ok kernel)
    (primitive afterFirst : PrimitiveState)
    (firstActual : (some plaintext, (first, afterFirst)) ∈ support
      ((liveSourceImpl execute sealing opening (.inr (1#u64, context))).run (kernel, primitive)))
    (client : OracleComp (LiveSpec SendContext ReceiveContext SendOutput Pqxdh.Bytes) Result)
    (result : Result × (ConcreteRatchetKernel × PrimitiveState))
    (continued : result ∈ support ((simulateQ (liveSourceImpl execute sealing opening) client).run (first, afterFirst))) :
    let session := (established, PqxdhRefinement.absBytes candidate.associated_data)
    ∃ transcript after,
      LiveSourceTrace execute sealing opening (first, afterFirst) transcript result.2 ∧
      LiveRepresents result.2.1 after ∧
      LiveTrace (withInterpreter cr execute) sealing opening
        (liveCommittedToken (withInterpreter cr execute) session kernel, afterFirst)
        transcript (after, result.2.2) ∧
      after.context = (⟨candidate.server_binding, candidate.assigned_key_id⟩,
        PqxdhRefinement.absBytes candidate.associated_data) := by
  have metadata := (live_commit_binding candidate sender plaintext established pinned committed).1
  have bootstrap := (live_sequence_one cr execute sealing opening root initial
    (established, PqxdhRefinement.absBytes candidate.associated_data) context kernel initialized
    primitive afterFirst first plaintext firstActual).1
  obtain ⟨transcript, after, sourceTrace, represented, processTrace⟩ :=
    live_supported_client cr execute sealing opening client (first, afterFirst) _ bootstrap result continued
  exact ⟨transcript, after, sourceTrace, represented, processTrace,
    by simpa only [liveCommittedToken, metadata] using processTrace.session⟩

end beaconcrypt_core.ratchet.concrete

/--
info: 'beaconcrypt_core.ratchet.concrete.RelativeFutureResult.live_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.RelativeFutureResult.live_cache

/--
info: 'beaconcrypt_core.ratchet.concrete.RelativeFutureResult.live_represents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.RelativeFutureResult.live_represents

/--
info: 'beaconcrypt_core.ratchet.concrete.live_cached_represents' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_cached_represents

/--
info: 'beaconcrypt_core.ratchet.concrete.live_cached_material' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_cached_material

/--
info: 'beaconcrypt_core.ratchet.concrete.live_cached_open' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_cached_open

/--
info: 'beaconcrypt_core.ratchet.concrete.live_future_open' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_future_open

/--
info: 'beaconcrypt_core.ratchet.concrete.live_receive_prepare' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_receive_prepare

/--
info: 'beaconcrypt_core.ratchet.concrete.ReceiveKdfTrace.live_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.ReceiveKdfTrace.live_interpretation

/--
info: 'beaconcrypt_core.ratchet.concrete.LiveOpenRefines.finish_represents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.LiveOpenRefines.finish_represents

/--
info: 'beaconcrypt_core.ratchet.concrete.live_receive_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_receive_interpretation

/--
info: 'beaconcrypt_core.ratchet.concrete.live_send_prepare' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_send_prepare

/--
info: 'beaconcrypt_core.ratchet.concrete.live_send_interpretation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_send_interpretation

/--
info: 'beaconcrypt_core.ratchet.concrete.live_source_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_source_step

/--
info: 'beaconcrypt_core.ratchet.concrete.live_source_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_source_trace

/--
info: 'beaconcrypt_core.ratchet.concrete.live_client_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_client_trace

/--
info: 'beaconcrypt_core.ratchet.concrete.live_supported_client' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_supported_client

/--
info: 'beaconcrypt_core.ratchet.concrete.live_initialize_beacon' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_initialize_beacon

/--
info: 'beaconcrypt_core.ratchet.concrete.live_prepared_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_prepared_one

/--
info: 'beaconcrypt_core.ratchet.concrete.live_sequence_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_sequence_one

/--
info: 'beaconcrypt_core.ratchet.concrete.LiveStep.session' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.LiveStep.session

/--
info: 'beaconcrypt_core.ratchet.concrete.LiveTrace.session' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.LiveTrace.session

/--
info: 'beaconcrypt_core.ratchet.concrete.live_commit_binding' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_commit_binding

/--
info: 'beaconcrypt_core.ratchet.concrete.live_authenticated_client' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_authenticated_client
