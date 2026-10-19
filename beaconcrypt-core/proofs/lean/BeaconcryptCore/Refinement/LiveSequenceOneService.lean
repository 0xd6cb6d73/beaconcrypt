import BeaconcryptCore.Refinement.LiveSequenceOne

/-!
# Functional operations of the live sequence-one worker

These eight statements connect the concrete cursor and private cache search/rebuild operations to the source token, retaining exact counters, actual chains/materials, cache order and capacity. They describe the worker operations used by the separate ProVerif draft.

They do not prove the complete replicated applied-pi execution, network observation, knowledge or Horn-token linearity semantics. The source-to-ideal cryptographic hop remains separate. Only live execution is in scope; no storage or restoration interface is modeled.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core.ratchet.control
open OracleComp BeaconcryptCore.Computational

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace beaconcrypt_core.ratchet.concrete

/-- The pending worker carries the saved token separately from these four staged fields. -/
structure LiveCursor where
  counter : Nat
  chain : ratchet.RatchetChain
  cache : List (Nat × ratchet.RatchetMaterial)
  room : Nat

/-- One iteration of PS1FutureStep uses the actual material, prepends its tagged slot, and consumes room. -/
def liveCursorNext {AD PT CT : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (cursor : LiveCursor) : LiveCursor :=
  ⟨cursor.counter + 1, cr.kdfChain cursor.chain,
    (cursor.counter + 1, cr.kdfMsg cursor.chain) :: cursor.cache, cursor.room - 1⟩

/-- The staged state after a source-selected number of skipped steps. -/
def liveCursorAt {AD PT CT Session : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (token : LiveToken Session) (steps : Nat) : LiveCursor :=
  ⟨token.receiveSequence + steps, Ratchet.chainAt cr token.receiveChain steps,
    liveFutureCache cr token.receiveChain token.receiveSequence steps token.cache,
    token.room - steps⟩

/-- The literal staging operation in the replicated worker preserves the entire cursor formula. -/
theorem live_cursor_next {AD PT CT Session : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (token : LiveToken Session) (steps : Nat) :
    liveCursorNext cr (liveCursorAt cr token steps) =
      liveCursorAt cr token (steps + 1) := by
  simp [liveCursorNext, liveCursorAt, liveFutureCache,
    Ratchet.chainAt, Ratchet.msgKeyAt, Function.iterate_succ_apply', List.range_succ,
    Nat.sub_sub, Nat.add_assoc]

/-- The sequence syntax used in crypto.pvl distinguishes zero and first; positive successors retain every mathematical counter. -/
inductive LiveSequenceTerm where
  | zero
  | first
  | next (previous : LiveSequenceTerm)

def liveSequenceTerm : Nat → LiveSequenceTerm
  | 0 => .zero
  | 1 => .first
  | n + 2 => .next (liveSequenceTerm (n + 1))

def liveSequenceNext : LiveSequenceTerm → LiveSequenceTerm
  | .zero => .first
  | other => .next other

/-- PS1's zero-sensitive successor implements the mathematical successor on every represented counter. -/
theorem live_sequence_successor (counter : Nat) :
    liveSequenceNext (liveSequenceTerm counter) = liveSequenceTerm (counter + 1) := by
  cases counter with
  | zero => rfl
  | succ n => cases n <;> rfl

/-- This relation is the no-output recursive branch of PS1FutureStep, before the optional opening. -/
inductive LiveSkip {AD PT CT : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (target : Nat) : LiveCursor → LiveCursor → Prop
  | skip (cursor) (different : target ≠ cursor.counter + 1) (room : 0 < cursor.room) :
      LiveSkip cr target cursor (liveCursorNext cr cursor)

/-- Every admitted future prefix has a finite sequence of actual replicated-worker skip transitions. -/
theorem live_worker_prefix {AD PT CT Session : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (token : LiveToken Session) (target steps : Nat)
    (room : steps ≤ token.room) (before : token.receiveSequence + steps < target) :
    Relation.ReflTransGen (LiveSkip cr target)
      (liveCursorAt cr token 0) (liveCursorAt cr token steps) := by
  induction steps with
  | zero => exact .refl
  | succ steps ih =>
    rw [← live_cursor_next]
    exact .tail (ih (by omega) (by omega))
      (.skip _ (by simp only [liveCursorAt]; omega)
        (by simp only [liveCursorAt]; omega))

/-- Successful target opening installs the current staged cache and advances only its target chain step. -/
def liveCursorPublish {AD PT CT Session : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (saved : LiveToken Session) (cursor : LiveCursor) : LiveToken Session :=
  { saved with
    receiveSequence := cursor.counter + 1
    receiveChain := cr.kdfChain cursor.chain
    cache := cursor.cache
    room := cursor.room }

/-- The final future-worker publication is the complete token used by the source trace theorem. -/
theorem live_worker_publication {AD PT CT Session : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (token : LiveToken Session) (steps : Nat) :
    liveCursorPublish cr token (liveCursorAt cr token steps) =
      liveFutureToken cr token (token.receiveSequence + steps + 1) := by
  simp [liveCursorPublish, liveCursorAt, liveFutureToken,
    Ratchet.chainAt, Function.iterate_succ_apply', Nat.add_assoc]

/-- Prepared worker openings expose the concrete cached branch or a finite actual pending-channel walk. -/
inductive LiveWorkerPrepared {AD PT CT Session : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (saved : LiveToken Session) (target : Nat) :
    ratchet.RatchetMaterial → LiveToken Session → Prop
  | cached (index : Fin 50) (material)
      (lookup : saved.cache[index.val]? = some (target, material)) :
      LiveWorkerPrepared cr saved target material (liveCachedToken saved index.val)
  | future (cursor : LiveCursor)
      (steps : Relation.ReflTransGen (LiveSkip cr target)
        (liveCursorAt cr saved 0) cursor)
      (targetEq : target = cursor.counter + 1) :
      LiveWorkerPrepared cr saved target (cr.kdfMsg cursor.chain)
        (liveCursorPublish cr saved cursor)

/-- Every source-prepared opening reaches the same actual material and complete publication in the replicated future/cached worker. -/
theorem LivePrepared.worker {AD PT CT Session : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (saved : LiveToken Session) (target : Nat) (material : ratchet.RatchetMaterial)
    (after : LiveToken Session) (prepared : LivePrepared cr saved target material after) :
    LiveWorkerPrepared cr saved target material after := by
  cases prepared with
  | cached index material lookup => exact .cached index material lookup
  | future skipped targetEq room =>
    rw [targetEq, ← live_worker_publication]
    exact .future (liveCursorAt cr saved skipped.val)
      (live_worker_prefix cr saved _ skipped.val room (by omega)) rfl

/-- PS1CacheRebuild moves the reversed visited prefix back onto the new tail, one private message at a time. -/
def liveCacheRebuild {α : Type} : List α → List α → List α
  | [], after => after
  | head :: tail, after => liveCacheRebuild tail (head :: after)

/-- The rebuild worker changes no visited value and preserves its original order. -/
theorem live_cache_rebuild {α : Type} (before after : List α) :
    liveCacheRebuild before after = before.reverse ++ after := by
  induction before generalizing after with
  | nil => rfl
  | cons head tail ih => simp [liveCacheRebuild, ih, List.append_assoc]

/-- The lookup worker remembers the original newest slot and tests each actual sequence tag. -/
def liveCacheSearch {Material : Type} (last : Nat × Material) (target : Nat) :
    List (Nat × Material) → List (Nat × Material) → Option (Material × List (Nat × Material))
  | [], _ => none
  | (sequence, material) :: tail, before =>
      if target = sequence then some (material, liveCacheRebuild before (last :: tail))
      else liveCacheSearch last target tail ((sequence, material) :: before)

/-- Every ordered cached case reaches the same material and source last-slot swap without a giant negative destructor branch. -/
theorem live_cache_search {Material : Type}
    (last : Nat × Material) (target : Nat) (material : Material)
    (before tail reversed : List (Nat × Material))
    (different : ∀ entry ∈ before, target ≠ entry.1) :
    liveCacheSearch last target (before ++ (target, material) :: tail) reversed =
      some (material, liveCacheRebuild reversed (before ++ last :: tail)) := by
  induction before generalizing reversed with
  | nil => simp [liveCacheSearch]
  | cons head rest ih =>
    rcases head with ⟨sequence, value⟩
    simp only [List.cons_append, liveCacheSearch,
      ite_eq_right (different (sequence, value) (by simp))]
    simpa only [liveCacheRebuild] using ih ((sequence, value) :: reversed)
      (fun entry member => different entry (by simp [member]))

/-- PS1Receive tests the newest entry, then dispatches the exact private search/rebuild workers. -/
def liveCachePop {Material : Type} (target : Nat) :
    List (Nat × Material) → Option (Material × List (Nat × Material))
  | [] => none
  | last :: tail =>
      if target = last.1 then some (last.2, tail)
      else liveCacheSearch last target tail []

/-- The new private traversal has the same selected later-slot result as every ordered generated cache case. -/
theorem live_cache_case {Material : Type}
    (last : Nat × Material) (target : Nat) (material : Material)
    (before tail : List (Nat × Material)) (newest : target ≠ last.1)
    (different : ∀ entry ∈ before, target ≠ entry.1) :
    liveCachePop target (last :: (before ++ (target, material) :: tail)) =
      some (material, registrationCacheSwap (last :: (before ++ (target, material) :: tail))
        (before.length + 1)) := by
  simp [liveCachePop, newest, live_cache_search last target material before tail [] different,
    liveCacheRebuild, registrationCacheSwap_case]

end beaconcrypt_core.ratchet.concrete

/--
info: 'beaconcrypt_core.ratchet.concrete.live_cursor_next' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_cursor_next

/--
info: 'beaconcrypt_core.ratchet.concrete.live_sequence_successor' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_sequence_successor

/--
info: 'beaconcrypt_core.ratchet.concrete.live_worker_prefix' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_worker_prefix

/--
info: 'beaconcrypt_core.ratchet.concrete.live_worker_publication' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_worker_publication

/--
info: 'beaconcrypt_core.ratchet.concrete.LivePrepared.worker' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.LivePrepared.worker

/--
info: 'beaconcrypt_core.ratchet.concrete.live_cache_rebuild' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_cache_rebuild

/--
info: 'beaconcrypt_core.ratchet.concrete.live_cache_search' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_cache_search

/--
info: 'beaconcrypt_core.ratchet.concrete.live_cache_case' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_cache_case
