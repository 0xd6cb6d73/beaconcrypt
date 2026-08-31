import BeaconcryptCore.Refinement.RatchetControl
import BeaconcryptCore.Model.Ratchet

/-!
# The generated ratchet logic refines the handwritten bounded symmetric ratchet

`BeaconcryptCore/Model/Ratchet.lean` contains a handwritten, cryptography-aware model of a
symmetric single ratchet: a sender chain, a receiver chain, a store of skipped message
keys bounded by `Ratchet.maxSkip`, authenticated decryption, and a receive step
(`Ratchet.recvStep`) that is state neutral on every rejection.

`BeaconcryptCore/Extraction/Funs.lean` contains the ratchet *control plane* extracted
from the Rust source.  It is key agnostic: it tracks sequence numbers only
(`send_sequence`, `receive_sequence`, and a `SequenceCache` of derived-but-unconsumed
sequence numbers), and it is driven by the caller in four steps —
`plan_receive_until`, a number of `advance_receive` key derivations,
`lookup_receive_key`, and `finish_receive`, the last of which is told whether the
authenticated decryption of the incoming message succeeded.

This file connects the two.  It

* packages the four generated steps into the receive driver `receiveMessage`, which
  performs the key derivations on a copy of the state and commits them only if the
  message authenticates (this is what makes the composite step state neutral, as
  required of the handwritten model);
* defines the refinement relation `Refines`, which says that the concrete state
  represents the abstract one: `receive_sequence` is the next expected abstract index,
  the abstract chain key and the abstract stored keys are the ones derived from the
  session's base chain key, and the cache holds exactly the sequence numbers
  (abstract index `+ 1`) of the abstract skipped keys;
* proves the main refinement theorem `receiveMessage_refines`: for every incoming
  message, `receiveMessage` returns the outcome that the handwritten step returns, and
  the resulting concrete state again represents the resulting abstract state;
* proves the corresponding statement for the send path (`advance_send_refines`);
* proves the exact bound-50 case: the generated planner charges only retained skipped
  keys against the cache, while the incoming target is advanced without being cached.
  Consequently the generated driver refines `Ratchet.recvStep` directly, including a
  receive with exactly 50 outstanding skipped keys.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Result

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-! ## Handwritten-chain facts -/

namespace Ratchet

variable {CK MK AD PT CT : Type}

/-- The skipped keys derived from a chain key that is itself `base` steps along the
session chain: index `base + j`, and the key of message `base + j`. -/
theorem skipKeys_eq_map_range (c : Crypto CK MK AD PT CT) (ck0 : CK) (base cnt : ℕ) :
    skipKeys c (chainAt c ck0 base) base cnt =
      (List.range cnt).map (fun j => (base + j, msgKeyAt c ck0 (base + j))) := by
  induction cnt generalizing base with
  | zero => simp [skipKeys]
  | succ n ih =>
    have hchain : c.kdfChain (chainAt c ck0 base) = chainAt c ck0 (base + 1) := by
      simp [chainAt, Function.iterate_succ_apply']
    rw [skipKeys, hchain, ih (base + 1), List.range_succ_eq_map]
    simp [msgKeyAt, Nat.add_comm, Nat.add_left_comm]

/-- Advancing a chain key in two stages is advancing it once. -/
theorem chainAt_chainAt (c : Crypto CK MK AD PT CT) (ck : CK) (a b : ℕ) :
    chainAt c (chainAt c ck a) b = chainAt c ck (a + b) := by
  simp [chainAt, ← Function.iterate_add_apply, Nat.add_comm]

/-- The key of the message `b` steps past the chain key that is itself `a` steps along
the session chain is the key of message `a + b`. -/
theorem msgKeyAt_chainAt (c : Crypto CK MK AD PT CT) (ck : CK) (a b : ℕ) :
    msgKeyAt c (chainAt c ck a) b = msgKeyAt c ck (a + b) := by
  simp [msgKeyAt, chainAt_chainAt]

end Ratchet

/-! ## The generated receive driver -/

namespace beaconcrypt_core.ratchet.control

/-- The outcome of one receive step of the generated control plane. -/
inductive RecvOutcome
  /-- The message was authentic and is delivered; its key is consumed. -/
  | delivered
  /-- The message is a replay (or its key has already been consumed). -/
  | replay
  /-- Accepting the message would need more outstanding keys than the cache holds. -/
  | tooManySkipped
  /-- The message failed authentication. -/
  | authFail
deriving DecidableEq, Repr

/-- Perform `k` key derivations with the generated `advance_receive`, returning `none`
if the control plane refuses one of them. -/
def deriveKeys (state : RatchetState) : ℕ → Result (Option RatchetState)
  | 0 => ok (some state)
  | k + 1 => do
      let adv ← advance_receive state
      match adv.sequence with
      | core.option.Option.None => ok none
      | core.option.Option.Some _ => deriveKeys adv.state k

/-- One receive step of the generated control plane. Cached targets are looked up and
removed. Future targets derive and cache only the preceding skipped keys, then use
`advance_receive_target` for the uncached target itself. Private derivations are
committed only when the message authenticates. -/
def receiveMessage (state : RatchetState) (target : Std.U64) (authenticated : Bool) :
    Result (RecvOutcome × RatchetState) := do
  let plan ← plan_receive_until state target
  match plan.sequence with
  | core.option.Option.None => ok (RecvOutcome.tooManySkipped, state)
  | core.option.Option.Some tgt =>
      if plan.derivations = 0#u64 then
        let found ← lookup_receive_key state tgt
        match found with
        | core.option.Option.None => ok (RecvOutcome.replay, state)
        | core.option.Option.Some slot =>
            let fin ← finish_receive state tgt slot authenticated
            match fin.disposition with
            | ReceiveDisposition.Consumed => ok (RecvOutcome.delivered, fin.state)
            | ReceiveDisposition.Retained => ok (RecvOutcome.authFail, state)
            | ReceiveDisposition.Missing => ok (RecvOutcome.replay, state)
      else
        let derived ← deriveKeys state (plan.derivations.val - 1)
        match derived with
        | none => ok (RecvOutcome.tooManySkipped, state)
        | some state1 =>
            let advanced ← advance_receive_target state1
            match advanced.sequence with
            | core.option.Option.None => ok (RecvOutcome.tooManySkipped, state)
            | core.option.Option.Some sequence =>
                if sequence = tgt then
                  if authenticated then ok (RecvOutcome.delivered, advanced.state)
                  else ok (RecvOutcome.authFail, state)
                else ok (RecvOutcome.tooManySkipped, state)

/-! ## The sequence numbers held in the cache -/

/-- The list of sequence numbers currently held in the receive cache. -/
def cacheSeqs (c : SequenceCache) : List ℕ :=
  (List.range c.len.val).map (fun i => (c.entries.val[i]!).val)

theorem cacheSeqs_length (c : SequenceCache) : (cacheSeqs c).length = c.len.val := by
  simp [cacheSeqs]

theorem mem_cacheSeqs_iff (c : SequenceCache) (v : ℕ) :
    v ∈ cacheSeqs c ↔ ∃ i, i < c.len.val ∧ (c.entries.val[i]!).val = v := by
  simp [cacheSeqs, List.mem_map, List.mem_range]

/-- Mapping over `List.range` with a value overridden at one index is a `List.set`. -/
theorem map_range_if_eq_set {α : Type} (m slot : ℕ) (f : ℕ → α) (x : α) :
    (List.range m).map (fun i => if i = slot then x else f i)
      = ((List.range m).map f).set slot x := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_set]
    simp at h1
    by_cases hs : slot = i
    · simp [hs]
    · rw [if_neg hs, if_neg (fun h : i = slot => hs h.symm)]

/-- A swap-remove: overwriting the entry at `slot` with the value `v` that used to sit at
the end removes the entry at `slot` from the list, up to a permutation. -/
theorem perm_swap_remove {α : Type} [Inhabited α] (A : List α) (slot : ℕ) (v : α)
    (h : slot < A.length) : (A[slot]! :: A.set slot v).Perm (A ++ [v]) := by
  have hA : A = A.take slot ++ A[slot]! :: A.drop (slot + 1) := by
    conv_lhs => rw [show A = A.set slot A[slot]! from by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]; simp]
    rw [List.set_eq_take_append_cons_drop, if_pos h]
  rw [List.set_eq_take_append_cons_drop, if_pos h]
  refine List.Perm.trans (List.perm_middle).symm ?_
  conv_rhs => rw [hA]
  rw [List.append_assoc]
  exact List.Perm.append_left _
    (List.Perm.cons _ (List.perm_append_singleton v (A.drop (slot + 1))).symm)

/-- One key derivation appends the new sequence number at the end of the cache. -/
theorem advance_receive_cacheSeqs (st : RatchetState)
    (hmax : st.receive_sequence ≠ core.num.U64.MAX) (hlen : st.receive_cache.len.val < 50) :
    ∃ adv, advance_receive st = ok adv ∧
      adv.state.receive_sequence.val = st.receive_sequence.val + 1 ∧
      adv.state.send_sequence = st.send_sequence ∧
      adv.state.receive_cache.len.val = st.receive_cache.len.val + 1 ∧
      adv.sequence = core.option.Option.Some adv.state.receive_sequence ∧
      cacheSeqs adv.state.receive_cache =
        cacheSeqs st.receive_cache ++ [st.receive_sequence.val + 1] := by
  obtain ⟨z, hz, hzval⟩ := receive_next_ok st hmax
  obtain ⟨c', hc', hc'len, hc'entries⟩ :=
    SequenceCache.append_ok st.receive_cache z (by scalar_tac) hlen
  refine ⟨_, advance_receive_of_append_some st hmax z hz c' st.receive_cache.len hc',
    hzval, rfl, hc'len, rfl, ?_⟩
  have hcast : (UScalar.cast UScalarTy.Usize st.receive_cache.len).val
      = st.receive_cache.len.val := by simp_scalar
  show cacheSeqs c' = _
  simp only [cacheSeqs]
  rw [hc'len, List.range_succ, hc'entries]
  simp only [Std.Array.set_val_eq, hcast, List.map_append, List.map_cons, List.map_nil]
  congr 1
  · apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
      List.getElem?_set_ne (by omega)]
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_self (by simp; omega)]
    simpa using hzval

/-- `k` key derivations append the `k` next sequence numbers to the cache. -/
theorem deriveKeys_spec (st : RatchetState) (k : ℕ)
    (hmax : st.receive_sequence.val + k < 2 ^ 64)
    (hlen : st.receive_cache.len.val + k ≤ 50) :
    ∃ st', deriveKeys st k = ok (some st') ∧
      st'.receive_sequence.val = st.receive_sequence.val + k ∧
      st'.send_sequence = st.send_sequence ∧
      st'.receive_cache.len.val = st.receive_cache.len.val + k ∧
      cacheSeqs st'.receive_cache =
        cacheSeqs st.receive_cache ++
          (List.range k).map (fun j => st.receive_sequence.val + 1 + j) := by
  induction k generalizing st with
  | zero => exact ⟨st, rfl, by simp, rfl, by simp, by simp⟩
  | succ k ih =>
    have hmaxne : st.receive_sequence ≠ core.num.U64.MAX := by
      intro hcon
      rw [hcon] at hmax
      simp [core.num.U64.MAX, U64.rMax] at hmax
      omega
    obtain ⟨adv, hadv, hrs, hss, hlen', hsome, hcache⟩ :=
      advance_receive_cacheSeqs st hmaxne (by omega)
    obtain ⟨st', hst', hrs2, hss2, hlen2, hcache2⟩ := ih adv.state (by omega) (by omega)
    refine ⟨st', ?_, by omega, by rw [hss2, hss], by omega, ?_⟩
    · simp only [deriveKeys, hadv, bind_tc_ok, hsome]
      exact hst'
    · rw [hcache2, hcache, hrs, List.append_assoc]
      congr 1
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Function.comp_def, List.singleton_append]
      congr 1
      apply List.map_congr_left
      intro j _
      omega

/-- The lookup finds a sequence number that is in the cache. -/
theorem lookup_receive_key_of_mem (st : RatchetState) (target : Std.U64) (hst : st.Wf)
    (hmem : target.val ∈ cacheSeqs st.receive_cache) :
    ∃ slot, lookup_receive_key st target = ok (core.option.Option.Some slot) ∧
      slot.val < st.receive_cache.len.val ∧
      st.receive_cache.entries.val[slot.val]! = target := by
  obtain ⟨i, hi, hval⟩ := (mem_cacheSeqs_iff _ _).1 hmem
  exact lookup_receive_key_complete st target i hst hi (UScalar.eq_of_val_eq hval)

/-- The lookup misses a sequence number that is not in the cache. -/
theorem lookup_receive_key_of_not_mem (st : RatchetState) (target : Std.U64) (hst : st.Wf)
    (hmem : target.val ∉ cacheSeqs st.receive_cache) :
    lookup_receive_key st target = ok core.option.Option.None := by
  obtain ⟨res, hres⟩ := lookup_receive_key_ok st target hst
  cases hcase : res with
  | none => rw [hres, hcase]
  | some slot =>
    rw [hcase] at hres
    obtain ⟨hslot, hentry⟩ := lookup_receive_key_sound st target slot hst hres
    exact absurd ((mem_cacheSeqs_iff _ _).2 ⟨slot.val, hslot, by rw [hentry]⟩) hmem

/-- Consuming an authentic message removes exactly its sequence number from the cache
(by a swap-remove, so the remaining entries are permuted). -/
theorem finish_receive_consumed_cacheSeqs (st : RatchetState) (target : Std.U64)
    (slot : Std.U8) (hst : st.Wf) (hslot : slot.val < st.receive_cache.len.val)
    (hentry : st.receive_cache.entries.val[slot.val]! = target) :
    ∃ r, finish_receive st target slot true = ok r ∧
      r.disposition = ReceiveDisposition.Consumed ∧
      r.state.send_sequence = st.send_sequence ∧
      r.state.receive_sequence = st.receive_sequence ∧
      r.state.receive_cache.len.val = st.receive_cache.len.val - 1 ∧
      (cacheSeqs r.state.receive_cache).Perm
        ((cacheSeqs st.receive_cache).erase target.val) := by
  obtain ⟨r, hr, hdisp, hlen, hss, hrs, -, hpt⟩ :=
    finish_receive_consumed st target slot hst hslot hentry
  refine ⟨{ state := r.state, disposition := r.disposition }, by simp [finish_receive, hr],
    hdisp, hss, hrs, hlen, ?_⟩
  have hentry' : (st.receive_cache.entries.val[slot.val]?.getD default : Std.U64) = target := by
    rw [← List.getElem!_eq_getElem?_getD]; exact hentry
  set len := st.receive_cache.len.val with hlendef
  set A := (List.range (len - 1)).map (fun i => (st.receive_cache.entries.val[i]!).val) with hA
  set v := (st.receive_cache.entries.val[len - 1]!).val with hv
  have hAlen : A.length = len - 1 := by simp [hA]
  have hnew : cacheSeqs r.state.receive_cache = A.set slot.val v := by
    show (List.range r.state.receive_cache.len.val).map _ = _
    rw [hlen, ← map_range_if_eq_set]
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    rw [hpt i (by rw [hlen]; exact hi)]
    split <;> rfl
  have hold : cacheSeqs st.receive_cache = A ++ [v] := by
    show (List.range len).map _ = _
    rw [show len = (len - 1) + 1 by omega, List.range_succ]
    simp [hA, hv]
  rw [hnew, hold]
  by_cases hcase : slot.val < len - 1
  · have hAslot : A[slot.val]! = target.val := by
      rw [hA, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
      simp [hentry']
    have hperm := perm_swap_remove A slot.val v (by omega)
    rw [hAslot] at hperm
    have hmem : target.val ∈ A ++ [v] := hperm.mem_iff.1 (by simp)
    exact (hperm.trans (List.perm_cons_erase hmem)).cons_inv
  · have hslotv : slot.val = len - 1 := by omega
    have htv : target.val = v := by rw [hv, ← hslotv, hentry]
    rw [List.set_eq_of_length_le (show A.length ≤ slot.val by omega), htv]
    refine List.Perm.symm ?_
    calc ((A ++ [v]).erase v).Perm ((v :: A).erase v) :=
          List.Perm.erase v (List.perm_append_singleton v A)
      _ = A := by simp

/-! ## Lists of stored keys -/

/-- Removing the entry for `idx` from a store with distinct indices: filtering and
erasing agree. -/
theorem filter_map_eq_erase {MK : Type} (l : List (ℕ × MK)) (idx : ℕ)
    (hnd : (l.map Prod.fst).Nodup) :
    (l.filter (fun p => !(p.1 == idx))).map (fun p => p.1 + 1)
      = (l.map (fun p => p.1 + 1)).erase (idx + 1) := by
  induction l with
  | nil => simp
  | cons p t ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    by_cases hp : p.1 = idx
    · have hfil : t.filter (fun q => !(q.1 == idx)) = t := by
        apply List.filter_eq_self.2
        intro q hq
        simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
        intro hcon
        exact hnd.1 (List.mem_map.2 ⟨q, hq, by rw [hcon, hp]⟩)
      simp [hp, hfil]
    · simp [hp, ih hnd.2]

theorem mem_of_lookup_eq_some {MK : Type} {l : List (ℕ × MK)} {a : ℕ} {b : MK}
    (h : List.lookup a l = some b) : (a, b) ∈ l := by
  obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.1 h
  simp

theorem lookup_ne_none_of_mem_fst {MK : Type} {l : List (ℕ × MK)} {a : ℕ}
    (h : a ∈ l.map Prod.fst) : ∃ b, List.lookup a l = some b := by
  cases hl : List.lookup a l with
  | none =>
    obtain ⟨p, hp, hp2⟩ := List.mem_map.1 h
    have := List.lookup_eq_none_iff.1 hl p hp
    simp [hp2] at this
  | some b => exact ⟨b, rfl⟩

/-! ## The refinement relation -/

variable {CK MK AD PT CT : Type}

/-- The concrete control-plane state `st` represents the abstract receiving state `s` of
the handwritten ratchet whose session chain key is `ck0`:

* the concrete receive counter is the next expected abstract message index (abstract
  index `i` is carried on the wire as sequence number `i + 1`);
* the abstract chain key is the session chain key advanced that far, and every stored
  abstract key is the key of its message;
* the cache holds exactly the sequence numbers of the abstract skipped keys. -/
structure Refines (cr : Ratchet.Crypto CK MK AD PT CT) (ck0 : CK)
    (s : Ratchet.RecvState CK MK) (st : RatchetState) : Prop where
  /-- The cache holds at most 50 entries. -/
  wf : st.Wf
  /-- The concrete receive counter is the next expected abstract index. -/
  seq : st.receive_sequence.val = s.n
  /-- Sequence numbers stay inside `u64`. -/
  lt : s.n < 2 ^ 64
  /-- The abstract chain key is the session key advanced to the next expected index. -/
  chain : s.ck = Ratchet.chainAt cr ck0 s.n
  /-- Every stored abstract key is the message key of its index. -/
  keys : ∀ p ∈ s.skipped, p.2 = Ratchet.msgKeyAt cr ck0 p.1
  /-- Stored keys are for messages before the next expected index. -/
  keys_lt : ∀ p ∈ s.skipped, p.1 < s.n
  /-- Stored indices are pairwise distinct. -/
  nodup : (s.skipped.map Prod.fst).Nodup
  /-- The cache holds exactly the sequence numbers of the stored abstract keys. -/
  cache : (cacheSeqs st.receive_cache).Perm (s.skipped.map (fun p => p.1 + 1))

/-- A represented abstract state is well formed in the sense of the handwritten model. -/
theorem Refines.recvWf {cr : Ratchet.Crypto CK MK AD PT CT} {ck0 : CK}
    {s : Ratchet.RecvState CK MK} {st : RatchetState} (h : Refines cr ck0 s st) :
    Ratchet.RecvWf s := by
  refine ⟨?_, h.keys_lt, h.nodup⟩
  have hl := h.cache.length_eq
  rw [cacheSeqs_length] at hl
  simp only [List.length_map] at hl
  have hwf := h.wf
  simp only [RatchetState.Wf, SequenceCache.Wf] at hwf
  simp only [Ratchet.maxSkip]
  omega

/-- The concrete outcome that corresponds to an outcome of the handwritten step. -/
def absOutcome (r : Except Ratchet.RecvError PT) : RecvOutcome :=
  match r with
  | .ok _ => RecvOutcome.delivered
  | .error .replay => RecvOutcome.replay
  | .error .tooManySkipped => RecvOutcome.tooManySkipped
  | .error .authFail => RecvOutcome.authFail

/-! ## The refinement theorems -/

/-- **The send path refines the handwritten sender.**  The generated `advance_send`
hands out the key of the message the handwritten `sendStep` sends next (abstract index
`i` travels as sequence number `i + 1`), and moves the send counter on by one. -/
theorem advance_send_refines (cr : Ratchet.Crypto CK MK AD PT CT)
    (ss : Ratchet.SendState CK) (st : RatchetState) (ad : AD) (pt : PT)
    (hseq : st.send_sequence.val = ss.n) (hmax : st.send_sequence ≠ core.num.U64.MAX) :
    ∃ adv, advance_send st = ok adv ∧ adv.key.available = true ∧
      adv.key.sequence.val = (Ratchet.sendStep cr ss ad pt).1.idx + 1 ∧
      adv.state.receive_sequence = st.receive_sequence ∧
      adv.state.receive_cache = st.receive_cache ∧
      adv.state.send_sequence.val = (Ratchet.sendStep cr ss ad pt).2.n := by
  obtain ⟨adv, hadv, hss, hrs, hrc, -, hkey⟩ := advance_send_ok st hmax
  exact ⟨adv, hadv, by rw [hkey], by rw [hkey]; simp [Ratchet.sendStep]; omega, hrs, hrc,
    by simp [Ratchet.sendStep]; omega⟩

/-- **The generated receive logic refines the handwritten one.**

If the concrete state represents the abstract one, and the caller reports the result of
authenticating the incoming ciphertext with the message key of sequence number `target`,
then the generated driver returns exactly the outcome of the handwritten receive step on
the corresponding abstract message, and the state it returns again represents the
abstract state the handwritten step produces. -/
theorem receiveMessage_refines (cr : Ratchet.Crypto CK MK AD PT CT) (ck0 : CK)
    (s : Ratchet.RecvState CK MK) (st : RatchetState) (h : Refines cr ck0 s st)
    (target : Std.U64) (htarget : 1 ≤ target.val) (ad : AD) (ct : CT) (auth : Bool)
    (hauth : auth = (cr.dec (Ratchet.msgKeyAt cr ck0 (target.val - 1)) ad ct).isSome) :
    ∃ st',
      receiveMessage st target auth =
        ok (absOutcome (Ratchet.recvStep cr s ad ⟨target.val - 1, ct⟩).1, st') ∧
      Refines cr ck0 (Ratchet.recvStep cr s ad ⟨target.val - 1, ct⟩).2 st' := by
  obtain ⟨hwf, hseq, hlt, hchain, hkeys, hkeys_lt, hnodup, hcache⟩ := h
  have hwf50 : st.receive_cache.len.val ≤ 50 := hwf
  have hlencache : st.receive_cache.len.val = s.skipped.length := by
    have h2 := hcache.length_eq
    rw [cacheSeqs_length] at h2
    simpa using h2
  have htlt : target.val < 2 ^ 64 := by scalar_tac
  have hzero : (0#u64).val = 0 := rfl
  set idx := target.val - 1 with hidxdef
  have htv : target.val = idx + 1 := by omega
  cases hl : List.lookup idx s.skipped with
  | some mk =>
    have hmem : (idx, mk) ∈ s.skipped := mem_of_lookup_eq_some hl
    have hkey : mk = Ratchet.msgKeyAt cr ck0 idx := hkeys _ hmem
    have hidxlt : idx < s.n := hkeys_lt _ hmem
    have hmemc : target.val ∈ cacheSeqs st.receive_cache :=
      hcache.mem_iff.2 (List.mem_map.2 ⟨(idx, mk), hmem, by simp only []; omega⟩)
    have hplan := plan_receive_until_replay st target (by omega)
    obtain ⟨slot, hlook, hslot, hentry⟩ := lookup_receive_key_of_mem st target hwf hmemc
    cases hdec : cr.dec mk ad ct with
    | none =>
      have hauthf : auth = false := by rw [hauth, ← hkey, hdec]; rfl
      have hfin : finish_receive st target slot false =
          ok { state := st, disposition := ReceiveDisposition.Retained } := by
        simp [finish_receive,
          finish_receive_with_removal_retained st target slot hwf hslot hentry]
      have habs : Ratchet.recvStep cr s ad ⟨idx, ct⟩ = (.error .authFail, s) := by
        simp only [Ratchet.recvStep, hl, hdec]
      refine ⟨st, ?_, (by rw [habs]; exact ⟨hwf, hseq, hlt, hchain, hkeys, hkeys_lt, hnodup, hcache⟩)⟩
      simp only [receiveMessage, hplan, bind_tc_ok, hzero, hlook, hauthf, hfin,
        habs, absOutcome]
      simp
    | some pt =>
      have hautht : auth = true := by rw [hauth, ← hkey, hdec]; rfl
      obtain ⟨r, hfin, hdisp, hss, hrs, hlen, hperm⟩ :=
        finish_receive_consumed_cacheSeqs st target slot hwf hslot hentry
      have habs : Ratchet.recvStep cr s ad ⟨idx, ct⟩ =
          (.ok pt, { s with skipped := s.skipped.filter (fun p => !(p.1 == idx)) }) := by
        simp only [Ratchet.recvStep, hl, hdec]
      refine ⟨r.state, ?_, ?_⟩
      · simp only [receiveMessage, hplan, bind_tc_ok, hzero, hlook, hautht, hfin,
          hdisp, habs, absOutcome]
        simp
      · rw [habs]
        refine ⟨?_, ?_, hlt, hchain, ?_, ?_, ?_, ?_⟩
        · show r.state.receive_cache.len.val ≤ 50
          omega
        · show r.state.receive_sequence.val = s.n
          rw [hrs]; exact hseq
        · exact fun p hp => hkeys p (List.mem_of_mem_filter hp)
        · exact fun p hp => hkeys_lt p (List.mem_of_mem_filter hp)
        · exact hnodup.sublist (List.Sublist.map _ List.filter_sublist)
        · show (cacheSeqs r.state.receive_cache).Perm
            ((s.skipped.filter (fun p => !(p.1 == idx))).map (fun p => p.1 + 1))
          rw [filter_map_eq_erase s.skipped idx hnodup, ← htv]
          exact hperm.trans (List.Perm.erase target.val hcache)
  | none =>
    by_cases hidxlt : idx < s.n
    · have hnotmem : target.val ∉ cacheSeqs st.receive_cache := by
        intro hcon
        obtain ⟨p, hp, hp2⟩ := List.mem_map.1 (hcache.mem_iff.1 hcon)
        obtain ⟨b, hb⟩ := lookup_ne_none_of_mem_fst (List.mem_map.2 ⟨p, hp,
          show p.1 = idx by omega⟩)
        rw [hl] at hb
        simp at hb
      have hplan := plan_receive_until_replay st target (by omega)
      have hlook := lookup_receive_key_of_not_mem st target hwf hnotmem
      have habs : Ratchet.recvStep cr s ad ⟨idx, ct⟩ = (.error .replay, s) := by
        simp only [Ratchet.recvStep, hl]
        rw [if_pos hidxlt]
      refine ⟨st, ?_, (by rw [habs]; exact ⟨hwf, hseq, hlt, hchain, hkeys, hkeys_lt, hnodup, hcache⟩)⟩
      simp only [receiveMessage, hplan, bind_tc_ok, hzero, hlook, habs, absOutcome]
      simp
    · rw [Nat.not_lt] at hidxlt
      set gap := idx - s.n with hgapdef
      by_cases hover : Ratchet.maxSkip < gap + s.skipped.length
      · have hplan : plan_receive_until st target =
            ok { sequence := core.option.Option.None, derivations := 0#u64 } := by
          have hover50 : 50 < gap + s.skipped.length := by
            simpa [Ratchet.maxSkip] using hover
          by_cases hg : 50 < gap
          · exact plan_receive_until_reject_of_gap_gt st target (by omega)
          · exact plan_receive_until_reject_of_cache_full st target (by omega) (by omega)
              (by omega)
        have habs : Ratchet.recvStep cr s ad ⟨idx, ct⟩ = (.error .tooManySkipped, s) := by
          simp only [Ratchet.recvStep, hl]
          rw [if_neg (by omega), if_pos (by omega)]
        refine ⟨st, ?_, (by rw [habs]; exact ⟨hwf, hseq, hlt, hchain, hkeys, hkeys_lt, hnodup, hcache⟩)⟩
        simp only [receiveMessage, hplan, bind_tc_ok, habs, absOutcome]
      · rw [Nat.not_lt] at hover
        have hover50 : gap + s.skipped.length ≤ 50 := by
          simpa [Ratchet.maxSkip] using hover
        obtain ⟨d, hplan, hdval⟩ :=
          plan_receive_until_accept st target (by omega) (by omega)
        have hdv : d.val = gap + 1 := by omega
        have hdne : d ≠ 0#u64 := by
          intro hd0
          have hd0val := congrArg UScalar.val hd0
          simp at hd0val
          omega
        have hdpred : d.val - 1 = gap := by omega
        obtain ⟨st1, hderive, hrs1, hss1, hlen1, hcache1⟩ :=
          deriveKeys_spec st gap (by omega) (by omega)
        have hrs1idx : st1.receive_sequence.val = idx := by omega
        have hst1max : st1.receive_sequence ≠ core.num.U64.MAX := by
          intro hmax
          have hmaxval := congrArg UScalar.val hmax
          simp [core.num.U64.MAX, U64.rMax] at hmaxval
          omega
        obtain ⟨advanced, hadvance, hrsAdvanced, hssAdvanced, hcacheAdvanced,
          hsequence⟩ := advance_receive_target_ok st1 hst1max
        have hrsTarget : advanced.state.receive_sequence = target := by
          apply UScalar.eq_of_val_eq
          omega
        have hsequenceTarget : advanced.sequence = core.option.Option.Some target := by
          rw [hsequence, hrsTarget]
        have hmk : Ratchet.msgKeyAt cr s.ck gap = Ratchet.msgKeyAt cr ck0 idx := by
          rw [hchain, Ratchet.msgKeyAt_chainAt]
          congr 1
          omega
        cases hdec : cr.dec (Ratchet.msgKeyAt cr s.ck gap) ad ct with
        | none =>
          have hauthf : auth = false := by rw [hauth, ← hmk, hdec]; rfl
          have habs : Ratchet.recvStep cr s ad ⟨idx, ct⟩ = (.error .authFail, s) := by
            simp only [Ratchet.recvStep, hl]
            rw [if_neg (by omega), if_neg (by omega), ← hgapdef, hdec]
          refine ⟨st, ?_, (by rw [habs]; exact ⟨hwf, hseq, hlt, hchain, hkeys, hkeys_lt, hnodup, hcache⟩)⟩
          simp only [receiveMessage, hplan, bind_tc_ok, if_neg hdne, hdpred, hderive,
            hadvance, hsequenceTarget, hauthf, habs, absOutcome]
          simp
        | some pt =>
          have hautht : auth = true := by rw [hauth, ← hmk, hdec]; rfl
          have habs : Ratchet.recvStep cr s ad ⟨idx, ct⟩ =
              (.ok pt, { ck := Ratchet.chainAt cr s.ck (gap + 1), n := idx + 1,
                         skipped := s.skipped ++ Ratchet.skipKeys cr s.ck s.n gap }) := by
            simp only [Ratchet.recvStep, hl]
            rw [if_neg (by omega), if_neg (by omega), ← hgapdef, hdec]
          refine ⟨advanced.state, ?_, ?_⟩
          · simp only [receiveMessage, hplan, bind_tc_ok, if_neg hdne, hdpred, hderive,
              hadvance, hsequenceTarget, hautht, habs, absOutcome]
            simp
          · rw [habs]
            have hlenAdvanced : advanced.state.receive_cache.len.val =
                st.receive_cache.len.val + gap := by
              rw [hcacheAdvanced, hlen1]
            have hsk : Ratchet.skipKeys cr s.ck s.n gap
                = (List.range gap).map
                    (fun j => (s.n + j, Ratchet.msgKeyAt cr ck0 (s.n + j))) := by
              rw [hchain]
              exact Ratchet.skipKeys_eq_map_range cr ck0 s.n gap
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · show advanced.state.receive_cache.len.val ≤ 50
              rw [hlenAdvanced, hlencache]
              omega
            · have hrsTargetVal := congrArg UScalar.val hrsTarget
              simpa only using hrsTargetVal.trans htv
            · show idx + 1 < 2 ^ 64
              omega
            · show Ratchet.chainAt cr s.ck (gap + 1) = Ratchet.chainAt cr ck0 (idx + 1)
              rw [hchain, Ratchet.chainAt_chainAt]
              congr 1
              omega
            · intro p hp
              rcases List.mem_append.1 hp with hp' | hp'
              · exact hkeys p hp'
              · rw [hsk] at hp'
                obtain ⟨j, -, rfl⟩ := List.mem_map.1 hp'
                rfl
            · intro p hp
              show p.1 < idx + 1
              rcases List.mem_append.1 hp with hp' | hp'
              · have := hkeys_lt p hp'; omega
              · rw [hsk] at hp'
                obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp'
                simp only [List.mem_range] at hj
                simp only []
                omega
            · show ((s.skipped ++ Ratchet.skipKeys cr s.ck s.n gap).map Prod.fst).Nodup
              rw [List.map_append, hsk, List.map_map]
              refine List.Nodup.append hnodup ?_ ?_
              · apply List.Nodup.map ?_ List.nodup_range
                intro a b hab
                simp only [Function.comp_apply] at hab
                omega
              · intro a ha hb
                obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
                obtain ⟨j, hj, hj2⟩ := List.mem_map.1 hb
                simp only [List.mem_range, Function.comp_apply] at hj hj2
                have := hkeys_lt p hp
                omega
            · show (cacheSeqs advanced.state.receive_cache).Perm
                ((s.skipped ++ Ratchet.skipKeys cr s.ck s.n gap).map (fun p => p.1 + 1))
              rw [hcacheAdvanced, hcache1, List.map_append, hsk, List.map_map]
              refine List.Perm.append hcache ?_
              apply List.Perm.of_eq
              apply List.map_congr_left
              intro j _
              simp only [Function.comp_apply]
              omega

/-- **State neutrality of the composite receive step.**  Whenever the generated driver
does not deliver the message — a replay, an exhausted skip budget, or a failed
authentication — the state it returns is the state it was given, bit for bit. -/
theorem receiveMessage_state_neutral (st : RatchetState) (target : Std.U64) (auth : Bool)
    (o : RecvOutcome) (st' : RatchetState) (h : receiveMessage st target auth = ok (o, st'))
    (ho : o ≠ RecvOutcome.delivered) : st' = st := by
  unfold receiveMessage at h
  cases hplan : plan_receive_until st target with
  | fail e => rw [hplan] at h; simp at h
  | div => rw [hplan] at h; simp at h
  | ok plan =>
    rw [hplan] at h
    simp only [bind_tc_ok] at h
    cases hsq : plan.sequence with
    | none => rw [hsq] at h; simp at h; exact h.2.symm
    | some tgt =>
      rw [hsq] at h
      simp only at h
      by_cases hzero : plan.derivations = 0#u64
      · rw [if_pos hzero] at h
        cases hlk : lookup_receive_key st tgt with
        | fail e => rw [hlk] at h; simp at h
        | div => rw [hlk] at h; simp at h
        | ok found =>
          rw [hlk] at h
          simp only [bind_tc_ok] at h
          cases hf : found with
          | none => rw [hf] at h; simp at h; exact h.2.symm
          | some slot =>
            rw [hf] at h
            simp only at h
            cases hfin : finish_receive st tgt slot auth with
            | fail e => rw [hfin] at h; simp at h
            | div => rw [hfin] at h; simp at h
            | ok fin =>
              rw [hfin] at h
              simp only [bind_tc_ok] at h
              cases hdisp : fin.disposition with
              | Consumed => rw [hdisp] at h; simp at h; exact absurd h.1.symm ho
              | Retained => rw [hdisp] at h; simp at h; exact h.2.symm
              | Missing => rw [hdisp] at h; simp at h; exact h.2.symm
      · rw [if_neg hzero] at h
        cases hd : deriveKeys st (plan.derivations.val - 1) with
        | fail e => rw [hd] at h; simp at h
        | div => rw [hd] at h; simp at h
        | ok derived =>
          rw [hd] at h
          simp only [bind_tc_ok] at h
          cases hderived : derived with
          | none => rw [hderived] at h; simp at h; exact h.2.symm
          | some st1 =>
            rw [hderived] at h
            simp only at h
            cases hadv : advance_receive_target st1 with
            | fail e => rw [hadv] at h; simp at h
            | div => rw [hadv] at h; simp at h
            | ok advanced =>
              rw [hadv] at h
              simp only [bind_tc_ok] at h
              cases hsq' : advanced.sequence with
              | none => rw [hsq'] at h; simp at h; exact h.2.symm
              | some sequence =>
                rw [hsq'] at h
                simp only at h
                by_cases heq : sequence = tgt
                · rw [if_pos heq] at h
                  cases hauth : auth
                  · rw [hauth] at h; simp at h; exact h.2.symm
                  · rw [hauth] at h; simp at h; exact absurd h.1.symm ho
                · rw [if_neg heq] at h
                  simp at h
                  exact h.2.symm

end beaconcrypt_core.ratchet.control
