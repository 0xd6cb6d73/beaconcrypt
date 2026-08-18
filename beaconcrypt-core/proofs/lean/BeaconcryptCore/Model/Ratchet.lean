import Mathlib

/-!
# A symmetric single ratchet with authenticated encryption

This file formalises a *symmetric single ratchet* (the symmetric-key, or "chain key",
ratchet of a Double-Ratchet style messaging protocol), together with its main
correctness and safety properties.

The model is parametric in the cryptographic primitives, which are bundled in the
structure `Ratchet.Crypto`:

* `kdfChain : CK → CK`  advances the chain key,
* `kdfMsg   : CK → MK`  derives the message key of the current chain link,
* `enc / dec`           an authenticated encryption scheme with associated data,
  whose only assumed property is decryption correctness (`dec_enc`); an
  authentication failure is modelled by `dec` returning `none`.

The sender keeps a chain key together with the number of messages already sent.
The receiver keeps a chain key, the index of the next expected message and a store
of *skipped message keys* for out-of-order delivery.  At most
`Ratchet.maxSkip = 50` skipped messages may be outstanding on the receive path;
a message requiring more skips than that is rejected.

Main results:

* `Ratchet.recvStep_of_sendStep_inOrder`  – in-order round trip.
* `Ratchet.recvStep_skip_ahead`           – accepting a message that skips `k ≤ 50` messages.
* `Ratchet.recvStep_delivers_skipped`     – later delivery of a skipped message.
* `Ratchet.recvStep_reject_tooManySkipped` – rejection beyond the bound of 50.
* `Ratchet.recvStep_state_neutral_of_error` – state neutrality on any rejection,
  in particular on authentication failure,
* `Ratchet.recvStep_authFail_no_new_skipped` – no skipped keys are stored on
  authentication failure.
* `Ratchet.recvStep_replay_rejected`       – replays are rejected.
* `Ratchet.RecvWf.recvStep`                – the receive state stays well formed,
  so the skipped-key store never exceeds 50 entries.
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Ratchet

/-- The maximum number of skipped messages the receive path tolerates. -/
def maxSkip : ℕ := 50

/-- The cryptographic primitives the ratchet is built from.

`CK` chain keys, `MK` message keys, `AD` associated data, `PT` plaintexts,
`CT` ciphertexts.  `dec` returns `none` to model an authentication failure. -/
structure Crypto (CK MK AD PT CT : Type) where
  /-- Advance the chain key by one link. -/
  kdfChain : CK → CK
  /-- Derive the message key of the current chain link. -/
  kdfMsg : CK → MK
  /-- Authenticated encryption. -/
  enc : MK → AD → PT → CT
  /-- Authenticated decryption; `none` means the ciphertext failed authentication. -/
  dec : MK → AD → CT → Option PT
  /-- Correctness of the authenticated encryption scheme. -/
  dec_enc : ∀ k ad p, dec k ad (enc k ad p) = some p

variable {CK MK AD PT CT : Type}

/-- The chain key of the ratchet after `i` further steps. -/
def chainAt (c : Crypto CK MK AD PT CT) (ck : CK) (i : ℕ) : CK :=
  c.kdfChain^[i] ck

/-- The message key used for the message `i` steps ahead of chain key `ck`. -/
def msgKeyAt (c : Crypto CK MK AD PT CT) (ck : CK) (i : ℕ) : MK :=
  c.kdfMsg (chainAt c ck i)

/-- A wire message: the index of the message in the chain, and its ciphertext. -/
structure Msg (CT : Type) where
  /-- Position of the message in the sending chain. -/
  idx : ℕ
  /-- The authenticated ciphertext. -/
  ct : CT
deriving DecidableEq

/-- The sending state: current chain key and number of messages already sent. -/
structure SendState (CK : Type) where
  /-- Current sending chain key. -/
  ck : CK
  /-- Number of messages sent so far. -/
  n : ℕ

/-- The receiving state: current chain key, index of the next expected message,
and the store of skipped message keys. -/
structure RecvState (CK MK : Type) where
  /-- Current receiving chain key. -/
  ck : CK
  /-- Index of the next expected message. -/
  n : ℕ
  /-- Message keys of messages that were skipped and may still arrive. -/
  skipped : List (ℕ × MK)

/-- Send one message: emit the ciphertext for the current message key and advance
the sending chain. -/
def sendStep (c : Crypto CK MK AD PT CT) (s : SendState CK) (ad : AD) (pt : PT) :
    Msg CT × SendState CK :=
  (⟨s.n, c.enc (c.kdfMsg s.ck) ad pt⟩, ⟨c.kdfChain s.ck, s.n + 1⟩)

/-- The message keys for the `cnt` messages starting at index `base`, derived from
chain key `ck`. -/
def skipKeys (c : Crypto CK MK AD PT CT) (ck : CK) (base : ℕ) : ℕ → List (ℕ × MK)
  | 0 => []
  | cnt + 1 => (base, c.kdfMsg ck) :: skipKeys c (c.kdfChain ck) (base + 1) cnt

/-- Why an incoming message was rejected. -/
inductive RecvError
  /-- The message index lies before the next expected one and is not a stored skip. -/
  | replay
  /-- Accepting the message would require more than `maxSkip` outstanding skips. -/
  | tooManySkipped
  /-- The ciphertext failed authentication. -/
  | authFail
deriving DecidableEq, Repr

/-- Receive one message.  Returns the outcome together with the new receiving state;
on every rejection the returned state is the unchanged input state. -/
def recvStep (c : Crypto CK MK AD PT CT) (s : RecvState CK MK) (ad : AD) (m : Msg CT) :
    Except RecvError PT × RecvState CK MK :=
  match List.lookup m.idx s.skipped with
  | some mk =>
      match c.dec mk ad m.ct with
      | some pt => (.ok pt, { s with skipped := s.skipped.filter (fun p => !(p.1 == m.idx)) })
      | none => (.error .authFail, s)
  | none =>
      if m.idx < s.n then (.error .replay, s)
      else if maxSkip < (m.idx - s.n) + s.skipped.length then (.error .tooManySkipped, s)
      else
        match c.dec (msgKeyAt c s.ck (m.idx - s.n)) ad m.ct with
        | some pt =>
            (.ok pt,
              { ck := chainAt c s.ck (m.idx - s.n + 1),
                n := m.idx + 1,
                skipped := s.skipped ++ skipKeys c s.ck s.n (m.idx - s.n) })
        | none => (.error .authFail, s)

/-- Well-formedness of a receiving state: at most `maxSkip` stored skipped keys,
all of them for indices before the next expected one, and no duplicate indices. -/
structure RecvWf (s : RecvState CK MK) : Prop where
  /-- The skipped-key store never holds more than `maxSkip = 50` keys. -/
  bound : s.skipped.length ≤ maxSkip
  /-- Stored keys are for messages before the next expected index. -/
  keys_lt : ∀ p ∈ s.skipped, p.1 < s.n
  /-- Stored keys have pairwise distinct indices. -/
  nodup : (s.skipped.map Prod.fst).Nodup

/-! ### Basic lemmas about `skipKeys` -/

theorem length_skipKeys (c : Crypto CK MK AD PT CT) (ck : CK) (base cnt : ℕ) :
    (skipKeys c ck base cnt).length = cnt := by
  induction cnt generalizing ck base with
  | zero => simp [skipKeys]
  | succ n ih => simp [skipKeys, ih]

theorem lookup_skipKeys (c : Crypto CK MK AD PT CT) (ck : CK) (base cnt j : ℕ)
    (hj : j < cnt) :
    List.lookup (base + j) (skipKeys c ck base cnt) = some (msgKeyAt c ck j) := by
  induction cnt generalizing ck base j with
  | zero => exact absurd hj (by omega)
  | succ n ih =>
    match j with
    | 0 => simp [skipKeys, msgKeyAt, chainAt]
    | j + 1 =>
      have hb : base + (j + 1) = (base + 1) + j := by omega
      rw [skipKeys, List.lookup_cons,
        show ((base + (j + 1)) == base) = false from by simp]
      rw [hb, ih (c.kdfChain ck) (base + 1) j (by omega)]
      simp [msgKeyAt, chainAt, Function.iterate_succ_apply]

theorem mem_skipKeys_index (c : Crypto CK MK AD PT CT) (ck : CK) (base cnt : ℕ)
    {p : ℕ × MK} (hp : p ∈ skipKeys c ck base cnt) : base ≤ p.1 ∧ p.1 < base + cnt := by
  induction cnt generalizing ck base with
  | zero => simp [skipKeys] at hp
  | succ n ih =>
    rw [skipKeys, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨le_rfl, by omega⟩
    · have := ih (c.kdfChain ck) (base + 1) hp
      exact ⟨by omega, by omega⟩

theorem nodup_skipKeys (c : Crypto CK MK AD PT CT) (ck : CK) (base cnt : ℕ) :
    ((skipKeys c ck base cnt).map Prod.fst).Nodup := by
  induction cnt generalizing ck base with
  | zero => simp [skipKeys]
  | succ n ih =>
    rw [skipKeys, List.map_cons, List.nodup_cons]
    refine ⟨?_, ih (c.kdfChain ck) (base + 1)⟩
    intro hmem
    obtain ⟨p, hp, hp2⟩ := List.mem_map.1 hmem
    have := mem_skipKeys_index c (c.kdfChain ck) (base + 1) n hp
    omega

/-- If every stored index is `< base`, nothing at or above `base` is found. -/
theorem lookup_eq_none_of_keys_lt {l : List (ℕ × MK)} {base i : ℕ}
    (h : ∀ p ∈ l, p.1 < base) (hi : base ≤ i) : List.lookup i l = none := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : a.1 < base := h a (by simp)
    have hne : ¬ (i = a.1) := by omega
    rw [show a = (a.1, a.2) from rfl, List.lookup_cons,
      show (i == a.1) = false from by simp [hne]]
    exact ih (fun p hp => h p (by simp [hp]))

/-! ### Case analysis for `recvStep` -/

/-- A message whose key is in the skipped store and which authenticates is delivered,
and its key is removed from the store. -/
theorem recvStep_stored_ok (c : Crypto CK MK AD PT CT) (s : RecvState CK MK) (ad : AD)
    (m : Msg CT) (mk : MK) (pt : PT) (hl : List.lookup m.idx s.skipped = some mk)
    (hd : c.dec mk ad m.ct = some pt) :
    recvStep c s ad m
      = (.ok pt, { s with skipped := s.skipped.filter (fun p => !(p.1 == m.idx)) }) := by
  simp only [recvStep, hl, hd]

/-- A message whose key is in the skipped store but which fails authentication is
rejected without any change of state. -/
theorem recvStep_stored_authFail (c : Crypto CK MK AD PT CT) (s : RecvState CK MK)
    (ad : AD) (m : Msg CT) (mk : MK) (hl : List.lookup m.idx s.skipped = some mk)
    (hd : c.dec mk ad m.ct = none) :
    recvStep c s ad m = (.error .authFail, s) := by
  simp only [recvStep, hl, hd]

/-- Replay protection: a message whose index lies before the next expected one and
whose key is not stored is rejected, without any change of state. -/
theorem recvStep_replay_rejected (c : Crypto CK MK AD PT CT) (s : RecvState CK MK)
    (ad : AD) (m : Msg CT) (hidx : m.idx < s.n)
    (hnew : List.lookup m.idx s.skipped = none) :
    recvStep c s ad m = (.error .replay, s) := by
  simp only [recvStep, hnew]
  rw [if_pos hidx]

/-- A message needing more skips than the store can hold is rejected, and the state is
left unchanged. -/
theorem recvStep_reject_tooManySkipped (c : Crypto CK MK AD PT CT) (s : RecvState CK MK)
    (ad : AD) (m : Msg CT) (hnew : List.lookup m.idx s.skipped = none)
    (hge : s.n ≤ m.idx) (hk : maxSkip < (m.idx - s.n) + s.skipped.length) :
    recvStep c s ad m = (.error .tooManySkipped, s) := by
  simp only [recvStep, hnew]
  rw [if_neg (by omega : ¬ m.idx < s.n), if_pos hk]

/-- In particular, with an empty store, a message skipping 51 messages is rejected. -/
theorem recvStep_reject_51 (c : Crypto CK MK AD PT CT) (ck : CK) (n : ℕ) (ad : AD)
    (ct : CT) :
    recvStep c ⟨ck, n, []⟩ ad ⟨n + 51, ct⟩ = (.error .tooManySkipped, ⟨ck, n, []⟩) :=
  recvStep_reject_tooManySkipped c ⟨ck, n, []⟩ ad ⟨n + 51, ct⟩ rfl (by simp)
    (by simp [maxSkip])

/-- A fresh message within the skip budget that authenticates is delivered: the chain
is ratcheted forward and the intervening message keys are stored. -/
theorem recvStep_chain_ok (c : Crypto CK MK AD PT CT) (s : RecvState CK MK) (ad : AD)
    (m : Msg CT) (pt : PT) (hnew : List.lookup m.idx s.skipped = none)
    (hge : s.n ≤ m.idx) (hk : ¬ maxSkip < (m.idx - s.n) + s.skipped.length)
    (hd : c.dec (msgKeyAt c s.ck (m.idx - s.n)) ad m.ct = some pt) :
    recvStep c s ad m
      = (.ok pt, ⟨chainAt c s.ck (m.idx - s.n + 1), m.idx + 1,
          s.skipped ++ skipKeys c s.ck s.n (m.idx - s.n)⟩) := by
  simp only [recvStep, hnew]
  rw [if_neg (by omega : ¬ m.idx < s.n), if_neg hk]
  simp only [hd]

/-- A fresh message within the skip budget that fails authentication is rejected
without any change of state: in particular the chain is *not* ratcheted forward and no
skipped keys are stored. -/
theorem recvStep_chain_authFail (c : Crypto CK MK AD PT CT) (s : RecvState CK MK)
    (ad : AD) (m : Msg CT) (hnew : List.lookup m.idx s.skipped = none)
    (hge : s.n ≤ m.idx) (hk : ¬ maxSkip < (m.idx - s.n) + s.skipped.length)
    (hd : c.dec (msgKeyAt c s.ck (m.idx - s.n)) ad m.ct = none) :
    recvStep c s ad m = (.error .authFail, s) := by
  simp only [recvStep, hnew]
  rw [if_neg (by omega : ¬ m.idx < s.n), if_neg hk]
  simp only [hd]

/-- Every run of `recvStep` falls into one of the six cases above. -/
theorem recvStep_cases (c : Crypto CK MK AD PT CT) (s : RecvState CK MK) (ad : AD)
    (m : Msg CT) :
    (∃ pt mk, List.lookup m.idx s.skipped = some mk ∧ c.dec mk ad m.ct = some pt ∧
        recvStep c s ad m
          = (.ok pt, { s with skipped := s.skipped.filter (fun p => !(p.1 == m.idx)) })) ∨
      (∃ pt, List.lookup m.idx s.skipped = none ∧ s.n ≤ m.idx ∧
        recvStep c s ad m
          = (.ok pt, ⟨chainAt c s.ck (m.idx - s.n + 1), m.idx + 1,
              s.skipped ++ skipKeys c s.ck s.n (m.idx - s.n)⟩)) ∨
      (∃ e, recvStep c s ad m = (.error e, s)) := by
  rcases Option.eq_none_or_eq_some (List.lookup m.idx s.skipped) with hl | ⟨mk, hl⟩
  · by_cases h1 : m.idx < s.n
    · exact Or.inr (Or.inr ⟨.replay, recvStep_replay_rejected c s ad m h1 hl⟩)
    · by_cases h2 : maxSkip < (m.idx - s.n) + s.skipped.length
      · exact Or.inr (Or.inr
          ⟨.tooManySkipped, recvStep_reject_tooManySkipped c s ad m hl (by omega) h2⟩)
      · rcases Option.eq_none_or_eq_some (c.dec (msgKeyAt c s.ck (m.idx - s.n)) ad m.ct)
          with hd | ⟨pt, hd⟩
        · exact Or.inr (Or.inr
            ⟨.authFail, recvStep_chain_authFail c s ad m hl (by omega) h2 hd⟩)
        · exact Or.inr (Or.inl
            ⟨pt, hl, by omega, recvStep_chain_ok c s ad m pt hl (by omega) h2 hd⟩)
  · rcases Option.eq_none_or_eq_some (c.dec mk ad m.ct) with hd | ⟨pt, hd⟩
    · exact Or.inr (Or.inr ⟨.authFail, recvStep_stored_authFail c s ad m mk hl hd⟩)
    · exact Or.inl ⟨pt, mk, hl, hd, recvStep_stored_ok c s ad m mk pt hl hd⟩

/-! ### State neutrality -/

/-- The ratchet is *state neutral*: whenever an incoming message is rejected — in
particular whenever it fails authentication — the receiving state is returned
unchanged. -/
theorem recvStep_state_neutral_of_error (c : Crypto CK MK AD PT CT) (s : RecvState CK MK)
    (ad : AD) (m : Msg CT) (e : RecvError) (h : (recvStep c s ad m).1 = .error e) :
    (recvStep c s ad m).2 = s := by
  rcases recvStep_cases c s ad m with ⟨pt, mk, _, _, hr⟩ | ⟨pt, _, _, hr⟩ | ⟨e', hr⟩ <;>
    rw [hr] at h ⊢ <;> simp at h ⊢

/-- On an authentication failure no message key is added to (or removed from) the
skipped-key store. -/
theorem recvStep_authFail_no_new_skipped (c : Crypto CK MK AD PT CT) (s : RecvState CK MK)
    (ad : AD) (m : Msg CT) (h : (recvStep c s ad m).1 = .error .authFail) :
    (recvStep c s ad m).2.skipped = s.skipped := by
  rw [recvStep_state_neutral_of_error c s ad m .authFail h]

/-! ### Well-formedness is preserved -/

theorem RecvWf.recvStep {c : Crypto CK MK AD PT CT} {s : RecvState CK MK}
    (hs : RecvWf s) (ad : AD) (m : Msg CT) : RecvWf (Ratchet.recvStep c s ad m).2 := by
  rcases Ratchet.recvStep_cases c s ad m with
    ⟨pt, mk, _, _, hr⟩ | ⟨pt, hl, hge, hr⟩ | ⟨e, hr⟩
  · rw [hr]
    dsimp only
    refine ⟨?_, ?_, ?_⟩
    · exact le_trans (List.length_filter_le _ _) hs.bound
    · exact fun p hp => hs.keys_lt p (List.mem_of_mem_filter hp)
    · exact List.Nodup.sublist (List.Sublist.map Prod.fst List.filter_sublist) hs.nodup
  · have hk : ¬ maxSkip < (m.idx - s.n) + s.skipped.length := by
      intro hcon
      rw [recvStep_reject_tooManySkipped c s ad m hl hge hcon] at hr
      simp at hr
    rw [hr]
    dsimp only
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.length_append, length_skipKeys]
      omega
    · intro p hp
      show p.1 < m.idx + 1
      rcases List.mem_append.1 hp with hp | hp
      · have := hs.keys_lt p hp; omega
      · have := mem_skipKeys_index c s.ck s.n (m.idx - s.n) hp; omega
    · simp only [List.map_append]
      refine List.Nodup.append hs.nodup (nodup_skipKeys _ _ _ _) ?_
      intro a ha hb
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
      obtain ⟨q, hq, hq2⟩ := List.mem_map.1 hb
      have h3 := hs.keys_lt p hp
      have h4 := mem_skipKeys_index c s.ck s.n (m.idx - s.n) hq
      omega
  · rw [hr]; exact hs

/-- Consequently the skipped-key store never exceeds 50 entries. -/
theorem recvStep_skipped_length_le {c : Crypto CK MK AD PT CT} {s : RecvState CK MK}
    (hs : RecvWf s) (ad : AD) (m : Msg CT) :
    (recvStep c s ad m).2.skipped.length ≤ maxSkip :=
  (hs.recvStep ad m).bound

/-! ### Correctness -/

/-- Accepting a message that skips `k` messages, provided the total number of
outstanding skipped keys stays within the bound of 50.  The `k` skipped message keys
are stored for later delivery. -/
theorem recvStep_skip_ahead (c : Crypto CK MK AD PT CT) (s : RecvState CK MK)
    (hwf : RecvWf s) (ad : AD) (pt : PT) (k : ℕ)
    (hk : k + s.skipped.length ≤ maxSkip) :
    recvStep c s ad ⟨s.n + k, c.enc (msgKeyAt c s.ck k) ad pt⟩
      = (.ok pt,
         ⟨chainAt c s.ck (k + 1), s.n + k + 1, s.skipped ++ skipKeys c s.ck s.n k⟩) := by
  have hlk : List.lookup (s.n + k) s.skipped = none :=
    lookup_eq_none_of_keys_lt hwf.keys_lt (by omega)
  have hsub : (Msg.mk (s.n + k) (c.enc (msgKeyAt c s.ck k) ad pt)).idx - s.n = k := by
    simp
  have h := recvStep_chain_ok c s ad ⟨s.n + k, c.enc (msgKeyAt c s.ck k) ad pt⟩ pt
    (by simpa using hlk) (by simp) (by rw [hsub]; omega)
    (by rw [hsub]; exact c.dec_enc _ _ _)
  rw [h, hsub]

/-- The next expected message, if it authenticates, is delivered: the chain advances
by one link and the skipped-key store is untouched. -/
theorem recvStep_inOrder (c : Crypto CK MK AD PT CT) (ck : CK) (n : ℕ)
    (skipped : List (ℕ × MK)) (hwf : RecvWf (⟨ck, n, skipped⟩ : RecvState CK MK))
    (ad : AD) (pt : PT) :
    recvStep c ⟨ck, n, skipped⟩ ad ⟨n, c.enc (c.kdfMsg ck) ad pt⟩
      = (.ok pt, ⟨c.kdfChain ck, n + 1, skipped⟩) := by
  have hb : skipped.length ≤ maxSkip := hwf.bound
  have h := recvStep_skip_ahead c ⟨ck, n, skipped⟩ hwf ad pt 0 (by simpa using hb)
  simpa [msgKeyAt, chainAt, skipKeys] using h

/-- In-order round trip: a message produced by a sender in sync with the receiver is
accepted, yields the original plaintext, advances the receiving chain by one link and
leaves the skipped-key store untouched. -/
theorem recvStep_of_sendStep_inOrder (c : Crypto CK MK AD PT CT) (ck : CK) (n : ℕ)
    (skipped : List (ℕ × MK)) (hwf : RecvWf (⟨ck, n, skipped⟩ : RecvState CK MK))
    (ad : AD) (pt : PT) :
    recvStep c ⟨ck, n, skipped⟩ ad (sendStep c ⟨ck, n⟩ ad pt).1
      = (.ok pt, ⟨c.kdfChain ck, n + 1, skipped⟩) :=
  recvStep_inOrder c ck n skipped hwf ad pt

/-- Out-of-order delivery: a message that was skipped is still delivered later, from
the skipped-key store, and its key is removed from the store. -/
theorem recvStep_delivers_skipped (c : Crypto CK MK AD PT CT) (s s' : RecvState CK MK)
    (hwf : RecvWf s) (ad : AD) (pt pt' : PT) (k j : ℕ) (hj : j < k)
    (hk : k + s.skipped.length ≤ maxSkip)
    (hs' : s' = (recvStep c s ad ⟨s.n + k, c.enc (msgKeyAt c s.ck k) ad pt⟩).2) :
    recvStep c s' ad ⟨s.n + j, c.enc (msgKeyAt c s.ck j) ad pt'⟩
      = (.ok pt', { s' with skipped := s'.skipped.filter (fun p => !(p.1 == s.n + j)) }) := by
  subst hs'
  rw [recvStep_skip_ahead c s hwf ad pt k hk]
  have h1 : List.lookup (s.n + j) s.skipped = none :=
    lookup_eq_none_of_keys_lt hwf.keys_lt (by omega)
  have h2 : List.lookup (s.n + j) (s.skipped ++ skipKeys c s.ck s.n k)
      = some (msgKeyAt c s.ck j) := by
    rw [List.lookup_append, h1, lookup_skipKeys c s.ck s.n k j hj]
    rfl
  exact recvStep_stored_ok c _ ad ⟨s.n + j, c.enc (msgKeyAt c s.ck j) ad pt'⟩ _ pt'
    (by simpa using h2) (c.dec_enc _ _ _)

/-! ### A whole session

The single-step results are lifted to a whole run of the ratchet: the sender emits a
stream of messages, and a receiver started in sync with the sender decrypts them all,
staying in sync. -/

/-- The sending state after `i` messages have been sent. -/
def sendRun (c : Crypto CK MK AD PT CT) (s0 : SendState CK) (ad : ℕ → AD) (pt : ℕ → PT) :
    ℕ → SendState CK
  | 0 => s0
  | i + 1 => (sendStep c (sendRun c s0 ad pt i) (ad i) (pt i)).2

/-- The `i`-th message emitted by the sender. -/
def sentMsg (c : Crypto CK MK AD PT CT) (s0 : SendState CK) (ad : ℕ → AD) (pt : ℕ → PT)
    (i : ℕ) : Msg CT :=
  (sendStep c (sendRun c s0 ad pt i) (ad i) (pt i)).1

/-- The receiving state after the first `i` messages of a stream have been processed. -/
def recvRun (c : Crypto CK MK AD PT CT) (r0 : RecvState CK MK) (ad : ℕ → AD)
    (msgs : ℕ → Msg CT) : ℕ → RecvState CK MK
  | 0 => r0
  | i + 1 => (recvStep c (recvRun c r0 ad msgs i) (ad i) (msgs i)).2

theorem sendRun_eq (c : Crypto CK MK AD PT CT) (s0 : SendState CK) (ad : ℕ → AD)
    (pt : ℕ → PT) (i : ℕ) : sendRun c s0 ad pt i = ⟨chainAt c s0.ck i, s0.n + i⟩ := by
  induction i with
  | zero => simp [sendRun, chainAt]
  | succ i ih =>
    simp only [sendRun, ih, sendStep, chainAt, ← Function.iterate_succ_apply']
    exact congrArg _ (by omega)

theorem sentMsg_eq (c : Crypto CK MK AD PT CT) (s0 : SendState CK) (ad : ℕ → AD)
    (pt : ℕ → PT) (i : ℕ) :
    sentMsg c s0 ad pt i = ⟨s0.n + i, c.enc (msgKeyAt c s0.ck i) (ad i) (pt i)⟩ := by
  simp [sentMsg, sendStep, sendRun_eq, msgKeyAt]

/-- A receiver started in sync with the sender stays in sync while receiving the
message stream in order: after `i` messages its chain key is the sender's `i`-th chain
key, it expects message `i`, and its skipped-key store is empty. -/
theorem recvRun_inOrder_state (c : Crypto CK MK AD PT CT) (s0 : SendState CK)
    (ad : ℕ → AD) (pt : ℕ → PT) (i : ℕ) :
    recvRun c ⟨s0.ck, s0.n, []⟩ ad (sentMsg c s0 ad pt) i
      = ⟨chainAt c s0.ck i, s0.n + i, []⟩ := by
  induction i with
  | zero => simp [recvRun, chainAt]
  | succ i ih =>
    have hwf : RecvWf (⟨chainAt c s0.ck i, s0.n + i, []⟩ : RecvState CK MK) :=
      ⟨by simp [maxSkip], by simp, by simp⟩
    have hmsg : sentMsg c s0 ad pt i
        = ⟨s0.n + i, c.enc (c.kdfMsg (chainAt c s0.ck i)) (ad i) (pt i)⟩ := by
      simp [sentMsg_eq, msgKeyAt]
    rw [recvRun, ih, hmsg,
      recvStep_inOrder c (chainAt c s0.ck i) (s0.n + i) [] hwf (ad i) (pt i)]
    simp only [chainAt, ← Function.iterate_succ_apply']
    rfl

/-- Whole-session correctness: every message of the stream is authenticated and
decrypted to the plaintext the sender encrypted. -/
theorem recvRun_inOrder_ok (c : Crypto CK MK AD PT CT) (s0 : SendState CK) (ad : ℕ → AD)
    (pt : ℕ → PT) (i : ℕ) :
    (recvStep c (recvRun c ⟨s0.ck, s0.n, []⟩ ad (sentMsg c s0 ad pt) i) (ad i)
      (sentMsg c s0 ad pt i)).1 = .ok (pt i) := by
  have hwf : RecvWf (⟨chainAt c s0.ck i, s0.n + i, []⟩ : RecvState CK MK) :=
    ⟨by simp [maxSkip], by simp, by simp⟩
  have hmsg : sentMsg c s0 ad pt i
      = ⟨s0.n + i, c.enc (c.kdfMsg (chainAt c s0.ck i)) (ad i) (pt i)⟩ := by
    simp [sentMsg_eq, msgKeyAt]
  rw [recvRun_inOrder_state, hmsg,
    recvStep_inOrder c (chainAt c s0.ck i) (s0.n + i) [] hwf (ad i) (pt i)]

/-! ### A concrete instance

A toy instantiation of the primitives, showing that the model is non-vacuous: every
branch of `recvStep` — in-order delivery, skipping, delivery of a skipped message,
rejection past the bound of 50, and authentication failure — is actually reachable. -/

namespace Example

/-- Toy primitives: chain keys and message keys are numbers, and a ciphertext carries
the message key it was produced with, which is what `dec` authenticates. -/
def testCrypto : Crypto ℕ ℕ Unit ℕ (ℕ × ℕ) where
  kdfChain ck := ck + 1
  kdfMsg ck := 2 * ck
  enc k _ p := (k, p)
  dec k _ ct := if ct.1 = k then some ct.2 else none
  dec_enc := by intro k ad p; simp

/-- In-order delivery. -/
example :
    recvStep testCrypto ⟨0, 0, []⟩ () ⟨0, (0, 42)⟩ = (.ok 42, ⟨1, 1, []⟩) := rfl

/-- Skipping three messages stores their keys. -/
example :
    recvStep testCrypto ⟨0, 0, []⟩ () ⟨3, (6, 42)⟩
      = (.ok 42, ⟨4, 4, [(0, 0), (1, 2), (2, 4)]⟩) := rfl

/-- A skipped message delivered afterwards, using the stored key. -/
example :
    recvStep testCrypto ⟨4, 4, [(0, 0), (1, 2), (2, 4)]⟩ () ⟨1, (2, 7)⟩
      = (.ok 7, ⟨4, 4, [(0, 0), (2, 4)]⟩) := rfl

/-- Skipping 51 messages is rejected, with the state unchanged. -/
example :
    recvStep testCrypto ⟨0, 0, []⟩ () ⟨51, (102, 42)⟩
      = (.error .tooManySkipped, ⟨0, 0, []⟩) := rfl

/-- A forged ciphertext fails authentication and leaves the state untouched. -/
example :
    recvStep testCrypto ⟨0, 0, []⟩ () ⟨3, (7, 42)⟩ = (.error .authFail, ⟨0, 0, []⟩) := rfl

/-- Tampering with a message whose key is in the skipped store is also state neutral. -/
example :
    recvStep testCrypto ⟨4, 4, [(0, 0), (1, 2), (2, 4)]⟩ () ⟨1, (3, 7)⟩
      = (.error .authFail, ⟨4, 4, [(0, 0), (1, 2), (2, 4)]⟩) := rfl

/-- Replaying an already delivered message is rejected. -/
example :
    recvStep testCrypto ⟨1, 1, []⟩ () ⟨0, (0, 42)⟩ = (.error .replay, ⟨1, 1, []⟩) := rfl

end Example

end Ratchet
