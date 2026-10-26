-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftLor

/-!
# Guessing a fresh message of the record-ideal world: `FreshGuessStatement` (items 4 and 5, world facts)

**Statement.** `idealRecords_fresh` proves `PqxdhRecordLiftIdeal.FreshGuessStatement` as defined: in mode P, for every environment, adversary and claim read from the adversary's output (no `Frame` or budget premise), the probability in `idealRecords` that the claimed fresh message was sent on a handle holding a hidden slot and equals the claimed guess is at most `2^-min`, where `min` is the fresh bounds' minimal message length.

**Proof.** First, the event depends on a view only through its hiding projection (`freshHit_hiding`, `freshEvent_hiding`), so by `PqxdhRecordLiftLor.law_zeros` its law in `idealRecords` equals its law in the random-ciphertext world with every hidden seal plaintext zeroed. Second (`hitAt_bound`), fix a claimed index `i` and message length `ℓ`. For every offset vector `d` of `ℓ` bytes, the zeroed world is coupled with itself by a `PqxdhRecordLiftSwap.Swap` coupling on the flattened world of `PqxdhRecordLiftFlat` (`world_couple`): the native coin of byte `j` of the `i`-th admitted fresh message is relabelled by adding `d_j` modulo 256 (`bytes_couple`, `shiftByte_coin`), so that message is shifted by `d` (`shiftFrom`, `shiftLedger`) while every other coin is drawn equally. Queries other than that fresh message commute with the shift (`ledger_shift_forward`, `ledger_shift_test`, `ledger_shift_fresh`, `commute_couple`); its send of either the message or its shift, which have the same length, is the same computation on a handle without a caller-known kernel (`send_couple`, from `PqxdhRecordLiftFlat.nativeImpl_send_zeros`); a send on a caller-known handle is an escape (`FreshEscaped`), kept by every later query (`freshEscaped_keep`) because fresh entries are only appended and caller-known kernels persist, and in an escaped run the message's handle holds no slot (`handleSlot_known`), so neither side hits (`hitAt_escaped`, `shiftedHit_escaped`). The relation also carries that every fresh message has at least the minimal length (`FreshLong`, `ledger_freshLong`, `uniformBytes_length`). Hence the hit at `(i, ℓ)` has the probability of the shifted hit for every `d` (`hitAt_shift`); the `256^ℓ` shifted hits exclude each other (`shiftedHit_disjoint`, `extend_offsets`) and each implies the claim `(i, ℓ)` (`shiftedHit_key`), and for `ℓ` below the minimal length no shifted hit is possible, so `Pr[hit at (i, ℓ)] ≤ 256^-min · Pr[claim (i, ℓ)]`. Third (`fresh_zeros`), every hit is a hit at its claim (`freshEvent_cover`) and claims exclude each other (`keyAt_unique`), so summing over `(i, ℓ)` gives at most `256^-min · 1 ≤ 2^-min`. The per-claim weighting keeps the bound at `2^-min`; a bound of `2^-min` for each index separately would only give the number of fresh messages times `2^-min`.

**Contracts.** No theorem of this module has an assumption or contract hypothesis, and no security game enters; contracts reached are listed per theorem in `doc/impl/record-lift-facts.md`. New Claude work.
-/

open OracleComp OracleSpec ENNReal CoreModels Aeneas MeasureTheory
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftFresh
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftFlat PqxdhRecordLiftSwap
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds Spec FullSpec Handle asModeO)
open PqxdhDeploymentSecrecy (Ledger FreshEntry)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

/-! ### Byte shifts -/

/-- Shift a byte by an offset, modulo 256. -/
def shiftByte (byte : UInt8) (offset : Fin 256) : UInt8 := byte + UInt8.ofNat offset.val

/-- The byte of a coin relabelled by an offset is the shifted byte of the coin. -/
theorem shiftByte_coin (coin offset : Fin 256) :
    shiftByte (UInt8.ofNat coin.val) offset = UInt8.ofNat (coin + offset).val := by
  apply UInt8.toNat_inj.mp
  simp [shiftByte, UInt8.toNat_add, Fin.val_add]

/-- Shifting by one offset is injective in the byte. -/
theorem shiftByte_injective (offset : Fin 256) (first second : UInt8)
    (same : shiftByte first offset = shiftByte second offset) : first = second := by
  have h := congrArg UInt8.toNat same
  simp only [shiftByte, UInt8.toNat_add, UInt8.toNat_ofNat'] at h
  have h₁ := UInt8.toNat_lt first
  have h₂ := UInt8.toNat_lt second
  have h₃ := offset.isLt
  exact UInt8.toNat_inj.mp (by omega)

/-- A shifted byte determines the offset. -/
theorem shiftByte_offset (byte : UInt8) (first second : Fin 256)
    (same : shiftByte byte first = shiftByte byte second) : first = second := by
  have h := congrArg UInt8.toNat same
  simp only [shiftByte, UInt8.toNat_add, UInt8.toNat_ofNat'] at h
  have h₁ := UInt8.toNat_lt byte
  have h₂ := first.isLt
  have h₃ := second.isLt
  exact Fin.ext (by omega)

/-- Shift the bytes of a message by per-position offsets, the first byte at position `start`. -/
def shiftFrom (offsets : ℕ → Fin 256) : ℕ → Pqxdh.Bytes → Pqxdh.Bytes
  | _, [] => []
  | start, byte :: rest => shiftByte byte (offsets start) :: shiftFrom offsets (start + 1) rest

/-- A shift keeps the length. -/
theorem shiftFrom_length (offsets : ℕ → Fin 256) (start : ℕ) (message : Pqxdh.Bytes) :
    (shiftFrom offsets start message).length = message.length := by
  induction message generalizing start with
  | nil => rfl
  | cons byte rest ih => simp only [shiftFrom, List.length_cons, ih]

/-- A shift is injective in the message. -/
theorem shiftFrom_injective (offsets : ℕ → Fin 256) (start : ℕ) (first second : Pqxdh.Bytes)
    (same : shiftFrom offsets start first = shiftFrom offsets start second) : first = second := by
  induction first generalizing start second with
  | nil =>
      cases second with
      | nil => rfl
      | cons _ _ => simp [shiftFrom] at same
  | cons byte rest ih =>
      cases second with
      | nil => simp [shiftFrom] at same
      | cons byte' rest' =>
          simp only [shiftFrom, List.cons.injEq] at same
          rw [shiftByte_injective _ _ _ same.1, ih (start + 1) rest' same.2]

/-- Two shifts of one message agree only if their offsets agree on the message's positions. -/
theorem shiftFrom_offsets (first second : ℕ → Fin 256) (start : ℕ) (message : Pqxdh.Bytes)
    (same : shiftFrom first start message = shiftFrom second start message) :
    ∀ j, start ≤ j → j < start + message.length → first j = second j := by
  induction message generalizing start with
  | nil =>
      intro j h₁ h₂
      simp only [List.length_nil, Nat.add_zero] at h₂
      omega
  | cons byte rest ih =>
      simp only [shiftFrom, List.cons.injEq] at same
      intro j h₁ h₂
      rcases Nat.eq_or_lt_of_le h₁ with rfl | lt
      · exact shiftByte_offset byte _ _ same.1
      · simp only [List.length_cons] at h₂
        exact ih (start + 1) same.2 j lt (by omega)

/-- The per-position offsets of a shift of the first `length` positions. -/
def extend {length : ℕ} (offsets : Fin length → Fin 256) (j : ℕ) : Fin 256 :=
  if h : j < length then offsets ⟨j, h⟩ else 0

/-- Shifts of a message of length `length` by distinct offsets differ. -/
theorem extend_offsets {length : ℕ} (message : Pqxdh.Bytes) (hlength : message.length = length)
    (first second : Fin length → Fin 256)
    (same : shiftFrom (extend first) 0 message = shiftFrom (extend second) 0 message) : first = second := by
  funext j
  have h := shiftFrom_offsets _ _ 0 message same j.val (Nat.zero_le _) (by omega)
  simpa only [extend, j.isLt, ↓reduceDIte] using h

/-! ### The shift of one fresh message in the ledger -/

/-- Shift the message of a fresh entry. -/
def shiftEntry (offsets : ℕ → Fin 256) (entry : FreshEntry) : FreshEntry :=
  { entry with message := shiftFrom offsets 0 entry.message }

/-- Shift the message of the `index`-th fresh entry of a ledger. -/
def shiftLedger (index : ℕ) (offsets : ℕ → Fin 256) (ledger : Ledger) : Ledger :=
  { ledger with fresh := ledger.fresh.modify index (shiftEntry offsets) }

/-- The empty ledger is unshifted. -/
theorem shiftLedger_empty (index : ℕ) (offsets : ℕ → Fin 256) :
    shiftLedger index offsets Ledger.empty = Ledger.empty := by
  simp [shiftLedger, PqxdhDeploymentSecrecy.Ledger.empty]

/-- Modifying a list at an index other than its length commutes with appending one element. -/
theorem modify_append_ne {α : Type} (l : List α) (a : α) (i : ℕ) (f : α → α) (h : l.length ≠ i) :
    (l ++ [a]).modify i f = l.modify i f ++ [a] := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_modify, List.getElem?_append, List.length_modify, List.getElem?_singleton]
  by_cases hj : j < l.length
  · simp [hj]
  · by_cases hl : j - l.length = 0
    · have : j = l.length := by omega
      subst this
      simp [Ne.symm h]
    · simp [hj, hl]

/-- Modifying a list at its length after appending one element modifies that element. -/
theorem modify_append_length {α : Type} (l : List α) (a : α) (f : α → α) :
    (l ++ [a]).modify l.length f = l ++ [f a] := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_modify, List.getElem?_append, List.getElem?_singleton]
  by_cases hj : j < l.length
  · simp [hj, Nat.ne_of_gt hj]
  · by_cases hl : j - l.length = 0
    · have : j = l.length := by omega
      subst this
      simp
    · have : l.length ≠ j := by omega
      simp [hj, hl, this]

/-- Appending a fresh entry at another index commutes with the shift. -/
theorem shiftLedger_append (index : ℕ) (offsets : ℕ → Fin 256) (ledger : Ledger)
    (other : ledger.fresh.length ≠ index) (query : PqxdhDeploymentInterface.Query) (reply : FullSpec.Range query)
    (entry : FreshEntry) :
    { (shiftLedger index offsets ledger).record query reply with
        fresh := (shiftLedger index offsets ledger).fresh ++ [entry] } =
      shiftLedger index offsets { ledger.record query reply with fresh := ledger.fresh ++ [entry] } := by
  simp only [shiftLedger, PqxdhDeploymentSecrecy.Ledger.record, modify_append_ne _ _ _ _ other]

/-- Appending the `index`-th fresh entry and its shift. -/
theorem shiftLedger_target (offsets : ℕ → Fin 256) (ledger : Ledger) (query : PqxdhDeploymentInterface.Query)
    (reply : FullSpec.Range query) (handle : Handle) (message : Pqxdh.Bytes)
    (answer : Option RawCtxSourceSend.Encrypted) :
    { (shiftLedger ledger.fresh.length offsets ledger).record query reply with
        fresh := (shiftLedger ledger.fresh.length offsets ledger).fresh ++
          [⟨handle, shiftFrom offsets 0 message, answer⟩] } =
      shiftLedger ledger.fresh.length offsets
        { ledger.record query reply with fresh := ledger.fresh ++ [⟨handle, message, answer⟩] } := by
  simp only [shiftLedger, PqxdhDeploymentSecrecy.Ledger.record, modify_append_length,
    List.modify_eq_self (Nat.le_refl _)]
  rfl

/-- A forwarded query commutes with the shift. -/
theorem ledger_shift_forward (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (bounds : FreshBounds) (index : ℕ) (offsets : ℕ → Fin 256) (query : Spec.Domain) (ledger : Ledger) :
    (PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds (.inl query)).run
        (shiftLedger index offsets ledger) =
      (fun p => (p.1, shiftLedger index offsets p.2)) <$>
        (PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds (.inl query)).run ledger := by
  rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, PqxdhDeploymentSecrecy.ledgerImpl_forward, Functor.map_map]
  rfl

/-- A test commutes with the shift: the ledger's test step reads only the transcript and the test session. -/
theorem ledger_shift_test (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (bounds : FreshBounds) (index : ℕ) (offsets : ℕ → Fin 256) (handle : Handle) (left right : Pqxdh.Bytes)
    (ledger : Ledger) :
    (PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds (.inr (.test handle left right))).run
        (shiftLedger index offsets ledger) =
      (fun p => (p.1, shiftLedger index offsets p.2)) <$>
        (PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds (.inr (.test handle left right))).run
          ledger := by
  rcases ledger with ⟨transcript, test, fresh⟩
  simp only [shiftLedger, PqxdhDeploymentSecrecy.ledgerImpl, StateT.run]
  by_cases admissible : PqxdhDeploymentSecrecy.Admissible left right
  · simp only [admissible, ↓reduceIte]
    cases test with
    | none =>
        simp only [map_bind, map_pure]
        rfl
    | some session =>
        by_cases same : PqxdhDeploymentSecrecy.SameSession crypto codec serverKid transcript session.first handle
        · simp only [same, ↓reduceIte, map_bind, map_pure]
          rfl
        · simp only [same, ↓reduceIte, map_pure]
          rfl
  · simp only [admissible, ↓reduceIte, map_pure]
    rfl

/-- A fresh query other than the admitted `index`-th one commutes with the shift. -/
theorem ledger_shift_fresh (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (bounds : FreshBounds) (index : ℕ) (offsets : ℕ → Fin 256) (handle : Handle) (length : ℕ) (ledger : Ledger)
    (other : ¬((bounds.min ≤ length ∧ length ≤ bounds.max) ∧ ledger.fresh.length = index)) :
    (PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds (.inr (.fresh handle length))).run
        (shiftLedger index offsets ledger) =
      (fun p => (p.1, shiftLedger index offsets p.2)) <$>
        (PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds (.inr (.fresh handle length))).run
          ledger := by
  simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run]
  split
  · rename_i admitted
    have hne : ledger.fresh.length ≠ index := fun h => other ⟨admitted, h⟩
    simp only [map_bind, map_pure, shiftLedger_append index offsets ledger hne]
  · simp only [map_pure]
    rfl

/-! ### Ledger invariants -/

/-- Every fresh message of the ledger has at least the minimal length. -/
def FreshLong (bounds : FreshBounds) (ledger : Ledger) : Prop :=
  ∀ entry ∈ ledger.fresh, bounds.min ≤ entry.message.length

/-- A uniform message has the requested length. -/
theorem uniformBytes_length (length : ℕ) :
    ∀ message ∈ support (PqxdhDeploymentSecrecy.uniformBytes length), message.length = length := by
  induction length with
  | zero =>
      intro message hmessage
      simp only [PqxdhDeploymentSecrecy.uniformBytes, support_pure, Set.mem_singleton_iff] at hmessage
      subst hmessage
      rfl
  | succ length ih =>
      intro message hmessage
      simp only [PqxdhDeploymentSecrecy.uniformBytes] at hmessage
      obtain ⟨_, _, hmessage⟩ := (mem_support_bind_iff _ _ _).mp hmessage
      obtain ⟨rest, hrest, hmessage⟩ := (mem_support_bind_iff _ _ _).mp hmessage
      obtain rfl := (mem_support_pure_iff _ _).mp hmessage
      simp only [List.length_cons, ih rest hrest]

/-- Every secrecy-ledger step keeps the minimal length of fresh messages. -/
theorem ledger_freshLong (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (bounds : FreshBounds) (query : FullSpec.Domain) (ledger : Ledger) (long : FreshLong bounds ledger) :
    ∀ p ∈ support ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds query).run ledger),
      FreshLong bounds p.2 := by
  intro p hp
  rcases query with forwarded | (⟨handle, left, right⟩ | ⟨handle, length⟩)
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, support_map] at hp
    obtain ⟨reply, _, rfl⟩ := hp
    exact long
  · simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run] at hp
    repeat' split at hp
    all_goals first
      | obtain rfl := (mem_support_pure_iff _ _).mp hp
        exact long
      | obtain ⟨_, _, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
        first
          | obtain rfl := (mem_support_pure_iff _ _).mp hp
            exact long
          | obtain ⟨_, _, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
            obtain rfl := (mem_support_pure_iff _ _).mp hp
            exact long
  · simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run] at hp
    split at hp
    · rename_i admitted
      obtain ⟨message, hmessage, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      obtain ⟨_, _, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      obtain rfl := (mem_support_pure_iff _ _).mp hp
      intro entry hentry
      rcases List.mem_append.mp hentry with hentry | hentry
      · exact long entry hentry
      · rw [List.mem_singleton.mp hentry, uniformBytes_length length message hmessage]
        exact admitted.1
    · obtain rfl := (mem_support_pure_iff _ _).mp hp
      exact long

/-- Every secrecy-ledger step only appends fresh entries. -/
theorem ledger_fresh_prefix (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (bounds : FreshBounds) (query : FullSpec.Domain) (ledger : Ledger) :
    ∀ p ∈ support ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds query).run ledger),
      ∃ extra, p.2.fresh = ledger.fresh ++ extra := by
  intro p hp
  rcases query with forwarded | (⟨handle, left, right⟩ | ⟨handle, length⟩)
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, support_map] at hp
    obtain ⟨reply, _, rfl⟩ := hp
    exact ⟨[], (List.append_nil _).symm⟩
  · simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run] at hp
    repeat' split at hp
    all_goals first
      | obtain rfl := (mem_support_pure_iff _ _).mp hp
        exact ⟨[], (List.append_nil _).symm⟩
      | obtain ⟨_, _, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
        first
          | obtain rfl := (mem_support_pure_iff _ _).mp hp
            exact ⟨[], (List.append_nil _).symm⟩
          | obtain ⟨_, _, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
            obtain rfl := (mem_support_pure_iff _ _).mp hp
            exact ⟨[], (List.append_nil _).symm⟩
  · simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run] at hp
    split at hp
    · obtain ⟨_, _, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      obtain ⟨_, _, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      obtain rfl := (mem_support_pure_iff _ _).mp hp
      exact ⟨_, rfl⟩
    · obtain rfl := (mem_support_pure_iff _ _).mp hp
      exact ⟨[], (List.append_nil _).symm⟩

/-! ### Related and escaped states -/

/-- Full states of the two coupled runs: the same native state, the right ledger the left one with its `index`-th fresh message shifted, and long fresh messages. -/
def FreshRelated (bounds : FreshBounds) (index : ℕ) (offsets : ℕ → Fin 256) (s t : Ledger × NativeState n E) :
    Prop :=
  t.2 = s.2 ∧ t.1 = shiftLedger index offsets s.1 ∧ FreshLong bounds s.1

/-- The run has escaped: the `index`-th fresh message went to a handle that now holds a caller-known kernel. -/
def FreshEscaped (index : ℕ) (s : Ledger × NativeState n E) : Prop :=
  ∃ entry, s.1.fresh[index]? = some entry ∧ KnownAt s.2.1.2 entry.handle

/-- Every adversary query keeps an escape: fresh entries are only appended and caller-known kernels persist. -/
theorem freshEscaped_keep (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (index : ℕ) (query : FullSpec.Domain)
    (s : Ledger × NativeState n E) (escaped : FreshEscaped index s) :
    ∀ p ∈ support ((fullImpl modes replace setup codec route env serverKid bounds query).run s),
      FreshEscaped index p.2 := by
  obtain ⟨ledger, state⟩ := s
  obtain ⟨entry, hentry, hknown⟩ := escaped
  intro p hp
  rw [fullImpl_run, support_map] at hp
  obtain ⟨z, hz, rfl⟩ := hp
  obtain ⟨extra, hextra⟩ := ledger_fresh_prefix setup.source.crypto codec serverKid bounds query ledger z.1
    (support_run_fst _ _ _ z hz)
  dsimp only at hentry hknown
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hentry
  refine ⟨entry, ?_, ?_⟩
  · dsimp only
    rw [hextra, List.getElem?_append_left hlt]
    exact hentry
  · exact support_keep_oracle (nativeImpl modes replace setup codec route env)
      (fun ns => KnownAt ns.1.2 entry.handle)
      (fun q ns known => nativeImpl_known modes replace setup codec route env entry.handle q ns known) _ state hknown
      z hz

/-! ### One coupled adversary query -/

/-- A query whose ledger step commutes with the shift is coupled with itself, with related states. -/
theorem commute_couple (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (index : ℕ) (offsets : ℕ → Fin 256)
    (query : FullSpec.Domain) (ledger : Ledger) (state : NativeState n E) (long : FreshLong bounds ledger)
    (commute : (PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds query).run
        (shiftLedger index offsets ledger) = (fun p => (p.1, shiftLedger index offsets p.2)) <$>
          (PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds query).run ledger) :
    Swap (SimRel (FreshRelated bounds index offsets) (FreshEscaped index) (FreshEscaped index))
      ((fullImpl modes replace setup codec route env serverKid bounds query).run (ledger, state))
      ((fullImpl modes replace setup codec route env serverKid bounds query).run
        (shiftLedger index offsets ledger, state)) := by
  rw [fullImpl_run, fullImpl_run, commute, simulateQ_map, StateT.run_map, Functor.map_map]
  refine (Swap.refl_support ((simulateQ (nativeImpl modes replace setup codec route env)
    ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds query).run ledger)).run state)
    (R := fun a b => a = b ∧ a ∈ support ((simulateQ (nativeImpl modes replace setup codec route env)
      ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds query).run ledger)).run state))
    fun a ha => ⟨rfl, ha⟩).map ?_
  rintro a b ⟨rfl, ha⟩
  exact Or.inl ⟨rfl, rfl, rfl,
    ledger_freshLong setup.source.crypto codec serverKid bounds query ledger long a.1 (support_run_fst _ _ _ a ha)⟩

/-- The sends of a message and of its shift, followed by ledger updates related by the shift, are coupled: with equal replies and related states when the handle holds no caller-known kernel (the zeroed sends are the same computation), and as an escape otherwise. -/
theorem send_couple (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (bounds : FreshBounds) (index : ℕ)
    (offsets : ℕ → Fin 256) (handle : Handle) (first second : Pqxdh.Bytes) (length : first.length = second.length)
    (state : NativeState n E) (update₁ update₂ : Option RawCtxSourceSend.Encrypted → Ledger)
    (shift : ∀ r, update₂ r = shiftLedger index offsets (update₁ r)) (long : ∀ r, FreshLong bounds (update₁ r))
    (logged : ∀ r, (∃ entry, (update₁ r).fresh[index]? = some entry ∧ entry.handle = handle) ∧
      ∃ entry, (update₂ r).fresh[index]? = some entry ∧ entry.handle = handle) :
    Swap (SimRel (FreshRelated bounds index offsets) (FreshEscaped index) (FreshEscaped index))
      ((fun p => (p.1, (update₁ p.1, p.2))) <$> (simulateQ (nativeImpl modes zeros setup codec route env)
        (PqxdhDeploymentSecrecy.send handle first)).run state)
      ((fun p => (p.1, (update₂ p.1, p.2))) <$> (simulateQ (nativeImpl modes zeros setup codec route env)
        (PqxdhDeploymentSecrecy.send handle second)).run state) := by
  by_cases known : KnownAt state.1.2 handle
  · have keep : ∀ (message : Pqxdh.Bytes),
        ∀ p ∈ support ((simulateQ (nativeImpl modes zeros setup codec route env)
          (PqxdhDeploymentSecrecy.send handle message)).run state), KnownAt p.2.1.2 handle := fun message =>
      support_keep_oracle (nativeImpl modes zeros setup codec route env) (fun ns => KnownAt ns.1.2 handle)
        (fun q ns hk => nativeImpl_known modes zeros setup codec route env handle q ns hk) _ state known
    refine Swap.escape _ _ fun a ha b hb => Or.inr ⟨?_, ?_⟩
    · rw [support_map] at ha
      obtain ⟨z, hz, rfl⟩ := ha
      obtain ⟨entry, hentry, hhandle⟩ := (logged z.1).1
      exact ⟨entry, hentry, hhandle ▸ keep first z hz⟩
    · rw [support_map] at hb
      obtain ⟨z, hz, rfl⟩ := hb
      obtain ⟨entry, hentry, hhandle⟩ := (logged z.1).2
      exact ⟨entry, hentry, hhandle ▸ keep second z hz⟩
  · rw [← nativeImpl_send_zeros modes setup codec route env handle first second length state known]
    refine (Swap.refl _ (R := Eq) fun _ => rfl).map ?_
    rintro a b rfl
    exact Or.inl ⟨rfl, rfl, shift a.1, long a.1⟩

/-- **Relabelled message coins.** The native coins of a uniform message, the coin of byte `j` relabelled by adding `offsets (start + j)`, couple two continuations that are coupled on a message and its shift. -/
theorem bytes_couple {α β : Type} {R : α → β → Prop} (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (offsets : ℕ → Fin 256) (length : ℕ) :
    ∀ (start : ℕ) (state : NativeState n E) (f : Pqxdh.Bytes × NativeState n E → ProbComp α)
      (g : Pqxdh.Bytes × NativeState n E → ProbComp β),
      (∀ message st, message.length = length → Swap R (f (message, st)) (g (shiftFrom offsets start message, st))) →
      Swap R ((simulateQ (nativeImpl modes replace setup codec route env)
          (PqxdhDeploymentSecrecy.uniformBytes length)).run state >>= f)
        ((simulateQ (nativeImpl modes replace setup codec route env)
          (PqxdhDeploymentSecrecy.uniformBytes length)).run state >>= g) := by
  induction length with
  | zero =>
      intro start state f g next
      simp only [PqxdhDeploymentSecrecy.uniformBytes, simulateQ_pure, StateT.run_pure, pure_bind]
      exact next [] state rfl
  | succ length ih =>
      intro start state f g next
      simp only [PqxdhDeploymentSecrecy.uniformBytes, simulateQ_bind, StateT.run_bind, PqxdhDeploymentSecrecy.coin,
        simulateQ_spec_query, bind_assoc, simulateQ_pure, StateT.run_pure, pure_bind]
      rw [nativeImpl_coin]
      simp only [bind_map_left]
      refine .query_bind 255 (fun r => r + offsets start)
        ⟨add_left_injective _, fun y => ⟨y - offsets start, sub_add_cancel y _⟩⟩ _ _ fun coin => ?_
      refine ih (start + 1) (state.1, coinStep state.2) _ _ fun message st hlength => ?_
      have h := next (UInt8.ofNat coin.val :: message) st (by simp only [List.length_cons, hlength])
      simp only [shiftFrom, shiftByte_coin] at h
      exact h

/-- The admitted fresh query: the native coins of a uniform message, then its send and the ledger update. -/
theorem fullImpl_fresh (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (handle : Handle) (length : ℕ)
    (ledger : Ledger) (state : NativeState n E) (admitted : bounds.min ≤ length ∧ length ≤ bounds.max) :
    (fullImpl modes replace setup codec route env serverKid bounds (.inr (.fresh handle length))).run
        (ledger, state) =
      (simulateQ (nativeImpl modes replace setup codec route env)
          (PqxdhDeploymentSecrecy.uniformBytes length)).run state >>= fun p =>
        (fun q => (q.1, ({ ledger.record (.inr (.fresh handle length)) q.1 with
            fresh := ledger.fresh ++ [⟨handle, p.1, q.1⟩] }, q.2))) <$>
          (simulateQ (nativeImpl modes replace setup codec route env)
            (PqxdhDeploymentSecrecy.send handle p.1)).run p.2 := by
  have step : (PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds
      (.inr (.fresh handle length))).run ledger =
        PqxdhDeploymentSecrecy.uniformBytes length >>= fun message =>
          PqxdhDeploymentSecrecy.send handle message >>= fun reply =>
            pure (reply, { ledger.record (.inr (.fresh handle length)) reply with
              fresh := ledger.fresh ++ [⟨handle, message, reply⟩] }) := by
    simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run, admitted, and_self, ↓reduceIte]
  rw [fullImpl_run, step, simulateQ_bind, StateT.run_bind, map_bind]
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, map_eq_bind_pure_comp,
    Function.comp_apply, pure_bind, bind_assoc]
  rfl

/-- The admitted `index`-th fresh query is coupled with itself, its message coins relabelled by the shift. -/
theorem target_couple (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (offsets : ℕ → Fin 256) (handle : Handle) (length : ℕ) (ledger : Ledger) (state : NativeState n E)
    (admitted : bounds.min ≤ length ∧ length ≤ bounds.max) (long : FreshLong bounds ledger) :
    Swap (SimRel (FreshRelated bounds ledger.fresh.length offsets) (FreshEscaped ledger.fresh.length)
        (FreshEscaped ledger.fresh.length))
      ((fullImpl modes zeros setup codec route env serverKid bounds (.inr (.fresh handle length))).run
        (ledger, state))
      ((fullImpl modes zeros setup codec route env serverKid bounds (.inr (.fresh handle length))).run
        (shiftLedger ledger.fresh.length offsets ledger, state)) := by
  rw [fullImpl_fresh modes zeros setup codec route env serverKid bounds handle length ledger state admitted,
    fullImpl_fresh modes zeros setup codec route env serverKid bounds handle length _ state admitted]
  refine bytes_couple modes zeros setup codec route env offsets length 0 state _ _ fun message st hlength => ?_
  refine send_couple modes setup codec route env bounds ledger.fresh.length offsets handle message
    (shiftFrom offsets 0 message) (shiftFrom_length offsets 0 message).symm st
    (fun r => { ledger.record (.inr (.fresh handle length)) r with fresh := ledger.fresh ++ [⟨handle, message, r⟩] })
    (fun r => { (shiftLedger ledger.fresh.length offsets ledger).record (.inr (.fresh handle length)) r with
      fresh := (shiftLedger ledger.fresh.length offsets ledger).fresh ++ [⟨handle, shiftFrom offsets 0 message, r⟩] })
    (fun r => shiftLedger_target offsets ledger (.inr (.fresh handle length)) r handle message r) (fun r => ?_) (fun r => ⟨?_, ?_⟩)
  · intro entry hentry
    rcases List.mem_append.mp hentry with hentry | hentry
    · exact long entry hentry
    · rw [List.mem_singleton.mp hentry, hlength]
      exact admitted.1
  · exact ⟨_, List.getElem?_concat_length, rfl⟩
  · refine ⟨⟨handle, shiftFrom offsets 0 message, r⟩, ?_, rfl⟩
    simp [shiftLedger]

/-- **One coupled query.** In the zeroed-plaintext world, every adversary query from related states is coupled: with the native coins of the `index`-th admitted fresh message relabelled by the shift, the replies are equal and the states related, or both runs escape. -/
theorem step_couple (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (index : ℕ) (offsets : ℕ → Fin 256) (query : FullSpec.Domain) (s t : Ledger × NativeState n E)
    (related : FreshRelated bounds index offsets s t) :
    Swap (SimRel (FreshRelated bounds index offsets) (FreshEscaped index) (FreshEscaped index))
      ((fullImpl modes zeros setup codec route env serverKid bounds query).run s)
      ((fullImpl modes zeros setup codec route env serverKid bounds query).run t) := by
  obtain ⟨ledger, state⟩ := s
  obtain ⟨ledger', state'⟩ := t
  obtain ⟨hstate, hledger, long⟩ := related
  dsimp only at hstate hledger long
  subst state' ledger'
  rcases query with forwarded | (⟨handle, left, right⟩ | ⟨handle, length⟩)
  · exact commute_couple modes zeros setup codec route env serverKid bounds index offsets _ ledger state long
      (ledger_shift_forward _ codec serverKid bounds index offsets forwarded ledger)
  · exact commute_couple modes zeros setup codec route env serverKid bounds index offsets _ ledger state long
      (ledger_shift_test _ codec serverKid bounds index offsets handle left right ledger)
  · by_cases target : (bounds.min ≤ length ∧ length ≤ bounds.max) ∧ ledger.fresh.length = index
    · obtain ⟨admitted, rfl⟩ := target
      exact target_couple modes setup codec route env serverKid bounds offsets handle length ledger state admitted
        long
    · exact commute_couple modes zeros setup codec route env serverKid bounds index offsets _ ledger state long
        (ledger_shift_fresh _ codec serverKid bounds index offsets handle length ledger target)

/-! ### The final observations -/

/-- The claimed index and the length of the claimed fresh message, when the adversary claims an index that has a fresh message. -/
def freshKey (claim : X → Option (Nat × Pqxdh.Bytes)) (view : View n E X) : Option (ℕ × ℕ) :=
  view.result.bind fun value => (claim value.1).bind fun pair =>
    (value.2.1.fresh[pair.1]?).map fun entry => (pair.1, entry.message.length)

open Classical in
/-- The fresh-message hit with a given claimed index and message length. -/
noncomputable def hitAt (claim : X → Option (Nat × Pqxdh.Bytes)) (index length : ℕ) (view : View n E X) : Bool :=
  decide (FreshHit claim view ∧ freshKey claim view = some (index, length))

open Classical in
/-- The claimed index and message length are the given ones. -/
noncomputable def keyAt (claim : X → Option (Nat × Pqxdh.Bytes)) (index length : ℕ) (view : View n E X) : Bool :=
  decide (freshKey claim view = some (index, length))

open Classical in
/-- The shifted hit: the claimed `index`-th fresh message, of length `length` (at least the minimal length), went to a hidden handle and equals the guess shifted by `offsets`. -/
noncomputable def shiftedHit (bounds : FreshBounds) (claim : X → Option (Nat × Pqxdh.Bytes)) (index length : ℕ)
    (offsets : Fin length → Fin 256) (view : View n E X) : Bool :=
  decide (bounds.min ≤ length ∧ ∃ value ∈ view.result, ∃ guess entry, claim value.1 = some (index, guess) ∧
    value.2.1.fresh[index]? = some entry ∧ (view.slots entry.handle).isSome ∧ entry.message.length = length ∧
    entry.message = shiftFrom (extend offsets) 0 guess)

/-- On related final states, the hit on the left equals the shifted hit on the right. -/
theorem hitAt_shift (bounds : FreshBounds) (claim : X → Option (Nat × Pqxdh.Bytes)) (index length : ℕ)
    (offsets : Fin length → Fin 256) (x : X) (ledger : Ledger) (environment : E)
    (produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame))
    (raw : PqxdhRecordLiftWorld.RawCounters) (slots : Handle → Option (Slot n)) (long : FreshLong bounds ledger) :
    hitAt claim index length (⟨some (x, ledger, environment), produced, raw, slots⟩ : View n E X) =
      shiftedHit bounds claim index length offsets
        ⟨some (x, shiftLedger index (extend offsets) ledger, environment), produced, raw, slots⟩ := by
  unfold hitAt shiftedHit
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨⟨value, hvalue, index', guess, entry, hclaim, hentry, hslot, hmessage⟩, hkey⟩
    simp only [Option.mem_def, Option.some.injEq] at hvalue
    subst hvalue
    simp only [freshKey, Option.bind_some, hclaim, hentry, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at hkey
    obtain ⟨rfl, rfl⟩ := hkey
    refine ⟨long entry (List.mem_of_getElem? hentry), _, rfl, guess, shiftEntry (extend offsets) entry, hclaim,
      ?_, hslot, ?_, ?_⟩
    · simp [shiftLedger, hentry]
    · simp [shiftEntry, shiftFrom_length]
    · simp [shiftEntry, hmessage]
  · rintro ⟨_, value, hvalue, guess, entry, hclaim, hentry, hslot, hlength, hmessage⟩
    simp only [Option.mem_def, Option.some.injEq] at hvalue
    subst hvalue
    simp only [shiftLedger, List.getElem?_modify, ↓reduceIte] at hentry
    cases horiginal : ledger.fresh[index]? with
    | none => simp [horiginal] at hentry
    | some original =>
    simp only [horiginal, Option.map_eq_map, Option.map_some, Option.some.injEq] at hentry
    subst hentry
    have same : original.message = guess := shiftFrom_injective _ _ _ _ hmessage
    refine ⟨⟨_, rfl, index, guess, original, hclaim, horiginal, hslot, same⟩, ?_⟩
    simp only [shiftEntry, shiftFrom_length] at hlength
    simp [freshKey, hclaim, horiginal, hlength]

/-- A caller-known kernel maps to no slot. -/
theorem handleSlot_known (control : PqxdhRecordLiftProtocol.Control n) (handle : Handle)
    (known : KnownAt control handle) : handleSlot control handle = none := by
  cases handle with
  | peer keyId =>
      obtain ⟨server, peer, kernel, hs, hp, hk⟩ := known
      simp [handleSlot, peerSlot, hs, hp, hk, PqxdhRecordLiftWorldCompiler.StoredKernel.origin]
  | owner owner =>
      obtain ⟨shell, kernel, ho⟩ := known
      simp [handleSlot, ownerSlot, ho, PqxdhRecordLiftWorldCompiler.Phase.origin,
        PqxdhRecordLiftWorldCompiler.StoredKernel.origin]

/-- An escaped run has no hit at the escaped index. -/
theorem hitAt_escaped (claim : X → Option (Nat × Pqxdh.Bytes)) (index length : ℕ) (x : X) (ledger : Ledger)
    (state : NativeState n E) (produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame))
    (raw : PqxdhRecordLiftWorld.RawCounters) (escaped : FreshEscaped index (ledger, state)) :
    hitAt claim index length (⟨some (x, ledger, state.1.1), produced, raw, handleSlot state.1.2⟩ : View n E X) =
      false := by
  obtain ⟨known, hknown, hkernel⟩ := escaped
  dsimp only at hknown hkernel
  simp only [hitAt, decide_eq_false_iff_not]
  rintro ⟨⟨value, hvalue, index', guess, entry, hclaim, hentry, hslot, _⟩, hkey⟩
  simp only [Option.mem_def, Option.some.injEq] at hvalue
  subst hvalue
  simp only [freshKey, Option.bind_some, hclaim, hentry, Option.map_some, Option.some.injEq,
    Prod.mk.injEq] at hkey
  obtain ⟨rfl, rfl⟩ := hkey
  dsimp only at hentry hslot
  rw [hentry, Option.some.injEq] at hknown
  subst hknown
  rw [handleSlot_known _ _ hkernel] at hslot
  exact absurd hslot (by simp)

/-- An escaped run has no shifted hit at the escaped index. -/
theorem shiftedHit_escaped (bounds : FreshBounds) (claim : X → Option (Nat × Pqxdh.Bytes)) (index length : ℕ)
    (offsets : Fin length → Fin 256) (x : X) (ledger : Ledger) (state : NativeState n E)
    (produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame))
    (raw : PqxdhRecordLiftWorld.RawCounters) (escaped : FreshEscaped index (ledger, state)) :
    shiftedHit bounds claim index length offsets
      (⟨some (x, ledger, state.1.1), produced, raw, handleSlot state.1.2⟩ : View n E X) = false := by
  obtain ⟨known, hknown, hkernel⟩ := escaped
  dsimp only at hknown hkernel
  simp only [shiftedHit, decide_eq_false_iff_not]
  rintro ⟨_, value, hvalue, guess, entry, _, hentry, hslot, _⟩
  simp only [Option.mem_def, Option.some.injEq] at hvalue
  subst hvalue
  dsimp only at hentry hslot
  rw [hentry, Option.some.injEq] at hknown
  subst hknown
  rw [handleSlot_known _ _ hkernel] at hslot
  exact absurd hslot (by simp)

/-! ### The coupled world -/

/-- **World coupling.** The CTX world with zeroed hidden plaintexts is coupled with itself so that the hit with claimed index `index` and message length `length` on one side equals the hit shifted by `offsets` on the other: the native coins of the `index`-th admitted fresh message are relabelled by the shift, so that message is shifted while every reply and every other state agrees, unless that message went to a caller-known handle, in which case neither side hits. -/
theorem world_couple (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (claim : X → Option (Nat × Pqxdh.Bytes))
    (index length : ℕ) (offsets : Fin length → Fin 256) :
    Swap (fun r₁ r₂ => hitAt claim index length (ctxView r₁) =
        shiftedHit bounds claim index length offsets (ctxView r₂))
      (ctxRun modes zeros setup codec route env serverKid bounds mode adversary)
      (ctxRun modes zeros setup codec route env serverKid bounds mode adversary) := by
  rw [ctxRun_flat]
  refine (Swap.refl (startup modes zeros setup codec route env) (R := Eq) fun _ => rfl).bind fun born _ hborn => ?_
  subst hborn
  rcases born with ⟨⟨_ | ⟨created, initial⟩, control⟩, secret⟩
  · exact .pure _ _ (by simp [ctxView, viewOf, hitAt, shiftedHit, FreshHit])
  · refine (Swap.refl (install modes zeros setup codec route created control secret) (R := Eq) fun _ => rfl).bind
      fun installed _ hinstalled => ?_
    subst hinstalled
    refine (Swap.simulateQ_run (fullImpl modes zeros setup codec route env serverKid bounds)
      (fullImpl modes zeros setup codec route env serverKid bounds) (FreshRelated bounds index (extend offsets))
      (FreshEscaped index) (FreshEscaped index)
      (freshEscaped_keep modes zeros setup codec route env serverKid bounds index)
      (freshEscaped_keep modes zeros setup codec route env serverKid bounds index)
      (step_couple modes setup codec route env serverKid bounds index (extend offsets)) (asModeO mode adversary) _ _
      ⟨rfl, (shiftLedger_empty index (extend offsets)).symm, fun _ h => absurd h List.not_mem_nil⟩).map ?_
    rintro ⟨x₁, ledger₁, state₁⟩ ⟨x₂, ledger₂, state₂⟩ (⟨hx, hstate, hledger, long⟩ | ⟨escaped₁, escaped₂⟩)
    · dsimp only at hx hstate hledger long
      subst x₂ state₂ ledger₂
      exact hitAt_shift bounds claim index length offsets x₁ ledger₁ state₁.1.1 _ _ _ long
    · exact (hitAt_escaped claim index length x₁ ledger₁ state₁ _ _ escaped₁).trans
        (shiftedHit_escaped bounds claim index length offsets x₂ ledger₂ state₂ _ _ escaped₂).symm

/-! ### Averaging over shifts -/

/-- The law of a Boolean observation at `true` is the measure of the set where it holds. -/
theorem evalDist_map_true {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α] (work : ProbComp α)
    (observe : α → Bool) : 𝒟[observe <$> work] {true} = 𝒟[work] {a | observe a = true} := by
  rw [evalDist_map_of_discrete, Measure.map_apply .of_discrete (measurableSet_singleton _)]
  rfl

/-- A shifted hit has the claimed index and message length. -/
theorem shiftedHit_key (bounds : FreshBounds) (claim : X → Option (Nat × Pqxdh.Bytes)) (index length : ℕ)
    (offsets : Fin length → Fin 256) (view : View n E X)
    (hit : shiftedHit bounds claim index length offsets view = true) : keyAt claim index length view = true := by
  simp only [shiftedHit, decide_eq_true_eq] at hit
  obtain ⟨_, value, hvalue, guess, entry, hclaim, hentry, _, hlength, _⟩ := hit
  rw [Option.mem_def] at hvalue
  simp [keyAt, freshKey, hvalue, hclaim, hentry, hlength]

/-- Shifted hits by distinct offsets exclude each other. -/
theorem shiftedHit_disjoint (bounds : FreshBounds) (claim : X → Option (Nat × Pqxdh.Bytes)) (index length : ℕ)
    (first second : Fin length → Fin 256) (view : View n E X)
    (h₁ : shiftedHit bounds claim index length first view = true)
    (h₂ : shiftedHit bounds claim index length second view = true) : first = second := by
  simp only [shiftedHit, decide_eq_true_eq] at h₁ h₂
  obtain ⟨_, value, hvalue, guess, entry, hclaim, hentry, _, hlength, hmessage⟩ := h₁
  obtain ⟨_, value', hvalue', guess', entry', hclaim', hentry', _, _, hmessage'⟩ := h₂
  rw [Option.mem_def] at hvalue hvalue'
  rw [hvalue, Option.some.injEq] at hvalue'
  subst hvalue'
  rw [hclaim, Option.some.injEq, Prod.mk.injEq] at hclaim'
  obtain ⟨_, rfl⟩ := hclaim'
  rw [hentry, Option.some.injEq] at hentry'
  subst hentry'
  have hguess : guess.length = length := by rw [← hlength, hmessage, shiftFrom_length]
  exact extend_offsets guess hguess first second (hmessage.symm.trans hmessage')

/-- **One claimed index and length.** In the CTX world with zeroed hidden plaintexts (any key modes and observation mode), the hit with claimed index `index` and message length `length` has probability at most `256^-min` times the probability of that claim: the hit has the same probability as every one of its `256^length` shifts (`world_couple`), the shifts exclude each other and each implies the claim. -/
theorem hitAt_bound (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (claim : X → Option (Nat × Pqxdh.Bytes))
    (index length : ℕ) :
    𝒟[(fun result => hitAt claim index length (ctxView result)) <$>
        ctxRun modes zeros setup codec route env serverKid bounds mode adversary] {true} ≤
      ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ * 𝒟[(fun result => keyAt claim index length (ctxView result)) <$>
        ctxRun modes zeros setup codec route env serverKid bounds mode adversary] {true} := by
  have same : ∀ offsets : Fin length → Fin 256,
      𝒟[(fun result => hitAt claim index length (ctxView result)) <$>
          ctxRun modes zeros setup codec route env serverKid bounds mode adversary] {true} =
        𝒟[(fun result => shiftedHit bounds claim index length offsets (ctxView result)) <$>
          ctxRun modes zeros setup codec route env serverKid bounds mode adversary] {true} := fun offsets => by
    rw [(world_couple modes setup codec route env serverKid bounds mode adversary claim index length
      offsets).evalDist_map _ _ fun _ _ related => related]
  generalize ctxRun modes zeros setup codec route env serverKid bounds mode adversary = work at same ⊢
  let _ : MeasurableSpace (Client n E X × CtxPrivate n) := ⊤
  have _ : DiscreteMeasurableSpace (Client n E X × CtxPrivate n) := ⟨fun _ => trivial⟩
  by_cases short : length < bounds.min
  · rw [same (fun _ => 0), evalDist_map_true]
    have empty : {result : Client n E X × CtxPrivate n |
        shiftedHit bounds claim index length (fun _ => 0) (ctxView result) = true} = ∅ := by
      ext result
      simp only [shiftedHit, decide_eq_true_eq, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h
      omega
    rw [empty, measure_empty]
    exact zero_le
  · have long : bounds.min ≤ length := Nat.le_of_not_lt short
    have sum : ∑ offsets : Fin length → Fin 256,
        𝒟[(fun result => shiftedHit bounds claim index length offsets (ctxView result)) <$> work] {true} ≤
          𝒟[(fun result => keyAt claim index length (ctxView result)) <$> work] {true} := by
      simp only [evalDist_map_true]
      rw [← measure_biUnion_finset]
      · apply measure_mono
        intro result hresult
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_univ, exists_true_left] at hresult ⊢
        obtain ⟨offsets, hit⟩ := hresult
        exact shiftedHit_key bounds claim index length offsets _ hit
      · intro first _ second _ distinct
        exact Set.disjoint_left.mpr fun result h₁ h₂ =>
          distinct (shiftedHit_disjoint bounds claim index length first second _ h₁ h₂)
      · intro _ _
        exact .of_discrete
    have card : ∑ _offsets : Fin length → Fin 256,
        𝒟[(fun result => hitAt claim index length (ctxView result)) <$> work] {true} =
          ((256 ^ length : ℕ) : ℝ≥0∞) * 𝒟[(fun result => hitAt claim index length (ctxView result)) <$> work] {true} := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
    have scaled : ((256 ^ bounds.min : ℕ) : ℝ≥0∞) *
        𝒟[(fun result => hitAt claim index length (ctxView result)) <$> work] {true} ≤
          𝒟[(fun result => keyAt claim index length (ctxView result)) <$> work] {true} :=
      calc _ ≤ ((256 ^ length : ℕ) : ℝ≥0∞) *
            𝒟[(fun result => hitAt claim index length (ctxView result)) <$> work] {true} := by
            gcongr
        _ = ∑ offsets : Fin length → Fin 256,
            𝒟[(fun result => shiftedHit bounds claim index length offsets (ctxView result)) <$> work] {true} := by
            rw [← card]
            exact Finset.sum_congr rfl fun offsets _ => same offsets
        _ ≤ _ := sum
    exact (ENNReal.mul_le_iff_le_inv (by simp) (ENNReal.natCast_ne_top _)).mp scaled

/-- A fresh-message hit is a hit with some claimed index and message length. -/
theorem freshEvent_cover (claim : X → Option (Nat × Pqxdh.Bytes)) (view : View n E X)
    (hit : freshEvent claim view = true) : ∃ key : ℕ × ℕ, hitAt claim key.1 key.2 view = true := by
  simp only [freshEvent, decide_eq_true_eq] at hit
  obtain ⟨value, hvalue, index, guess, entry, hclaim, hentry, hslot, hmessage⟩ := hit
  refine ⟨(index, entry.message.length), ?_⟩
  simp only [hitAt, decide_eq_true_eq]
  refine ⟨⟨value, hvalue, index, guess, entry, hclaim, hentry, hslot, hmessage⟩, ?_⟩
  rw [Option.mem_def] at hvalue
  simp [freshKey, hvalue, hclaim, hentry]

/-- A view has at most one claimed index and message length. -/
theorem keyAt_unique (claim : X → Option (Nat × Pqxdh.Bytes)) (first second : ℕ × ℕ) (view : View n E X)
    (h₁ : keyAt claim first.1 first.2 view = true) (h₂ : keyAt claim second.1 second.2 view = true) :
    first = second := by
  simp only [keyAt, decide_eq_true_eq] at h₁ h₂
  rw [h₁, Option.some.injEq] at h₂
  simpa only [Prod.mk.eta] using h₂

/-- **Fresh-message guessing with zeroed hidden plaintexts.** In the CTX world with zeroed hidden plaintexts (any key modes and observation mode), the adversary's claim hits a fresh message on a hidden handle with probability at most `2^-min`: summing the per-claim bound over the claimed index and message length, the claims exclude each other, so their probabilities add up to at most one. -/
theorem fresh_zeros (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (claim : X → Option (Nat × Pqxdh.Bytes)) :
    𝒟[(fun result => freshEvent claim (ctxView result)) <$>
        ctxRun modes zeros setup codec route env serverKid bounds mode adversary] {true} ≤
      ((2 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ := by
  have bound := fun key : ℕ × ℕ =>
    hitAt_bound modes setup codec route env serverKid bounds mode adversary claim key.1 key.2
  generalize ctxRun modes zeros setup codec route env serverKid bounds mode adversary = work at bound ⊢
  let _ : MeasurableSpace (Client n E X × CtxPrivate n) := ⊤
  have _ : DiscreteMeasurableSpace (Client n E X × CtxPrivate n) := ⟨fun _ => trivial⟩
  simp only [evalDist_map_true] at bound ⊢
  calc 𝒟[work] {result | freshEvent claim (ctxView result) = true}
      ≤ 𝒟[work] (⋃ key : ℕ × ℕ, {result | hitAt claim key.1 key.2 (ctxView result) = true}) := by
        apply measure_mono
        intro result hresult
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion] at hresult ⊢
        exact freshEvent_cover claim _ hresult
    _ ≤ ∑' key : ℕ × ℕ, 𝒟[work] {result | hitAt claim key.1 key.2 (ctxView result) = true} :=
        measure_iUnion_le _
    _ ≤ ∑' key : ℕ × ℕ, ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ *
          𝒟[work] {result | keyAt claim key.1 key.2 (ctxView result) = true} := ENNReal.tsum_le_tsum bound
    _ = ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ *
          𝒟[work] (⋃ key : ℕ × ℕ, {result | keyAt claim key.1 key.2 (ctxView result) = true}) := by
        rw [ENNReal.tsum_mul_left, ← measure_iUnion]
        · intro first second distinct
          exact Set.disjoint_left.mpr fun result h₁ h₂ => distinct (keyAt_unique claim first second _ h₁ h₂)
        · intro _
          exact .of_discrete
    _ ≤ ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ * 1 := by
        gcongr
        exact (measure_mono (Set.subset_univ _)).trans (evalDist_apply_univ_le_one work)
    _ ≤ ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ := by
        rw [mul_one]
        exact ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (Nat.pow_le_pow_left (by norm_num) _))

/-! ### Transfer to the record-ideal world -/

/-- A fresh-message hit depends on a view only through its hiding projection. -/
theorem freshHit_hiding (claim : X → Option (Nat × Pqxdh.Bytes)) (first second : View n E X)
    (same : hidingView first = hidingView second) (hit : FreshHit claim first) : FreshHit claim second := by
  obtain ⟨value, hvalue, index, guess, entry, hclaim, hentry, hslot, hmessage⟩ := hit
  simp only [hidingView, Prod.mk.injEq] at same
  obtain ⟨results, _, _, slots⟩ := same
  rw [Option.mem_def] at hvalue
  rw [hvalue, Option.map_some] at results
  obtain ⟨value', hvalue', hmap⟩ := Option.map_eq_some_iff.mp results.symm
  simp only [Prod.mk.injEq] at hmap
  obtain ⟨outputs, _, _, freshes, _⟩ := hmap
  refine ⟨value', hvalue', index, guess, entry, ?_, ?_, ?_, hmessage⟩
  · rw [outputs]
    exact hclaim
  · rw [freshes]
    exact hentry
  · rw [← slots]
    exact hslot

/-- The fresh-message event depends on a view only through its hiding projection. -/
theorem freshEvent_hiding (claim : X → Option (Nat × Pqxdh.Bytes)) (first second : View n E X)
    (same : hidingView first = hidingView second) : freshEvent claim first = freshEvent claim second := by
  unfold freshEvent
  rw [propext ⟨freshHit_hiding claim first second same, freshHit_hiding claim second first same.symm⟩]

/-- **`FreshGuessStatement` (H-5 `idealRecords_hiding`, fresh-message form for CE-APP), delivered.** In mode P, for every environment, adversary and claim read from the adversary's output, the probability in `idealRecords` that the claimed fresh message was sent on a hidden handle and equals the guess is at most `2^-min`. No contract. -/
theorem idealRecords_fresh (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Std.U64) (bounds : FreshBounds) (n : Nat) :
    FreshGuessStatement setup codec route serverKid bounds n := by
  intro E X env adversary claim
  rw [PqxdhRecordLiftLor.law_zeros setup codec route env serverKid bounds adversary _ (freshEvent_hiding claim)]
  exact fresh_zeros (fun _ => .random) setup codec route env serverKid bounds .P adversary claim

end BeaconcryptCore.Computational.PqxdhRecordLiftFresh

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.shiftByte_coin' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.shiftByte_coin

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.shiftByte_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.shiftByte_injective

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.shiftByte_offset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.shiftByte_offset

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.shiftFrom_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.shiftFrom_length

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.shiftFrom_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.shiftFrom_injective

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.shiftFrom_offsets' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.shiftFrom_offsets

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.extend_offsets' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.extend_offsets

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.shiftLedger_empty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.shiftLedger_empty

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.modify_append_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.modify_append_ne

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.modify_append_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.modify_append_length

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.shiftLedger_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.shiftLedger_append

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.shiftLedger_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.shiftLedger_target

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.ledger_shift_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.ledger_shift_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.ledger_shift_test' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.ledger_shift_test

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.ledger_shift_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.ledger_shift_fresh

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.uniformBytes_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.uniformBytes_length

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.ledger_freshLong' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.ledger_freshLong

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.ledger_fresh_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.ledger_fresh_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.freshEscaped_keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.freshEscaped_keep

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.commute_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.commute_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.send_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.send_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.bytes_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.bytes_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.fullImpl_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.fullImpl_fresh

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.target_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.target_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.step_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.step_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.hitAt_shift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.hitAt_shift

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.handleSlot_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.handleSlot_known

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.hitAt_escaped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.hitAt_escaped

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.shiftedHit_escaped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.shiftedHit_escaped

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.world_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.world_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.evalDist_map_true' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.evalDist_map_true

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.shiftedHit_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.shiftedHit_key

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.shiftedHit_disjoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.shiftedHit_disjoint

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.hitAt_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.hitAt_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.freshEvent_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.freshEvent_cover

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.keyAt_unique' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.keyAt_unique

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.fresh_zeros' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.fresh_zeros

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.freshHit_hiding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.freshHit_hiding

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.freshEvent_hiding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.freshEvent_hiding

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFresh.idealRecords_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFresh.idealRecords_fresh
