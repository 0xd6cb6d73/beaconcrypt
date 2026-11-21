import BeaconcryptCore.Computational.CtxNonceAeadIndDollar
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Constructive bounded validation nonce search

The reduction encodes at most one more counter than the used-list length into twelve nonce bytes and scans for a value absent from that list. Correctness follows from exact decoding and the pigeonhole argument. This is protocol-reduction bookkeeping, not an implementation or security proof for any primitive.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CtxConstructiveNonce
open CtxRomAuth

/-- Explicit little-endian encoding of an index into exactly twelve nonce bytes. -/
def nonceOfIndex (index : Fin (256 ^ 12)) : CtxNonce :=
  let digits := Nat.digits 256 index.val
  ⟨(digits ++ List.replicate (12 - digits.length) 0).map UInt8.ofNat, by
    have bounded : digits.length ≤ 12 := (Nat.digits_length_le_iff (by decide : 1 < 256) index.val).mpr index.isLt
    simp only [List.length_map, List.length_append, List.length_replicate]
    omega⟩

/-- The explicit nonce byte encoding recovers its finite index. -/
theorem nonceOfIndex_decode (index : Fin (256 ^ 12)) :
    Nat.ofDigits 256 ((nonceOfIndex index).toList.map UInt8.toNat) = index.val := by
  have bounded : ∀ digit ∈ Nat.digits 256 index.val ++ List.replicate (12 - (Nat.digits 256 index.val).length) 0,
      digit < 256 := by
    intro digit member
    simp only [List.mem_append, List.mem_replicate] at member
    rcases member with digits | ⟨_, rfl⟩
    · exact Nat.digits_lt_base (by decide) digits
    · decide
  have mapped : ((Nat.digits 256 index.val ++ List.replicate (12 - (Nat.digits 256 index.val).length) 0).map UInt8.ofNat).map UInt8.toNat =
      Nat.digits 256 index.val ++ List.replicate (12 - (Nat.digits 256 index.val).length) 0 := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id' (Nat.digits 256 index.val ++ List.replicate (12 - (Nat.digits 256 index.val).length) 0)]
    apply List.map_congr_left
    intro digit member
    exact Nat.mod_eq_of_lt (bounded digit member)
  change Nat.ofDigits 256 (((Nat.digits 256 index.val ++ List.replicate (12 - (Nat.digits 256 index.val).length) 0).map UInt8.ofNat).map UInt8.toNat) = _
  rw [mapped, Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]

/-- Different bounded counters produce different exact nonce bytes. -/
theorem nonceOfIndex_injective : Function.Injective nonceOfIndex := by
  intro left right equal
  apply Fin.ext
  have decoded := congrArg (fun nonce => Nat.ofDigits 256 (nonce.toList.map UInt8.toNat)) equal
  simpa only [nonceOfIndex_decode] using decoded

/-- Construct only count+1 candidates, never enumerate the nonce universe. -/
def candidates (count : ℕ) (bounded : count < 256 ^ 12) : List CtxNonce :=
  List.ofFn fun index : Fin (count + 1) =>
    nonceOfIndex ⟨index.val, lt_of_lt_of_le index.isLt (Nat.succ_le_of_lt bounded)⟩

@[simp] theorem candidates_length (count : ℕ) (bounded : count < 256 ^ 12) :
    (candidates count bounded).length = count + 1 := by simp [candidates]

/-- The bounded scan has count+1 distinct choices. -/
theorem candidates_nodup (count : ℕ) (bounded : count < 256 ^ 12) :
    (candidates count bounded).Nodup := by
  apply List.nodup_ofFn_ofInjective
  intro left right equal
  apply Fin.ext
  exact congrArg (fun index : Fin (256 ^ 12) => index.val) (nonceOfIndex_injective equal)

/-- A count+1 candidate scan contains a fresh value for any used list of length count, even if that list has duplicates. -/
theorem candidates_have_fresh (used : List CtxNonce) (bounded : used.length < 256 ^ 12) :
    ∃ nonce ∈ candidates used.length bounded, nonce ∉ used := by
  by_contra absent
  have subset : candidates used.length bounded ⊆ used := by
    intro nonce member
    by_contra fresh
    exact absent ⟨nonce, member, fresh⟩
  have length := (List.subperm_of_subset (candidates_nodup used.length bounded) subset).length_le
  rw [candidates_length] at length
  omega

/-- A bounded executable scan chooses the first unused nonce from length(used)+1 explicit byte encodings. -/
def chooseNonce (used : List CtxNonce) : CtxNonce :=
  if bounded : used.length < 256 ^ 12 then
    ((candidates used.length bounded).find? fun nonce => decide (nonce ∉ used)).getD
      (nonceOfIndex ⟨0, by decide⟩)
  else nonceOfIndex ⟨0, by decide⟩

/-- The fallback is unreachable under the actual strict nonce-space budget. -/
theorem chooseNonce_not_mem (used : List CtxNonce) (bounded : used.length < 256 ^ 12) :
    chooseNonce used ∉ used := by
  unfold chooseNonce
  simp only [bounded, dite_eq_left]
  cases found : (candidates used.length bounded).find? (fun nonce => decide (nonce ∉ used)) with
  | none =>
    have noneFound := List.find?_eq_none.mp found
    obtain ⟨nonce, member, fresh⟩ := candidates_have_fresh used bounded
    have contradiction := noneFound nonce member
    simp [fresh] at contradiction
  | some nonce =>
    have fresh := List.find?_some found
    simpa using fresh

/-- The source sealing cap bounds the constructed scan by qSeal+1 explicit candidates. -/
theorem candidates_length_le_of_seal_bound (used : List CtxNonce) (bound : used.length < 256 ^ 12)
    (qSeal : ℕ) (sealed : used.length ≤ qSeal) :
    (candidates used.length bound).length ≤ qSeal + 1 := by
  rw [candidates_length]
  omega

/-- Freshness uses the exact 96-bit nonce-space condition of the conventional reduction. -/
theorem chooseNonce_not_mem_of_seal_bound (used : List CtxNonce) (qSeal : ℕ)
    (sealed : used.length ≤ qSeal) (space : qSeal < 2 ^ 96) : chooseNonce used ∉ used := by
  apply chooseNonce_not_mem
  have equality : (256 : ℕ) ^ 12 = 2 ^ 96 := by norm_num
  rw [equality]
  exact lt_of_le_of_lt sealed space

/-- The deterministic bounded scan consumes no primitive or random-oracle query. Its local byte/list work is still real computation. -/
theorem chooseNonce_no_queries (used : List CtxNonce) :
    (pure (chooseNonce used) : ProbComp CtxNonce).IsTotalQueryBound 0 := by trivial

end BeaconcryptCore.Computational.CtxConstructiveNonce

/--
info: 'BeaconcryptCore.Computational.CtxConstructiveNonce.nonceOfIndex_decode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CtxConstructiveNonce.nonceOfIndex_decode

/--
info: 'BeaconcryptCore.Computational.CtxConstructiveNonce.candidates_nodup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CtxConstructiveNonce.candidates_nodup

/--
info: 'BeaconcryptCore.Computational.CtxConstructiveNonce.chooseNonce_not_mem_of_seal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CtxConstructiveNonce.chooseNonce_not_mem_of_seal_bound

/--
info: 'BeaconcryptCore.Computational.CtxConstructiveNonce.chooseNonce_no_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CtxConstructiveNonce.chooseNonce_no_queries
