import BeaconcryptCore.Refinement.RatchetInterpreter

/-! Direct byte-layout and scalar arithmetic counterparts of the raw F* ratchet helpers. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
open ratchet.concrete

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BeaconcryptCore.Refinement.RatchetByteSurface

theorem symmetric_ratchet_kdf_request_is_exact (input : Std.Array Std.U8 32#usize) :
    ratchet.SymmetricRatchetKdfRequest.new input = ok { input, info := ratchet.SYM_RATCHET_INFO } := rfl

theorem ratchet_chain_bytes_extensionality (left right : ratchet.RatchetChain)
    (h : left.bytes = right.bytes) : left = right := by
  cases left; cases right; simp_all

theorem u64_value_extensionality (left right : Std.U64) (h : left.val = right.val) : left = right :=
  Std.UScalar.eq_of_val_eq h

theorem u8_value_extensionality (left right : Std.U8) (h : left.val = right.val) : left = right :=
  Std.UScalar.eq_of_val_eq h

theorem positive_at_most_one_is_one (n : Nat) (hpos : 0 < n) (hle : n ≤ 1) : n = 1 := by omega

theorem u64_below_max_is_not_max (n : Std.U64) (h : n.val < core.num.U64.MAX.val) : n ≠ core.num.U64.MAX := by
  intro heq
  simp [heq] at h

theorem u64_successor_value (n : Std.U64) (h : n.val < core.num.U64.MAX.val) :
    ∃ next, n + 1#u64 = ok next ∧ next.val = n.val + 1 := by
  simpa using ratchet.control.uscalar_add_eq_ok n 1#u64 (by
    simpa [core.num.U64.MAX, Std.U64.rMax, Std.UScalar.max_def] using Nat.succ_le_of_lt h)

theorem u64_value_is_bounded (n : Std.U64) : n.val ≤ core.num.U64.MAX.val := by
  simpa [core.num.U64.MAX, Std.U64.rMax] using Nat.le_pred_of_lt n.bv.isLt

/-- Every byte of the exact production splitter has the historical F* offset and fixed field length. -/
theorem ratchet_kdf_output_split_is_exact (output : Std.Array Std.U8 76#usize) :
    ∃ result, ratchet.split_ratchet_kdf_output output = ok result ∧
      result.key.bytes.val.length = 32 ∧ result.next_chain.bytes.val.length = 32 ∧ result.nonce.bytes.val.length = 12 ∧
      (∀ i : Nat, i < 32 → result.key.bytes.val[i]! = output.val[i]!) ∧
      (∀ i : Nat, i < 32 → result.next_chain.bytes.val[i]! = output.val[i + 32]!) ∧
      (∀ i : Nat, i < 12 → result.nonce.bytes.val[i]! = output.val[i + 64]!) :=
  (PanicFreedom.split_ratchet_kdf_output_exact output).elim fun result hr =>
    ⟨result, hr.1, by simp, by simp, by simp,
      fun i hi => by simp [hr.2.1, List.getElem!_eq_getElem?_getD, hi],
      fun i hi => by simp [hr.2.2.1, List.getElem!_eq_getElem?_getD, hi],
      fun i hi => by simp [hr.2.2.2, List.getElem!_eq_getElem?_getD, hi]⟩

/-- A fixed executor receives the exact old chain and label, and the production decoder returns every key, chain, and nonce byte at its fixed offset. -/
theorem ratchet_step_uses_exact_chain_and_partition (oldChain : ratchet.RatchetChain)
    (execute : KdfInterpreter) :
    ratchet.SymmetricRatchetKdfRequest.new oldChain.bytes =
      ok { input := oldChain.bytes, info := ratchet.SYM_RATCHET_INFO } ∧
    ratchet_step_from_response (execute { input := oldChain.bytes, info := ratchet.SYM_RATCHET_INFO }) =
      ok (interpretedStep execute oldChain) ∧
    (∀ i : Nat, i < 32 → (interpretedStep execute oldChain).material.key.bytes.val[i]! =
      (interpretedResponse execute oldChain).bytes.val[i]!) ∧
    (∀ i : Nat, i < 32 → (interpretedStep execute oldChain).chain.bytes.val[i]! =
      (interpretedResponse execute oldChain).bytes.val[i + 32]!) ∧
    (∀ i : Nat, i < 12 → (interpretedStep execute oldChain).material.nonce.bytes.val[i]! =
      (interpretedResponse execute oldChain).bytes.val[i + 64]!) := by
  obtain ⟨split, hsplit, _, _, _, hkey, hchain, hnonce⟩ :=
    ratchet_kdf_output_split_is_exact (interpretedResponse execute oldChain).bytes
  have hdecode : ratchet_step_from_response (interpretedResponse execute oldChain) =
      ok { chain := split.next_chain, material := { key := split.key, nonce := split.nonce } } := by
    simp [ratchet_step_from_response, ratchet.RatchetKdfResponse.as_bytes, hsplit]
  have hchosen := RustM.ok.inj ((interpretedStep_spec execute oldChain).symm.trans hdecode)
  exact ⟨rfl, interpretedStep_spec execute oldChain, by simpa only [hchosen] using hkey,
    by simpa only [hchosen] using hchain, by simpa only [hchosen] using hnonce⟩

end BeaconcryptCore.Refinement.RatchetByteSurface
