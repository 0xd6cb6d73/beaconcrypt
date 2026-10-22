-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AuthenticationExtraction.Funs
import BeaconcryptCore.Refinement.PqxdhEncoding
import BeaconcryptCore.Model.Pqxdh.TranscriptAuth

/-!
The runtime authentication constants, role-separated signing input, and associated-data overwrite refine the deterministic byte model through the current isolated Hax extraction.
These theorems establish byte construction only; hashing, ML-DSA security, codec parsing, and the adapter's native primitive calls remain outside this refinement.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM PqxdhRefinement beaconcrypt_authentication_core Pqxdh

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace TranscriptAuthInputsRefinement

/-- The extracted request domain matches the model's deployed literal bytes. -/
theorem init_domain_abs : absBytes authentication.INIT_DOMAIN = TranscriptAuth.initDomain := by
  simp [absBytes, authentication.INIT_DOMAIN, TranscriptAuth.initDomain, absByte, Std.Array.make]

/-- The extracted response domain matches the model's deployed literal bytes. -/
theorem response_domain_abs : absBytes authentication.RESPONSE_DOMAIN = TranscriptAuth.responseDomain := by
  simp [absBytes, authentication.RESPONSE_DOMAIN, TranscriptAuth.responseDomain, absByte, Std.Array.make]

/-- The extracted ML-DSA context matches the model's deployed literal bytes. -/
theorem signing_context_abs : absBytes authentication.SIGNING_CONTEXT = TranscriptAuth.signingContext := by
  simp [absBytes, authentication.SIGNING_CONTEXT, TranscriptAuth.signingContext, absByte, Std.Array.make]

/-- The extracted beacon label matches the corresponding model role. -/
theorem beacon_label_abs : absBytes authentication.BEACON_LABEL = TranscriptAuth.roleLabel .beacon := by
  simp [absBytes, authentication.BEACON_LABEL, TranscriptAuth.roleLabel, absByte, Std.Array.make]

/-- The extracted server label matches the corresponding model role. -/
theorem server_label_abs : absBytes authentication.SERVER_LABEL = TranscriptAuth.roleLabel .server := by
  simp [absBytes, authentication.SERVER_LABEL, TranscriptAuth.roleLabel, absByte, Std.Array.make]

private theorem index_sub_eq {Output : Type} {n : Std.Usize} (bytes : Std.Array Std.U8 n)
    (index offset : Std.Usize) (lower : offset.val ≤ index.val)
    (upper : index.val - offset.val < n.val) (fits : index.val < 2 ^ 32)
    (next : Std.U8 → RustM Output) :
    (do let adjusted ← index - offset; let byte ← Std.Array.index_usize bytes adjusted; next byte) =
      next bytes.val[index.val - offset.val]! := by
  rw [usize_sub_eq index offset lower]
  simp only [bind_tc_ok]
  have value := usize_mk_val (index.val - offset.val) (by omega)
  rw [index_usize_eq bytes _ (by omega), value]
  simp only [bind_tc_ok]

private theorem from_fn_list {Closure : Type} (size : Std.Usize)
    (inst : core.ops.function.FnMut Closure Std.Usize Std.U8) (closure : Closure)
    (bytes : List Std.U8) (width : bytes.length = size.val)
    (each : ∀ index, index < size.val →
      inst.call_mut closure ⟨BitVec.ofNat _ index⟩ = ok (bytes[index]!, closure)) :
    ∃ output, core.array.from_fn size inst closure = ok output ∧ output.val = bytes := by
  simpa only [← width, map_range_getElem!] using
    from_fn_pure size inst closure (fun index => bytes[index]!) each

private theorem getByte_append (left right : List Std.U8) (index : Nat) :
    (left ++ right)[index]! =
      if index < left.length then left[index]! else right[index - left.length]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append]
  split_ifs <;> rfl

private theorem ad_closure_list (base : Std.Array Std.U8 281#usize)
    (server beacon : Std.Array Std.U8 64#usize) (index : Nat) (bound : index < 281) :
    let closure : authentication.bind_associated_data.closure := (base, server, beacon)
    authentication.bind_associated_data.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
        closure ⟨BitVec.ofNat _ index⟩ =
      ok ((base.val.take 153 ++ server.val ++ beacon.val)[index]!, closure) := by
  have value := usize_mk_val index (by omega)
  simp only [authentication.bind_associated_data.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut,
    Std.UScalar.lt_equiv, value, getByte_append, List.length_append, Std.Array.length_eq, List.length_take]
  dsimp! only [authentication.bind_associated_data.closure]
  norm_num only [Std.UScalar.ofNatCore_val_eq]
  rcases (show index < 153 ∨ (153 ≤ index ∧ index < 217) ∨ 217 ≤ index by omega) with
    region | region | region
  all_goals repeat' first | rw [ite_eq_left (by omega)] | rw [ite_eq_right (by omega)]
  all_goals try erw [index_sub_eq]
  all_goals dsimp only [Std.UScalarTy.numBits] at value
  all_goals norm_num only [value, Std.UScalar.ofNatCore_val_eq]
  all_goals try omega
  all_goals try rfl
  erw [index_usize_eq]
  all_goals simp only [bind_tc_ok, value, Std.UScalar.ofNatCore_val_eq]
  all_goals first | omega | simp only [List.getElem!_eq_getElem?_getD, List.getElem?_take_of_lt region]

/-- The runtime AD builder preserves the classical prefix and fills both fingerprint slots. -/
theorem bind_associated_data_abs (base : Std.Array Std.U8 281#usize)
    (server beacon : Std.Array Std.U8 64#usize) :
    ∃ output, authentication.bind_associated_data base server beacon = ok output ∧
      absBytes output = TranscriptAuth.fillAssociatedData (absBytes base)
        (absBytes server) (absBytes beacon) := by
  unfold authentication.bind_associated_data
  obtain ⟨output, run, bytes⟩ := from_fn_list 281#usize
    authentication.bind_associated_data.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
    (base, server, beacon) (base.val.take 153 ++ server.val ++ beacon.val)
    (by simp [Std.Array.length_eq]) (fun index bound => ad_closure_list base server beacon index bound)
  refine ⟨output, run, ?_⟩
  simp only [absBytes, bytes, List.map_append, List.map_take,
    TranscriptAuth.fillAssociatedData, TranscriptAuth.associatedData]

def absRole : authentication.AuthRole → TranscriptAuth.Role
  | .Beacon => .beacon
  | .Server => .server

private theorem signature_closure_list (label : Std.Array Std.U8 34#usize)
    (digest : Std.Array Std.U8 64#usize) (index : Nat) (bound : index < 163) :
    let closure : authentication.build_signature_input.closure := (label, digest)
    authentication.build_signature_input.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
        closure ⟨BitVec.ofNat _ index⟩ =
      ok ((List.replicate 64 (32#u8) ++ label.val ++ [0#u8] ++ digest.val)[index]!, closure) := by
  have value := usize_mk_val index (by omega)
  have eq_iff (left right : Std.Usize) : left = right ↔ left.val = right.val :=
    ⟨Std.UScalar.val_eq_of_eq, Std.UScalar.eq_of_val_eq⟩
  simp only [authentication.build_signature_input.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut,
    Std.UScalar.lt_equiv, eq_iff, value, getByte_append, List.length_append, Std.Array.length_eq,
    List.length_replicate, List.length_cons, List.length_nil]
  dsimp! only [authentication.build_signature_input.closure]
  norm_num only [Std.UScalar.ofNatCore_val_eq]
  rcases (show index < 64 ∨ (64 ≤ index ∧ index < 98) ∨ index = 98 ∨ 99 ≤ index by omega) with
    region | region | region | region
  all_goals repeat' first | rw [ite_eq_left (by omega)] | rw [ite_eq_right (by omega)]
  all_goals try erw [index_sub_eq]
  all_goals dsimp only [Std.UScalarTy.numBits] at value
  all_goals norm_num only [value, Std.UScalar.ofNatCore_val_eq, region]
  all_goals try omega
  all_goals try rfl
  change ok (32#u8, label, digest) = ok ((List.replicate 64 (32#u8))[index]!, label, digest)
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_replicate_of_lt region, Option.getD_some]

/-- The runtime signing-input builder emits the exact role-separated model message. -/
theorem build_signature_input_abs (role : authentication.AuthRole)
    (digest : Std.Array Std.U8 64#usize) :
    ∃ output, authentication.build_signature_input role digest = ok output ∧
      absBytes output = TranscriptAuth.signatureInput (absRole role) (absBytes digest) := by
  let label : Std.Array Std.U8 34#usize := match role with
    | .Beacon => authentication.BEACON_LABEL
    | .Server => authentication.SERVER_LABEL
  obtain ⟨output, run, bytes⟩ := from_fn_list 163#usize
    authentication.build_signature_input.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
    (label, digest) (List.replicate 64 (32#u8) ++ label.val ++ [0#u8] ++ digest.val)
    (by simp [Std.Array.length_eq]) (fun index bound => signature_closure_list label digest index bound)
  refine ⟨output, ?_, ?_⟩
  · cases role <;> simpa only [authentication.build_signature_input, label, bind_tc_ok] using run
  · cases role <;> simp [absBytes, bytes, label, absRole, TranscriptAuth.signatureInput,
      ← beacon_label_abs, ← server_label_abs, absByte]

end TranscriptAuthInputsRefinement

/-- info: 'TranscriptAuthInputsRefinement.init_domain_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TranscriptAuthInputsRefinement.init_domain_abs
/-- info: 'TranscriptAuthInputsRefinement.response_domain_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TranscriptAuthInputsRefinement.response_domain_abs
/-- info: 'TranscriptAuthInputsRefinement.signing_context_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TranscriptAuthInputsRefinement.signing_context_abs
/-- info: 'TranscriptAuthInputsRefinement.beacon_label_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TranscriptAuthInputsRefinement.beacon_label_abs
/-- info: 'TranscriptAuthInputsRefinement.server_label_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TranscriptAuthInputsRefinement.server_label_abs
/-- info: 'TranscriptAuthInputsRefinement.build_signature_input_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TranscriptAuthInputsRefinement.build_signature_input_abs
/-- info: 'TranscriptAuthInputsRefinement.bind_associated_data_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TranscriptAuthInputsRefinement.bind_associated_data_abs
