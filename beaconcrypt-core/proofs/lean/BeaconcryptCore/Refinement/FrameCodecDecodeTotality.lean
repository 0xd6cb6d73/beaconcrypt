-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.FrameCodecTotality
import BeaconcryptCore.Refinement.FrameCodecRoundtrip

/-! The complete extracted frame decoder returns an ordinary optional frame for every byte slice. All header accesses and successive canonical-argument suffixes are within the actual input; malformed encodings retain their rejection branches. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_parse
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.FrameCodecDecodeTotality
open FrameCodecTotality FrameCodecRoundtrip

private theorem slice_index_exact (input : Slice U8) (index : Usize)
    (bound : index.val < input.val.length) :
    Slice.index_usize input index = ok input.val[index.val]! := by
  unfold Slice.index_usize
  rw [Slice.getElem?_Usize_eq, List.getElem?_eq_getElem bound,
    getElem!_pos input.val index.val bound]

/-- Every complete input, including a malformed or truncated frame, returns normally from the actual extracted decoder. -/
theorem decode_total (input : Slice U8) : ∃ reply, frame.decode input = ok reply := by
  by_cases large : 33554432 < input.val.length
  · exact ⟨.None, decode_oversize input large⟩
  · by_cases short : input.val.length < 3
    · exact ⟨.None, decode_short input short⟩
    · have notLarge : ¬ input.len > (33554432#usize) := by
        simp only [UScalar.lt_equiv, Slice.len_val, Slice.length, UScalar.ofNatCore_val_eq]
        omega
      have notShort : ¬ input.len < (3#usize) := by
        simp only [UScalar.lt_equiv, Slice.len_val, Slice.length, UScalar.ofNatCore_val_eq]
        omega
      simp only [frame.decode, core.slice.Slice.len, rust_primitives.slice.slice_length,
        beaconcrypt_parse.beaconcrypt_core.transport.MAX_MESSAGE_SIZE,
        _root_.beaconcrypt_core.transport.MAX_MESSAGE_SIZE, bind_tc_ok,
        notLarge, notShort, ite_false]
      rw [slice_index_exact input 0#usize (by norm_num; omega)]
      simp only [bind_tc_ok]
      split
      · exact ⟨.None, rfl⟩
      · rw [slice_index_exact input 1#usize (by norm_num; omega)]
        simp only [bind_tc_ok]
        split
        · exact ⟨.None, rfl⟩
        · rw [slice_index_exact input 2#usize (by norm_num; omega)]
          simp only [bind_tc_ok]
          split
          · exact ⟨.None, rfl⟩
          · rw [suffix_exact input 3#usize (by norm_num; omega)]
            simp only [bind_tc_ok, show (3#usize).val = 3 from rfl]
            obtain ⟨first, firstRead, firstBound⟩ := decode_argument_total (suffix input 3) 0#u8
            rw [firstRead]
            cases first with
            | none =>
                simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                  core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
                  core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
                  bind_tc_ok]
                exact ⟨.None, rfl⟩
            | some first =>
                rcases first with ⟨sequence, usedFirst⟩
                simp! only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                  core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, bind_tc_ok]
                rw [suffix_exact (suffix input 3) usedFirst firstBound.2]
                simp only [bind_tc_ok]
                obtain ⟨second, secondRead, secondBound⟩ :=
                  decode_argument_total (suffix (suffix input 3) usedFirst.val) 0#u8
                rw [secondRead]
                cases second with
                | none =>
                    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
                      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
                      bind_tc_ok]
                    exact ⟨.None, rfl⟩
                | some second =>
                    rcases second with ⟨sender, usedSecond⟩
                    simp! only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, bind_tc_ok]
                    rw [suffix_exact _ usedSecond secondBound.2]
                    simp only [bind_tc_ok]
                    obtain ⟨third, thirdRead, thirdBound⟩ :=
                      decode_argument_total (suffix (suffix (suffix input 3) usedFirst.val) usedSecond.val) 2#u8
                    rw [thirdRead]
                    cases third with
                    | none =>
                        simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                          core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
                          core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
                          bind_tc_ok]
                        exact ⟨.None, rfl⟩
                    | some third =>
                        rcases third with ⟨length, usedThird⟩
                        simp! only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                          core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, bind_tc_ok]
                        rw [suffix_exact _ usedThird thirdBound.2]
                        simp only [bind_tc_ok, lift]
                        split
                        · exact ⟨.None, rfl⟩
                        · exact ⟨.Some ⟨sequence, sender, _⟩, rfl⟩

end BeaconcryptCore.Refinement.FrameCodecDecodeTotality

/-- info: 'BeaconcryptCore.Refinement.FrameCodecDecodeTotality.decode_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecDecodeTotality.decode_total
