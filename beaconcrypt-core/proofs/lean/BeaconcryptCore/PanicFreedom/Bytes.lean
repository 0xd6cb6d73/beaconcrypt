import BeaconcryptCore.Refinement.PqxdhCore

/-! Totality and exact byte partitions for the extracted fixed-size KDF operations. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BeaconcryptCore.PanicFreedom

private theorem ratchet_nonce_byte (output : Std.Array Std.U8 76#usize) (i : Std.Usize)
    (hi : i.val < 12) :
    ratchet.split_ratchet_kdf_output.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
      output i = ok (output.val[i.val + 64]!, output) := by
  obtain ⟨j, hj, hjv⟩ := usize_add_val i 32#usize (lt_numBits _ (by simp; omega))
  obtain ⟨k, hk, hkv⟩ := usize_add_val j 32#usize (lt_numBits _ (by simp at hjv ⊢; omega))
  simp [ratchet.split_ratchet_kdf_output.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut,
    commitment.AEAD_KEY_SIZE, ratchet.RATCHET_CHAIN_SIZE, hj, hk,
    index_usize_eq output k (by simp at hjv hkv ⊢; omega), hjv, hkv, Nat.add_assoc]

private theorem ratchet_chain_byte (output : Std.Array Std.U8 76#usize) (i : Std.Usize)
    (hi : i.val < 32) :
    ratchet.split_ratchet_kdf_output.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
      output i = ok (output.val[i.val + 32]!, output) := by
  obtain ⟨j, hj, hjv⟩ := usize_add_val i 32#usize (lt_numBits _ (by simp; omega))
  simp [ratchet.split_ratchet_kdf_output.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut,
    commitment.AEAD_KEY_SIZE, hj, index_usize_eq output j (by simp at hjv ⊢; omega), hjv]

/-- Every 76-byte response splits normally, with the exact key, chain, and nonce byte regions. -/
theorem split_ratchet_kdf_output_exact (output : Std.Array Std.U8 76#usize) :
    ∃ result, ratchet.split_ratchet_kdf_output output = ok result ∧
      result.key.bytes.val = (List.range 32).map (fun i => output.val[i]!) ∧
      result.next_chain.bytes.val = (List.range 32).map (fun i => output.val[i + 32]!) ∧
      result.nonce.bytes.val = (List.range 12).map (fun i => output.val[i + 64]!) := by
  obtain ⟨key, hkey, hkeyBytes⟩ := from_fn_pure 32#usize
    ratchet.split_ratchet_kdf_output.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8 output
    (fun i => output.val[i]!) (fun i hi => by
      have hv := usize_mk_val i (by scalar_tac)
      simp only [ratchet.split_ratchet_kdf_output.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut,
        index_usize_eq output ⟨BitVec.ofNat _ i⟩ (by scalar_tac), hv, bind_tc_ok])
  obtain ⟨chain, hchain, hchainBytes⟩ := from_fn_pure 32#usize
    ratchet.split_ratchet_kdf_output.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU8 output
    (fun i => output.val[i + 32]!) (fun i hi => by
      have hv := usize_mk_val i (by scalar_tac)
      simpa only [hv] using ratchet_chain_byte output ⟨BitVec.ofNat _ i⟩ (by scalar_tac))
  obtain ⟨nonce, hnonce, hnonceBytes⟩ := from_fn_pure 12#usize
    ratchet.split_ratchet_kdf_output.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU8 output
    (fun i => output.val[i + 64]!) (by
      intro i hi
      have hv := usize_mk_val i (by simp at hi; omega)
      simpa only [hv] using ratchet_nonce_byte output ⟨BitVec.ofNat _ i⟩ (by scalar_tac))
  exact ⟨⟨⟨key⟩, ⟨chain⟩, ⟨nonce⟩⟩, by simp [ratchet.split_ratchet_kdf_output, hkey, hchain, hnonce,
    ratchet.RatchetKey.from_bytes, ratchet.RatchetChain.from_bytes, ratchet.RatchetNonce.from_bytes],
    by simpa using hkeyBytes, by simpa using hchainBytes, by simpa using hnonceBytes⟩

private theorem initial_right_byte (output : Std.Array Std.U8 64#usize) (i : Std.Usize)
    (hi : i.val < 32) :
    pqxdh.split_initial_ratchet_kdf_output.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
      output i = ok (output.val[i.val + 32]!, output) := by
  obtain ⟨j, hj, hjv⟩ := usize_add_val i 32#usize (lt_numBits _ (by simp; omega))
  simp [pqxdh.split_initial_ratchet_kdf_output.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut,
    pqxdh.RATCHET_CHAIN_SIZE, ratchet.RATCHET_CHAIN_SIZE, hj,
    index_usize_eq output j (by simp at hjv ⊢; omega), hjv]

/-- Initialization accepts every response array and every represented role descriptor without panic. -/
theorem split_initial_ratchet_kdf_output_ok (output : Std.Array Std.U8 64#usize)
    (initialization : pqxdh.RatchetInitialization) :
    ∃ chains, pqxdh.split_initial_ratchet_kdf_output output initialization = ok chains := by
  obtain ⟨left, hleft, _⟩ := from_fn_pure 32#usize
    pqxdh.split_initial_ratchet_kdf_output.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8 output
    (fun i => output.val[i]!) (fun i hi => by
      have hv := usize_mk_val i (by scalar_tac)
      simp only [pqxdh.split_initial_ratchet_kdf_output.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut,
        index_usize_eq output ⟨BitVec.ofNat _ i⟩ (by scalar_tac), hv, bind_tc_ok])
  obtain ⟨right, hright, _⟩ := from_fn_pure 32#usize
    pqxdh.split_initial_ratchet_kdf_output.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU8 output
    (fun i => output.val[i + 32]!) (fun i hi => by
      have hv := usize_mk_val i (by scalar_tac)
      simpa only [hv] using initial_right_byte output ⟨BitVec.ofNat _ i⟩ (by scalar_tac))
  by_cases h : initialization.send_offset = 0#u8 <;>
    simp [pqxdh.split_initial_ratchet_kdf_output, hleft, hright, h, ratchet.RatchetChain.from_bytes]

theorem split_ratchet_kdf_output_ok (output : Std.Array Std.U8 76#usize) :
    ∃ result, ratchet.split_ratchet_kdf_output output = ok result :=
  (split_ratchet_kdf_output_exact output).imp (fun _ h => h.1)

/-- No cryptographic response law is needed to interpret a fixed-length KDF response safely. -/
theorem ratchet_step_from_response_ok (response : ratchet.RatchetKdfResponse) :
    ∃ step, ratchet.concrete.ratchet_step_from_response response = ok step := by
  obtain ⟨result, hresult⟩ := split_ratchet_kdf_output_ok response.bytes
  simp [ratchet.concrete.ratchet_step_from_response, ratchet.RatchetKdfResponse.as_bytes, hresult]

/-- Initial KDF resumption is total for arbitrary represented pending state and response bytes. -/
theorem resume_initial_ratchet_kdf_ok (pending : pqxdh.concrete.InitialRatchetKdfPending)
    (response : pqxdh.concrete.InitialRatchetKdfResponse) :
    ∃ kernel, pqxdh.concrete.resume_initial_ratchet_kdf pending response = ok kernel := by
  obtain ⟨chains, hchains⟩ := split_initial_ratchet_kdf_output_ok response.bytes pending.initialization
  simp [pqxdh.concrete.resume_initial_ratchet_kdf,
    pqxdh.concrete.InitialRatchetKdfResponse.as_bytes, hchains, pqxdh.InitialRatchetChains.into_parts,
    ratchet.concrete.ConcreteRatchetKernel.new, ratchet.concrete.ConcreteRatchetKernel.from_counters,
    ratchet.refined.RefinedRatchet.from_counters, ratchet.control.RatchetState.from_counters,
    ratchet.control.SequenceCache.empty, ratchet.refined.empty_material_slots]

end BeaconcryptCore.PanicFreedom
