-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterRatchetKdfExtraction.Funs
import BeaconcryptCore.PanicFreedom.AdapterNormal
import BeaconcryptCore.PanicFreedom.Trivial

/-! The original ratchet HKDF wrapper retains both Result.expect calls. Safety needs successful HKDF API execution on the reached legal inputs, not just normal Err returns. The contracts select one output width and couple expansion to the PRK actually returned by the selected extract dictionary. Output-length preservation models the native mutable-slice borrow and supports exact returned-byte correspondence; primitive security is separate. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.PanicFreedom.AdapterRatchetKdf
open Refinement AdapterNormal
/-- Replacing only the kernel proof of a diagnostic string's size leaves its value unchanged. -/
theorem diagnostic_bound_irrelevant (message : String)
    (first second : message.toByteArray.size ≤ U32.max) :
    toStr message first = toStr message second := rfl

theorem reached_input_widths (request : ratchet.SymmetricRatchetKdfRequest) :
    request.input.to_slice.length = 32 ∧ request.info.to_slice.length = 41 :=
  ⟨Array.length_to_slice _, Array.length_to_slice _⟩

theorem zeroed_output_width (size : Usize) :
    (Array.repeat size 0#u8).to_slice.length = size.val := Array.length_to_slice _

variable [PublicWrapperPlatform.Material]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable [crypto : PublicWrapperPlatform.CryptoOperations]
variable [operations : AdapterRatchetKdfPrimitive.Operations]

/-- Only zero-initialized storage of the selected width and PRKs returned by this extract operation are reached. -/
structure Contracts (size : Usize) : Prop where
  extract : ∀ request : ratchet.SymmetricRatchetKdfRequest,
    ∃ prk, crypto.extract .None request.input.to_slice = ok (.Ok prk)
  expand : size.val ≤ 16320 → ∀ (request : ratchet.SymmetricRatchetKdfRequest) prk,
    crypto.extract .None request.input.to_slice = ok (.Ok prk) →
    ∃ after, operations.expandInto (Array.repeat size 0#u8).to_slice (.Some request.info.to_slice) prk =
      ok (.Ok (), after) ∧ after.length = size.val

/-- Direct RustM execution of the original body; write-back is pure even without a length law. -/
theorem symmetric_returns_of_calls (size : Usize) (bound : size.val ≤ 16320)
    (request : ratchet.SymmetricRatchetKdfRequest)
    (prk : beaconcrypt_crypto.crypto_kdf.hkdf.sha512.Prk) (after : Slice U8)
    (extracted : crypto.extract .None request.input.to_slice = ok (.Ok prk))
    (expanded : operations.expandInto (Array.repeat size 0#u8).to_slice (.Some request.info.to_slice) prk =
      ok (.Ok (), after)) :
    beaconcrypt_ratchet_kdf.ratchet.symmetric_ratchet_hkdf size request =
      ok (Array.from_slice (Array.repeat size 0#u8) after) := by
  have within : (255 * 64 : Nat) < 2 ^ System.Platform.numBits := by scalar_tac
  have scaled : (255#usize * 64#usize : RustM Usize) = ok 16320#usize := by simp [HMul.hMul, UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt, within]
  have admitted : size ≤ 16320#usize := by scalar_tac
  simp! only [beaconcrypt_ratchet_kdf.ratchet.symmetric_ratchet_hkdf, scaled,
    massert, admitted, ↓reduceIte, ratchet.SymmetricRatchetKdfRequest.impl.input,
    ratchet.SymmetricRatchetKdfRequest.impl.info, lift, bind_tc_ok,
    beaconcrypt_crypto.crypto_kdf.hkdf.sha512.extract, extracted,
    core.result.Result.expect, zeroize.Zeroizing.new,
    zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
    core.Array.Insts.CoreOpsIndexIndexMut.index_mut, core.array.Array.as_mut_slice,
    rust_primitives.slice.array_as_mut_slice, Array.to_slice_mut,
    core.Slice.Insts.CoreOpsIndexIndexMut.index_mut,
    core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
    beaconcrypt_crypto.crypto_kdf.hkdf.sha512.expand_into, expanded,
    zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]

theorem symmetric_ratchet_hkdf_total (size : Usize) (contracts : Contracts size)
    (bound : size.val ≤ 16320) (request : ratchet.SymmetricRatchetKdfRequest) :
    Normal (beaconcrypt_ratchet_kdf.ratchet.symmetric_ratchet_hkdf size request) := by
  exact (contracts.extract request).elim fun prk extracted =>
    (contracts.expand bound request prk extracted).elim fun after result =>
    ⟨_, symmetric_returns_of_calls size bound request prk after extracted result.1⟩

theorem ratchet_hkdf_total (contracts : Contracts 76#usize)
    (request : ratchet.SymmetricRatchetKdfRequest) :
    Normal (beaconcrypt_ratchet_kdf.ratchet.ratchet_hkdf request) := by
  exact normal_bind _ _ (symmetric_ratchet_hkdf_total 76#usize contracts (by scalar_tac) request)
    (fun bytes => Trivial.ratchet_RatchetKdfResponse_from_bytes_total bytes)

theorem initial_ratchet_hkdf_total (contracts : Contracts 64#usize)
    (request : ratchet.SymmetricRatchetKdfRequest) :
    Normal (beaconcrypt_ratchet_kdf.ratchet.initial_ratchet_hkdf request) := by
  exact symmetric_ratchet_hkdf_total 64#usize contracts (by scalar_tac) request

/-- The native write-back contains exactly the expansion's returned bytes; no model fallback is used. -/
theorem symmetric_output_bytes (size : Usize) (contracts : Contracts size)
    (bound : size.val ≤ 16320) (request : ratchet.SymmetricRatchetKdfRequest) :
    ∃ prk after result,
      crypto.extract .None request.input.to_slice = ok (.Ok prk) ∧
      operations.expandInto (Array.repeat size 0#u8).to_slice (.Some request.info.to_slice) prk =
        ok (.Ok (), after) ∧
      beaconcrypt_ratchet_kdf.ratchet.symmetric_ratchet_hkdf size request = ok result ∧
      result.val = after.val ∧ after.length = size.val := by
  exact (contracts.extract request).elim fun prk extracted =>
    (contracts.expand bound request prk extracted).elim fun after result =>
    ⟨prk, after, Array.from_slice (Array.repeat size 0#u8) after, extracted, result.1,
      symmetric_returns_of_calls size bound request prk after extracted result.1,
      Array.from_slice_val _ after result.2, result.2⟩

end BeaconcryptCore.PanicFreedom.AdapterRatchetKdf

/-- info: 'BeaconcryptCore.PanicFreedom.AdapterRatchetKdf.diagnostic_bound_irrelevant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.AdapterRatchetKdf.diagnostic_bound_irrelevant

/-- info: 'BeaconcryptCore.PanicFreedom.AdapterRatchetKdf.reached_input_widths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.AdapterRatchetKdf.reached_input_widths

/-- info: 'BeaconcryptCore.PanicFreedom.AdapterRatchetKdf.zeroed_output_width' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.AdapterRatchetKdf.zeroed_output_width

/-- info: 'BeaconcryptCore.PanicFreedom.AdapterRatchetKdf.symmetric_returns_of_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.AdapterRatchetKdf.symmetric_returns_of_calls

/-- info: 'BeaconcryptCore.PanicFreedom.AdapterRatchetKdf.symmetric_ratchet_hkdf_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.AdapterRatchetKdf.symmetric_ratchet_hkdf_total

/-- info: 'BeaconcryptCore.PanicFreedom.AdapterRatchetKdf.ratchet_hkdf_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.AdapterRatchetKdf.ratchet_hkdf_total

/-- info: 'BeaconcryptCore.PanicFreedom.AdapterRatchetKdf.initial_ratchet_hkdf_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.AdapterRatchetKdf.initial_ratchet_hkdf_total

/-- info: 'BeaconcryptCore.PanicFreedom.AdapterRatchetKdf.symmetric_output_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.AdapterRatchetKdf.symmetric_output_bytes
