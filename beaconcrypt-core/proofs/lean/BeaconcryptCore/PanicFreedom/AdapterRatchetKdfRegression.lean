-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterRatchetKdf

/-! The two Result.expect calls in the original ratchet KDF executor cannot be certified from primitive normality alone. Ordinary extract or expand Result.Err returns are explicit represented panic obstructions. A positive synthetic execution model witnesses satisfiable contracts while unrelated entropy operations diverge. These statements do not assume formatter totality, native primitive correspondence or cryptographic security. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.PanicFreedom.AdapterRatchetKdfRegression
open Refinement AdapterNormal
variable [PublicWrapperPlatform.Material]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable [crypto : PublicWrapperPlatform.CryptoOperations]
variable [operations : AdapterRatchetKdfPrimitive.Operations]

theorem extract_error_panics (size : Usize) (bound : size.val ≤ 16320)
    (request : ratchet.SymmetricRatchetKdfRequest) (error : primitive.Error)
    (extracted : crypto.extract .None request.input.to_slice = ok (.Err error)) :
    beaconcrypt_ratchet_kdf.ratchet.symmetric_ratchet_hkdf size request = fail .panic := by
  have within : (255 * 64 : Nat) < 2 ^ System.Platform.numBits := by scalar_tac
  have scaled : (255#usize * 64#usize : RustM Usize) = ok 16320#usize := by
    simp [HMul.hMul, UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt, within]
  have admitted : size ≤ 16320#usize := by scalar_tac
  simp! only [beaconcrypt_ratchet_kdf.ratchet.symmetric_ratchet_hkdf, scaled,
    massert, admitted, ↓reduceIte, ratchet.SymmetricRatchetKdfRequest.impl.input,
    lift, bind_tc_ok, beaconcrypt_crypto.crypto_kdf.hkdf.sha512.extract, extracted,
    core.result.Result.expect, core.panicking.internal.panic, bind_tc_fail]

theorem expand_error_panics (size : Usize) (bound : size.val ≤ 16320)
    (request : ratchet.SymmetricRatchetKdfRequest)
    (prk : beaconcrypt_crypto.crypto_kdf.hkdf.sha512.Prk) (after : Slice U8)
    (error : primitive.Error)
    (extracted : crypto.extract .None request.input.to_slice = ok (.Ok prk))
    (expanded : operations.expandInto (Array.repeat size 0#u8).to_slice
      (.Some request.info.to_slice) prk = ok (.Err error, after)) :
    beaconcrypt_ratchet_kdf.ratchet.symmetric_ratchet_hkdf size request = fail .panic := by
  have within : (255 * 64 : Nat) < 2 ^ System.Platform.numBits := by scalar_tac
  have scaled : (255#usize * 64#usize : RustM Usize) = ok 16320#usize := by
    simp [HMul.hMul, UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt, within]
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
    core.panicking.internal.panic, bind_tc_fail]

@[instance_reducible] def successfulCrypto
    (prk : beaconcrypt_crypto.crypto_kdf.hkdf.sha512.Prk) : PublicWrapperPlatform.CryptoOperations :=
  { crypto with extract := fun _ _ => ok (.Ok prk)
                kxGenerate := fun _ _ => div }

@[instance_reducible] def successfulExpansion (size : Usize) : AdapterRatchetKdfPrimitive.Operations :=
  { operations with expandInto := fun before _ _ =>
      if before.length = size.val then ok (.Ok (), before) else div }

theorem mock_contracts (size : Usize) (prk : beaconcrypt_crypto.crypto_kdf.hkdf.sha512.Prk) :
    letI := successfulCrypto prk
    letI := successfulExpansion size
    AdapterRatchetKdf.Contracts size := by
  let _ := successfulCrypto prk
  let _ := successfulExpansion size
  refine { extract := fun _ => ⟨prk, rfl⟩, expand := ?_ }
  intro _ request key called
  exact ⟨_, ite_eq_left (AdapterRatchetKdf.zeroed_output_width size),
    AdapterRatchetKdf.zeroed_output_width size⟩

omit operations in
theorem unrelated_generation_diverges (prk : beaconcrypt_crypto.crypto_kdf.hkdf.sha512.Prk)
    {R E : Type} (generator : rand_core.TryCryptoRng R E) (rng : R) :
    (successfulCrypto prk).kxGenerate generator rng = div := rfl

theorem mock_symmetric_total (size : Usize) (bound : size.val ≤ 16320)
    (prk : beaconcrypt_crypto.crypto_kdf.hkdf.sha512.Prk)
    (request : ratchet.SymmetricRatchetKdfRequest) :
    letI := successfulCrypto prk
    letI := successfulExpansion size
    Normal (beaconcrypt_ratchet_kdf.ratchet.symmetric_ratchet_hkdf size request) := by
  have selected := mock_contracts size prk
  let _ := successfulCrypto prk
  let _ := successfulExpansion size
  exact AdapterRatchetKdf.symmetric_ratchet_hkdf_total size selected bound request

omit crypto in
theorem unselected_expansion_diverges (selected requested : Usize)
    (different : requested.val ≠ selected.val)
    (info : core.option.Option (Slice U8))
    (prk : beaconcrypt_crypto.crypto_kdf.hkdf.sha512.Prk) :
    (successfulExpansion selected).expandInto (Array.repeat requested 0#u8).to_slice info prk = div := by
  apply ite_eq_right
  intro same
  exact different ((AdapterRatchetKdf.zeroed_output_width requested).symm.trans same)

end BeaconcryptCore.PanicFreedom.AdapterRatchetKdfRegression
