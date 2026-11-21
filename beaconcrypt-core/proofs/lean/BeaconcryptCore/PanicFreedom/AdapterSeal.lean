-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterSealExtraction.Funs
import BeaconcryptCore.Refinement.RegistrationInputs
import BeaconcryptCore.PanicFreedom.AdapterSealJoin
import BeaconcryptCore.Refinement.AdapterSealSourceJoin

/-! Native sealing safety requires normal conversions, detached AEAD and the reached fixed-two joining callback. AEAD errors and malformed tag lengths remain normal rejection. No successful encryption or tag-size law is required. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.PanicFreedom.AdapterSeal
open Refinement
variable [primitives : AdapterSealPrimitive.Operations]
variable [joining : AdapterSealJoinCallbacks.Operations]

structure PrimitiveContracts : Prop where
  fromKey : ∀ value, ∃ result, primitives.fromKey value = ok result
  fromNonce : ∀ value, ∃ result, primitives.fromNonce value = ok result
  aead : ∀ plaintext associated nonce key, ∃ result, primitives.aead plaintext associated nonce key = ok result

structure Contracts : Prop extends PrimitiveContracts where
  join : ∀ parts : Array (Slice U8) 2#usize, ∃ result, joining.join parts = ok result

theorem execute_seal_request_total (contracts : Contracts) (request : record_effects.AeadSealRequest) :
    ∃ result, beaconcrypt_seal.ratchet.execute_seal_request request = ok result := by
  obtain ⟨key, keyed⟩ := contracts.fromKey request.key
  obtain ⟨nonce, nonced⟩ := contracts.fromNonce request.nonce
  cases plaintextCase : request.plaintext with
  | Single plaintext =>
    obtain ⟨reply, sealed⟩ := contracts.aead plaintext (.Some (Array.to_slice request.associated_data)) nonce key
    cases reply with
    | Err error =>
      exact ⟨.None, by simp! only [beaconcrypt_seal.ratchet.execute_seal_request,
        core.convert.Into.Blanket.into,
        beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf.Key.Insts.CoreConvertFromArrayU832,
        beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf.Nonce.Insts.CoreConvertFromArrayU812,
        keyed, nonced, plaintextCase, core.array.Array.as_slice, rust_primitives.slice.array_as_slice,
        beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf.encrypt_detached,
        sealed, core.result.Result.ok,
        core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
        bind_tc_ok]⟩
    | Ok value =>
      obtain ⟨adapted, tagged⟩ := RegistrationInputs.copied_slice_total 16#usize value.2
      cases adapted <;> exact ⟨_, by
        simp! only [beaconcrypt_seal.ratchet.execute_seal_request,
          core.convert.Into.Blanket.into,
          beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf.Key.Insts.CoreConvertFromArrayU832,
          beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf.Nonce.Insts.CoreConvertFromArrayU812,
          keyed, nonced, plaintextCase, core.array.Array.as_slice, rust_primitives.slice.array_as_slice,
          beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf.encrypt_detached,
          sealed, core.result.Result.ok, alloc.vec.Vec.as_slice, rust_primitives.sequence.seq_to_slice, tagged,
          core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
          core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
          bind_tc_ok]
        rfl⟩
  | Prefixed «prefix» application =>
    obtain ⟨joined, joinedRun⟩ := contracts.join (Array.make 2#usize [Array.to_slice «prefix», application])
    cases joined with
    | none =>
      exact ⟨.None, by simp! only [beaconcrypt_seal.ratchet.execute_seal_request,
        core.convert.Into.Blanket.into,
        beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf.Key.Insts.CoreConvertFromArrayU832,
        beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf.Nonce.Insts.CoreConvertFromArrayU812,
        keyed, nonced, plaintextCase, core.array.Array.as_slice, rust_primitives.slice.array_as_slice,
        beaconcrypt_seal.ratchet.join_record_parts, joinedRun,
        core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
        bind_tc_ok]⟩
    | some bytes =>
      obtain ⟨reply, sealed⟩ := contracts.aead bytes (.Some (Array.to_slice request.associated_data)) nonce key
      cases reply with
      | Err error =>
        refine ⟨.None, ?_⟩
        simp! only [beaconcrypt_seal.ratchet.execute_seal_request,
          core.convert.Into.Blanket.into,
          beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf.Key.Insts.CoreConvertFromArrayU832,
          beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf.Nonce.Insts.CoreConvertFromArrayU812,
          keyed, nonced, plaintextCase, core.array.Array.as_slice, rust_primitives.slice.array_as_slice,
          beaconcrypt_seal.ratchet.join_record_parts, joinedRun,
          zeroize.Zeroizing.new, zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
          core.option.Option.as_ref, alloc.vec.Vec.as_slice, rust_primitives.sequence.seq_to_slice,
          beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf.encrypt_detached,
          sealed, core.result.Result.ok,
          core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
          core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
          bind_tc_ok]
      | Ok value =>
        obtain ⟨adapted, tagged⟩ := RegistrationInputs.copied_slice_total 16#usize value.2
        cases adapted <;> exact ⟨_, by
          simp! only [beaconcrypt_seal.ratchet.execute_seal_request,
            core.convert.Into.Blanket.into,
            beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf.Key.Insts.CoreConvertFromArrayU832,
            beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf.Nonce.Insts.CoreConvertFromArrayU812,
            keyed, nonced, plaintextCase, core.array.Array.as_slice, rust_primitives.slice.array_as_slice,
            beaconcrypt_seal.ratchet.join_record_parts, joinedRun,
            zeroize.Zeroizing.new, zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
            core.option.Option.as_ref, alloc.vec.Vec.as_slice, rust_primitives.sequence.seq_to_slice,
            beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf.encrypt_detached,
            sealed, core.result.Result.ok, tagged,
            core.option.Option.Insts.CoreOpsTry_traitTry.branch,
            core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
            core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
            bind_tc_ok]
          rfl⟩

omit joining in
theorem execute_seal_request_source_total [allocator : AdapterWirePrimitive.Operations]
    (contracts : PrimitiveContracts) (allocation : AdapterWire.Contracts)
    (other : AdapterSealJoinCallbacks.Operations) (request : record_effects.AeadSealRequest) :
    ∃ result, @beaconcrypt_seal.ratchet.execute_seal_request primitives
      (AdapterSealSourceJoin.sourceCallbacks other) request = ok result := by
  exact @execute_seal_request_total primitives (AdapterSealSourceJoin.sourceCallbacks other)
    (@Contracts.mk primitives (AdapterSealSourceJoin.sourceCallbacks other) contracts
      (fun parts => AdapterSealJoin.join_total allocation parts)) request

end BeaconcryptCore.PanicFreedom.AdapterSeal
