-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterPublicWrapperExtraction.LocalOperations
import BeaconcryptCore.AdapterPublicWrapperExtraction.PlatformOperations
import BeaconcryptCore.AdapterRegistrationWriterExtraction.Funs
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace beaconcrypt_public_wrapper
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Material]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Platform]
variable [primitive : BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]
variable [ops : BeaconcryptCore.Refinement.PublicWrapperPlatform.LocalOperations]
abbrev auth.MldsaIdentity.public_key := @BeaconcryptCore.Refinement.PublicWrapperPlatform.LocalOperations.auth_MldsaIdentity_public_key _ _ ops
abbrev auth.MldsaIdentity.sign_requested := @BeaconcryptCore.Refinement.PublicWrapperPlatform.LocalOperations.auth_MldsaIdentity_sign_requested _ _ ops
abbrev ratchet.initial_ratchet_hkdf := @BeaconcryptCore.Refinement.PublicWrapperPlatform.LocalOperations.ratchet_initial_ratchet_hkdf _ _ ops
abbrev collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13.build_hasher := @BeaconcryptCore.Refinement.PublicWrapperPlatform.LocalOperations.collections_KeyedHasher_Insts_CoreHashBuildHasherSipHasher13_build_hasher _ _ ops
abbrev ratchet.execute_seal_request := @BeaconcryptCore.Refinement.PublicWrapperPlatform.LocalOperations.ratchet_execute_seal_request _ _ ops
abbrev ratchet.execute_write_request := @BeaconcryptCore.Refinement.PublicWrapperPlatform.LocalOperations.ratchet_execute_write_request _ _ ops
variable [BeaconcryptCore.Refinement.RegistrationWriterPrimitive.Operations]
variable [BeaconcryptCore.Refinement.AdapterWirePrimitive.Operations]
abbrev wire.encode_init := beaconcrypt_registration_writer.wire.encode_init
abbrev wire.encode_response := beaconcrypt_registration_writer.wire.encode_response
variable [beaconcrypt.auth.Operations] [beaconcrypt.ratchet.Operations]
abbrev auth.execute_hash := beaconcrypt.auth.execute_hash
abbrev auth.authenticate_init := beaconcrypt.auth.authenticate_init
abbrev auth.authenticate_response := beaconcrypt.auth.authenticate_response
abbrev ratchet.execute_open_request := beaconcrypt.ratchet.execute_open_request
abbrev ratchet.execute_commitment_hash := beaconcrypt.ratchet.execute_commitment_hash
abbrev ratchet.ratchet_hkdf := beaconcrypt.ratchet.ratchet_hkdf
variable [crypto : BeaconcryptCore.Refinement.PublicWrapperPlatform.CryptoOperations]
def pqxdh.NoEntropy.Insts.Rand_coreTryRngCryptoError.try_fill_bytes
    (before : pqxdh.NoEntropy) (bytes : Slice U8) :
    RustM (core.result.Result Unit beaconcrypt_crypto.CryptoError × pqxdh.NoEntropy × Slice U8) :=
  ok (.Err crypto.errorToken, before, bytes)
def pqxdh.NoEntropy.Insts.Rand_coreTryRngCryptoError.try_next_u32
    (before : pqxdh.NoEntropy) :
    RustM (core.result.Result U32 beaconcrypt_crypto.CryptoError × pqxdh.NoEntropy) :=
  ok (.Err crypto.errorToken, before)
def pqxdh.NoEntropy.Insts.Rand_coreTryRngCryptoError.try_next_u64
    (before : pqxdh.NoEntropy) :
    RustM (core.result.Result U64 beaconcrypt_crypto.CryptoError × pqxdh.NoEntropy) :=
  ok (.Err crypto.errorToken, before)
def server.registration_application_bytes (input : beaconcrypt_core.transport.RegistrationApplication) : RustM (Slice U8) :=
  match input with
  | .Witness bytes => lift (Array.to_slice bytes)
  | .Provided bytes => ok bytes

def beacon.ProviderBeaconBeacon.finish_registration.closure.Insts.CoreOpsFunctionFnOnceTuplekexresponseOptionResponsePacket.call_once
    (_capture : beacon.ProviderBeaconBeacon.finish_registration.closure)
    (response : beaconcrypt_parse.transport.kexresponse) :
    RustM (core.option.Option beaconcrypt_core.registration.ResponsePacket) :=
  beaconcrypt_core.registration.ResponsePacket.from_slices response.identity_key response.ephemeral_key
    response.kem_cipher_text response.key_id response.app_cipher_text response.signature

def server.ProviderServerServer.build_registration_response.closure.Insts.CoreOpsFunctionFnOnceTupleSharedPairVecU8ArrayU816PairSharedSliceU8ArrayU816.call_once
    (_capture : server.ProviderServerServer.build_registration_response.closure)
    (input : alloc.vec.Vec U8 × Array U8 16#usize) : RustM (Slice U8 × Array U8 16#usize) := do
  let slice ← alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref input.1
  ok (slice, input.2)
end beaconcrypt_public_wrapper
