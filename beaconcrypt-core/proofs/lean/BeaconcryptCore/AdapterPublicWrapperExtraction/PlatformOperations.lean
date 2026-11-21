-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterPublicWrapperExtraction.Types
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.PublicWrapperPlatform
variable [material : Material] [platform : Platform] [Allocator] [primitive : AdapterInitEdPrimitive.Operations]
class CryptoOperations where
  errorToken : primitive.Error
  errorInstance : core.error.Error primitive.Error
  kxSecretBytes : beaconcrypt_crypto.crypto_kx.SecretKey → RustM (Array U8 32#usize)
  convertPublic : beaconcrypt_crypto.crypto_sign.PublicKey → RustM (core.result.Result (Array U8 32#usize) primitive.Error)
  convertSecret : beaconcrypt_crypto.crypto_sign.SecretKey → RustM (core.result.Result (Array U8 32#usize) primitive.Error)
  scalarMult : Slice U8 → Slice U8 → RustM (core.result.Result (Array U8 32#usize) primitive.Error)
  kemPublicFromBytes : Slice U8 → RustM (core.result.Result beaconcrypt_crypto.crypto_kem.mlkem768.PublicKey primitive.Error)
  kemCipherFromBytes : Slice U8 → RustM (core.result.Result beaconcrypt_crypto.crypto_kem.mlkem768.Ciphertext primitive.Error)
  kemCipherBytes : beaconcrypt_crypto.crypto_kem.mlkem768.Ciphertext → RustM (Array U8 1088#usize)
  kemSharedBytes : beaconcrypt_crypto.crypto_kem.mlkem768.SharedSecret → RustM (Array U8 32#usize)
  encapsulate {R E : Type} : rand_core.TryCryptoRng R E → beaconcrypt_crypto.crypto_kem.mlkem768.PublicKey → R → RustM (core.result.Result (beaconcrypt_crypto.crypto_kem.mlkem768.Ciphertext × beaconcrypt_crypto.crypto_kem.mlkem768.SharedSecret) primitive.Error × R)
  decapsulate : beaconcrypt_crypto.crypto_kem.mlkem768.Ciphertext → beaconcrypt_crypto.crypto_kem.mlkem768.SecretKey → RustM (core.result.Result beaconcrypt_crypto.crypto_kem.mlkem768.SharedSecret primitive.Error)
  extract : core.option.Option (Slice U8) → Slice U8 → RustM (core.result.Result beaconcrypt_crypto.crypto_kdf.hkdf.sha512.Prk primitive.Error)
  expand : Usize → core.option.Option (Slice U8) → beaconcrypt_crypto.crypto_kdf.hkdf.sha512.Prk → RustM (core.result.Result (alloc.vec.Vec U8) primitive.Error)
  edPublicBytes : beaconcrypt_crypto.crypto_sign.PublicKey → RustM (Array U8 32#usize)
  edSign : Slice U8 → beaconcrypt_crypto.crypto_sign.SecretKey → RustM (core.result.Result (alloc.vec.Vec U8) primitive.Error)
  kxPublicBytes : beaconcrypt_crypto.crypto_kx.PublicKey → RustM (Array U8 32#usize)
  kemPublicBytes : beaconcrypt_crypto.crypto_kem.mlkem768.PublicKey → RustM (Array U8 1184#usize)
  kxGenerate {R E : Type} : rand_core.TryCryptoRng R E → R → RustM (core.result.Result beaconcrypt_crypto.crypto_kx.KeyPair primitive.Error × R)
class ContainerOperations where
  arrayHash {T : Type} : (N : Usize) → core.hash.Hash T → core.hash.Hash (Array T N)
  hasher : core.hash.Hasher platform.HashState
  setContains {K S A Q H : Type} : core.cmp.Eq K → core.hash.Hash K → core.hash.BuildHasher S H → hashbrown.alloc.inner.Allocator A → core.hash.Hash Q → hashbrown.Equivalent Q K → hashbrown.set.HashSet K S A → Q → RustM Bool
  setReserve {K S A H : Type} : core.cmp.Eq K → core.hash.Hash K → core.hash.BuildHasher S H → hashbrown.alloc.inner.Allocator A → hashbrown.set.HashSet K S A → Usize → RustM (core.result.Result Unit platform.ReserveError × hashbrown.set.HashSet K S A)
  setInsert {K S A H : Type} : core.cmp.Eq K → core.hash.Hash K → core.hash.BuildHasher S H → hashbrown.alloc.inner.Allocator A → hashbrown.set.HashSet K S A → K → RustM (Bool × hashbrown.set.HashSet K S A)
  mapContains {K V S A Q H : Type} : core.cmp.Eq K → core.hash.Hash K → core.hash.BuildHasher S H → hashbrown.alloc.inner.Allocator A → core.hash.Hash Q → hashbrown.Equivalent Q K → hashbrown.map.HashMap K V S A → Q → RustM Bool
  mapReserve {K V S A H : Type} : core.cmp.Eq K → core.hash.Hash K → core.hash.BuildHasher S H → hashbrown.alloc.inner.Allocator A → hashbrown.map.HashMap K V S A → Usize → RustM (core.result.Result Unit platform.ReserveError × hashbrown.map.HashMap K V S A)
  mapEntry {K V S A H : Type} : core.cmp.Eq K → core.hash.Hash K → core.hash.BuildHasher S H → hashbrown.alloc.inner.Allocator A → hashbrown.map.HashMap K V S A → K → RustM (hashbrown.map.Entry K V S A × (hashbrown.map.Entry K V S A → hashbrown.map.HashMap K V S A))
  vacantInsert {K V S A H : Type} : hashbrown.alloc.inner.Allocator A → core.hash.Hash K → core.hash.BuildHasher S H → hashbrown.map.VacantEntry K V S A → V → RustM (V × (V → hashbrown.map.VacantEntry K V S A))
class Codecs where
  decodeInit : Slice U8 → RustM (core.option.Option beaconcrypt_parse.transport.initkex)
  decodeResponse : Slice U8 → RustM (core.option.Option beaconcrypt_parse.transport.kexresponse)
end BeaconcryptCore.Refinement.PublicWrapperPlatform
namespace beaconcrypt_crypto
open BeaconcryptCore.Refinement.PublicWrapperPlatform
variable [Material] [Platform] [primitive : BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations] [ops : CryptoOperations]
def crypto_sign.PublicKey.as_bytes := ops.edPublicBytes
def crypto_sign.sign := ops.edSign
def crypto_kx.PublicKey.as_bytes := ops.kxPublicBytes
def crypto_kem.mlkem768.PublicKey.as_bytes := ops.kemPublicBytes
def crypto_kx.KeyPair.generate_with_rng {R E : Type} (rng : rand_core.TryCryptoRng R E) := ops.kxGenerate rng
def CryptoError.Insts.CoreErrorError := ops.errorInstance
def crypto_kx.SecretKey.as_bytes := ops.kxSecretBytes
def crypto_sign.ed25519_pk_to_curve25519 := ops.convertPublic
def crypto_sign.ed25519_sk_to_curve25519 := ops.convertSecret
def crypto_scalarmult.scalarmult := ops.scalarMult
def crypto_kem.mlkem768.PublicKey.from_bytes := ops.kemPublicFromBytes
def crypto_kem.mlkem768.Ciphertext.from_bytes := ops.kemCipherFromBytes
def crypto_kem.mlkem768.Ciphertext.as_bytes := ops.kemCipherBytes
def crypto_kem.mlkem768.SharedSecret.as_bytes := ops.kemSharedBytes
def crypto_kem.mlkem768.decapsulate := ops.decapsulate
def crypto_kem.mlkem768.encapsulate_with_rng {R E : Type} (rng : rand_core.TryCryptoRng R E) := ops.encapsulate rng
def crypto_kdf.hkdf.sha512.extract := ops.extract
def crypto_kdf.hkdf.sha512.expand := ops.expand
end beaconcrypt_crypto
namespace CoreModels
open BeaconcryptCore.Refinement.PublicWrapperPlatform
variable [platform : Platform]
def alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref {T : Type} (self : alloc.sync.Arc T) : RustM T := ok (platform.arcView self)
end CoreModels
namespace siphasher.sip
open BeaconcryptCore.Refinement.PublicWrapperPlatform
variable [Platform] [Allocator] [ops : ContainerOperations]
def SipHasher13.Insts.CoreHashHasher := ops.hasher
end siphasher.sip
namespace hashbrown
open BeaconcryptCore.Refinement.PublicWrapperPlatform
variable [Platform] [Allocator] [ops : ContainerOperations]
abbrev set.HashSet.contains := @ContainerOperations.setContains _ _ ops
abbrev set.HashSet.try_reserve := @ContainerOperations.setReserve _ _ ops
abbrev set.HashSet.insert := @ContainerOperations.setInsert _ _ ops
abbrev map.HashMap.contains_key := @ContainerOperations.mapContains _ _ ops
abbrev map.HashMap.try_reserve := @ContainerOperations.mapReserve _ _ ops
abbrev map.HashMap.entry := @ContainerOperations.mapEntry _ _ ops
abbrev map.VacantEntry.insert := @ContainerOperations.vacantInsert _ _ ops
end hashbrown
namespace beaconcrypt_parse
open BeaconcryptCore.Refinement.PublicWrapperPlatform
variable [Codecs]
def decode_init := Codecs.decodeInit
def decode_response := Codecs.decodeResponse
end beaconcrypt_parse

namespace BeaconcryptCore.Refinement.PublicWrapperPlatform
def assignedKeyId (binding : beaconcrypt_core.session.SessionBinding) : RustM U64 :=
  ok (beaconcrypt_core.session.SessionBinding.assigned_key_id binding)
def beaconIdentity (binding : beaconcrypt_core.session.SessionBinding) : RustM (Array U8 32#usize) :=
  ok (beaconcrypt_core.session.SessionBinding.beacon_identity_public_key binding)
end BeaconcryptCore.Refinement.PublicWrapperPlatform

namespace CoreModels
open BeaconcryptCore.Refinement.PublicWrapperPlatform
@[instance_reducible] def core.Array.Insts.CoreCmpEq {T : Type} (N : Usize) (equal : core.cmp.Eq T) : core.cmp.Eq (Array T N) where
  PartialEqInst := core.Array.Insts.CoreCmpPartialEqArray N equal.PartialEqInst
@[instance_reducible] def core.borrow.Borrow.Blanket (T : Type) : core.borrow.Borrow T T where
  borrow value := ok value
variable [Platform] [Allocator] [ops : ContainerOperations]
abbrev core.Array.Insts.CoreHashHash := @ContainerOperations.arrayHash _ _ ops
end CoreModels
namespace BeaconcryptCore.Refinement.PublicWrapperPlatform
def peerBinding {T : Type} (peer : beaconcrypt_core.peer.Peer T) : RustM beaconcrypt_core.session.SessionBinding :=
  ok (beaconcrypt_core.peer.Peer.binding peer)
end BeaconcryptCore.Refinement.PublicWrapperPlatform

namespace zeroize
@[instance_reducible] def P.Insts.CoreOpsFunctionFnOnceTupleZZeroizing {T : Type} (_zero : Zeroize T) :
    core.ops.function.FnOnce (T → RustM (Zeroizing T)) T (Zeroizing T) where
  call_once function value := function value
end zeroize
