-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterPublicWrapperExtraction.Funs
import BeaconcryptCore.Refinement.AdapterRecordRequestMonad

/-! Effectful interfaces for the actual selected public wrapper bodies. Static error/hash dictionaries remain the original source interfaces. Polymorphic RNG and container arguments remain typed method fields, and private containers are interpreted by trusted state rather than exposed to an external allocator. Concrete child interpretations expand their separately checked source request bodies. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad
open PublicWrapperPlatform (Material Platform Allocator)
open beaconcrypt_public_wrapper
variable [material : Material] [platform : Platform] [Allocator] [primitive : AdapterInitEdPrimitive.Operations]

class LocalOperations (m : Type → Type) where
  auth_MldsaIdentity_public_key : auth.MldsaIdentity → m (Array Std.U8 1952#usize)
  auth_MldsaIdentity_sign_requested :
    auth.MldsaIdentity → beaconcrypt_core.registration.MldsaSigningRequest →
      m (core.option.Option (alloc.vec.Vec Std.U8))
  ratchet_initial_ratchet_hkdf :
    beaconcrypt_core.ratchet.SymmetricRatchetKdfRequest → m (Array Std.U8
      64#usize)
  collections_KeyedHasher_Insts_CoreHashBuildHasherSipHasher13_build_hasher : collections.KeyedHasher → m siphasher.sip.SipHasher13
  ratchet_execute_seal_request :
    beaconcrypt_core.record_effects.AeadSealRequest → m (core.option.Option
      ((alloc.vec.Vec Std.U8) × (Array Std.U8 16#usize)))
  ratchet_execute_write_request :
    beaconcrypt_core.record_effects.RecordWriteRequest → m
      (core.option.Option (alloc.vec.Vec Std.U8))
class CryptoOperations (m : Type → Type) where
  kxSecretBytes : beaconcrypt_crypto.crypto_kx.SecretKey → m (Array U8 32#usize)
  convertPublic : beaconcrypt_crypto.crypto_sign.PublicKey → m (core.result.Result (Array U8 32#usize) primitive.Error)
  convertSecret : beaconcrypt_crypto.crypto_sign.SecretKey → m (core.result.Result (Array U8 32#usize) primitive.Error)
  scalarMult : Slice U8 → Slice U8 → m (core.result.Result (Array U8 32#usize) primitive.Error)
  kemPublicFromBytes : Slice U8 → m (core.result.Result beaconcrypt_crypto.crypto_kem.mlkem768.PublicKey primitive.Error)
  kemCipherFromBytes : Slice U8 → m (core.result.Result beaconcrypt_crypto.crypto_kem.mlkem768.Ciphertext primitive.Error)
  kemCipherBytes : beaconcrypt_crypto.crypto_kem.mlkem768.Ciphertext → m (Array U8 1088#usize)
  kemSharedBytes : beaconcrypt_crypto.crypto_kem.mlkem768.SharedSecret → m (Array U8 32#usize)
  encapsulate {R E : Type} : rand_core.TryCryptoRng R E → beaconcrypt_crypto.crypto_kem.mlkem768.PublicKey → R → m (core.result.Result (beaconcrypt_crypto.crypto_kem.mlkem768.Ciphertext × beaconcrypt_crypto.crypto_kem.mlkem768.SharedSecret) primitive.Error × R)
  decapsulate : beaconcrypt_crypto.crypto_kem.mlkem768.Ciphertext → beaconcrypt_crypto.crypto_kem.mlkem768.SecretKey → m (core.result.Result beaconcrypt_crypto.crypto_kem.mlkem768.SharedSecret primitive.Error)
  extract : core.option.Option (Slice U8) → Slice U8 → m (core.result.Result beaconcrypt_crypto.crypto_kdf.hkdf.sha512.Prk primitive.Error)
  expand : Usize → core.option.Option (Slice U8) → beaconcrypt_crypto.crypto_kdf.hkdf.sha512.Prk → m (core.result.Result (alloc.vec.Vec U8) primitive.Error)
  edPublicBytes : beaconcrypt_crypto.crypto_sign.PublicKey → m (Array U8 32#usize)
  edSign : Slice U8 → beaconcrypt_crypto.crypto_sign.SecretKey → m (core.result.Result (alloc.vec.Vec U8) primitive.Error)
  kxPublicBytes : beaconcrypt_crypto.crypto_kx.PublicKey → m (Array U8 32#usize)
  kemPublicBytes : beaconcrypt_crypto.crypto_kem.mlkem768.PublicKey → m (Array U8 1184#usize)
  kxGenerate {R E : Type} : rand_core.TryCryptoRng R E → R → m (core.result.Result beaconcrypt_crypto.crypto_kx.KeyPair primitive.Error × R)

class ContainerOperations (m : Type → Type) where
  setContains {K S A Q H : Type} : core.cmp.Eq K → core.hash.Hash K → core.hash.BuildHasher S H → hashbrown.alloc.inner.Allocator A → core.hash.Hash Q → hashbrown.Equivalent Q K → hashbrown.set.HashSet K S A → Q → m Bool
  setReserve {K S A H : Type} : core.cmp.Eq K → core.hash.Hash K → core.hash.BuildHasher S H → hashbrown.alloc.inner.Allocator A → hashbrown.set.HashSet K S A → Usize → m (core.result.Result Unit platform.ReserveError × hashbrown.set.HashSet K S A)
  setInsert {K S A H : Type} : core.cmp.Eq K → core.hash.Hash K → core.hash.BuildHasher S H → hashbrown.alloc.inner.Allocator A → hashbrown.set.HashSet K S A → K → m (Bool × hashbrown.set.HashSet K S A)
  mapContains {K V S A Q H : Type} : core.cmp.Eq K → core.hash.Hash K → core.hash.BuildHasher S H → hashbrown.alloc.inner.Allocator A → core.hash.Hash Q → hashbrown.Equivalent Q K → hashbrown.map.HashMap K V S A → Q → m Bool
  mapReserve {K V S A H : Type} : core.cmp.Eq K → core.hash.Hash K → core.hash.BuildHasher S H → hashbrown.alloc.inner.Allocator A → hashbrown.map.HashMap K V S A → Usize → m (core.result.Result Unit platform.ReserveError × hashbrown.map.HashMap K V S A)
  mapEntry {K V S A H : Type} : core.cmp.Eq K → core.hash.Hash K → core.hash.BuildHasher S H → hashbrown.alloc.inner.Allocator A → hashbrown.map.HashMap K V S A → K → m (hashbrown.map.Entry K V S A × (hashbrown.map.Entry K V S A → hashbrown.map.HashMap K V S A))
  vacantInsert {K V S A H : Type} : hashbrown.alloc.inner.Allocator A → core.hash.Hash K → core.hash.BuildHasher S H → hashbrown.map.VacantEntry K V S A → V → m (V × (V → hashbrown.map.VacantEntry K V S A))

class Codecs (m : Type → Type) where
  decodeInit : Slice U8 → m (core.option.Option beaconcrypt_parse.transport.initkex)
  decodeResponse : Slice U8 → m (core.option.Option beaconcrypt_parse.transport.kexresponse)
@[instance_reducible] def rustLocalOperations [ops : PublicWrapperPlatform.LocalOperations] : LocalOperations RustM where
  auth_MldsaIdentity_public_key := ops.auth_MldsaIdentity_public_key
  auth_MldsaIdentity_sign_requested := ops.auth_MldsaIdentity_sign_requested
  ratchet_initial_ratchet_hkdf := ops.ratchet_initial_ratchet_hkdf
  collections_KeyedHasher_Insts_CoreHashBuildHasherSipHasher13_build_hasher := ops.collections_KeyedHasher_Insts_CoreHashBuildHasherSipHasher13_build_hasher
  ratchet_execute_seal_request := ops.ratchet_execute_seal_request
  ratchet_execute_write_request := ops.ratchet_execute_write_request

@[instance_reducible] def rustCryptoOperations [ops : PublicWrapperPlatform.CryptoOperations] : CryptoOperations RustM where
  kxSecretBytes := ops.kxSecretBytes
  convertPublic := ops.convertPublic
  convertSecret := ops.convertSecret
  scalarMult := ops.scalarMult
  kemPublicFromBytes := ops.kemPublicFromBytes
  kemCipherFromBytes := ops.kemCipherFromBytes
  kemCipherBytes := ops.kemCipherBytes
  kemSharedBytes := ops.kemSharedBytes
  encapsulate := ops.encapsulate
  decapsulate := ops.decapsulate
  extract := ops.extract
  expand := ops.expand
  edPublicBytes := ops.edPublicBytes
  edSign := ops.edSign
  kxPublicBytes := ops.kxPublicBytes
  kemPublicBytes := ops.kemPublicBytes
  kxGenerate := ops.kxGenerate

@[instance_reducible] def rustContainerOperations [ops : PublicWrapperPlatform.ContainerOperations] : ContainerOperations RustM where
  setContains := ops.setContains
  setReserve := ops.setReserve
  setInsert := ops.setInsert
  mapContains := ops.mapContains
  mapReserve := ops.mapReserve
  mapEntry := ops.mapEntry
  vacantInsert := ops.vacantInsert

@[instance_reducible] def rustCodecs [ops : PublicWrapperPlatform.Codecs] : Codecs RustM where
  decodeInit := ops.decodeInit
  decodeResponse := ops.decodeResponse

class ChildOperations (m : Type → Type) where
  executeHash : registration.HashRequest → m (Option (Std.Array U8 64#usize))
  authenticateInit : session.ServerAuthenticationPin → registration.InitPacket → m (Option registration.AuthenticatedInit)
  authenticateResponse : registration.BeaconPending → Option registration.ResponsePacket →
    m (core.result.Result registration.AuthenticatedResponse pqxdh.BeaconAborted)
  commitmentHash : commitment.CommitmentTranscript → m (Option (Std.Array U8 64#usize) × commitment.CommitmentTranscript)
  openRequest : Option record.AeadRequest → m (Option (alloc.vec.Vec U8))
  ratchetHkdf : ratchet.SymmetricRatchetKdfRequest → m ratchet.RatchetKdfResponse
  compare : Slice U8 → Slice U8 → m Bool
  encodeInit : beaconcrypt_parse.transport.initkex → m (Option (alloc.vec.Vec U8))
  encodeResponse : beaconcrypt_parse.transport.kexresponse → m (Option (alloc.vec.Vec U8))

@[instance_reducible] def rustChildOperations [beaconcrypt.auth.Operations] [beaconcrypt.ratchet.Operations]
    [RegistrationWriterPrimitive.Operations] [AdapterWirePrimitive.Operations] :
    ChildOperations RustM where
  executeHash := beaconcrypt.auth.execute_hash
  authenticateInit := beaconcrypt.auth.authenticate_init
  authenticateResponse := beaconcrypt.auth.authenticate_response
  commitmentHash := beaconcrypt.ratchet.execute_commitment_hash
  openRequest := beaconcrypt.ratchet.execute_open_request
  ratchetHkdf := beaconcrypt.ratchet.ratchet_hkdf
  compare := beaconcrypt_crypto.utils.memcmp
  encodeInit := beaconcrypt_registration_writer.wire.encode_init
  encodeResponse := beaconcrypt_registration_writer.wire.encode_response

attribute [instance] rustLocalOperations rustCryptoOperations rustContainerOperations rustCodecs rustChildOperations

@[instance_reducible] def LocalOperations.toRust (implementation : LocalOperations RustM) : PublicWrapperPlatform.LocalOperations where
  auth_MldsaIdentity_public_key := implementation.auth_MldsaIdentity_public_key
  auth_MldsaIdentity_sign_requested := implementation.auth_MldsaIdentity_sign_requested
  ratchet_initial_ratchet_hkdf := implementation.ratchet_initial_ratchet_hkdf
  collections_KeyedHasher_Insts_CoreHashBuildHasherSipHasher13_build_hasher := implementation.collections_KeyedHasher_Insts_CoreHashBuildHasherSipHasher13_build_hasher
  ratchet_execute_seal_request := implementation.ratchet_execute_seal_request
  ratchet_execute_write_request := implementation.ratchet_execute_write_request

omit [Allocator] primitive in
theorem LocalOperations.rust_roundtrip [ops : PublicWrapperPlatform.LocalOperations] :
    (rustLocalOperations).toRust = ops := by
  cases ops
  rfl

@[instance_reducible] def CryptoOperations.toRust (implementation : CryptoOperations RustM) (constants : PublicWrapperPlatform.CryptoOperations) : PublicWrapperPlatform.CryptoOperations where
  errorToken := constants.errorToken
  errorInstance := constants.errorInstance
  kxSecretBytes := implementation.kxSecretBytes
  convertPublic := implementation.convertPublic
  convertSecret := implementation.convertSecret
  scalarMult := implementation.scalarMult
  kemPublicFromBytes := implementation.kemPublicFromBytes
  kemCipherFromBytes := implementation.kemCipherFromBytes
  kemCipherBytes := implementation.kemCipherBytes
  kemSharedBytes := implementation.kemSharedBytes
  encapsulate := implementation.encapsulate
  decapsulate := implementation.decapsulate
  extract := implementation.extract
  expand := implementation.expand
  edPublicBytes := implementation.edPublicBytes
  edSign := implementation.edSign
  kxPublicBytes := implementation.kxPublicBytes
  kemPublicBytes := implementation.kemPublicBytes
  kxGenerate := implementation.kxGenerate

omit platform [Allocator] in
theorem CryptoOperations.rust_roundtrip [ops : PublicWrapperPlatform.CryptoOperations] :
    (rustCryptoOperations).toRust ops = ops := by
  cases ops
  rfl

@[instance_reducible] def ContainerOperations.toRust (implementation : ContainerOperations RustM) (constants : PublicWrapperPlatform.ContainerOperations) : PublicWrapperPlatform.ContainerOperations where
  arrayHash := constants.arrayHash
  hasher := constants.hasher
  setContains := implementation.setContains
  setReserve := implementation.setReserve
  setInsert := implementation.setInsert
  mapContains := implementation.mapContains
  mapReserve := implementation.mapReserve
  mapEntry := implementation.mapEntry
  vacantInsert := implementation.vacantInsert

omit material primitive in
theorem ContainerOperations.rust_roundtrip [ops : PublicWrapperPlatform.ContainerOperations] :
    (rustContainerOperations).toRust ops = ops := by
  cases ops
  rfl

@[instance_reducible] def Codecs.toRust (implementation : Codecs RustM) : PublicWrapperPlatform.Codecs where
  decodeInit := implementation.decodeInit
  decodeResponse := implementation.decodeResponse

omit material platform [Allocator] primitive in
theorem Codecs.rust_roundtrip [ops : PublicWrapperPlatform.Codecs] :
    (rustCodecs).toRust = ops := by
  cases ops
  rfl

section Callbacks
variable {m : Type → Type} {Self Input Output : Type}

structure FnOnce (m : Type → Type) (Self Input Output : Type) where
  call_once : Self → Input → m Output

structure FnMut (m : Type → Type) (Self Input Output : Type) where
  FnOnceInst : FnOnce m Self Input Output
  call_mut : Self → Input → m (Output × Self)

structure Fn (m : Type → Type) (Self Input Output : Type) where
  FnMutInst : FnMut m Self Input Output
  call : Self → Input → m Output

def FnOnce.liftRust [AdapterRecordRequestMonad.LiftRust m]
    (implementation : core.ops.function.FnOnce Self Input Output) : FnOnce m Self Input Output where
  call_once capture input := AdapterRecordRequestMonad.liftRust (implementation.call_once capture input)

def FnMut.liftRust [AdapterRecordRequestMonad.LiftRust m]
    (implementation : core.ops.function.FnMut Self Input Output) : FnMut m Self Input Output where
  FnOnceInst := FnOnce.liftRust implementation.FnOnceInst
  call_mut capture input := AdapterRecordRequestMonad.liftRust (implementation.call_mut capture input)

def Fn.liftRust [AdapterRecordRequestMonad.LiftRust m]
    (implementation : core.ops.function.Fn Self Input Output) : Fn m Self Input Output where
  FnMutInst := FnMut.liftRust implementation.FnMutInst
  call capture input := AdapterRecordRequestMonad.liftRust (implementation.call capture input)

def FnOnce.toRust (implementation : FnOnce RustM Self Input Output) : core.ops.function.FnOnce Self Input Output where
  call_once := implementation.call_once

def FnMut.toRust (implementation : FnMut RustM Self Input Output) : core.ops.function.FnMut Self Input Output where
  FnOnceInst := implementation.FnOnceInst.toRust
  call_mut := implementation.call_mut

def Fn.toRust (implementation : Fn RustM Self Input Output) : core.ops.function.Fn Self Input Output where
  FnMutInst := implementation.FnMutInst.toRust
  call := implementation.call

namespace Option
variable [Monad m] {T U F : Type}
def map (implementation : FnOnce m F T U) (input : core.option.Option T) (capture : F) : m (core.option.Option U) :=
  match input with
  | .none => pure .none
  | .some value => do
      let result ← implementation.call_once capture value
      pure (.some result)

def and_then (implementation : FnOnce m F T (core.option.Option U))
    (input : core.option.Option T) (capture : F) : m (core.option.Option U) :=
  match input with
  | .none => pure .none
  | .some value => implementation.call_once capture value
end Option

omit material platform primitive [Allocator] in
theorem FnOnce.rust_roundtrip (implementation : core.ops.function.FnOnce Self Input Output) :
    (FnOnce.liftRust (m := RustM) implementation).toRust = implementation := by
  cases implementation
  rfl

omit material platform primitive [Allocator] in
theorem FnMut.rust_roundtrip (implementation : core.ops.function.FnMut Self Input Output) :
    (FnMut.liftRust (m := RustM) implementation).toRust = implementation := by
  cases implementation with
  | mk parent call => cases parent; rfl

omit material platform primitive [Allocator] in
theorem Fn.rust_roundtrip (implementation : core.ops.function.Fn Self Input Output) :
    (Fn.liftRust (m := RustM) implementation).toRust = implementation := by
  cases implementation with
  | mk parent call => cases parent with
    | mk once update => cases once; rfl

omit material platform primitive [Allocator] in
theorem Option.map_specializes {T U F : Type} (implementation : core.ops.function.FnOnce F T U)
    (input : core.option.Option T) (capture : F) :
    Option.map (FnOnce.liftRust (m := RustM) implementation) input capture =
      core.option.Option.map implementation input capture := by
  cases input <;> rfl

omit material platform primitive [Allocator] in
theorem Option.and_then_specializes {T U F : Type}
    (implementation : core.ops.function.FnOnce F T (core.option.Option U))
    (input : core.option.Option T) (capture : F) :
    Option.and_then (FnOnce.liftRust (m := RustM) implementation) input capture =
      core.option.Option.and_then implementation input capture := by
  cases input <;> rfl

omit material platform primitive [Allocator] in
theorem Option.map_toRust {T U F : Type} (implementation : FnOnce RustM F T U)
    (input : core.option.Option T) (capture : F) :
    Option.map implementation input capture = core.option.Option.map implementation.toRust input capture := by
  cases input <;> rfl

omit material platform primitive [Allocator] in
theorem Option.and_then_toRust {T U F : Type} (implementation : FnOnce RustM F T (core.option.Option U))
    (input : core.option.Option T) (capture : F) :
    Option.and_then implementation input capture = core.option.Option.and_then implementation.toRust input capture := by
  cases input <;> rfl

end Callbacks

end BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.LocalOperations.rust_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.LocalOperations.rust_roundtrip

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.CryptoOperations.rust_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.CryptoOperations.rust_roundtrip

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.ContainerOperations.rust_roundtrip' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.ContainerOperations.rust_roundtrip

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.Codecs.rust_roundtrip' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.Codecs.rust_roundtrip

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.FnOnce.rust_roundtrip' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.FnOnce.rust_roundtrip

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.FnMut.rust_roundtrip' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.FnMut.rust_roundtrip

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.Fn.rust_roundtrip' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.Fn.rust_roundtrip

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.Option.map_specializes' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.Option.map_specializes

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.Option.and_then_specializes' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.Option.and_then_specializes

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.Option.map_toRust' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.Option.map_toRust

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.Option.and_then_toRust' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.Option.and_then_toRust
