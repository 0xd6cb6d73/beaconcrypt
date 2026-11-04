-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Extraction.Funs
import BeaconcryptCore.AdapterInitAuthenticationExtraction.FunsExternal
import BeaconcryptCore.RegistrationPrimitiveExtraction.Types
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.PublicWrapperPlatform
class Material where
  EdSecretKey : Type
  KxPublicKey : Type
  KxSecretKey : Type
  KemPublicKey : Type
  KemSecretKey : Type
  KemCiphertext : Type
  KemSharedSecret : Type
  KdfPrk : Type
  MldsaIdentity : Type
  KeygenError : Type
  SignError : Type
class Platform where
  Arc : Type → Type
  arcView {T : Type} : Arc T → T
  Hasher : Type
  HashState : Type
  Allocator : Type
  Map : Type → Type → Type → Type → Type
  Set : Type → Type → Type → Type
  Occupied : Type → Type → Type → Type → Type
  Vacant : Type → Type → Type → Type → Type
  ReserveError : Type
end BeaconcryptCore.Refinement.PublicWrapperPlatform
namespace beaconcrypt_crypto
open BeaconcryptCore.Refinement.PublicWrapperPlatform
namespace crypto_sign
abbrev SecretKey [material : Material] := material.EdSecretKey
structure KeyPair [Material] [BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations] where
  public_key : PublicKey
  secret_key : SecretKey
end crypto_sign
namespace crypto_kx
abbrev PublicKey [material : Material] := material.KxPublicKey
abbrev SecretKey [material : Material] := material.KxSecretKey
structure KeyPair [Material] where
  public_key : PublicKey
  secret_key : SecretKey
end crypto_kx
namespace crypto_kem.mlkem768
abbrev PublicKey [material : Material] := material.KemPublicKey
abbrev SecretKey [material : Material] := material.KemSecretKey
structure KeyPair [Material] where
  public_key : PublicKey
  secret_key : SecretKey
end crypto_kem.mlkem768
abbrev CryptoError [primitive : BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations] := primitive.Error
abbrev crypto_kem.mlkem768.Ciphertext [material : Material] := material.KemCiphertext
abbrev crypto_kem.mlkem768.SharedSecret [material : Material] := material.KemSharedSecret
abbrev crypto_kdf.hkdf.sha512.Prk [material : Material] := material.KdfPrk
end beaconcrypt_crypto
namespace CoreModels
abbrev alloc.sync.Arc [platform : BeaconcryptCore.Refinement.PublicWrapperPlatform.Platform]
    (T : Type) := platform.Arc T
end CoreModels
namespace hashbrown
open BeaconcryptCore.Refinement.PublicWrapperPlatform
abbrev alloc.inner.Global [platform : Platform] := platform.Allocator
abbrev map.HashMap [platform : Platform] (K V S A : Type) := platform.Map K V S A
abbrev set.HashSet [platform : Platform] (K S A : Type) := platform.Set K S A
abbrev map.OccupiedEntry [platform : Platform] (K V S A : Type) := platform.Occupied K V S A
abbrev map.VacantEntry [platform : Platform] (K V S A : Type) := platform.Vacant K V S A
inductive map.Entry [Platform] (K V S A : Type) where
  | Occupied (entry : map.OccupiedEntry K V S A)
  | Vacant (entry : map.VacantEntry K V S A)
end hashbrown
namespace siphasher.sip
abbrev SipHasher13 [platform : BeaconcryptCore.Refinement.PublicWrapperPlatform.Platform] := platform.HashState
end siphasher.sip
namespace rand_core
structure TryRng (R E : Type) where
  coreerrorErrorInst : core.error.Error E
  try_fill_bytes : R → Slice U8 → RustM (CoreModels.core.result.Result Unit E × R × Slice U8)
  try_next_u32 : R → RustM (CoreModels.core.result.Result U32 E × R)
  try_next_u64 : R → RustM (CoreModels.core.result.Result U64 E × R)
structure TryCryptoRng (R E : Type) where
  TryRngInst : TryRng R E
end rand_core
namespace beaconcrypt_public_wrapper
abbrev auth.MldsaIdentity [material : BeaconcryptCore.Refinement.PublicWrapperPlatform.Material] := material.MldsaIdentity
abbrev collections.KeyedHasher [platform : BeaconcryptCore.Refinement.PublicWrapperPlatform.Platform] := platform.Hasher
end beaconcrypt_public_wrapper

namespace CoreModels
structure core.hash.BuildHasher (Self H : Type) where
  HasherInst : core.hash.Hasher H
  build_hasher : Self → RustM H
end CoreModels
namespace hashbrown
structure Equivalent (Q K : Type) where
  equivalent : Q → K → RustM Bool
@[instance_reducible] def Equivalent.Blanket {Q K : Type}
    (equal : core.cmp.Eq Q) (borrowed : core.borrow.Borrow K Q) : Equivalent Q K where
  equivalent query key := do
    let value ← borrowed.borrow key
    equal.PartialEqInst.eq query value
end hashbrown
namespace BeaconcryptCore.Refinement.PublicWrapperPlatform
class Allocator where
  Capability : Type → Type
  defaultCapability [platform : Platform] : Capability platform.Allocator
end BeaconcryptCore.Refinement.PublicWrapperPlatform
namespace hashbrown
abbrev alloc.inner.Allocator [allocator : BeaconcryptCore.Refinement.PublicWrapperPlatform.Allocator]
    (A : Type) := allocator.Capability A
def alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
    [platform : BeaconcryptCore.Refinement.PublicWrapperPlatform.Platform]
    [allocator : BeaconcryptCore.Refinement.PublicWrapperPlatform.Allocator] :
    alloc.inner.Allocator alloc.inner.Global := allocator.defaultCapability
end hashbrown

namespace zeroize
structure Zeroize (_T : Type) where
structure Zeroizing (T : Type) where
  value : T
structure DefaultIsZeroes (_T : Type) where
@[instance_reducible] def U8.Insts.ZeroizeDefaultIsZeroes : DefaultIsZeroes U8 := {}
@[instance_reducible] def Zeroize.Blanket {T : Type} (_zero : DefaultIsZeroes T) : Zeroize T := {}
@[instance_reducible] def Array.Insts.ZeroizeZeroize {T : Type} (N : Usize) (_zero : Zeroize T) : Zeroize (Array T N) := {}
@[instance_reducible] def alloc.vec.Vec.Insts.ZeroizeZeroize {T : Type} (_zero : Zeroize T) : Zeroize (CoreModels.alloc.vec.Vec T) := {}
def Zeroizing.new {T : Type} (_zero : Zeroize T) (value : T) : RustM (Zeroizing T) := ok ⟨value⟩
def Zeroizing.Insts.CoreOpsDerefDeref.deref {T : Type} (_zero : Zeroize T) (value : Zeroizing T) : RustM T := ok value.value
end zeroize
