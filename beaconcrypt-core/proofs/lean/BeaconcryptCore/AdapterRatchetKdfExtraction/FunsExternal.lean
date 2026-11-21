-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterRatchetKdfExtraction.Types

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true

namespace beaconcrypt_crypto
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Material]
variable [primitive : BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]
variable [operations : BeaconcryptCore.Refinement.AdapterRatchetKdfPrimitive.Operations]

def crypto_kdf.hkdf.sha512.expand_into := operations.expandInto
def CryptoError.Insts.CoreFmtDebug := operations.errorDebug

end beaconcrypt_crypto

namespace zeroize

def Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut {T : Type}
    (_zero : Zeroize T) (self : Zeroizing T) : RustM (T × (T → Zeroizing T)) :=
  ok (self.value, fun value => ⟨value⟩)

end zeroize
