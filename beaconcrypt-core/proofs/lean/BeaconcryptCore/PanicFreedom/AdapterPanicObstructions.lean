-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterConstructors
import BeaconcryptCore.PanicFreedom.AdapterPublicOrdinary

/-! Exact represented counterexamples to unconditional adapter totality. These statements preserve the intentional constructor panic and the synchronous slot ownership discipline. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.PanicFreedom.AdapterPanicObstructions
open Refinement beaconcrypt_public_wrapper

theorem take_empty_panics :
    beaconcrypt_public_ordinary.ratchet.RatchetKernelSlot.take ⟨none⟩ = fail .panic := rfl

theorem deref_empty_panics :
    beaconcrypt_public_ordinary.ratchet.RatchetKernelSlot.Insts.CoreOpsDerefDerefConcreteRatchetKernel.deref ⟨none⟩ = fail .panic := rfl

theorem put_populated_panics (before after : ratchet.concrete.ConcreteRatchetKernel) :
    beaconcrypt_public_ordinary.ratchet.RatchetKernelSlot.put ⟨some before⟩ after = fail .panic := rfl

variable [PublicWrapperPlatform.Material] [PublicWrapperPlatform.Platform]
variable [AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.CryptoOperations]
variable [AdapterBeaconConstructorPrimitive.Operations] [AdapterBeaconConstructorPrimitive.Standard]
variable [beaconcrypt.auth.Operations]

omit [PublicWrapperPlatform.Platform] in
theorem beacon_new_of_error (identifier : U64) (identityKey mldsaKey : Slice U8)
    (rejected : beaconcrypt_constructor.beacon.Beacon.try_new identifier identityKey mldsaKey = ok (.Err ())) :
    beaconcrypt_constructor.beacon.Beacon.new identifier identityKey mldsaKey = fail .panic := by
  simp only [beaconcrypt_constructor.beacon.Beacon.new, rejected, bind_tc_ok, core.result.Result.expect]
  rfl

variable [AdapterServerConstructorPrimitive.Standard]

omit [PublicWrapperPlatform.CryptoOperations] [beaconcrypt.auth.Operations] in
theorem server_new_of_error (identifier : U64) (identitySeed mldsaSeed : core.option.Option (Slice U8))
    (rejected : beaconcrypt_server_constructor.server.Server.try_new identifier identitySeed mldsaSeed = ok (.Err ())) :
    beaconcrypt_server_constructor.server.Server.new identifier identitySeed mldsaSeed = fail .panic := by
  simp only [beaconcrypt_server_constructor.server.Server.new, rejected, bind_tc_ok, core.result.Result.expect]
  rfl

end BeaconcryptCore.PanicFreedom.AdapterPanicObstructions
