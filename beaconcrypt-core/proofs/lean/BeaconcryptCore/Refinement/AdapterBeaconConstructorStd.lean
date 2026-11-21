-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterBeaconConstructorNative
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The two std constructor entries delegate to the same checked caller-RNG constructor. The panicking entry retains its literal expect operation and failure message, so no totality or availability statement is silently added. -/
namespace BeaconcryptCore.Refinement.AdapterBeaconConstructorStd
open AdapterPublicWrapperRustT (RustT)
open BeaconcryptCore.Computational
open PqxdhServerAuthExperiment (Setup Checks)
open AdapterBeaconConstructorNative (M Leaves)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable [standard : AdapterBeaconConstructorPrimitive.Standard]
variable [generators : AdapterBeaconConstructorRequestMonad.Operations (RustT (M n KemSK source Auxiliary m))]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations (RustT (M n KemSK source Auxiliary m))]
variable [children : AdapterPublicWrapperRequestMonad.ChildOperations (RustT (M n KemSK source Auxiliary m))]
variable (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (view : AdapterPublicWrapperState.MaterialView source KemSK) (kem : AdapterBeaconConstructorKem.Representation view Unit)
variable (leaves : Leaves (n := n) (Auxiliary := Auxiliary) coins setup checks representation created standard.os view kem)

omit children in
theorem try_new (keyId : U64) (identityKey mldsaKey : Slice U8) :
    beaconcrypt_constructor_request.beacon.Beacon.try_new (m := RustT (M n KemSK source Auxiliary m)) keyId identityKey mldsaKey =
      Prod.fst <$> AdapterBeaconConstructorNative.sourceAll coins setup checks representation created standard.os view kem leaves keyId identityKey mldsaKey () := by
  unfold beaconcrypt_constructor_request.beacon.Beacon.try_new
  simp only [beaconcrypt_crypto.OsRng.Insts.Rand_coreTryCryptoRngError]
  rw [AdapterBeaconConstructorNative.source_all coins setup checks representation created standard.os view kem leaves]
  simp only [bind_pure_comp]

omit children in
theorem new_entry (keyId : U64) (identityKey mldsaKey : Slice U8) :
    beaconcrypt_constructor_request.beacon.Beacon.new (m := RustT (M n KemSK source Auxiliary m)) keyId identityKey mldsaKey = (do
      let result ← Prod.fst <$> AdapterBeaconConstructorNative.sourceAll coins setup checks representation created standard.os view kem leaves keyId identityKey mldsaKey ()
      AdapterPublicWrapperLiftFunction.call (m := RustT (M n KemSK source Auxiliary m)) core.result.Result.expect
        beaconcrypt_constructor.error.KeyGenError.Insts.CoreFmtDebug result
        (toStr "Failed to construct beacon" AdapterBeaconConstructorString.failure_bound)) := by
  unfold beaconcrypt_constructor_request.beacon.Beacon.new
  rw [try_new coins setup checks representation created view kem leaves]

end BeaconcryptCore.Refinement.AdapterBeaconConstructorStd

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorStd.try_new' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorStd.try_new

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorStd.new_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorStd.new_entry
