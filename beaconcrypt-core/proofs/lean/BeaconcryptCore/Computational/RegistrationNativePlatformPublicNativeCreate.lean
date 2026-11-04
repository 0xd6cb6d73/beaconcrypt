-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeLocal
/-! The corrected public create callback retains its actual constructor bill, including failed ML generation, pin hashing, identity/prekey draws, indexed KEM creation and owner allocation. External P remains literal and has a separate bill. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeCreate
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (EffectKind)
open PqxdhRecordLiftCtxProgramBounds (Weighted)
open RegistrationNativePlatformPublicFrontend (trusted)
open RegistrationNativePlatformPublicNativeLocal (bill)
open RegistrationNativePlatformPublicWorldBills (nativeBill)
variable {n : Nat} {I KemSK Platform : Type} {base : OracleSpec I}

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT S m X) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

/-- The actual corrected create branch has a source-derived native/global weighted bill. -/
theorem create_bound (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (qGenerate qSign qKem : Nat) (generation : source.generate.IsTotalQueryBound qGenerate)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativePlatformPublicFrontend.State source Platform) (kind : EffectKind) :
    Weighted (nativeBill (n := n) (KemSK := KemSK) qSign qKem kind)
      ((RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.beacon
        (RegistrationNativePlatformPublicOwners.create trusted setup source selected publicPrekey edPin mlPin keyId))).run before)
      (RegistrationNativeCreateCosts.createBill qGenerate qKem kind) := by
  apply RegistrationNativePlatformPublicNativeLocal.beacon_bound
  simp only [RegistrationNativePlatformPublicOwners.create, RegistrationNativePlatformPublicOwners.executeLocal,
    RegistrationNativePlatformGenericBundle.liftLegacy, StateT.run, map_apply, Weighted, isQueryBound_map_iff]
  exact RegistrationNativePlatformPublicNativeLocal.trusted_program qSign qKem kind _ _
    (RegistrationNativeCreateCosts.create_bound setup source qGenerate qKem generation edPin mlPin keyId _ _ kind) before.2
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeCreate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeCreate.create_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeCreate.create_bound
