-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicBundleMask
import BeaconcryptCore.Computational.RegistrationNativePublicOwners
import BeaconcryptCore.Computational.RegistrationNativePublicCreateMask
/-! Public creation and bundle callbacks use one common platform monad and the actual extracted stateful Init writer. Selected prekey scalars remain absent from executable owner state; only signed views reach the external writer. This module introduces no fixed pure codec or whole-source correspondence assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwners
open RegistrationNativePublicOwners (Owner State restore pack)
open RegistrationNativeBeaconFrontend (Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (PeerEncoding)
variable {n : Nat} {ι KemSK Auxiliary A E : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m]

abbrev M (source : RegistrationNativeMldsa.Source) (Auxiliary : Type) (m : Type → Type) :=
  StateT (State source) (StateT (EnvState Auxiliary) m)

def executeLocal (selected : Nat) (publicPrekey : PeerEncoding)
    (work : RegistrationNativePlatformGenericBundle.M source Auxiliary m A) : M source Auxiliary m A :=
  fun owners env => (fun result => ((result.1.1, pack selected publicPrekey result.1.2), result.2)) <$>
    (work.run (owners.map restore)).run env

noncomputable def create (implementation : QueryImpl (Trusted n KemSK) m)
    (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (selected : Nat) (publicPrekey : PeerEncoding) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64) : M source Auxiliary m (RustM (Option Nat)) :=
  executeLocal selected publicPrekey (RegistrationNativePlatformGenericBundle.liftLegacy implementation
    (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId))

noncomputable def bundle (implementation : QueryImpl (Trusted n KemSK) m)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) m)
    (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (selected : Nat) (publicPrekey : PeerEncoding) (index : Nat) :
    M source Auxiliary m (RustM (Option (alloc.vec.Vec U8))) :=
  executeLocal selected publicPrekey (RegistrationNativePlatformGenericBundle.bundle implementation setup source
    (RegistrationNativePlatformGenericBundle.encoderWith writer) index)

variable [LawfulMonad m]

theorem create_source (implementation : QueryImpl (Trusted n KemSK) m)
    (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : State source) (env : EnvState RegistrationServerRoleBackend.State)
    (canonical : RegistrationNativePublicOwnerMask.Canonical selected (setup.dh.publicKey scalar) owners) :
    Prod.map (Prod.map id (RegistrationNativePublicSourceState.owners scalar)) id <$>
      ((create implementation setup source selected (setup.dh.publicKey scalar) edPin mlPin keyId).run owners).run env =
      ((RegistrationNativePlatformGenericBundle.liftLegacy implementation
        (RegistrationNativeScalarEager.create setup source selected scalar edPin mlPin keyId)).run
          (RegistrationNativePublicSourceState.owners scalar owners)).run env := by
  have equation := RegistrationNativePublicCreateMask.create_mask (n := n) setup source selected scalar edPin mlPin keyId
    (owners.map restore) env
  rw [RegistrationNativePublicOwnerRestore.restored_dummy selected scalar (setup.dh.publicKey scalar) owners canonical] at equation
  have coupled := congrArg (simulateQ implementation) equation
  simpa only [create, executeLocal, StateT.run, RegistrationNativePlatformGenericBundle.liftLegacy,
    simulateQ_map, Functor.map_map, Prod.map_def, id_eq,
    RegistrationNativePublicOwnerRestore.restore_pack] using coupled

theorem bundle_source (implementation : QueryImpl (Trusted n KemSK) m)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) m)
    (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes) (index : Nat)
    (owners : State source) (env : EnvState Auxiliary)
    (canonical : RegistrationNativePublicOwnerMask.Canonical selected (setup.dh.publicKey scalar) owners) :
    Prod.map (Prod.map id (RegistrationNativePublicSourceState.owners scalar)) id <$>
      ((bundle implementation writer setup source selected (setup.dh.publicKey scalar) index).run owners).run env =
      ((RegistrationNativePlatformGenericBundle.bundle implementation setup source
        (RegistrationNativePlatformGenericBundle.encoderWith writer) index).run
          (RegistrationNativePublicSourceState.owners scalar owners)).run env := by
  have publicKey : ∀ owner, (owners.map restore)[selected]? = some owner →
      owner.prekeyPublic = PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar) := by
    intro owner found
    simp only [List.getElem?_map, Option.map_eq_some_iff] at found
    obtain ⟨exposed, present, rfl⟩ := found
    have chosen := canonical selected exposed present
    simp only [RegistrationNativePublicOwnerMask.At, ite_true] at chosen
    exact chosen.2
  have equation := RegistrationNativePlatformPublicBundleMask.bundle_mask implementation writer setup index selected scalar
    (setup.dh.publicKey scalar) (owners.map restore) env publicKey
  rw [RegistrationNativePublicOwnerRestore.restored_dummy selected scalar (setup.dh.publicKey scalar) owners canonical] at equation
  simpa only [bundle, executeLocal, StateT.run, Functor.map_map, Prod.map_def, id_eq,
    RegistrationNativePublicOwnerRestore.restore_pack] using equation
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwners

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwners.create_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwners.create_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwners.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwners.bundle_source
