-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterBeaconConstructorGeneration
import BeaconcryptCore.Refinement.AdapterBeaconConstructorKem
import BeaconcryptCore.Computational.RegistrationNativeBeaconCreateProgram
import BeaconcryptCore.Computational.RegistrationNativeBeaconBirth
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Literal owner-slot administration and assembly of newly generated source material. The private KEM row is the actual jointly sampled row; Ed/X25519 views are individual primitive guarantees. No initial Beacon-material relation or whole-constructor conclusion is a premise. Execution through the same source constructor is composed separately. -/
namespace BeaconcryptCore.Refinement.AdapterBeaconConstructorMaterial
open BeaconcryptCore.Computational
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhKemIndCca (MlKem768PublicKey)
open AdapterBeaconConstructorKem (Native)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

def appendWorld (keyId : U64) (edPin : Std.Array U8 32#usize) (before : PqxdhRecordLiftWorld.State n) : PqxdhRecordLiftWorld.State n :=
  let charged := PqxdhRecordLiftWorld.chargeEffect (.inr (.appendOwner keyId edPin .fresh)) before
  { charged with owners := charged.owners ++ [.inactive .fresh] }

def appendNative (keyId : U64) (edPin : Std.Array U8 32#usize) (before : Native n KemSK source) : Native n KemSK source :=
  { before with server := { before.server with world := { before.server.world with world :=
    (appendWorld keyId edPin before.server.world.world.1, before.server.world.world.2) } } }

theorem append_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (keyId : U64) (edPin : Std.Array U8 32#usize)
    (before : Native n KemSK source) :
    (RegistrationNativeExperiment.trusted setup checks representation created source (.inl (.inr (.appendOwner keyId edPin .fresh)))).run before =
    pure (before.server.world.world.1.owners.length, appendNative keyId edPin before) := by
  simp only [RegistrationNativeExperiment.trusted, RegistrationNativeExperiment.world,
    RegistrationNativeExperiment.server, PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability,
    StateT.run, map_pure, appendNative, appendWorld, PqxdhRecordLiftWorld.chargeEffect]

variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [generators : AdapterBeaconConstructorRequestMonad.Operations (AdapterPublicWrapperRustT.RustT m)]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations (AdapterPublicWrapperRustT.RustT m)]
variable {R Error : Type}

noncomputable def stored (setup : Setup base KemSK) (generator : rand_core.TryCryptoRng R Error)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (edSample : m PqxdhJointIdentity.IdentitySeed)
    (ed : AdapterBeaconConstructorGeneration.EdContract generator view setup.joint edSample)
    (kxSample : m PqxdhJointGapDh.ScalarBytes)
    (kx : AdapterBeaconConstructorGeneration.KxContract generator view (fun scalar => PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) kxSample)
    (kem : AdapterBeaconConstructorKem.Representation view R)
    (serverId : beaconcrypt_crypto.crypto_sign.PublicKey) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (identity : PqxdhJointIdentity.IdentitySeed)
    (prekey : PqxdhJointGapDh.ScalarBytes)
    (before : Native n KemSK source) (pair : MlKem768PublicKey × KemSK) (rng : R) : beaconcrypt_public_wrapper.beacon.Beacon :=
  ⟨ed.realize identity, keyId,
    .Fresh ⟨⟨view.edPublic serverId, keyId⟩⟩ (kx.realize prekey) (AdapterBeaconConstructorKem.receipt view kem before pair rng).pair,
    serverId, ⟨RegistrationNativeBeaconCreateProgram.pin (view.edPublic serverId) mlPin keyId⟩⟩

omit [LawfulMonad m] in
theorem initial (setup : Setup base KemSK) (generator : rand_core.TryCryptoRng R Error)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (edSample : m PqxdhJointIdentity.IdentitySeed)
    (ed : AdapterBeaconConstructorGeneration.EdContract generator view setup.joint edSample)
    (kxSample : m PqxdhJointGapDh.ScalarBytes)
    (kx : AdapterBeaconConstructorGeneration.KxContract generator view (fun scalar => PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) kxSample)
    (kem : AdapterBeaconConstructorKem.Representation view R)
    (serverId : beaconcrypt_crypto.crypto_sign.PublicKey) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (identity : PqxdhJointIdentity.IdentitySeed)
    (prekey : PqxdhJointGapDh.ScalarBytes)
    (before : Native n KemSK source) (pair : MlKem768PublicKey × KemSK) (world : PqxdhRecordLiftWorld.State n) (rng : R) :
    AdapterPublicWrapperState.Beacon view setup.joint
      (AdapterBeaconConstructorKem.after before pair world).pool
      (stored setup generator view edSample ed kxSample kx kem serverId mlPin keyId identity prekey before pair rng)
      (RegistrationNativeBeaconBirth.owner setup source
        (RegistrationNativeBeaconCreateProgram.pin (view.edPublic serverId) mlPin keyId) identity prekey
        (before.pool.keys.length, pair.1) world.owners.length)
      ((appendWorld keyId (view.edPublic serverId) world).owners[world.owners.length]?) := by
  constructor
  · exact ed.publicView _
  · exact ed.privateView _
  · rfl
  · rfl
  · rfl
  · refine ⟨rfl, ⟨kx.privateView _, kx.publicView _⟩, ?_, ?_⟩
    · exact AdapterBeaconConstructorKem.key_material view kem before pair world rng
    · simp [appendWorld, PqxdhRecordLiftWorld.chargeEffect]

end BeaconcryptCore.Refinement.AdapterBeaconConstructorMaterial

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorMaterial.append_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorMaterial.append_source

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorMaterial.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorMaterial.initial
