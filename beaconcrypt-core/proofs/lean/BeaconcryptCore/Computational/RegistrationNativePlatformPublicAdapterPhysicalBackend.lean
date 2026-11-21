-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStore
/-! The indexed KEM transcript is a model observation log. The actual source primitive uses its opaque secret directly. Erasing that log preserves the exact private key roster, auxiliary state, cache, counters, frames and external state; no identity or private-key injectivity is required. The monitored native execution retains its full transcript for security analysis. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSdkReification (Backend backend)
variable {n : Nat} {KemSK Platform : Type} {mlSource : RegistrationNativeMldsa.Source}

def erase (before : Backend n KemSK) : Backend n KemSK :=
  {before with pool:={before.pool with transcript:=[]}}

theorem canonical (before : Backend n KemSK) :
    (erase before).pool.transcript=[] ∧(erase before).pool.keys=before.pool.keys ∧
    (erase before).auxiliary=before.auxiliary ∧(erase before).world=before.world :=⟨rfl,rfl,rfl,rfl⟩

theorem idempotent (before : Backend n KemSK) : erase (erase before)=erase before :=rfl

theorem erase_pool_record (before : Backend n KemSK) (query : PqxdhLiveKemBirth.Query)
    (reply : PqxdhLiveKemBirth.Range KemSK query) :
    erase {before with pool:=PqxdhLiveKemBirth.record query reply before.pool}=erase before :=rfl

theorem erase_world (before : Backend n KemSK) (after : PqxdhRecordLiftWorld.State n) :
    erase {before with world:=after}={erase before with world:=after} :=rfl

theorem erase_auxiliary (before : Backend n KemSK) (after : RegistrationServerRoleBackend.State) :
    erase {before with auxiliary:=after}={erase before with auxiliary:=after} :=rfl

theorem erase_created (before : Backend n KemSK) (pair : PqxdhKemIndCca.MlKem768PublicKey×KemSK) :
    erase {before with pool:=(PqxdhLiveKemBirth.created before.pool pair).2}=
      {erase before with pool:=⟨before.pool.keys++[pair],[]⟩} :=rfl

def persistent (before : Backend n KemSK×Platform) : Backend n KemSK×Platform :=(erase before.1,before.2)

theorem persistent_idempotent (before : Backend n KemSK×Platform) : persistent (persistent before)=persistent before :=rfl

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {R : Type}
open RegistrationNativePlatformPublicAdapterStore (Store)

def normalize (before : Store n KemSK R Platform) : Store n KemSK R Platform :=
  {before with backend:=persistent before.backend}

theorem normalize_idempotent (before : Store n KemSK R Platform) : normalize (normalize before)=normalize before :=rfl

theorem normalize_create (before : Store n KemSK R Platform) (returned : AdapterBeaconConstructorBody.Outcome R)
    (after : Backend n KemSK×Platform) :
    normalize (RegistrationNativePlatformPublicAdapterStore.create before returned after)=
      RegistrationNativePlatformPublicAdapterStore.create (normalize before) returned (persistent after) :=rfl

theorem normalize_accept (before : Store n KemSK R Platform) (returned : AdapterPublicServerAgreementReceipt.Word R)
    (after : Backend n KemSK×Platform) :
    normalize (RegistrationNativePlatformPublicAdapterStore.accept before returned after)=
      RegistrationNativePlatformPublicAdapterStore.accept (normalize before) returned (persistent after) :=rfl

theorem normalize_server (before : Store n KemSK R Platform) (returned : beaconcrypt_public_wrapper.server.Server)
    (after : Backend n KemSK×Platform) :
    normalize (RegistrationNativePlatformPublicAdapterStore.server before returned after)=
      RegistrationNativePlatformPublicAdapterStore.server (normalize before) returned (persistent after) :=rfl

theorem normalize_beacon (before : Store n KemSK R Platform) (index : Nat) (returned : beaconcrypt_public_wrapper.beacon.Beacon)
    (after : Backend n KemSK×Platform) :
    normalize (RegistrationNativePlatformPublicAdapterStore.beacon before index returned after)=
      RegistrationNativePlatformPublicAdapterStore.beacon (normalize before) index returned (persistent after) :=rfl

theorem normalize_bundle (before : Store n KemSK R Platform) (index : Nat)
    (returned : core.option.Option (alloc.vec.Vec U8)×beaconcrypt_public_wrapper.beacon.Beacon×R)
    (after : Backend n KemSK×Platform) :
    normalize (RegistrationNativePlatformPublicAdapterStore.bundle before index returned after)=
      RegistrationNativePlatformPublicAdapterStore.bundle (normalize before) index returned (persistent after) :=rfl

theorem normalize_move (before : Store n KemSK R Platform) (index : Nat) :
    normalize (RegistrationNativePlatformPublicAdapterStore.move before index)=
      RegistrationNativePlatformPublicAdapterStore.move (normalize before) index :=rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.canonical
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.idempotent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.erase_pool_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.erase_pool_record
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.erase_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.erase_world
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.erase_auxiliary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.erase_auxiliary
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.erase_created' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.erase_created
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.persistent_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.persistent_idempotent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize_idempotent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize_create
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize_accept
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize_server
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize_beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize_beacon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize_bundle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize_move' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize_move
