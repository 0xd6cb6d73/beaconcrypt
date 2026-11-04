-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLeaves
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongServerBuildStep
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPinArrays
/-! The actual Builder reads opaque public identities and source containers. Its analysis dictionary adds only the chronological administrative map-query observation; reserve, entry and insertion execute the same individual source operations and retain their platform poststates. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDictionaries
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperStorage
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {n : Nat} {KemSK P : Type} {source : RegistrationNativeMldsa.Source}
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "Base"=>StateT P ProbComp
local notation "M"=>StateT (RegistrationNativePlatformCutJournal.State Native) Base

@[instance_reducible] def locals (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (original : LocalOperations (RustT Base)) : LocalOperations (RustT M) :=
  {RegistrationNativePlatformPublicAdapterLeaves.localOperations original with
    auth_MldsaIdentity_public_key:=fun identity=>pure (view.mldsa identity).publicKey}

@[instance_reducible] def crypto (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (previous : CryptoOperations (RustT M)) : CryptoOperations (RustT M) :=
  {previous with edPublicBytes:=fun key=>pure (view.edPublic key)}

@[instance_reducible] def containers (original : ContainerOperations (RustT Base)) : ContainerOperations (RustT M) :=
  {RegistrationNativePlatformPublicAdapterLeaves.containerOperations original with
    mapContains:=fun eq hash build allocate hashQuery equivalent collection query=>⟨do
      let result←StateT.lift (original.mapContains eq hash build allocate hashQuery equivalent collection query).run
      modify fun current=>({current.1 with server:=AdapterPublicServerPresenceNative.charged current.1.server 0#u64},current.2)
      pure result⟩}

theorem reserve (original : ContainerOperations (RustT Base)) (self : beaconcrypt_public_wrapper.server.Server)
    (allocated : Base AdapterPublicServerBuildPrefix.AllocationReply)
    (operation : (original.mapReserve core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
      beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
      hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator self.known_ids 1#usize).run=
      RustM.ok <$>allocated) :
    let : ContainerOperations (RustT M):=containers (n:=n) (source:=source) original
    (ContainerOperations.mapReserve (m:=RustT M) core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
      beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
      hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator self.known_ids 1#usize).run=
      RustM.ok <$>StateT.lift allocated := by
  change StateT.lift (original.mapReserve core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
    beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
    hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator self.known_ids 1#usize).run=_
  rw [operation]
  apply StateT.ext
  intro current
  simp only [StateT.run_lift,StateT.run_map,Functor.map_map,bind_pure_comp]

theorem contains (original : ContainerOperations (RustT Base)) (views : Views) (self : beaconcrypt_public_wrapper.server.Server) (identifier : U64)
    (operation : (original.mapContains core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
      beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
      hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
      core.U64.Insts.CoreHashHash (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq
        (core.borrow.Borrow.Blanket U64)) self.known_ids identifier).run=
      pure (RustM.ok (views.peer self.known_ids identifier).isSome))
    (current : RegistrationNativePlatformCutJournal.State Native) :
    let : ContainerOperations (RustT M):=containers (n:=n) (source:=source) original
    ((ContainerOperations.mapContains (m:=RustT M) core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
      beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
      hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
      core.U64.Insts.CoreHashHash (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq
        (core.borrow.Borrow.Blanket U64)) self.known_ids identifier).run).run current=
      pure (RustM.ok (views.peer self.known_ids identifier).isSome,
        ({current.1 with server:=AdapterPublicServerPresenceNative.charged current.1.server identifier},current.2)) := by
  change (do
    let result←StateT.lift (original.mapContains core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
      beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
      hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
      core.U64.Insts.CoreHashHash (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq
        (core.borrow.Borrow.Blanket U64)) self.known_ids identifier).run
    modify fun current : RegistrationNativePlatformCutJournal.State Native=>
      ({current.1 with server:=AdapterPublicServerPresenceNative.charged current.1.server 0#u64},current.2)
    pure result : M _).run current=_
  rw [operation]
  simp only [StateT.run_bind,StateT.run_lift,pure_bind,StateT.run_modify,StateT.run_pure]
  rfl

noncomputable def standard (original : ContainerOperations (RustT Base)) (views : Views) (self : beaconcrypt_public_wrapper.server.Server)
    (pending : peer.PeerInsert (alloc.vec.Vec U8)) (publicKey : ed.PublicKey)
    (law : let : ContainerOperations (RustT Base):=original
      AdapterPublicServerInstallFunctional.Standard (m:=Base) views self pending publicKey) :
    let : ContainerOperations (RustT M):=containers (n:=n) (source:=source) original
    AdapterPublicServerInstallFunctional.Standard (m:=M) views self pending publicKey := by
  let : ContainerOperations (RustT Base):=original
  let : ContainerOperations (RustT M):=containers (n:=n) (source:=source) original
  dsimp only at law ⊢
  refine ⟨(AdapterPublicServerInstallFunctional.Standard.entryReply (m:=Base) law), ?_,
    (AdapterPublicServerInstallFunctional.Standard.entryFootprint (m:=Base) law), ?_⟩
  · change (⟨StateT.lift (AdapterPublicServerInstall.entry (m:=Base) self.known_ids pending.peer.binding.assigned_key_id).run⟩ : RustT M _)=_
    rw [(AdapterPublicServerInstallFunctional.Standard.entryNormal (m:=Base) law)]
    rfl
  · intro vacant back same
    obtain ⟨result,inserted,footprint⟩:=AdapterPublicServerInstallFunctional.Standard.insertNormal (m:=Base) law vacant back same
    refine ⟨result,?_,footprint⟩
    change (⟨StateT.lift (AdapterPublicServerInstall.insert (m:=Base) vacant (AdapterPublicServerInstall.remote pending publicKey)).run⟩ :RustT M _)=_
    rw [inserted]
    rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDictionaries


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDictionaries.locals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDictionaries.locals

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDictionaries.crypto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDictionaries.crypto

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDictionaries.containers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDictionaries.containers

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDictionaries.reserve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDictionaries.reserve

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDictionaries.contains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDictionaries.contains

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDictionaries.standard' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDictionaries.standard
