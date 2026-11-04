-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDictionaries
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildBackend
/-! Actual source Builder prefix leaves preserve their full returned source values and platform state through the physical quotient. Pin operands come from the actual opaque Server object, while only the private hash cut and administrative map observation are removed. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPrefixPrimitives
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend backend worldBackend)
open RegistrationNativePlatformPublicAdapterRecordBackend (project)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {n : Nat} {KemSK P : Type} {mlSource : RegistrationNativeMldsa.Source}
local notation "Native"=>RegistrationNativeExperiment.State n KemSK mlSource
local notation "Base"=>StateT P ProbComp
local notation "SourceM"=>StateT (RegistrationNativePlatformCutJournal.State Native) Base
local notation "M"=>StateT (Backend n KemSK) Base

theorem reserve_source (original : ContainerOperations (RustT Base)) (known : AdapterPublicWrapperStorage.PeerMap)
    (before :RegistrationNativePlatformCutJournal.State Native) :
    let :ContainerOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterBuildDictionaries.containers (n:=n) (source:=mlSource) original
    Prod.map id (fun current=>backend current.1) <$>
      ((ContainerOperations.mapReserve (m:=RustT SourceM) core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
        beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
        hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator known 1#usize).run).run before=
      (StateT.lift (original.mapReserve core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
        beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
        hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator known 1#usize).run :M _).run (backend before.1) := by
  change Prod.map id (fun current=>backend current.1) <$>
    (StateT.lift (original.mapReserve core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
      beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
      hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator known 1#usize).run :SourceM _).run before=_
  simp only [StateT.run_lift,bind_pure_comp,Functor.map_map]
  rfl

theorem contains_source (original : ContainerOperations (RustT Base)) (known : AdapterPublicWrapperStorage.PeerMap)
    (identifier :U64) (before :RegistrationNativePlatformCutJournal.State Native) :
    let :ContainerOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterBuildDictionaries.containers (n:=n) (source:=mlSource) original
    Prod.map id (fun current=>backend current.1) <$>
      ((ContainerOperations.mapContains (m:=RustT SourceM) core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
        beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
        hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
        core.U64.Insts.CoreHashHash (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq
          (core.borrow.Borrow.Blanket U64)) known identifier).run).run before=
      (StateT.lift (original.mapContains core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
        beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
        hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
        core.U64.Insts.CoreHashHash (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq
          (core.borrow.Borrow.Blanket U64)) known identifier).run :M _).run (backend before.1) := by
  let requested :Base (RustM Bool):=(original.mapContains core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
    beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
    hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
    core.U64.Insts.CoreHashHash (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq
      (core.borrow.Borrow.Blanket U64)) known identifier).run
  let charge (current :RegistrationNativePlatformCutJournal.State Native):=
    ({current.1 with server:=AdapterPublicServerPresenceNative.charged current.1.server 0#u64},current.2)
  change Prod.map id (fun current=>backend current.1) <$>
    ((requested >>=fun result=>pure (result,before)) >>=fun current=>
      (pure ((),charge current.2) >>=fun middle=>pure (current.1,middle.2)))=
    (requested >>=fun result=>pure (result,backend before.1))
  simp only [bind_assoc,pure_bind,map_bind,map_pure,Prod.map,id_eq]
  apply bind_congr
  intro reply
  congr 1
  simp only [charge,backend,worldBackend,AdapterPublicServerPresenceNative.charged,
    PqxdhRecordLiftWorld.chargeEffect,PqxdhRecordLiftInterface.effectKind,Function.update_idem]

noncomputable def hash (coins :QueryImpl unifSpec Base)
    (sign :registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply) (request :registration.HashRequest) :M RegistrationNativeServerPinRecompute.HashReply :=
  (fun digest=>RustM.ok (core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest))) <$>
    RegistrationNativePlatformPublicAdapterBuildBackend.outgoing coins sign (.hash request)

variable {I : Type} {base :OracleSpec I} {Reader Response :Type}
omit material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem hash_source (coins :QueryImpl unifSpec Base)
    (sign :registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply) (setup :PqxdhServerAuthExperiment.Setup base KemSK) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (request :registration.HashRequest) (before :RegistrationNativePlatformCutJournal.State Native) :
    Prod.map id (fun current=>backend current.1) <$>
      (AdapterPublicServerCutPin.hash coins sign request).run before=
      (hash coins sign request).run (backend before.1) := by
  have localLaw:=RegistrationNativePlatformPublicAdapterBuildBackend.outgoing_source coins setup codec sign before.1.pool (.hash request) before.1.server.world
  change (fun result=>(result.1,project before.1.pool result.2)) <$>
    (RegistrationNativePlatformServerCompletion.outgoing coins sign (.hash request)).run before.1.server.world=_ at localLaw
  have actual :Prod.map id backend <$>
      (AdapterPublicServerCutPin.outgoing coins sign (.hash request)).run before.1=
      (RegistrationNativePlatformPublicAdapterBuildBackend.outgoing coins sign (.hash request)).run (backend before.1) := by
    rw [AdapterPublicServerCutPin.outgoing,AdapterPublicServerLocalLens.local_run]
    simpa only [Functor.map_map,Prod.map,id_eq,AdapterPublicServerLocalLens.putLocal,project,backend] using localLaw
  have same:=congrArg (fun computation=>(fun result=>(RustM.ok (core.option.Option.Some (RegistrationAuthenticationShared.digestArray result.1)),result.2)) <$>computation) actual
  change Prod.map id (fun current=>backend current.1) <$>
    ((fun digest=>RustM.ok (core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest))) <$>
      RegistrationNativePlatformCutJournal.hash (AdapterPublicServerCutPin.outgoing coins sign) request).run before=_
  rw [StateT.run_map,RegistrationNativePlatformCutJournal.hash_run]
  unfold hash
  rw [StateT.run_map]
  simpa only [Functor.map_map,Prod.map,id_eq] using same

noncomputable def pin (coins :QueryImpl unifSpec Base)
    (sign :registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply) (view :AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (self :beaconcrypt_public_wrapper.server.Server) :M RegistrationNativeServerPinRecompute.PinReply :=
  simulateQ (hash (n:=n) (KemSK:=KemSK) coins sign) (RegistrationNativeServerPinRecompute.program
    ⟨view.edPublic (platform.arcView self.identity).identity_key.public_key,(platform.arcView self.identity).identity_key_kid⟩
    (view.mldsa (platform.arcView self.identity).mldsa_identity).publicKey)

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem pin_source {E :Type} (coins :QueryImpl unifSpec Base)
    (sign :registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply)
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (view :AdapterPublicWrapperState.MaterialView mlSource KemSK) (originalLocal :LocalOperations (RustT Base))
    (previousCrypto :CryptoOperations (RustT SourceM)) (previousChildren :ChildOperations (RustT SourceM))
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (self :beaconcrypt_public_wrapper.server.Server) (before :RegistrationNativePlatformCutJournal.State Native) :
    let :LocalOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterBuildDictionaries.locals (n:=n) view originalLocal
    let :CryptoOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterBuildDictionaries.crypto view previousCrypto
    let :ChildOperations (RustT SourceM):=AdapterPublicServerSigningNative.children
      (AdapterPublicServerCutPin.outgoing coins sign) previousChildren (AdapterPublicServerCompletionNative.writer writer)
    Prod.map id (fun current=>backend current.1) <$>
      ((beaconcrypt_public_request.server.Server.authentication_pin (m:=RustT SourceM) self).run).run before=
      (pin coins sign view self).run (backend before.1) := by
  let :LocalOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterBuildDictionaries.locals (n:=n) view originalLocal
  let :CryptoOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterBuildDictionaries.crypto view previousCrypto
  let :ChildOperations (RustT SourceM):=AdapterPublicServerSigningNative.children
    (AdapterPublicServerCutPin.outgoing coins sign) previousChildren (AdapterPublicServerCompletionNative.writer writer)
  dsimp only
  rw [AdapterPublicWrapperPin.server_program self _ _ (AdapterPublicServerCutPin.hash coins sign) rfl rfl (fun _=>rfl)]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (fun current=>backend current.1)
    (hash_source coins sign setup codec) _ before

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPrefixPrimitives


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPrefixPrimitives.reserve_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPrefixPrimitives.reserve_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPrefixPrimitives.contains_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPrefixPrimitives.contains_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPrefixPrimitives.hash_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPrefixPrimitives.hash_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPrefixPrimitives.pin_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPrefixPrimitives.pin_source
