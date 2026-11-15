-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitialization
import BeaconcryptCore.Refinement.AdapterServerConstructorGeneration
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationPhysical
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
variable {n :Nat} {I KemSK R Error P :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [AdapterServerConstructorPrimitive.Standard]
variable [originalGenerators :AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto :CryptoOperations (RustT ProbComp)]
variable [originalLocal :LocalOperations (RustT (StateT P ProbComp))]
variable (setup :PqxdhServerAuthExperiment.Setup base KemSK)
variable (generator :rand_core.TryCryptoRng R Error) (view :AdapterPublicWrapperState.MaterialView source KemSK)
local notation "World"=>PqxdhRecordLiftWorld.State n
local notation "WorldM"=>StateT (PqxdhRecordLiftWorld.State n) ProbComp
noncomputable local instance generators :AdapterBeaconConstructorRequestMonad.Operations (RustT WorldM):=
  RegistrationNativePlatformPublicAdapterInitialization.generators (n:=n)
noncomputable local instance cryptography :CryptoOperations (RustT WorldM):=
  RegistrationNativePlatformPublicAdapterInitialization.cryptography (n:=n)
noncomputable local instance children :ChildOperations (RustT WorldM):=
  RegistrationNativePlatformPublicAdapterInitialization.children (n:=n)

noncomputable def raw (previous :P) (identityIndex :Nat) (identifier :U64) (rng :R) :=
  letI :LocalOperations (RustT WorldM):=RegistrationNativePlatformPublicAdapterInitialization.localOperations (n:=n) previous
  (AdapterServerConstructorRunner.run (n:=n) setup view identityIndex identifier generator rng).run PqxdhRecordLiftWorld.initial

noncomputable def sample (previous :P) (identityIndex :Nat) (identifier :U64) (rng :R) :=
  PFunctor.FreeM.attachSupp (raw (n:=n) setup generator view previous identityIndex identifier rng)

omit [PublicWrapperPlatform.Allocator] in
theorem source_erasure (previous :P) (identityIndex :Nat) (identifier :U64) (rng :R) :
    Subtype.val <$>sample (n:=n) setup generator view previous identityIndex identifier rng=
      raw (n:=n) setup generator view previous identityIndex identifier rng :=
  PFunctor.FreeM.map_attachSupp _

noncomputable def receipt (previous :P) (identityIndex :Nat) (identifier :U64) (rng :R)
    (packet :{value //value∈support (raw (n:=n) setup generator view previous identityIndex identifier rng)}) :
    letI :LocalOperations (RustT WorldM):=RegistrationNativePlatformPublicAdapterInitialization.localOperations (n:=n) previous
    {value //value∈support (AdapterServerConstructorRunner.game (n:=n) setup view identityIndex identifier generator rng)} :=by
  refine ⟨packet.val.1,?_⟩
  change packet.val.1∈support (Prod.fst <$>raw (n:=n) setup generator view previous identityIndex identifier rng)
  rw [support_map]
  exact ⟨packet.val,packet.property,rfl⟩

omit [PublicWrapperPlatform.Allocator] in
theorem ready_shape (previous :P) (identityIndex :Nat) (identifier :U64) (rng :R)
    (result :AdapterServerConstructorRunner.Receipt n KemSK R source×PqxdhRecordLiftWorld.State n)
    (ready :AdapterServerConstructorInitialized.Ready n KemSK R source)
    (supported :result∈support (raw (n:=n) setup generator view previous identityIndex identifier rng))
    (returned :result.1.ready=some ready) :
    ready.initial.state.server.world.auxiliary=RegistrationServerRoleBackend.empty ∧
    ready.initial.state.pool=PqxdhLiveKemBirth.empty ∧ready.initial.state.server.world.world.1=result.2 :=by
  let :LocalOperations (RustT WorldM):=RegistrationNativePlatformPublicAdapterInitialization.localOperations (n:=n) previous
  simp only [raw,AdapterServerConstructorRunner.run,StateT.run_bind,bind_pure_comp,mem_support_bind_iff] at supported
  obtain ⟨⟨called,current⟩,_generated,continued⟩:=supported
  cases called with
  | fail error | div=>
    cases continued
    cases returned
  | ok outcome=>
    rcases outcome with ⟨selected,nextRng⟩
    cases selected with
    | Err error=>
      cases continued
      cases returned
    | Ok self=>
      simp only [StateT.run_map,support_map] at continued
      obtain ⟨finished,reached,same⟩:=continued
      cases same
      unfold AdapterServerConstructorInitialized.finish at reached
      simp only [StateT.run,mem_support_bind_iff] at reached
      obtain ⟨installed,_installed,pinned,_pinned,closed⟩:=reached
      simp only [mem_support_pure_iff] at closed
      cases closed
      cases calledPin:pinned.1 with
      | fail error | div=>simp only [calledPin] at returned;cases returned
      | ok optional=>cases optional with
        | none=>simp only [calledPin] at returned;cases returned
        | some pin=>
          simp only [calledPin,Option.some.injEq] at returned
          cases returned
          exact ⟨rfl,rfl,rfl⟩

def initialStore (world :PqxdhRecordLiftWorld.State n)
    (ready :AdapterServerConstructorInitialized.Ready n KemSK R source) (previous :P) :
    RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P :=
  ⟨ready.stored,(fun _=>none),(fun _=>none),ready.rng,0,0,
    (⟨RegistrationServerRoleBackend.empty,PqxdhLiveKemBirth.empty,
      RegistrationNativePlatformSdkReification.worldBackend world⟩,previous)⟩

variable (views :AdapterPublicWrapperStorage.Views) (objects :AdapterServerConstructorObjects.Leaves views)
variable (ensureInit :StateT Unit ProbComp Bool)
variable (serverEd :AdapterServerConstructorJoint.EdContract generator view setup.joint (AdapterServerConstructorStartup.edCore ensureInit))
variable (ml :AdapterServerConstructorGeneration.MldsaContract generator view (RegistrationNativeMldsa.generate source))
variable (edGetter :∀key,originalCrypto.edPublicBytes key=pure (view.edPublic key))
variable (mlGetter :∀identity,(originalLocal.auth_MldsaIdentity_public_key identity).run=pure (.ok (view.mldsa identity).publicKey))

omit [PublicWrapperPlatform.Allocator] in
include objects serverEd ml edGetter mlGetter in
theorem native (previous :P) (identityIndex :Nat) (identifier :U64) (rng :R) :
    (fun packet=>AdapterServerConstructorRunner.nativeView packet.val.1) <$>
      sample (n:=n) setup generator view previous identityIndex identifier rng=
      RegistrationNativeExperiment.start (n:=n) setup source ensureInit identityIndex identifier :=by
  let :LocalOperations (RustT WorldM):=RegistrationNativePlatformPublicAdapterInitialization.localOperations (n:=n) previous
  have original:=AdapterServerConstructorRunner.native setup generator view views objects ensureInit
    (RegistrationNativePlatformPublicAdapterInitialization.signing (n:=n) setup generator view ensureInit serverEd)
    (RegistrationNativePlatformPublicAdapterInitialization.mldsa (n:=n) generator view ml)
    (RegistrationNativePlatformPublicAdapterInitialization.ed_public (n:=n) view edGetter)
    (RegistrationNativePlatformPublicAdapterInitialization.ml_public (n:=n) view mlGetter previous)
    identityIndex identifier rng
  have erased:=congrArg (fun computation=>(fun result=>AdapterServerConstructorRunner.nativeView result.1) <$>computation)
    (source_erasure (n:=n) setup generator view previous identityIndex identifier rng)
  simp only [Functor.map_map] at erased
  exact erased.trans (by simpa only [raw,AdapterServerConstructorRunner.game,Functor.map_map] using original)

include objects serverEd ml edGetter mlGetter in
noncomputable def carrier (previous :P) (identityIndex :Nat) (identifier :U64) (rng :R)
    (packet :{value //value∈support (raw (n:=n) setup generator view previous identityIndex identifier rng)})
    (ready :AdapterServerConstructorInitialized.Ready n KemSK R source) (returned :packet.val.1.ready=some ready) :=
  RegistrationNativePlatformPublicAdapterInitialization.carrier setup generator view views objects ensureInit serverEd ml edGetter mlGetter
    previous identityIndex identifier rng packet.val.1 ready
    (receipt (n:=n) setup generator view previous identityIndex identifier rng packet).property returned

omit [PublicWrapperPlatform.Allocator] in
include objects serverEd ml edGetter mlGetter in
theorem physical (previous :P) (identityIndex :Nat) (identifier :U64) (rng :R)
    (packet :{value //value∈support (raw (n:=n) setup generator view previous identityIndex identifier rng)})
    (ready :AdapterServerConstructorInitialized.Ready n KemSK R source) (returned :packet.val.1.ready=some ready) :
    RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize
      (RegistrationNativePlatformPublicAdapterStore.erase
        (carrier setup generator view views objects ensureInit serverEd ml edGetter mlGetter
          previous identityIndex identifier rng packet ready returned).base.objects)=
      initialStore packet.val.2 ready previous :=by
  have shape:=ready_shape setup generator view previous identityIndex identifier rng packet.val ready packet.property returned
  change (⟨ready.stored,(fun _=>none),(fun _=>none),ready.rng,0,0,
    (⟨ready.initial.state.server.world.auxiliary,{ready.initial.state.pool with transcript:=[]},
      RegistrationNativePlatformSdkReification.worldBackend ready.initial.state.server.world.world.1⟩,previous)⟩ :
      RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P)=_
  rw [shape.1,shape.2.1,shape.2.2]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationPhysical
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationPhysical.source_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationPhysical.source_erasure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationPhysical.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationPhysical.native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationPhysical.ready_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationPhysical.ready_shape

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationPhysical.physical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationPhysical.physical
