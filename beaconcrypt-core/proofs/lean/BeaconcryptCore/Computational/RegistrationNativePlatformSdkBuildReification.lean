-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerReification
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkBuildReification
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSdkReification RegistrationNativePlatformSdkServerReification
variable {n : Nat} {KemSK Platform : Type} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
private def attempts (world : PqxdhRecordLiftWorld.State n) : Nat :=
  (world.server.map (fun records=>records.records.rawAttempts)).getD 0
private def recordless (world : PqxdhRecordLiftWorld.State n) := worldBackend {world with server:=none}
private def image (before : RegistrationServerFrontendCompiler.State n) :=
  (before.world.auxiliary,recordless before.world.world.1,attempts before.world.world.1)
private theorem known (keyId : U64) (binding : PqxdhRecordLiftInterface.PeerBinding)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (before : PqxdhRecordLiftWorld.State n)
    (result : Bool×PqxdhRecordLiftWorld.State n)
    (supported : result∈support ((PqxdhRecordLiftWorld.effects (.inr (.installServer keyId binding (.known kernel)))).run before)) :
    (recordless result.2,attempts result.2)=(recordless before,attempts before) := by
  simp only [PqxdhRecordLiftWorld.effects,PqxdhRecordLiftWorld.capability,StateT.run] at supported
  unfold PqxdhRecordLiftWorld.installServer at supported
  cases server:before.server with
  | none =>
    simp only [PqxdhRecordLiftWorld.chargeEffect,server,support_pure,Set.mem_singleton_iff] at supported
    subst result
    simp only [recordless,worldBackend,PqxdhRecordLiftInterface.effectKind,Function.update_idem,attempts,server]
  | some server =>
    simp only [PqxdhRecordLiftWorld.chargeEffect,server] at supported
    split at supported
    · simp only [PqxdhRecordLiftWorld.resolve,PqxdhRecordLiftWorld.markUsed,StateT.run_pure,pure_bind,support_pure,Set.mem_singleton_iff] at supported
      subst result
      simp only [recordless,worldBackend,PqxdhRecordLiftInterface.effectKind,Function.update_idem,attempts,server,Option.map_some,Option.getD_some]
    · simp only [support_pure,Set.mem_singleton_iff] at supported
      subst result
      simp only [recordless,worldBackend,PqxdhRecordLiftInterface.effectKind,Function.update_idem,attempts,server,Option.map_some,Option.getD_some]
private theorem capability (pending : peer.PeerInsert (alloc.vec.Vec U8))
    (before : RegistrationServerFrontendCompiler.State n) (result : Bool×RegistrationServerFrontendCompiler.State n)
    (supported : result∈support ((AdapterPublicServerInstallNative.capability pending).run before)) : image result.2=image before := by
  simp only [AdapterPublicServerInstallNative.capability,RegistrationNativePlatformServerSdk.world,
    RegistrationWorldServerCompletion.capability,StateT.run,support_map] at supported
  obtain ⟨middle,called,rfl⟩:=supported
  obtain ⟨inner,called,rfl⟩:=called
  have kept:=known pending.peer.binding.assigned_key_id (PqxdhRecordLiftInterface.PeerBinding.ofSession pending.peer.binding)
    pending.peer.ratchet before.world.world.1 inner called
  exact congrArg (fun rest=>(before.world.auxiliary,rest)) kept
private theorem commit (reply : RustM (RegistrationWorldServerCompletion.Result (alloc.vec.Vec U8)))
    (before : RegistrationServerFrontendCompiler.State n) (result)
    (supported : result∈support ((RegistrationNativePlatformServerSdk.commit (m:=ProbComp) reply).run before)) :
    image result.2=image before := by
  cases reply with
  | fail error | div =>
    simp only [RegistrationNativePlatformServerSdk.commit,StateT.run,support_pure,Set.mem_singleton_iff] at supported
    subst result
    rfl
  | ok reply =>
    cases reply <;>
      simp only [RegistrationNativePlatformServerSdk.commit,StateT.run,support_pure,Set.mem_singleton_iff] at supported <;>
      subst result <;> rfl
private theorem world_pure {A : Type} (value : A) :
    RegistrationNativePlatformServerSdk.world (pure value : StateT (RegistrationServerRootCompiler.Local n) ProbComp A)=
      (pure value : StateT (RegistrationServerFrontendCompiler.State n) ProbComp A) := by
  apply StateT.ext
  intro before
  change (fun result=>(result.1,{before with world:=result.2})) <$>pure (value,before.world)=pure (value,before)
  rw [map_pure]
private theorem lift_id {A : Type} (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp A) :
    RegistrationNativePlatformServerSdk.liftNative (QueryImpl.id' unifSpec) work=work := by
  funext before
  exact simulateQ_id' (work.run before)
private theorem publication (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)))
    (before : RegistrationServerFrontendCompiler.State n) (result)
    (supported : result∈support ((AdapterPublicServerPublicationInstall.native (QueryImpl.id' unifSpec) control published).run before)) :
    image result.2=image before := by
  cases published with
  | fail error | div =>
    simp only [AdapterPublicServerPublicationInstall.native,RegistrationNativePlatformServerCompletion.continueResult,
      world_pure,pure_bind] at supported
    exact commit _ before result supported
  | ok published => cases published with
    | Err rejected =>
      simp only [AdapterPublicServerPublicationInstall.native,RegistrationNativePlatformServerCompletion.continueResult,
        world_pure,pure_bind] at supported
      exact commit _ before result supported
    | Ok published =>
      obtain ⟨reply,began,_retained⟩:=PeerOwnership.peer_insert_begin_retains control published
      cases reply with
      | Err rejected =>
        simp only [AdapterPublicServerPublicationInstall.native,RegistrationNativePlatformServerCompletion.continueResult,
          RegistrationNativePlatformServerCompletion.installWith,began,world_pure,pure_bind] at supported
        exact commit _ before result supported
      | Ok pending =>
        rw [AdapterPublicServerPublicationInstall.native_insert _ control published pending began] at supported
        simp only [StateT.run_bind,lift_id,mem_support_bind_iff] at supported
        obtain ⟨middle,called,continued⟩:=supported
        exact (commit _ middle.2 result continued).trans (capability pending before middle called)

private theorem tail (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)))
    (before : RegistrationServerFrontendCompiler.State n) :
    image (AdapterPublicServerTailCanonical.result control published before).2=image before := by
  apply publication control published before
  rw [AdapterPublicServerTailCanonical.native_run]
  exact Set.mem_singleton _

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
private theorem tail_native (control : pqxdh.ServerState)
    (publication : Option AdapterPublicServerBuildTrace.Publication) (raw : RegistrationNativePlatformCutJournal.State Native)
    (word : RustM AdapterPublicServerBuildBody.Reply) :
    image (AdapterPublicServerBuildPrefix.project control ((publication,word),raw)).2.server=image raw.1.server ∧
    (AdapterPublicServerBuildPrefix.project control ((publication,word),raw)).2.pool=raw.1.pool := by
  cases publication with
  | none => exact ⟨rfl,rfl⟩
  | some published => exact ⟨tail control published raw.1.server,rfl⟩

/-- Actual returned Server/map views reconstruct the known-install tail, preserving its reached backend. -/
theorem projected
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (control : pqxdh.ServerState) (publication : Option AdapterPublicServerBuildTrace.Publication)
    (word : AdapterPublicServerBuildBody.Reply) (raw : RegistrationNativePlatformCutJournal.State Native)
    (held : AdapterPublicWrapperState.Server view views created credential word.2
      (AdapterPublicServerBuildPrefix.project control ((publication,.ok word),raw)).2.server)
    (previous : Platform) :
    persistent (snapshot view views word.2 none (raw.1,previous)).committed=
      persistent ((AdapterPublicServerBuildPrefix.project control ((publication,.ok word),raw)).2,previous) := by
  let after:=(AdapterPublicServerBuildPrefix.project control ((publication,.ok word),raw)).2
  have kept:=tail_native control publication raw (.ok word)
  obtain ⟨records,present,matched⟩:=AdapterPublicOrdinaryServerReifier.related view views created credential word.2 after.server held
  have aux :=congrArg Prod.fst kept.1
  have erased:=congrArg (fun result=>result.2.1) kept.1
  have countEq:=congrArg (fun result=>result.2.2) kept.1
  change attempts after.server.world.world.1=attempts raw.1.server.world.world.1 at countEq
  change after.server.world.auxiliary=raw.1.server.world.auxiliary at aux
  change recordless after.server.world.world.1=recordless raw.1.server.world.world.1 at erased
  have counted : rawAttempts raw.1=records.records.rawAttempts := by
    change attempts raw.1.server.world.world.1=records.records.rawAttempts
    rw [←countEq]
    simp only [attempts,present,Option.map_some,Option.getD_some]
  have recordEq : some (AdapterPublicOrdinaryServerReifier.server view views word.2 (rawAttempts raw.1))=
      after.server.world.world.1.server := by rw [counted,matched]; exact present.symm
  have worldEq:=congrArg (fun world=>{world with server:=after.server.world.world.1.server}) erased.symm
  change worldBackend {raw.1.server.world.world.1 with server:=after.server.world.world.1.server}=
    worldBackend after.server.world.world.1 at worldEq
  change ((⟨raw.1.server.world.auxiliary,raw.1.pool,
    worldBackend {raw.1.server.world.world.1 with server:=some (AdapterPublicOrdinaryServerReifier.server view views word.2 (rawAttempts raw.1))}⟩ : Backend n KemSK),previous)=
    ((backend after),previous)
  rw [←kept.2,recordEq]
  exact Prod.ext (congrArg₂ (fun auxiliary world=>(⟨auxiliary,after.pool,world⟩ : Backend n KemSK)) aux.symm worldEq) rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkBuildReification

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkBuildReification.projected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkBuildReification.projected
