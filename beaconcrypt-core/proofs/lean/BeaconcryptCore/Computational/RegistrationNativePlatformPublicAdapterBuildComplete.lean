-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPublication
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildInstall
/-! Actual SDK first-record/publication and source map installation retain one physical execution. The normalized source interpreter keeps the same returned Server and publication receipt and executes the original container operations on the original persistent platform state. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildComplete
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend backend)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [primitive : AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {n : Nat} {I KemSK E P : Type} {base : OracleSpec I} {Reader Response : Type}
variable {mlSource : RegistrationNativeMldsa.Source}
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
variable (erased : commitment.CommitmentTranscript)
variable (sign : registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply)
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
local notation "Native"=>RegistrationNativeExperiment.State n KemSK mlSource
local notation "Local"=>RegistrationServerRootCompiler.Local n
local notation "Base"=>StateT P ProbComp
local notation "SourceM"=>StateT (RegistrationNativePlatformCutJournal.State Native) Base
local notation "M"=>StateT (Backend n KemSK) Base

noncomputable def complete (original : ContainerOperations (RustT Base))
    (self :beaconcrypt_public_wrapper.server.Server) (initial :registration.ServerInitialKdf) :=
  letI :ContainerOperations (RustT Base):=original
  (do
    let published←RegistrationNativePlatformPublicAdapterBuildPublication.beforeInstall coins setup codec view failure allocation helper erased sign writer initial
    let word←StateT.lift (AdapterPublicServerPublication.afterPublication (m:=Base) self published)
    pure (published,word) :M _)

theorem source (original : ContainerOperations (RustT Base))
    (fallback : registration.MldsaSigningRequest→StateT Native Base RegistrationSigningShared.SignReply)
    (self :beaconcrypt_public_wrapper.server.Server) (initial :registration.ServerInitialKdf)
    (before :RegistrationNativePlatformCutJournal.State Native) :
    let :ContainerOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterBuildDictionaries.containers (n:=n) (source:=mlSource) original
    Prod.map id (fun current=>backend current.1) <$>
      (AdapterPublicServerBuildTrace.complete coins setup codec view failure allocation helper erased sign writer fallback self initial).run before=
      (complete coins setup codec view failure allocation helper erased sign writer original self initial).run (backend before.1) := by
  let :ContainerOperations (RustT Base):=original
  let :ContainerOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterBuildDictionaries.containers (n:=n) (source:=mlSource) original
  have installer (published) : AdapterPublicServerPublication.afterPublication (m:=SourceM) self published=
      StateT.lift (AdapterPublicServerPublication.afterPublication (m:=Base) self published) := by
    exact RegistrationNativePlatformPublicAdapterBuildInstall.after_publication original self published
  dsimp only
  unfold AdapterPublicServerBuildTrace.complete AdapterPublicServerCompletionSource.receipt complete
  simp_rw [installer]
  simp only [StateT.run_bind,StateT.run_pure,map_bind]
  rw [←RegistrationNativePlatformPublicAdapterBuildPublication.cut_source coins setup codec view failure allocation helper erased sign writer fallback initial before,
    bind_map_left]
  apply bind_congr
  rintro ⟨published,current⟩
  simp only [StateT.run_lift,map_pure,bind_assoc,pure_bind,Prod.map,id_eq]

theorem record_source (previousLocal : LocalOperations (RustT SourceM))
    (previousChildren : ChildOperations (RustT SourceM)) (original : ContainerOperations (RustT Base))
    (fallback : registration.MldsaSigningRequest→StateT Native Base RegistrationSigningShared.SignReply)
    (self :beaconcrypt_public_wrapper.server.Server) (initial :registration.ServerInitialKdf)
    (before :RegistrationNativePlatformCutJournal.State Native) :
    let :ContainerOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterBuildDictionaries.containers (n:=n) (source:=mlSource) original
    let :LocalOperations (RustT SourceM):=AdapterPublicServerCompletionSource.localOperations
      (fun {A} (work :StateT Local Base A)=>AdapterPublicServerCompletionNative.inCut work)
      (AdapterPublicServerCompletionNative.outgoing coins sign) fallback previousLocal coins setup codec view failure allocation helper
    let :ChildOperations (RustT SourceM):=AdapterPublicServerCompletionSource.children
      (fun {A} (work :StateT Local Base A)=>AdapterPublicServerCompletionNative.inCut work)
      (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
      (AdapterPublicServerCompletionNative.writer writer)
    Prod.map id (fun current=>backend current.1) <$>
      (AdapterPublicServerBuildBody.record (m:=SourceM) self initial).run before=
      (Prod.snd <$>complete coins setup codec view failure allocation helper erased sign writer original self initial).run (backend before.1) := by
  let :ContainerOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterBuildDictionaries.containers (n:=n) (source:=mlSource) original
  dsimp only
  rw [AdapterPublicServerCompletionLifetime.source_marginal previousLocal previousChildren coins setup codec view failure allocation helper erased sign writer fallback self initial,
    StateT.run_map]
  change Prod.map id (fun current=>backend current.1) <$>
    (Prod.map Prod.snd id <$>
      (AdapterPublicServerBuildTrace.complete coins setup codec view failure allocation helper erased sign writer fallback self initial).run before)=_
  have same:=congrArg (fun computation=>(fun result=>(result.1.2,result.2)) <$>computation)
    (source coins setup codec view failure allocation helper erased sign writer original fallback self initial before)
  simpa only [Functor.map_map,Prod.map,id_eq] using same

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildComplete


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildComplete.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildComplete.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildComplete.record_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildComplete.record_source
