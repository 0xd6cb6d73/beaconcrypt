-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRecordBackend
import BeaconcryptCore.Refinement.AdapterPublicServerCompletionNative
/-! The response builder's physical first-record and publication leaves retain all actual randomness, shared cache and platform effects. Only chronological signing and record-request instrumentation is erased. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildBackend
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSdkReification (Backend worldBackend)
open RegistrationNativePlatformPublicAdapterRecordBackend (project)
variable {n : Nat} {I KemSK E P A Reader Response : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK)
variable (codec : PqxdhServerAuthExperiment.Codec Reader Response)
local notation "Local"=>RegistrationServerRootCompiler.Local n
local notation "Base"=>StateT P ProbComp
local notation "M"=>StateT (Backend n KemSK) Base

noncomputable def initial (request : ratchet.InitialRatchetKdfRequest) : M (Std.Array U8 64#usize) :=
  pure (RawCtxSourceHkdf.initialResponse setup.source.crypto request).bytes

noncomputable def ratchet (request : ratchet.SymmetricRatchetKdfRequest) : M ratchet.RatchetKdfResponse :=fun before=>
  simulateQ coins ((RegistrationNativePlatformPublicAdapterRecordBackend.record setup codec (.inl request)).run before)

theorem initial_source (pool : PqxdhLiveKemBirth.Pool KemSK) (request : ratchet.InitialRatchetKdfRequest) (before : Local) :
    Prod.map id (project pool) <$>(AdapterPublicServerNativeKdf.initial (m:=Base) setup request).run before=
      (initial (n:=n) (KemSK:=KemSK) (P:=P) setup request).run (project pool before) := by
  simp only [AdapterPublicServerNativeKdf.initial,StateT.run_bind,StateT.run_modify,pure_bind,StateT.run_pure,map_pure]
  rfl

theorem ratchet_source (pool : PqxdhLiveKemBirth.Pool KemSK) (request : ratchet.SymmetricRatchetKdfRequest) (before : Local) :
    Prod.map id (project pool) <$>(AdapterPublicServerNativeKdf.ratchet coins setup codec request).run before=
      (ratchet coins setup codec request).run (project pool before) := by
  have same:=congrArg (simulateQ coins)
    (RegistrationNativePlatformPublicAdapterRecordBackend.record_source setup codec pool (.inl request) before)
  simp only [simulateQ_map] at same
  unfold AdapterPublicServerNativeKdf.ratchet
  simp only [StateT.run_bind,bind_pure_comp]
  exact same

noncomputable def rawOutgoing (sign : registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl RegistrationSigningShared.Spec (StateT (Backend n KemSK) ProbComp)
  | .hash request=>RegistrationNativePlatformPublicAdapterRecordBackend.hash (RegistrationInputs.hashBytes request)
  | .sign request _payload _digest=>fun before=>
      (fun result=>(result.1,{before with world:=worldBackend result.2})) <$>
        (PqxdhRecordLiftWorld.sampled (sign request)).run before.world

noncomputable def outgoing (sign : registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl RegistrationSigningShared.Spec M :=fun query before=>simulateQ coins ((rawOutgoing sign query).run before)

include setup codec in
theorem outgoing_source (sign : registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply)
    (pool : PqxdhLiveKemBirth.Pool KemSK) (query : RegistrationSigningShared.Spec.Domain) (before : Local) :
    Prod.map id (project pool) <$>(RegistrationNativePlatformServerCompletion.outgoing coins sign query).run before=
      (outgoing coins sign query).run (project pool before) := by
  have raw : Prod.map id (project pool) <$>
      (RegistrationNativePlatformServerCompletion.nativeOutgoing sign query).run before=
      (rawOutgoing (n:=n) (KemSK:=KemSK) sign query).run (project pool before) := by
    cases query with
    | hash request=>
      have same:=RegistrationNativePlatformPublicAdapterRecordBackend.shared_source setup codec pool
        (.inl ((),RegistrationInputs.hashBytes request)) before
      simpa only [RegistrationNativePlatformServerCompletion.nativeOutgoing,RegistrationWorldSigning.outgoing,
        RegistrationWorldRecords.shared,RegistrationNativePlatformPublicAdapterRecordBackend.shared,
        rawOutgoing,StateT.run,Functor.map_map,Prod.map,id_eq,project] using same
    | sign request payload digest=>
      simp only [RegistrationNativePlatformServerCompletion.nativeOutgoing,RegistrationWorldSigning.outgoing,
        rawOutgoing,PqxdhRecordLiftWorld.sampled,project,worldBackend,StateT.run,bind_pure_comp,Functor.map_map,Prod.map,id_eq]
      simp only [Function.update_idem]
  have same:=congrArg (simulateQ coins) raw
  change Prod.map id (project pool) <$>simulateQ coins
    ((RegistrationNativePlatformServerCompletion.nativeOutgoing sign query).run before)=
    simulateQ coins ((rawOutgoing sign query).run (project pool before))
  simpa only [simulateQ_map] using same

theorem write_source (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base)
    (pool : PqxdhLiveKemBirth.Pool KemSK) (request : record_effects.RecordWriteRequest) (before : Local) :
    Prod.map id (project pool) <$>(RegistrationNativePlatformSourceBuild.write helper request).run before=
      (StateT.lift (RegistrationNativePlatformSourceCompletion.writeWith helper request) :M _).run (project pool before) := by
  simp only [RegistrationNativePlatformSourceBuild.write_run,StateT.run_lift,bind_pure_comp,Functor.map_map]
  rfl

theorem in_cut_source
    (work : StateT (RegistrationServerRootCompiler.Local n) Base A) (physical : M A)
    (law : ∀pool current,Prod.map id (project pool) <$>work.run current=physical.run (project pool current))
    (before : RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) :
    Prod.map id (fun current=>RegistrationNativePlatformSdkReification.backend current.1) <$>
      (AdapterPublicServerCompletionNative.inCut work).run before=
      physical.run (RegistrationNativePlatformSdkReification.backend before.1) := by
  have same:=law before.1.pool before.1.server.world
  change (fun result=>(result.1,project before.1.pool result.2)) <$>work.run before.1.server.world=_ at same
  change Prod.map id (fun current=>RegistrationNativePlatformSdkReification.backend current.1) <$>
    ((fun result=>(result.1,(result.2,before.2))) <$>
      (AdapterPublicServerLocalLens.localState work).run before.1)=_
  rw [AdapterPublicServerLocalLens.local_run]
  simpa only [Functor.map_map,Prod.map,id_eq,AdapterPublicServerLocalLens.putLocal,
    project,RegistrationNativePlatformSdkReification.backend] using same

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildBackend


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildBackend.initial_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildBackend.initial_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildBackend.ratchet_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildBackend.ratchet_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildBackend.outgoing_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildBackend.outgoing_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildBackend.write_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildBackend.write_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildBackend.in_cut_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildBackend.in_cut_source
