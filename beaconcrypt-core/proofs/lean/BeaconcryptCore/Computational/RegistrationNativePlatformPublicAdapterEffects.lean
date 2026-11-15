-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterWorldStore
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic
import BeaconcryptCore.Computational.RegistrationNativePlatformPackedState
/-! Direct experiment coin and hash observations run through the same persistent source World and platform, preserving every public-adapter object. Their next material relation is derived from the literal primitive interpreter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffects
open BeaconcryptCore.Refinement
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
variable {n : Nat} {I KemSK R Platform : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
abbrev Spec := unifSpec + (Pqxdh.Bytes →ₒ CtxRomAuth.CtxDigest)

noncomputable def world : QueryImpl Spec (StateT (PqxdhRecordLiftWorld.State n) ProbComp)
  | .inl coin=>PqxdhRecordLiftWorld.effects (.inl coin)
  | .inr bytes=>PqxdhRecordLiftWorld.effects (.inr (.hash bytes))

private theorem sampled_frame {A : Type} (work : ProbComp A) (before : PqxdhRecordLiftWorld.State n)
    (result : A ×PqxdhRecordLiftWorld.State n) (supported : result∈support ((PqxdhRecordLiftWorld.sampled work).run before)) :
    (result.2.server,result.2.owners)=(before.server,before.owners) := by
  simp only [PqxdhRecordLiftWorld.sampled,StateT.run,bind_pure_comp,support_map] at supported
  obtain ⟨draw,_called,rfl⟩:=supported
  rfl

theorem frame (query : Spec.Domain) (before : PqxdhRecordLiftWorld.State n)
    (result : Spec.Range query ×PqxdhRecordLiftWorld.State n) (supported : result∈support ((world query).run before)) :
    (result.2.server,result.2.owners)=(before.server,before.owners) := by
  cases query with
  | inl coin=>exact sampled_frame _ (PqxdhRecordLiftWorld.chargeEffect (.inl coin) before) result supported
  | inr bytes=>
    simp only [world,PqxdhRecordLiftWorld.effects,PqxdhRecordLiftWorld.capability,StateT.run,mem_support_bind_iff] at supported
    obtain ⟨middle,called,returned⟩:=supported
    simp only [support_pure,Set.mem_singleton_iff] at returned
    cases returned
    exact sampled_frame _ (PqxdhRecordLiftWorld.chargeEffect (.inr (.hash bytes)) before) middle called

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK)
variable (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (current : RegistrationNativeExperiment.State n KemSK source ×Platform)
variable (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)

noncomputable def step (query : Spec.Domain) :
    TotalStep (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
      (RegistrationNativePlatformExtractedSdkAdaptive.pack <$>
        (((RegistrationNativePlatformExperiment.liftNative coins (RegistrationNativeExperiment.world (world query))).run current.1).run current.2)) := by
  let sample:=(simulateQ coins ((world query).run current.1.server.world.world.1)).run current.2
  let post:=fun packet : (Spec.Range query ×PqxdhRecordLiftWorld.State n) ×Platform =>
    (AdapterPublicAgreementNativeWorldMap.putWorld current.1 packet.1.2,packet.2)
  refine {step:={
    Packet:=(Spec.Range query ×PqxdhRecordLiftWorld.State n) ×Platform
    sample:=sample
    sourceType:=Spec.Range query
    sourceReply:=fun packet=>.ok packet.1.1
    sourceState:=post
    sourceCall:=(fun packet=>(.ok packet.1.1,post packet)) <$>sample
    source_exact:=rfl
    native:=fun packet=>(packet.1.1,post packet)
    native_exact:=?_
    store:=?_},observe:=id,normal:=?_,reply:=?_}
  · unfold RegistrationNativePlatformExperiment.liftNative
    change (fun packet=>(packet.1.1,post packet)) <$>sample=
      RegistrationNativePlatformExtractedSdkAdaptive.pack <$>
        (simulateQ coins ((RegistrationNativeExperiment.world (world query)).run current.1)).run current.2
    rw [AdapterPublicAgreementNativeWorldMap.world_run,simulateQ_map,StateT.run_map,Functor.map_map]
    rfl
  · intro packet supported
    have nativeReached : packet.1∈support ((world query).run current.1.server.world.world.1) := by
      apply OracleComp.support_simulateQ_run'_subset coins _ current.2
      rw [StateT.run'_eq,support_map]
      exact ⟨packet,supported,rfl⟩
    have retained:=frame query current.1.server.world.world.1 packet.1 nativeReached
    exact RegistrationNativePlatformPublicAdapterWorldStore.update setup view views created credential current before packet.1.2 packet.2
      (congrArg Prod.fst retained) (congrArg Prod.snd retained)
  · intro packet _supported
    exact ⟨packet.1.1,rfl⟩
  · intro packet _supported returned actual
    exact (RustM.ok.inj actual).symm

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffects
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffects.frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffects.frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffects.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffects.step
