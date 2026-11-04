-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffects
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterNormalizedRaw
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalFrame
/-! The experiment's explicit coin and hash services use the same physical primitive cache and platform alongside actual adapter objects. Their full local source marginal is derived from the literal backend interpreter. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffectPhysical
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSdkReification (Backend backend persistent)
open RegistrationNativePlatformPublicAdapterStore (Store)
open RegistrationNativePlatformPublicAdapterEffects (Spec)
private theorem map_ok {A B : Type} (f : A→B) (value : A) :
    f <$>(RustM.ok value)=RustM.ok (f value) :=rfl
variable {n : Nat} {I KemSK R P : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)

noncomputable def leaf : QueryImpl Spec (StateT (Backend n KemSK) ProbComp)
  | .inl coin=>RegistrationNativePlatformSdkReification.backendLeaf setup checks representation created (.inl coin)
  | .inr bytes=>RegistrationNativePlatformSdkReification.backendLeaf setup checks representation created (.inr (.inl bytes))

theorem leaf_source (query : Spec.Domain) (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    Prod.map id backend <$>
      (RegistrationNativeExperiment.world (RegistrationNativePlatformPublicAdapterEffects.world query)).run before=
      (leaf setup checks representation created query).run (backend before) :=by
  cases query with
  | inl coin=>exact RegistrationNativePlatformSdkReification.coin_backend setup checks representation created coin before
  | inr bytes=>exact RegistrationNativePlatformSdkReification.hash_backend setup checks representation created bytes before

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]

def update {query : Spec.Domain} (before : Store n KemSK R P) (result : Spec.Range query×(Backend n KemSK×P)) :
    RustM (Spec.Range query×Store n KemSK R P)×(Backend n KemSK×P) :=
  (.ok (result.1,{before with backend:=result.2}),result.2)

noncomputable def run (coins : QueryImpl unifSpec (StateT P ProbComp)) (query : Spec.Domain)
    (before : Store n KemSK R P) :=
  (fun result=>update before (result.1.1,(result.1.2,result.2))) <$>
    (simulateQ coins ((leaf setup checks representation created query).run before.backend.1)).run before.backend.2

private theorem raw_native {N Reply : Type} {Private : N → Type} {target : ProbComp (Reply×N)}
    (call : RegistrationNativePlatformExtractedSdkPublic.TotalStep Private target)
    (physical : ∀current,Private current → Store n KemSK R P) (next : N → Store n KemSK R P)
    (retained : ∀packet,physical (call.step.native packet.val).2 (RegistrationNativePlatformExtractedSdkPublic.store call packet)=
      next (call.step.native packet.val).2) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw physical call=
      (fun result=>(RustM.ok (result.1,next result.2),(next result.2).backend)) <$>target :=by
  let observe:=fun result : Reply×N=>(RustM.ok (result.1,next result.2),(next result.2).backend)
  calc
    _=(fun packet=>observe (call.step.native packet.val)) <$>PFunctor.FreeM.attachSupp call.step.sample :=by
      unfold RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
      congr 1
      funext packet
      have reply:=call.reply packet.val packet.property (RegistrationNativePlatformExtractedSdkPublic.returned call packet)
        (RegistrationNativePlatformExtractedSdkPublic.returned_exact call packet)
      rw [reply,retained packet]
    _=(fun packet=>observe (call.step.native packet)) <$>call.step.sample :=by
      have same:=congrArg (fun computation=>(fun packet=>observe (call.step.native packet)) <$>computation)
        (RegistrationNativePlatformExtractedSdkAdaptive.attached_erase call.step.sample)
      simpa only [Functor.map_map] using same
    _=_:=by
      have same:=congrArg (fun computation=>observe <$>computation) call.step.native_exact
      simpa only [Functor.map_map] using same

theorem query (coins : QueryImpl unifSpec (StateT P ProbComp))
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : RegistrationNativeExperiment.State n KemSK mlSource×P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (selected : Spec.Domain) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
      (RegistrationNativePlatformSdkOrdinaryBeaconSelected.strongPhysical setup view views created credential)
      (RegistrationNativePlatformPublicAdapterEffects.step coins setup view views created credential current before selected)=
      run setup checks representation created coins selected (RegistrationNativePlatformPublicAdapterStore.erase before.base.objects) :=by
  let call:=RegistrationNativePlatformPublicAdapterEffects.step coins setup view views created credential current before selected
  let old:=RegistrationNativePlatformPublicAdapterStore.erase before.base.objects
  let next:=fun after : RegistrationNativeExperiment.State n KemSK mlSource×P=>{old with backend:=persistent after}
  have rawEq:=raw_native call (RegistrationNativePlatformSdkOrdinaryBeaconSelected.strongPhysical setup view views created credential)
    next (by intro packet;rfl)
  have sourceEq:=leaf_source setup checks representation created selected current.1
  have interpreted:=congrArg (fun computation=>(simulateQ coins computation).run current.2) sourceEq
  rw [simulateQ_map,StateT.run_map] at interpreted
  have mapped:=congrArg (fun computation=>(fun result=>update old (result.1.1,(result.1.2,result.2))) <$>computation) interpreted
  simp only [Functor.map_map,Prod.map,id_eq] at mapped
  have basis : old.backend=persistent current:=before.base.backend
  refine rawEq.trans ?_
  unfold run
  rw [basis]
  rw [Functor.map_map]
  change (fun result=> (RustM.ok (result.1.1,next (result.1.2,result.2)),(next (result.1.2,result.2)).backend)) <$>
    (simulateQ coins ((RegistrationNativeExperiment.world (RegistrationNativePlatformPublicAdapterEffects.world selected)).run current.1)).run current.2=_
  exact mapped

omit material platform ed in
theorem leaf_frame (selected : Spec.Domain) :
    RegistrationNativePlatformPublicAdapterPhysicalFrame.Compatible
      (leaf (n:=n) setup checks representation created selected) :=by
  intro before
  cases selected with
  | inl coin=>
    simp only [leaf,RegistrationNativePlatformSdkReification.backendLeaf,StateT.run,
      RegistrationNativePlatformPublicAdapterPhysicalBackend.erase]
    rw [Functor.map_map]
    rfl
  | inr bytes=>
    simp only [leaf,RegistrationNativePlatformSdkReification.backendLeaf,StateT.run,
      RegistrationNativePlatformPublicAdapterPhysicalBackend.erase]
    rw [Functor.map_map]
    rfl

theorem run_normalize (coins : QueryImpl unifSpec (StateT P ProbComp)) (selected : Spec.Domain)
    (before : Store n KemSK R P) :
    RegistrationNativePlatformPublicAdapterPhysicalOrdinary.normalize <$>
      run setup checks representation created coins selected before=
      run setup checks representation created coins selected
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize before) :=by
  have frame:=RegistrationNativePlatformPublicAdapterPhysicalFrame.interpret_frame coins
    (leaf setup checks representation created selected) (leaf_frame setup checks representation created selected) before.backend.1
  have evaluated:=congrArg (fun work=>work.run before.backend.2) frame
  rw [StateT.run_map] at evaluated
  have observed:=congrArg (fun work=>(fun result=>update
    (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize before)
    (result.1.1,(result.1.2,result.2))) <$>work) evaluated
  simpa only [run,Functor.map_map,Prod.map_def,id_eq,StateT.run,update,map_ok,
    RegistrationNativePlatformPublicAdapterPhysicalOrdinary.normalize,
    RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize,
    RegistrationNativePlatformPublicAdapterPhysicalBackend.persistent] using observed

theorem normalized (coins : QueryImpl unifSpec (StateT P ProbComp))
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : RegistrationNativeExperiment.State n KemSK mlSource×P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (selected : Spec.Domain) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
      (fun state objects=>RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize
        (RegistrationNativePlatformSdkOrdinaryBeaconSelected.strongPhysical setup view views created credential state objects))
      (RegistrationNativePlatformPublicAdapterEffects.step coins setup view views created credential current before selected)=
      run setup checks representation created coins selected
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize (RegistrationNativePlatformPublicAdapterStore.erase before.base.objects)) :=by
  exact (RegistrationNativePlatformPublicAdapterNormalizedRaw.raw _ _).trans
    ((congrArg (fun work=>RegistrationNativePlatformPublicAdapterPhysicalOrdinary.normalize <$>work)
      (query setup checks representation created coins view views credential current before selected)).trans
      (run_normalize setup checks representation created coins selected _))

variable {Value : Type}
noncomputable def pureStep
    (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : RegistrationNativeExperiment.State n KemSK mlSource×P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (value : Value) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
      (pure (value,current)) := {
  step:={
    Packet:=Unit
    sample:=pure ()
    sourceType:=Value
    sourceReply:=fun _=>.ok value
    sourceState:=fun _=>current
    sourceCall:=pure (.ok value,current)
    source_exact:=by rw [map_pure]
    native:=fun _=>(value,current)
    native_exact:=by rw [map_pure]
    store:=fun _ _=>before }
  observe:=id
  normal:=by intro _ _;exact ⟨value,rfl⟩
  reply:=by intro _ _ returned same;exact (RustM.ok.inj same).symm }

theorem pure_source
    (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : RegistrationNativeExperiment.State n KemSK mlSource×P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (value : Value) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
      (fun state objects=>RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize
        (RegistrationNativePlatformSdkOrdinaryBeaconSelected.strongPhysical setup view views created credential state objects))
      (pureStep setup view views created credential current before value)=
      pure (.ok (value,RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize
        (RegistrationNativePlatformPublicAdapterStore.erase before.base.objects)),
        RegistrationNativePlatformPublicAdapterPhysicalBackend.persistent (persistent current)) :=by
  let physical : ∀state : RegistrationNativeExperiment.State n KemSK mlSource×P,
      RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential state→Store n KemSK R P:=fun state objects=>RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize
    (RegistrationNativePlatformSdkOrdinaryBeaconSelected.strongPhysical setup view views created credential state objects)
  have law:=raw_native (pureStep setup view views created credential current before value) physical
    (fun _=>physical current before) (by intro packet;rfl)
  rw [map_pure] at law
  refine law.trans ?_
  apply congrArg pure
  apply Prod.ext
  · rfl
  · exact congrArg RegistrationNativePlatformPublicAdapterPhysicalBackend.persistent before.base.backend


end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffectPhysical
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffectPhysical.leaf_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffectPhysical.leaf_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffectPhysical.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffectPhysical.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffectPhysical.leaf_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffectPhysical.leaf_frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffectPhysical.run_normalize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffectPhysical.run_normalize
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffectPhysical.normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffectPhysical.normalized
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffectPhysical.pureStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffectPhysical.pureStep
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffectPhysical.pure_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffectPhysical.pure_source
