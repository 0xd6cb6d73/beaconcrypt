-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRecord
/-! The entire response first-record/hash/sign/writer source suffix has one physical marginal. The same actual source request trees, private source outputs and complete persistent effects survive erasure of only the private hash cut and signing/request journals. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPublication
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSdkReification (Backend backend)
open RegistrationNativePlatformPublicAdapterRecordBackend (project)
variable [primitive : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK E P A : Type} {base : OracleSpec I} {Reader Response : Type}
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
local notation "M"=>StateT (Backend n KemSK) Base

abbrev Spec :=(registration.ServerInitialKdf →ₒ RustM RegistrationServerRecordExecutor.Result)+
  (RegistrationSigningShared.Spec+(registration.SignedResponseView →ₒ RustM (core.option.Option (alloc.vec.Vec U8))))

private def stage {m : Type→Type} [Monad m]
    (first : m (RustM RegistrationServerRecordExecutor.Result))
    (outgoing : QueryImpl RegistrationSigningShared.Spec m)
    (encode : registration.SignedResponseView→m (RustM (core.option.Option (alloc.vec.Vec U8)))) :=do
  let recorded←first
  RegistrationNativePlatformServerPublication.continueResult recorded
    (RegistrationNativePlatformServerPublication.program outgoing encode)

private noncomputable def program (initial : registration.ServerInitialKdf) :
    OracleComp Spec (RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))) :=
  stage (Spec.query (.inl initial))
    (fun query=>Spec.query (.inr (.inl query))) (fun signed=>Spec.query (.inr (.inr signed)))

omit primitive in
private theorem interpret {m : Type→Type} [Monad m] [LawfulMonad m]
    (implementation : QueryImpl Spec m) (initial : registration.ServerInitialKdf) :
    simulateQ implementation (program initial)=
      stage (implementation (.inl initial))
        (fun query=>implementation (.inr (.inl query))) (fun signed=>implementation (.inr (.inr signed))) := by
  unfold program stage
  rw [simulateQ_bind,simulateQ_spec_query]
  apply bind_congr
  intro recorded
  cases recorded with
  | fail error | div=>rfl
  | ok recorded=>cases recorded with
    | Err previous=>rfl
    | Ok pending=>
      simp only [RegistrationNativePlatformServerPublication.continueResult]
      rw [RegistrationNativePlatformServerPublication.program_interpret]
      simp only [simulateQ_spec_query]

noncomputable def handler : QueryImpl Spec M
  | .inl initial=>RegistrationNativePlatformPublicAdapterBuildRecord.firstRecord coins setup codec view failure allocation helper erased initial
  | .inr (.inl query)=>RegistrationNativePlatformPublicAdapterBuildBackend.outgoing coins sign query
  | .inr (.inr signed)=>StateT.lift (RegistrationNativePlatformSourceCompletion.encodeWith writer signed)

private noncomputable def native : QueryImpl Spec (StateT Native Base)
  | .inl initial=>AdapterPublicServerLocalLens.localState
      (RegistrationNativePlatformSourceRecord.fromInitialWithHash
        (RegistrationNativePlatformServerCompletion.records coins setup codec)
        (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash coins setup codec erased)
        (RegistrationNativePlatformSourceBuild.write helper) initial)
  | .inr (.inl query)=>AdapterPublicServerCompletionNative.outgoing coins sign query
  | .inr (.inr signed)=>AdapterPublicServerSigningNative.encoder (AdapterPublicServerCompletionNative.writer writer) signed

omit primitive in
private theorem local_source (work : StateT Local Base A) (physical : M A)
    (law : ∀pool current,Prod.map id (project pool) <$>work.run current=physical.run (project pool current))
    (before : Native) :
    Prod.map id backend <$>(AdapterPublicServerLocalLens.localState work).run before=physical.run (backend before) := by
  have same:=law before.pool before.server.world
  change (fun result=>(result.1,project before.pool result.2)) <$>work.run before.server.world=_ at same
  rw [AdapterPublicServerLocalLens.local_run]
  simpa only [Functor.map_map,Prod.map,id_eq,AdapterPublicServerLocalLens.putLocal,backend,project] using same

theorem query_source (query : Spec.Domain) (before : Native) :
    Prod.map id backend <$>(native coins setup codec view failure allocation helper erased sign writer query).run before=
      (handler coins setup codec view failure allocation helper erased sign writer query).run (backend before) := by
  cases query with
  | inl initial=>
    exact local_source _ _ (fun pool current=>
      RegistrationNativePlatformPublicAdapterBuildRecord.source coins setup codec view failure allocation helper erased pool initial current) before
  | inr query=>cases query with
    | inl query=>
      exact local_source _ _ (fun pool current=>
        RegistrationNativePlatformPublicAdapterBuildBackend.outgoing_source coins setup codec sign pool query current) before
    | inr signed=>
      change Prod.map id backend <$>
        (AdapterPublicServerSigningNative.encoder (AdapterPublicServerCompletionNative.writer writer) signed).run before=_
      rw [AdapterPublicServerCompletionNative.encoder_source]
      apply local_source
      intro pool current
      simp only [RegistrationNativePlatformSourceBuild.encode_run,Functor.map_map]
      rfl

noncomputable def beforeInstall (initial : registration.ServerInitialKdf) :
    M (RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))) :=
  AdapterPublicServerCompletionCut.native
    (RegistrationNativePlatformPublicAdapterBuildRecord.firstRecord coins setup codec view failure allocation helper erased initial)
    (RegistrationNativePlatformPublicAdapterBuildBackend.outgoing coins sign)
    (fun signed=>StateT.lift (RegistrationNativePlatformSourceCompletion.encodeWith writer signed))

theorem source (initial : registration.ServerInitialKdf) (before : Native) :
    Prod.map id backend <$>
      (AdapterPublicServerCompletionNative.beforeInstall coins setup codec view failure allocation helper erased sign writer initial).run before=
      (beforeInstall coins setup codec view failure allocation helper erased sign writer initial).run (backend before) := by
  have same:=OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ backend
    (query_source coins setup codec view failure allocation helper erased sign writer) (program initial) before
  rw [interpret,interpret] at same
  exact same

theorem cut_source
    (fallback : registration.MldsaSigningRequest→StateT Native Base RegistrationSigningShared.SignReply)
    (initial : registration.ServerInitialKdf) (before : RegistrationNativePlatformCutJournal.State Native) :
    Prod.map id (fun current=>backend current.1) <$>
      (AdapterPublicServerCompletionSource.beforeInstall
        (fun {A} (work : StateT Local Base A)=>AdapterPublicServerCompletionNative.inCut work)
        (AdapterPublicServerCompletionNative.outgoing coins sign) fallback coins setup codec view failure allocation helper erased
        (AdapterPublicServerCompletionNative.writer writer) initial).run before=
      (beforeInstall coins setup codec view failure allocation helper erased sign writer initial).run (backend before.1) := by
  have erasedLaw:=congrArg (fun computation=>Prod.map id backend <$>computation)
    (AdapterPublicServerCompletionNative.erasure coins setup codec view failure allocation helper erased sign writer fallback initial before)
  have same:=source coins setup codec view failure allocation helper erased sign writer initial before.1
  simp only [Functor.map_map,Prod.map,id_eq] at erasedLaw
  exact erasedLaw.trans same

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPublication


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPublication.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPublication.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPublication.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPublication.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPublication.cut_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPublication.cut_source
