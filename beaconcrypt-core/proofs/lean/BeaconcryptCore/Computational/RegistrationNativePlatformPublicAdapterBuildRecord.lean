-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSealBackend
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildBackend
/-! The actual complete first-record source program projects to the same physical primitive interpreter. The proof composes the actual extracted seal and raw-writer request trees with the original KDF and shared commitment cache, including every failure and updated platform state. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRecord
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSdkReification (Backend)
open RegistrationNativePlatformPublicAdapterRecordBackend (project)
variable [primitive : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK E P : Type} {base : OracleSpec I} {Reader Response : Type}
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
variable (erased : commitment.CommitmentTranscript)
local notation "Local"=>RegistrationServerRootCompiler.Local n
local notation "M"=>StateT (Backend n KemSK) (StateT P ProbComp)

abbrev Spec :=RegistrationRecordPrimitives.Spec+
  ((record_effects.AeadSealRequest →ₒ RustM AdapterSealNative.Output)+
    ((commitment.CommitmentTranscript →ₒ RegistrationNativePlatformCommitment.HashReply)+
      (record_effects.RecordWriteRequest →ₒ RustM (core.option.Option (Slice U8)))))

private def program (initial : registration.ServerInitialKdf) : OracleComp Spec (RustM RegistrationServerRecordExecutor.Result) :=
  RegistrationNativePlatformSourceRecord.fromInitialWithHash
    (fun query=>Spec.query (.inl query)) (fun request=>Spec.query (.inr (.inl request)))
    (fun transcript=>Spec.query (.inr (.inr (.inl transcript))))
    (fun request=>Spec.query (.inr (.inr (.inr request)))) initial

omit primitive in
private theorem interpret {m : Type→Type} [Monad m] [LawfulMonad m]
    (implementation : QueryImpl Spec m) (initial : registration.ServerInitialKdf) :
    simulateQ implementation (program initial)=
      RegistrationNativePlatformSourceRecord.fromInitialWithHash
        (fun query=>implementation (.inl query)) (fun request=>implementation (.inr (.inl request)))
        (fun transcript=>implementation (.inr (.inr (.inl transcript))))
        (fun request=>implementation (.inr (.inr (.inr request)))) initial := by
  unfold program
  rw [RegistrationNativePlatformSourceRecord.fromInitialWithHash_map
    (Cslib.IsMonadHom.mk' (simulateQ_pure implementation) (simulateQ_bind implementation))]
  simp only [simulateQ_spec_query]

noncomputable def handler : QueryImpl Spec M
  | .inl query=>RegistrationNativePlatformPublicAdapterSealBackend.records coins setup codec query
  | .inr (.inl request)=>RegistrationNativePlatformPublicAdapterSealBackend.sealing coins setup codec view failure allocation request
  | .inr (.inr (.inl transcript))=>RegistrationNativePlatformPublicAdapterSealBackend.hash coins setup codec erased transcript
  | .inr (.inr (.inr request))=>StateT.lift (RegistrationNativePlatformSourceCompletion.writeWith helper request)

private noncomputable def native : QueryImpl Spec (StateT Local (StateT P ProbComp))
  | .inl query=>RegistrationNativePlatformServerCompletion.records coins setup codec query
  | .inr (.inl request)=>RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation request
  | .inr (.inr (.inl transcript))=>RegistrationNativePlatformSourceSeal.hash coins setup codec erased transcript
  | .inr (.inr (.inr request))=>RegistrationNativePlatformSourceBuild.write helper request

theorem query_source (pool : PqxdhLiveKemBirth.Pool KemSK) (query : Spec.Domain) (before : Local) :
    Prod.map id (project pool) <$>(native coins setup codec view failure allocation helper erased query).run before=
      (handler coins setup codec view failure allocation helper erased query).run (project pool before) := by
  cases query with
  | inl query=>exact RegistrationNativePlatformPublicAdapterSealBackend.records_source coins setup codec pool query before
  | inr query=>cases query with
    | inl request=>
      change Prod.map id (project pool) <$>(RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation request).run before=_
      rw [←RegistrationNativePlatformExtractedSourceSeal.sealing_source coins setup codec view failure allocation request]
      exact RegistrationNativePlatformPublicAdapterSealBackend.extracted_source coins setup codec view failure allocation pool request before
    | inr query=>cases query with
      | inl transcript=>exact RegistrationNativePlatformPublicAdapterSealBackend.hash_source coins setup codec pool erased transcript before
      | inr request=>exact RegistrationNativePlatformPublicAdapterBuildBackend.write_source helper pool request before

noncomputable def firstRecord (initial : registration.ServerInitialKdf) : M (RustM RegistrationServerRecordExecutor.Result) :=
  RegistrationNativePlatformSourceRecord.fromInitialWithHash
    (RegistrationNativePlatformPublicAdapterSealBackend.records coins setup codec)
    (RegistrationNativePlatformPublicAdapterSealBackend.sealing coins setup codec view failure allocation)
    (RegistrationNativePlatformPublicAdapterSealBackend.hash coins setup codec erased)
    (fun request=>StateT.lift (RegistrationNativePlatformSourceCompletion.writeWith helper request)) initial

theorem source (pool : PqxdhLiveKemBirth.Pool KemSK) (initial : registration.ServerInitialKdf) (before : Local) :
    Prod.map id (project pool) <$>
      (RegistrationNativePlatformSourceRecord.fromInitialWithHash
        (RegistrationNativePlatformServerCompletion.records coins setup codec)
        (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash coins setup codec erased)
        (RegistrationNativePlatformSourceBuild.write helper) initial).run before=
      (firstRecord coins setup codec view failure allocation helper erased initial).run (project pool before) := by
  have same:=OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (project pool)
    (query_source coins setup codec view failure allocation helper erased pool) (program initial) before
  rw [interpret,interpret] at same
  exact same

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRecord


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRecord.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRecord.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRecord.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRecord.source
