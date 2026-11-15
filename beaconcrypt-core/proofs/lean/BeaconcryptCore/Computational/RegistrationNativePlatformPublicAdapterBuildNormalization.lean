-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStore
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalFrame
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildNormalization
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend)
open RegistrationNativePlatformPublicAdapterPhysicalBackend (erase)
open RegistrationNativePlatformPublicAdapterPhysicalFrame
variable [primitive :AdapterSealPrimitive.Operations]
variable {n :Nat} {I KemSK E P :Type} {base :OracleSpec I} {Reader Response :Type}
variable {mlSource :RegistrationNativeMldsa.Source}
local notation "Base"=>StateT P ProbComp
local notation "M"=>StateT (Backend n KemSK) Base

omit primitive in
private theorem record_frame (setup :PqxdhServerAuthExperiment.Setup base KemSK)
    (codec :PqxdhServerAuthExperiment.Codec Reader Response) (query :RawCtxMixedOwner.NativeSpec.Domain) :
    Compatible (RegistrationNativePlatformPublicAdapterRecordBackend.record (n:=n) setup codec query) :=by
  intro before
  simp only [RegistrationNativePlatformPublicAdapterRecordBackend.record,StateT.run,Functor.map_map,Prod.map,id_eq,erase]

omit primitive in
private theorem hash_frame (bytes :Pqxdh.Bytes) :
    Compatible (RegistrationNativePlatformPublicAdapterRecordBackend.hash (n:=n) (KemSK:=KemSK) bytes) :=by
  intro before
  simp only [RegistrationNativePlatformPublicAdapterRecordBackend.hash,StateT.run,Functor.map_map,Prod.map,id_eq,erase]

omit primitive in
private theorem records_frame (coins :QueryImpl unifSpec Base) (setup :PqxdhServerAuthExperiment.Setup base KemSK)
    (codec :PqxdhServerAuthExperiment.Codec Reader Response) (query :RegistrationRecordPrimitives.Spec.Domain) :
    Compatible (RegistrationNativePlatformPublicAdapterSealBackend.records (n:=n) coins setup codec query) :=by
  apply interpret_frame coins
  unfold RegistrationNativePlatformPublicAdapterRecordBackend.records
  change Compatible (simulateQ (RegistrationNativePlatformPublicAdapterRecordBackend.shared setup codec) _)
  apply program_frame
  intro selected
  cases selected with
  | inl pair=>exact hash_frame pair.2
  | inr selected=>exact record_frame setup codec selected

omit primitive in
private theorem outgoing_frame (coins :QueryImpl unifSpec Base)
    (sign :registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (query :RegistrationSigningShared.Spec.Domain) :
    Compatible (RegistrationNativePlatformPublicAdapterBuildBackend.outgoing (n:=n) (KemSK:=KemSK) coins sign query) :=by
  apply interpret_frame coins
  cases query with
  | hash request=>exact hash_frame _
  | sign request payload digest=>
    intro before
    simp only [RegistrationNativePlatformPublicAdapterBuildBackend.rawOutgoing,StateT.run,Functor.map_map,Prod.map,id_eq,erase]

private theorem sealing_frame (coins :QueryImpl unifSpec Base) (setup :PqxdhServerAuthExperiment.Setup base KemSK)
    (codec :PqxdhServerAuthExperiment.Codec Reader Response) (view :RegistrationNativePlatformSourceSeal.KeyView)
    (failure :primitive.Error) (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (request :record_effects.AeadSealRequest) :
    Compatible (RegistrationNativePlatformPublicAdapterSealBackend.sealing (n:=n) coins setup codec view failure allocation request) :=by
  unfold RegistrationNativePlatformPublicAdapterSealBackend.sealing
  rw [QueryImpl.simulateQ_compose]
  apply program_frame
  intro selected
  cases selected with
  | reserve bytes capacity=>exact lift_frame _
  | aead plaintext associated nonce key=>
    change Compatible ((fun value=>RustM.ok (RegistrationNativePlatformSourceSeal.detached failure value)) <$>
      (fun before=>simulateQ coins ((RegistrationNativePlatformPublicAdapterRecordBackend.record setup codec
        (.inr (.inl (RegistrationNativePlatformSourceSeal.input view plaintext associated nonce key)))).run before) :M _))
    exact map_frame _ _ (interpret_frame coins _ (record_frame setup codec _))


omit primitive in
private theorem commitment_frame (coins :QueryImpl unifSpec Base) (setup :PqxdhServerAuthExperiment.Setup base KemSK)
    (codec :PqxdhServerAuthExperiment.Codec Reader Response) (old transcript :commitment.CommitmentTranscript) :
    Compatible (RegistrationNativePlatformPublicAdapterSealBackend.hash (n:=n) coins setup codec old transcript) :=by
  change Compatible ((fun reply=>RustM.ok (reply,old)) <$>
    RegistrationNativePlatformPublicAdapterSealBackend.records coins setup codec (.hash transcript))
  exact map_frame _ _ (records_frame coins setup codec _)

private theorem first_frame (coins :QueryImpl unifSpec Base) (setup :PqxdhServerAuthExperiment.Setup base KemSK)
    (codec :PqxdhServerAuthExperiment.Codec Reader Response) (view :RegistrationNativePlatformSourceSeal.KeyView)
    (failure :primitive.Error) (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (initial :registration.ServerInitialKdf) :
    Compatible (RegistrationNativePlatformPublicAdapterBuildRecord.firstRecord (n:=n) coins setup codec view failure allocation helper erased initial) :=by
  let work :OracleComp RegistrationNativePlatformPublicAdapterBuildRecord.Spec (RustM RegistrationServerRecordExecutor.Result):=
    RegistrationNativePlatformSourceRecord.fromInitialWithHash
      (fun query=>RegistrationNativePlatformPublicAdapterBuildRecord.Spec.query (.inl query))
      (fun request=>RegistrationNativePlatformPublicAdapterBuildRecord.Spec.query (.inr (.inl request)))
      (fun transcript=>RegistrationNativePlatformPublicAdapterBuildRecord.Spec.query (.inr (.inr (.inl transcript))))
      (fun request=>RegistrationNativePlatformPublicAdapterBuildRecord.Spec.query (.inr (.inr (.inr request)))) initial
  have code :simulateQ (RegistrationNativePlatformPublicAdapterBuildRecord.handler coins setup codec view failure allocation helper erased) work=
      RegistrationNativePlatformPublicAdapterBuildRecord.firstRecord (n:=n) coins setup codec view failure allocation helper erased initial :=by
    unfold work RegistrationNativePlatformPublicAdapterBuildRecord.firstRecord
    rw [RegistrationNativePlatformSourceRecord.fromInitialWithHash_map
      (Cslib.IsMonadHom.mk' (simulateQ_pure _) (simulateQ_bind _))]
    simp only [simulateQ_spec_query,RegistrationNativePlatformPublicAdapterBuildRecord.handler]
  rw [←code]
  apply program_frame
  intro selected
  cases selected with
  | inl selected=>exact records_frame coins setup codec selected
  | inr selected=>cases selected with
    | inl request=>exact sealing_frame coins setup codec view failure allocation request
    | inr selected=>cases selected with
      | inl transcript=>exact commitment_frame coins setup codec erased transcript
      | inr request=>exact lift_frame _

private theorem publication_frame (coins :QueryImpl unifSpec Base) (setup :PqxdhServerAuthExperiment.Setup base KemSK)
    (codec :PqxdhServerAuthExperiment.Codec Reader Response) (view :RegistrationNativePlatformSourceSeal.KeyView)
    (failure :primitive.Error) (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base) (initial :registration.ServerInitialKdf) :
    Compatible (RegistrationNativePlatformPublicAdapterBuildPublication.beforeInstall (n:=n) coins setup codec view failure allocation helper erased sign writer initial) :=by
  unfold RegistrationNativePlatformPublicAdapterBuildPublication.beforeInstall AdapterPublicServerCompletionCut.native
  apply bind_frame _ _ (first_frame coins setup codec view failure allocation helper erased initial)
  intro recorded
  cases recorded with
  | fail error | div=>exact pure_frame _
  | ok recorded=>cases recorded with
    | Err _=>exact pure_frame _
    | Ok pending=>
      let impl :QueryImpl (RegistrationSigningShared.Spec+(registration.SignedResponseView →ₒ RustM (core.option.Option (alloc.vec.Vec U8)))) M
        | .inl query=>RegistrationNativePlatformPublicAdapterBuildBackend.outgoing coins sign query
        | .inr signed=>StateT.lift (RegistrationNativePlatformSourceCompletion.encodeWith writer signed)
      change Compatible (RegistrationNativePlatformServerPublication.program
        (RegistrationNativePlatformPublicAdapterBuildBackend.outgoing coins sign)
        (fun signed=>StateT.lift (RegistrationNativePlatformSourceCompletion.encodeWith writer signed)) pending)
      have code:=RegistrationNativePlatformServerPublication.program_interpret impl
        (fun query=>(RegistrationSigningShared.Spec+(registration.SignedResponseView →ₒ RustM (core.option.Option (alloc.vec.Vec U8)))).query (.inl query))
        (fun signed=>(RegistrationSigningShared.Spec+(registration.SignedResponseView →ₒ RustM (core.option.Option (alloc.vec.Vec U8)))).query (.inr signed)) pending
      simp only [simulateQ_spec_query,impl] at code
      rw [←code]
      apply program_frame
      intro selected
      cases selected with
      | inl selected=>exact outgoing_frame coins sign selected
      | inr _=>exact lift_frame _


theorem publication_query (coins :QueryImpl unifSpec Base) (setup :PqxdhServerAuthExperiment.Setup base KemSK)
    (codec :PqxdhServerAuthExperiment.Codec Reader Response) (view :RegistrationNativePlatformSourceSeal.KeyView)
    (failure :primitive.Error) (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (query :RegistrationNativePlatformPublicAdapterBuildPublication.Spec.Domain) :
    Compatible (RegistrationNativePlatformPublicAdapterBuildPublication.handler (n:=n) coins setup codec view failure allocation helper erased sign writer query) :=by
  cases query with
  | inl initial=>exact first_frame coins setup codec view failure allocation helper erased initial
  | inr query=>cases query with
    | inl query=>exact outgoing_frame coins sign query
    | inr signed=>exact lift_frame _


variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]

theorem query (coins :QueryImpl unifSpec Base) (setup :PqxdhServerAuthExperiment.Setup base KemSK)
    (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (view :AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (original :ContainerOperations (RustT Base))
    (selected :RegistrationNativePlatformPublicAdapterBuildProgram.Spec.Domain) :
    Compatible (RegistrationNativePlatformPublicAdapterBuildSource.handler (n:=n) coins setup codec keyView failure allocation helper erased sign writer view original selected) :=by
  cases selected with
  | inl selected=>cases selected with
    | inl self=>
      unfold RegistrationNativePlatformPublicAdapterBuildSource.handler RegistrationNativePlatformPublicAdapterBuildPrefixPrimitives.pin
      apply program_frame
      intro request
      apply map_frame _
      exact outgoing_frame coins sign (.hash request)
    | inr request=>
      unfold RegistrationNativePlatformPublicAdapterBuildSource.handler RegistrationNativePlatformPublicAdapterBuildPrefixPrimitives.hash
      apply map_frame _
      exact outgoing_frame coins sign (.hash request)
  | inr selected=>cases selected with
    | inl pair=>exact lift_frame _
    | inr selected=>cases selected with
      | inl known=>exact lift_frame _
      | inr pair=>
        unfold RegistrationNativePlatformPublicAdapterBuildSource.handler RegistrationNativePlatformPublicAdapterBuildComplete.complete
        apply bind_frame _ _ (publication_frame coins setup codec keyView failure allocation helper erased sign writer pair.2)
        intro published
        apply bind_frame _ _ (lift_frame _)
        intro word
        exact pure_frame _

theorem program (coins :QueryImpl unifSpec Base) (setup :PqxdhServerAuthExperiment.Setup base KemSK)
    (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (view :AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (original :ContainerOperations (RustT Base))
    (self :beaconcrypt_public_wrapper.server.Server) (token :beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data :core.option.Option (Slice U8)) :
    Compatible (RegistrationNativePlatformPublicAdapterBuildSource.program (n:=n) coins setup codec keyView failure allocation helper erased sign writer view original self token data) :=
  program_frame _ (query coins setup codec keyView failure allocation helper erased sign writer view original) _


omit primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem committed (view :AdapterPublicWrapperState.MaterialView mlSource KemSK) (views :AdapterPublicWrapperStorage.Views) (self :beaconcrypt_public_wrapper.server.Server) (before :Backend n KemSK×P) :
    RegistrationNativePlatformPublicAdapterPhysicalBackend.persistent
      (RegistrationNativePlatformPublicAdapterBuildStore.committed view views self before)=
      RegistrationNativePlatformPublicAdapterBuildStore.committed view views self
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.persistent before) :=rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildNormalization

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildNormalization.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildNormalization.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildNormalization.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildNormalization.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildNormalization.committed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildNormalization.committed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildNormalization.publication_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildNormalization.publication_query
