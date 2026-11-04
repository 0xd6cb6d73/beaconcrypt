-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveMaterialService
import BeaconcryptCore.Computational.RegistrationNativePlatformServerServiceCut
/-! The complete current Server macro uses its stored Ready reference and the final successful service's exact physical poststate. Reassociation retains the same public signing receipts, persistent platform, selective material state, cursor, control and private service. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveMaterialExecution
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (WorldSpec)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveHiddenInterpreter (State)
open RegistrationNativePlatformSelectiveMaterialService (handler)
variable {n : Nat} {I KemSK ProviderState A Platform E Reader Response Secret : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))


variable (reserve : StateT Platform ProbComp Bool)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
abbrev Local (n : Nat) (Platform KemSK ProviderState : Type) :=
  RegistrationNativePlatformBoundCompiler.PublicState Platform × State n KemSK ProviderState
abbrev Runtime (n : Nat) (Platform KemSK ProviderState Secret : Type) :=
  RegistrationNativeHiddenEnvironmentWorld.State n (Local n Platform KemSK ProviderState) Secret

noncomputable def native : QueryImpl RegistrationNativePlatformServerFrontendProgram.Spec
    (StateT (Runtime n Platform KemSK ProviderState Secret) ProbComp) := fun query =>
  RegistrationNativeHiddenEnvironmentWorld.lower service codec route
    (((handler setup wire sign seed scalar candidate provider).mapStateTBase
      (RegistrationNativePlatformServerFrontendCompiler.target setup.source view failure allocation erased helper sign writer reserve)).flattenStateT query)

def attach {Value : Type}
    (result : (((((Value × RegistrationNativePlatformBoundCompiler.PublicState Platform) × State n KemSK ProviderState) ×
      CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × Secret)) : Value × Runtime n Platform KemSK ProviderState Secret :=
  (result.1.1.1.1.1,((((result.1.1.1.1.2,result.1.1.1.2),result.1.1.2),result.1.2),result.2))

/-- Every current macro is closed over its actual public/platform and private material state before the same physical World interpretation. -/
theorem program_source (work : OracleComp RegistrationNativePlatformServerFrontendProgram.Spec A)
    (before : Runtime n Platform KemSK ProviderState Secret) :
    (simulateQ (native setup wire sign seed scalar candidate provider view failure allocation erased helper writer reserve service codec route) work).run before =
      attach <$> CborRawRecordOriginFlatten.interpret service codec route
        ((simulateQ (handler setup wire sign seed scalar candidate provider)
          ((simulateQ (RegistrationNativePlatformServerFrontendCompiler.target setup.source view failure allocation erased helper sign writer reserve) work).run before.1.1.1.1)).run before.1.1.1.2)
        before.1.1.2 before.1.2 before.2 := by
  unfold native
  rw [← RegistrationNativeHiddenEnvironmentWorld.program_lower,RegistrationNativeHiddenEnvironmentWorld.lower_run,
    OracleComp.simulateQ_flattenStateT_run,← QueryImpl.simulateQ_mapStateTBase_run,bind_pure_comp,
    RegistrationNativeHiddenEnvironmentWorld.interpret_map,Functor.map_map]
  rfl

/-- The actual selected service macro supplies the physical hidden slot without any whole callback law. -/
theorem service_hidden (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (message : RegistrationNativeRelatedFamily.Message)
    (selected : ∀ bytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message = some bytes →
      RegistrationNativeSelectiveHiddenService.selected
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate bytes = true)
    (before after : Runtime n Platform KemSK ProviderState Secret) (peer : peer.PublishedPeer (alloc.vec.Vec U8))
    (supported : (.ok (.Ok peer),after) ∈ support
      ((native setup wire sign seed scalar candidate provider view failure allocation erased helper writer reserve service codec route
        (.service control initial message)).run before)) :
    ∃ slot, PqxdhRecordLiftIdeal.handleSlot after.1.2 (.peer peer.key_id) = some slot := by
  have source := program_source setup wire sign seed scalar candidate provider view failure allocation erased helper writer reserve service codec route
    (RegistrationNativePlatformServerFrontendProgram.Spec.query (.service control initial message)) before
  simp only [simulateQ_spec_query,RegistrationNativePlatformServerFrontendCompiler.target] at source
  rw [source,support_map] at supported
  obtain ⟨result,called,returned⟩ := supported
  have reply : result.1.1.1.1.1 = .ok (.Ok peer) := congrArg Prod.fst returned
  have sameControl : result.1.2 = after.1.2 := congrArg (fun value => value.2.1.2) returned
  obtain ⟨slot,hidden⟩ := RegistrationNativePlatformSelectiveMaterialService.service_hidden setup wire sign seed scalar candidate provider view failure allocation erased helper writer service codec route
    control initial message selected peer before.1.1.1.1 before.1.1.1.2 before.1.1.2 before.1.2 before.2 result called reply
  exact ⟨slot,sameControl ▸ hidden⟩
/-- A successful literal moved-token build installs the selected stored descriptor at its returned peer identifier in the same final physical state. -/
theorem build_hidden (handle : Nat) (application : Option (Slice U8)) (ready : RegistrationServerReferenceRoot.Ready)
    (front afterFront : RegistrationServerMaterialFrontend.State)
    (stored : front.sessions[handle]? = some (some ready))
    (selected : ∀ bytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar ready.reference = some bytes →
      RegistrationNativeSelectiveHiddenService.selected
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate bytes = true)
    (before after : Runtime n Platform KemSK ProviderState Secret) (keyId : U64) (bytes : alloc.vec.Vec U8)
    (supported : ((.ok (some (keyId,bytes)),afterFront),after) ∈ support
      ((simulateQ (native setup wire sign seed scalar candidate provider view failure allocation erased helper writer reserve service codec route)
        ((RegistrationNativePlatformServerFrontendProgram.program handle application).run front)).run before)) :
    ∃ slot, PqxdhRecordLiftIdeal.handleSlot after.1.2 (.peer keyId) = some slot := by
  obtain ⟨control,initial,calledBefore,peer,keyEqual,_bytesEqual,called⟩ :=
    RegistrationNativePlatformServerServiceCut.program
      (native setup wire sign seed scalar candidate provider view failure allocation erased helper writer reserve service codec route)
      handle application ready front afterFront stored before after keyId bytes supported
  obtain ⟨slot,hidden⟩ := service_hidden setup wire sign seed scalar candidate provider view failure allocation erased helper writer reserve service codec route
    control initial ready.reference selected calledBefore after peer called
  exact ⟨slot,keyEqual ▸ hidden⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveMaterialExecution

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveMaterialExecution.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveMaterialExecution.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveMaterialExecution.service_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveMaterialExecution.service_hidden

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveMaterialExecution.build_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveMaterialExecution.build_hidden
