-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveMaterialExecution
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCore
/-! The literal public build is the same actual four-leaf source macro at the same private material, platform and physical World state. Only the returned frontend representation is reassociated. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBuildSource
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (WorldSpec)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveHiddenInterpreter (State)
open RegistrationNativePlatformHiddenAllocationCore (close)
variable {n : Nat} {I KemSK ProviderState Platform E Reader Response Secret A : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
local notation "backend" => RegistrationNativePlatformSelectiveEntropyBackend.handler setup wire sign seed scalar candidate provider
local notation "material" => RegistrationNativePlatformSelectiveMaterialService.handler setup wire sign seed scalar candidate provider

/-- The actual public build embedding closes each material/effect/allocator request through the same source dictionary. -/
theorem embedding (work : OracleComp (RegistrationNativePlatformServerFrontendCompiler.Spec n) A) :
    simulateQ backend (simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
      (simulateQ RegistrationNativePlatformPublicFrontend.buildEmbedding work)) = simulateQ material work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]
  | query_bind query next ih =>
    have leaf : simulateQ backend (simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
        (RegistrationNativePlatformPublicFrontend.buildEmbedding query)) = material query := by
      cases query with
      | inl message =>
        simp only [RegistrationNativePlatformPublicFrontend.buildEmbedding,
          RegistrationNativePlatformPublicFrontend.localQuery, RegistrationNativePlatformPublicFrontend.embedLocal,
          simulateQ_spec_query, RegistrationNativePlatformSelectiveEntropyBackend.handler,
          RegistrationNativePlatformSelectiveMaterialService.handler]
      | inr effect => cases effect with
        | inl effect =>
          apply StateT.ext
          intro before
          simp only [RegistrationNativePlatformPublicFrontend.buildEmbedding, RegistrationNativePlatformPublicFrontend.effect,
            RegistrationNativePlatformPublicFrontend.localQuery, RegistrationNativePlatformPublicFrontend.embedLocal,
            simulateQ_spec_query,
            RegistrationNativePlatformSelectiveEntropyBackend.handler, RegistrationNativeSelectiveHiddenInterpreter.handler,
            RegistrationNativeSelectiveHiddenInterpreter.onBase, RegistrationNativeHiddenInterpreter.handler,
            RegistrationNativeHiddenInterpreter.effect,
            RegistrationNativePlatformSelectiveMaterialService.handler,
            RegistrationNativePlatformRecordHiddenStage.lowerEffects, StateT.run]
          rfl
        | inr coin => rfl
    simp only [simulateQ_bind, simulateQ_spec_query, leaf]
    congr 1
    funext reply
    exact ih reply

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

abbrev SourceState (n : Nat) (Platform KemSK ProviderState Secret : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativePlatformHiddenAllocationCore.State n Platform (State n KemSK ProviderState) Secret source

def macroBefore (before : SourceState n Platform KemSK ProviderState Secret source) :
    RegistrationNativePlatformSelectiveMaterialExecution.Runtime n Platform KemSK ProviderState Secret :=
  (((((before.1.1.1.1.1.environment.receipts,before.1.1.1.1.2),before.1.1.1.2),before.1.1.2),before.1.2),before.2)

def restore (before : RegistrationNativePublicFrontend.State source)
    (result : (RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8) × RegistrationServerMaterialFrontend.State) ×
      RegistrationNativePlatformSelectiveMaterialExecution.Runtime n Platform KemSK ProviderState Secret) :
    RustM (Option (U64 × Pqxdh.Bytes)) × SourceState n Platform KemSK ProviderState Secret source :=
  (RegistrationNativePlatformPublicFrontend.responseBytes result.1.1,
    ((((({before with server := result.1.2, environment := {before.environment with
      receipts := result.2.1.1.1.1.1, recordRequests := []}},result.2.1.1.1.1.2),result.2.1.1.1.2),result.2.1.1.2),result.2.1.2),result.2.2))

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- The complete current public callback has the same macro execution and every reached private/platform/physical state. -/
theorem build_run (handle : Nat) (application : Option (Slice U8))
    (before : SourceState n Platform KemSK ProviderState Secret source) :
    (RegistrationNativeHiddenEnvironmentWorld.lower service codec route
      (close backend (RegistrationNativePlatformPublicFrontend.executeLocal
        (RegistrationNativePlatformPublicFrontend.build setup sign view failure allocation erased helper writer reserve handle application source)))).run before =
    restore before.1.1.1.1.1 <$>
      (simulateQ (RegistrationNativePlatformSelectiveMaterialExecution.native setup wire sign seed scalar candidate provider
        view failure allocation erased helper writer reserve service codec route)
        ((RegistrationNativePlatformServerFrontendProgram.program handle application).run before.1.1.1.1.1.server)).run (macroBefore before) := by
  rw [RegistrationNativePlatformSelectiveMaterialExecution.program_source]
  unfold RegistrationNativeHiddenEnvironmentWorld.lower close
    RegistrationNativePlatformPublicFrontend.executeLocal RegistrationNativePlatformPublicFrontend.build
  simp only [StateT.run, simulateQ_map, Functor.map_map]
  rw [embedding]
  simp only [map_apply, RegistrationNativeHiddenEnvironmentWorld.interpret_map, Functor.map_map]
  rfl

omit primitive in
private theorem response_success (reply : RustM (Option (U64 × alloc.vec.Vec U8))) (keyId : U64) (bytes : Pqxdh.Bytes)
    (successful : RegistrationNativePlatformPublicFrontend.responseBytes reply = .ok (some (keyId,bytes))) :
    ∃ encoded, reply = .ok (some (keyId,encoded)) := by
  cases reply with
  | fail error | div => cases successful
  | ok optional => cases optional with
    | none => cases successful
    | some pair =>
      rcases pair with ⟨key,encoded⟩
      cases successful
      exact ⟨encoded,rfl⟩

/-- A successful literal public build attaches the selected stored reference to its same returned physical peer, after every source and platform effect. -/
theorem build_hidden (handle : Nat) (application : Option (Slice U8)) (ready : RegistrationServerReferenceRoot.Ready)
    (before after : SourceState n Platform KemSK ProviderState Secret source)
    (stored : before.1.1.1.1.1.server.sessions[handle]? = some (some ready))
    (selected : ∀ bytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar ready.reference = some bytes →
      RegistrationNativeSelectiveHiddenService.selected
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate bytes = true)
    (keyId : U64) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some (keyId,bytes)),after) ∈ support
      ((RegistrationNativeHiddenEnvironmentWorld.lower service codec route
        (close backend (RegistrationNativePlatformPublicFrontend.executeLocal
          (RegistrationNativePlatformPublicFrontend.build setup sign view failure allocation erased helper writer reserve handle application source)))).run before)) :
    ∃ slot, PqxdhRecordLiftIdeal.handleSlot after.1.2 (.peer keyId) = some slot := by
  rw [build_run,support_map] at supported
  obtain ⟨result,actual,returned⟩ := supported
  have reply : RegistrationNativePlatformPublicFrontend.responseBytes result.1.1 = .ok (some (keyId,bytes)) := congrArg Prod.fst returned
  have sameControl : result.2.1.2 = after.1.2 := congrArg (fun value => value.2.1.2) returned
  obtain ⟨encoded,successful⟩ := response_success result.1.1 keyId bytes reply
  have actual' : ((.ok (some (keyId,encoded)),result.1.2),result.2) ∈ support
      ((simulateQ (RegistrationNativePlatformSelectiveMaterialExecution.native setup wire sign seed scalar candidate provider
        view failure allocation erased helper writer reserve service codec route)
        ((RegistrationNativePlatformServerFrontendProgram.program handle application).run before.1.1.1.1.1.server)).run (macroBefore before)) := by
    have same : ((.ok (some (keyId,encoded)),result.1.2),result.2) = result := by
      apply Prod.ext
      · apply Prod.ext
        · exact successful.symm
        · rfl
      · rfl
    rw [same]
    exact actual
  obtain ⟨slot,hidden⟩ := RegistrationNativePlatformSelectiveMaterialExecution.build_hidden setup wire sign seed scalar candidate provider
    view failure allocation erased helper writer reserve service codec route handle application ready before.1.1.1.1.1.server result.1.2
    stored selected (macroBefore before) result.2 keyId encoded actual'
  exact ⟨slot,sameControl ▸ hidden⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBuildSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBuildSource.embedding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBuildSource.embedding
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBuildSource.build_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBuildSource.build_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBuildSource.build_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBuildSource.build_hidden
