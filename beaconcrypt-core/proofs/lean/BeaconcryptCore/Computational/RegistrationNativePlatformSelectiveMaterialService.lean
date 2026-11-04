-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenStage
import BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendCompiler
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemandWorld
import BeaconcryptCore.Computational.RegistrationNativeSelectiveDemandRealized
/-! The current source demand/publication client closes over the same selective private state and World. Its effectful source publication threads public signing receipts and platform state; only the explicit demand changes the private material tables. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveMaterialService
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (WorldSpec)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveHiddenInterpreter (State)
open RegistrationNativePlatformRecordHiddenStage (lowerEffects)
variable {n : Nat} {I KemSK ProviderState A Platform E Reader Response Secret : Type} {base : OracleSpec I}

noncomputable def handler (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) :
    QueryImpl (RegistrationNativePlatformServerFrontendCompiler.Spec n)
      (StateT (State n KemSK ProviderState) (OracleComp (WorldSpec n)))
  | .inl message => RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider
      (.inl (.inr (.inl (.inl message))))
  | .inr query => StateT.lift (lowerEffects query)

/-- Actual source World effects preserve the selective private material coordinate on the same execution. -/
theorem effects_program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativePlatformEffectCompiler.Spec n) A) (before : State n KemSK ProviderState) :
    (simulateQ (handler setup wire sign seed scalar candidate provider)
      (simulateQ RegistrationNativePlatformServerFrontendCompiler.embed work)).run before =
      (fun value => (value,before)) <$> simulateQ lowerEffects work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure,StateT.run_pure,map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,RegistrationNativePlatformServerFrontendCompiler.embed,
      handler,StateT.run_bind,StateT.run_lift,bind_pure_comp,bind_map_left,map_bind,ih]

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

/-- The literal selected branch retains its whole public/P result and unchanged private material state through World lowering. -/
theorem branch_source (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (choice : RegistrationNativePairedChoice.Choice n)
    (previous : RegistrationNativePlatformBoundCompiler.PublicState Platform) (before : State n KemSK ProviderState) :
    (simulateQ (handler setup wire sign seed scalar candidate provider)
      ((RegistrationNativePlatformServerFrontendCompiler.liftEffects
        (RegistrationNativePlatformServerRestrictedService.branch setup.source view failure allocation erased helper sign writer control initial choice)).run previous)).run before =
      (fun value => (value,before)) <$> simulateQ lowerEffects
        ((RegistrationNativePlatformServerRestrictedService.branch setup.source view failure allocation erased helper sign writer control initial choice).run previous) := by
  exact effects_program setup wire sign seed scalar candidate provider _ before

/-- Every supported actual selected source branch installs at the same returned peer key and its own hidden slot. -/
theorem branch_hidden
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (reference : RegistrationNativePairedDemand.Reference n) (peer : peer.PublishedPeer (alloc.vec.Vec U8))
    (previous : RegistrationNativePlatformBoundCompiler.PublicState Platform) (before : State n KemSK ProviderState)
    (shell : CborRecordWorldClient.Shell) (world : PqxdhRecordLiftProtocol.Control n) (secret : Secret)
    (result : ((((RustM (RegistrationHiddenInstall.Result (alloc.vec.Vec U8)) × RegistrationNativePlatformBoundCompiler.PublicState Platform) × State n KemSK ProviderState) ×
      CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      ((simulateQ (handler setup wire sign seed scalar candidate provider)
        ((RegistrationNativePlatformServerFrontendCompiler.liftEffects
          (RegistrationNativePlatformServerRestrictedService.branch setup.source view failure allocation erased helper sign writer control initial (.hidden reference))).run previous)).run before) shell world secret))
    (successful : result.1.1.1.1.1 = .ok (.Ok peer)) :
    PqxdhRecordLiftIdeal.handleSlot result.1.2 (.peer peer.key_id) = some reference.slot := by
  rw [branch_source,RegistrationNativeHiddenEnvironmentWorld.interpret_map,support_map] at supported
  obtain ⟨native,called,returned⟩ := supported
  cases returned
  exact RegistrationNativePlatformRecordHiddenStage.server service codec route setup.source view failure allocation erased helper sign writer control initial reference peer
    previous shell world secret native called successful
omit primitive in
/-- A selected successful demand supplies its own realized input and hidden reference on the actual World path. -/
theorem demand_hidden
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (message : RegistrationNativeRelatedFamily.Message)
    (selected : ∀ bytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message = some bytes →
      RegistrationNativeSelectiveHiddenService.selected
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate bytes = true)
    (before : State n KemSK ProviderState) (shell : CborRecordWorldClient.Shell)
    (world : PqxdhRecordLiftProtocol.Control n) (secret : Secret)
    (result : (((Option (RegistrationNativePairedChoice.Choice n) × State n KemSK ProviderState) × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      ((handler setup wire sign seed scalar candidate provider (.inl message)).run before) shell world secret))
    (choice : RegistrationNativePairedChoice.Choice n) (chosen : result.1.1.1.1 = some choice) :
    ∃ reference, choice = .hidden reference := by
  have original := RegistrationNativeRecordHandleSlots.open_support service codec route _ shell world secret result supported
  change (result.1.1.1.1,result.1.1.1.2) ∈ support
    ((RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider
      (.inl (.inr (.inl (.inl message))))).run before) at original
  rw [chosen] at original
  obtain ⟨bytes,realized⟩ := RegistrationNativeSelectiveDemandRealized.source setup wire sign seed scalar candidate provider message before result.1.1.1.2 choice original
  obtain ⟨reference,hidden,_slot,_material⟩ := RegistrationNativeSelectiveHiddenDemandWorld.source_demand setup wire sign seed scalar candidate provider message bytes before result.1.1.1.2 choice realized (selected bytes realized) original
  exact ⟨reference,hidden⟩

/-- The actual current source service attaches a selected successful public peer result to its literal physical hidden slot. -/
theorem service_hidden
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (message : RegistrationNativeRelatedFamily.Message)
    (selected : ∀ bytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message = some bytes →
      RegistrationNativeSelectiveHiddenService.selected
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate bytes = true)
    (peer : peer.PublishedPeer (alloc.vec.Vec U8))
    (previous : RegistrationNativePlatformBoundCompiler.PublicState Platform) (before : State n KemSK ProviderState)
    (shell : CborRecordWorldClient.Shell) (world : PqxdhRecordLiftProtocol.Control n) (secret : Secret)
    (result : ((((RustM (RegistrationHiddenInstall.Result (alloc.vec.Vec U8)) × RegistrationNativePlatformBoundCompiler.PublicState Platform) × State n KemSK ProviderState) ×
      CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      ((simulateQ (handler setup wire sign seed scalar candidate provider)
        ((RegistrationNativePlatformServerFrontendCompiler.service setup.source view failure allocation erased helper sign writer control initial message).run previous)).run before) shell world secret))
    (successful : result.1.1.1.1.1 = .ok (.Ok peer)) :
    ∃ slot, PqxdhRecordLiftIdeal.handleSlot result.1.2 (.peer peer.key_id) = some slot := by
  simp only [RegistrationNativePlatformServerFrontendCompiler.service,StateT.run_bind,StateT.run_lift,
    bind_pure_comp,bind_map_left,simulateQ_bind,simulateQ_spec_query,
    StateT.run_bind,handler] at supported
  rw [CborRawRecordOriginFlatten.interpret_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,demanded,continued⟩ := supported
  cases chosen : middle.1.1.1.1 with
  | none =>
    simp only [chosen,simulateQ_pure,StateT.run_pure,CborRawRecordOriginFlatten.interpret_pure,mem_support_pure_iff] at continued
    subst result
    cases successful
  | some choice =>
    obtain ⟨reference,hidden⟩ := demand_hidden setup wire sign seed scalar candidate provider service codec route message selected
      before shell world secret middle demanded choice chosen
    subst choice
    simp only [chosen] at continued
    exact ⟨reference.slot,branch_hidden setup wire sign seed scalar candidate provider view failure allocation erased helper writer service codec route
      control initial reference peer previous middle.1.1.1.2 middle.1.1.2 middle.1.2 middle.2 result continued successful⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveMaterialService

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveMaterialService.effects_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveMaterialService.effects_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveMaterialService.branch_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveMaterialService.branch_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveMaterialService.branch_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveMaterialService.branch_hidden

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveMaterialService.demand_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveMaterialService.demand_hidden

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveMaterialService.service_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveMaterialService.service_hidden
