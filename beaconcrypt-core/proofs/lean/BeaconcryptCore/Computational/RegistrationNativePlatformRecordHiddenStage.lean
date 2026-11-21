-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentWorld
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenPublication
import BeaconcryptCore.Computational.RegistrationNativePlatformServerRestrictedService
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconOwner
/-! The actual stateful selected branches install their own hidden reference at their literal successful returned handle. Arbitrary earlier publication/opening effects and every external platform poststate are retained before that installation cut. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenStage
open PqxdhRecordLiftInterface (WorldSpec EnvEffects effectLift coinLift Slot)
open PqxdhRecordLiftProtocol (Control)
variable {n : Nat} {S Platform E Reader Response Secret Value : Type}

def lowerEffects : QueryImpl (RegistrationNativePlatformEffectCompiler.Spec n) (OracleComp (WorldSpec n))
  | .inl query => effectLift query
  | .inr coin => coinLift coin

/-- The literal installation effect changes no public platform or receipt coordinate. -/
theorem effects (work : OracleComp (EnvEffects n) Value) (before : S) :
    simulateQ lowerEffects ((simulateQ RegistrationNativePlatformEffectCompiler.effect work).run before) =
      (fun value => (value,before)) <$> simulateQ effectLift work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure,StateT.run_pure,map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,
      RegistrationNativePlatformEffectCompiler.effect,StateT.run_lift,bind_pure_comp,
      lowerEffects,bind_map_left,map_bind,ih]

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
/-- A successful literal corrected Server hidden branch installs its actual returned key at that same hidden slot. -/
theorem server
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (reference : RegistrationNativePairedDemand.Reference n) (peer : peer.PublishedPeer (alloc.vec.Vec U8))
    (before : RegistrationNativePlatformBoundCompiler.PublicState Platform)
    (shell : CborRecordWorldClient.Shell) (world : Control n) (secret : Secret)
    (result : (((RustM (RegistrationHiddenInstall.Result (alloc.vec.Vec U8)) × RegistrationNativePlatformBoundCompiler.PublicState Platform) ×
      CborRecordWorldClient.Shell) × Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      (simulateQ lowerEffects ((RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial (.hidden reference)).run before)) shell world secret))
    (successful : result.1.1.1.1 = .ok (.Ok peer)) :
    PqxdhRecordLiftIdeal.handleSlot result.1.2 (.peer peer.key_id) = some reference.slot := by
  simp only [RegistrationNativePlatformServerRestrictedService.branch,
    RegistrationNativePlatformPairedServerCompiler.hidden,simulateQ_bind,simulateQ_spec_query,
    StateT.run_bind,RegistrationNativePlatformPairedServerCompiler.target] at supported
  rw [CborRawRecordOriginFlatten.interpret_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,_published,continued⟩ := supported
  have forwarded : simulateQ
      (RegistrationNativePlatformPairedServerCompiler.target source view failure allocation erased helper sign writer initial
        (PqxdhDeploymentHiddenLayout.joinOutput reference.material RegistrationBoundPublication.fixedSeed))
      (simulateQ RegistrationNativePlatformPairedServerCompiler.forward (RegistrationHiddenInstall.after control reference.slot middle.1.1.1.1)) =
      simulateQ RegistrationNativePlatformEffectCompiler.effect (RegistrationHiddenInstall.after control reference.slot middle.1.1.1.1) := by
    rw [← QueryImpl.simulateQ_compose]
    congr 1
  rw [forwarded] at continued
  have afterEq := effects (RegistrationHiddenInstall.after control reference.slot middle.1.1.1.1) middle.1.1.1.2
  rw [afterEq,RegistrationNativeHiddenEnvironmentWorld.interpret_map,support_map] at continued
  obtain ⟨installed,reached,returned⟩ := continued
  cases returned
  exact RegistrationNativePlatformRecordHiddenPublication.server_after service codec route control reference.slot middle.1.1.1.1 peer
    middle.1.1.2 middle.1.2 middle.2 installed reached successful

omit primitive in
/-- The corrected Beacon hidden branch retains the arbitrary actual raw prefix and installs at the same physical owner slot. -/
theorem beacon
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (raw : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT S (OracleComp (WorldSpec n))))
    (owner : Nat) (slot : Slot n) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (output : PqxdhServerAuthKeySchedule.Output) (completed : RegistrationBeaconSeed.PublicCompleted)
    (before : S) (shell : CborRecordWorldClient.Shell) (world : Control n) (secret : Secret)
    (result : (((RustM RegistrationNativePairedBeaconService.Result × S) × CborRecordWorldClient.Shell) × Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      ((RegistrationNativePlatformPairedBeaconOwner.hiddenStage source raw (fun query => StateT.lift (effectLift query)) owner slot descriptor output).run before)
      shell world secret))
    (successful : result.1.1.1.1 = .ok (.Ok completed)) :
    PqxdhRecordLiftIdeal.handleSlot result.1.2 (.owner owner) = some slot := by
  simp only [RegistrationNativePlatformPairedBeaconOwner.hiddenStage,StateT.run_bind] at supported
  rw [CborRawRecordOriginFlatten.interpret_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,_opened,continued⟩ := supported
  have afterEq : ((RegistrationNativePlatformPairedBeaconService.after
      (fun query => StateT.lift (effectLift query)) owner (fun _ => .hidden slot) middle.1.1.1.1).run middle.1.1.1.2) =
      (fun result => (result,middle.1.1.1.2)) <$> RegistrationNativePlatformPairedBeaconService.after effectLift owner (fun _ => .hidden slot) middle.1.1.1.1 := by
    cases middle.1.1.1.1 with
    | fail error | div => rfl
    | ok result => cases result <;> rfl
  rw [afterEq,RegistrationNativeHiddenEnvironmentWorld.interpret_map,support_map] at continued
  obtain ⟨installed,reached,returned⟩ := continued
  cases returned
  exact RegistrationNativePlatformRecordHiddenPublication.beacon service codec route owner slot middle.1.1.1.1 completed
    middle.1.1.2 middle.1.2 middle.2 installed reached successful
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenStage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenStage.effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenStage.effects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenStage.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenStage.server

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenStage.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenStage.beacon
