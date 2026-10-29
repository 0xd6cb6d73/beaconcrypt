-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordHiddenPublication
import BeaconcryptCore.Computational.RegistrationNativeCommonCompiler
import BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentWorld

/-! The actual current-environment material44 stages install their own hidden reference on success. Prefix record/signing callbacks run before the literal native installation, and its reached cursor/control/private cache is retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRecordHiddenStage
open PqxdhRecordLiftInterface (WorldSpec EnvEffects effectLift Slot)
open PqxdhRecordLiftProtocol (Control)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {Auxiliary Encoded Reader Response Secret Value : Type}

theorem effects (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (EnvEffects n) Value) (before : EnvState Auxiliary) :
    (simulateQ (RegistrationNativeCommonCompiler.common effectLift source writer sign)
      (simulateQ RegistrationHiddenInstall.effectLift work)).run before =
      (fun value => (value, before)) <$> simulateQ effectLift work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, RegistrationHiddenInstall.effectLift,
        RegistrationNativeCommonCompiler.common, StateT.run_bind, StateT.run_lift,
        bind_pure_comp, bind_map_left, map_bind, ih]

private theorem server_after (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (control : pqxdh.ServerState) (slot : Slot n)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded)) (peer : peer.PublishedPeer Encoded)
    (shell : CborRecordWorldClient.Shell) (before : Control n) (secret : Secret)
    (result : ((RustM (RegistrationHiddenInstall.Result Encoded) × CborRecordWorldClient.Shell) × Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      (simulateQ effectLift (RegistrationHiddenInstall.after control slot published)) shell before secret))
    (successful : result.1.1.1 = .ok (.Ok peer)) :
    PqxdhRecordLiftIdeal.handleSlot result.1.2 (.peer peer.key_id) = some slot := by
  cases published with
  | fail error | div =>
      simp only [RegistrationHiddenInstall.after, ] at supported
      subst result
      cases successful
  | ok published => cases published with
    | Err previous =>
        simp only [RegistrationHiddenInstall.after, ] at supported
        subst result
        cases successful
    | Ok published =>
        exact RegistrationNativeRecordHiddenPublication.server service codec route control slot published peer
          shell before secret result supported successful

/-- Successful actual current-environment Server material44 completion installs its exact hidden reference at the returned peer ID. -/
theorem server (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded) (control : pqxdh.ServerState)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (reference : RegistrationNativePairedDemand.Reference n)
    (peer : peer.PublishedPeer Encoded) (env : EnvState Auxiliary) (shell : CborRecordWorldClient.Shell)
    (before : Control n) (secret : Secret)
    (result : (((RustM (RegistrationHiddenInstall.Result Encoded) × EnvState Auxiliary) × CborRecordWorldClient.Shell) × Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      ((simulateQ (RegistrationNativeCommonCompiler.common effectLift source writer sign)
        (RegistrationNativePairedServerService.hiddenStage encode control initial reference)).run env) shell before secret))
    (successful : result.1.1.1.1 = .ok (.Ok peer)) :
    PqxdhRecordLiftIdeal.handleSlot result.1.2 (.peer peer.key_id) = some reference.slot := by
  simp only [RegistrationNativePairedServerService.hiddenStage, simulateQ_bind, StateT.run_bind] at supported
  rw [CborRawRecordOriginFlatten.interpret_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, _published, continued⟩ := supported
  rw [effects, RegistrationNativeHiddenEnvironmentWorld.interpret_map, support_map] at continued
  obtain ⟨installed, reached, returned⟩ := continued
  cases returned
  exact server_after service codec route control reference.slot middle.1.1.1.1 peer
    middle.1.1.2 middle.1.2 middle.2 installed reached successful

/-- Successful actual current-environment Beacon material44 completion installs its exact hidden reference at the physical owner. -/
theorem beacon (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (reference : RegistrationNativePairedDemand.Reference n) (completed : RegistrationBeaconSeed.PublicCompleted)
    (env : EnvState Auxiliary) (shell : CborRecordWorldClient.Shell) (before : Control n) (secret : Secret)
    (result : (((RustM RegistrationNativePairedBeaconService.Result × EnvState Auxiliary) × CborRecordWorldClient.Shell) × Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      ((simulateQ (RegistrationNativeCommonCompiler.common effectLift source writer sign)
        (RegistrationNativePairedBeaconService.hiddenStage source owner sender descriptor reference)).run env) shell before secret))
    (successful : result.1.1.1.1 = .ok (.Ok completed)) :
    PqxdhRecordLiftIdeal.handleSlot result.1.2 (.owner owner) = some reference.slot := by
  simp only [RegistrationNativePairedBeaconService.hiddenStage, RegistrationNativePairedBeaconService.privateHiddenStage,
    simulateQ_bind, StateT.run_bind] at supported
  rw [CborRawRecordOriginFlatten.interpret_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, _opened, continued⟩ := supported
  rw [effects, RegistrationNativeHiddenEnvironmentWorld.interpret_map, support_map] at continued
  obtain ⟨installed, reached, returned⟩ := continued
  cases returned
  exact RegistrationNativeRecordHiddenPublication.beacon service codec route owner sender reference.slot middle.1.1.1.1 completed
    middle.1.1.2 middle.1.2 middle.2 installed reached successful

end BeaconcryptCore.Computational.RegistrationNativeRecordHiddenStage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordHiddenStage.effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordHiddenStage.effects
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordHiddenStage.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordHiddenStage.server
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordHiddenStage.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordHiddenStage.beacon
