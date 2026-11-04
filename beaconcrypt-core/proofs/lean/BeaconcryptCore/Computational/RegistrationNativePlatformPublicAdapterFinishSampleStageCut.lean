-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishStageCut
import BeaconcryptCore.Computational.RegistrationNativePlatformPackedState
import BeaconcryptCore.Computational.RegistrationNativePlatformInterpret
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSampleStageCut
open BeaconcryptCore.Refinement
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
open AdapterPublicFinishLifetime (packet)
variable {n :Nat} {I KemSK P Log A :Type} {base :OracleSpec I} {mlSource :RegistrationNativeMldsa.Source}
local notation "Native"=>RegistrationNativeExperiment.State n KemSK mlSource
variable (coins :QueryImpl unifSpec (StateT P ProbComp))
variable (setup :PqxdhServerAuthExperiment.Setup base KemSK) (checks :PqxdhServerAuthExperiment.Checks)
variable (representation :RegistrationServerRoleBackend.ConvertedIdentity setup) (created :PqxdhLiveServerConstruction.Created Unit)

noncomputable def implementation :QueryImpl (Trusted n KemSK) (StateT (Native×P) ProbComp):=fun query=>
  RegistrationNativePlatformPackedState.pack (RegistrationNativePlatformInterpret.state coins
    (RegistrationNativeExperiment.trusted setup checks representation created mlSource query))

theorem free_source (work :OracleComp (Trusted n KemSK) A) (before :Native) (previous :P) :
    (simulateQ (implementation coins setup checks representation created) work).run (before,previous)=
      (fun result=>(result.1.1,(result.1.2,result.2))) <$>
        (simulateQ coins ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource) work).run before)).run previous :=by
  unfold implementation
  rw [←RegistrationNativePlatformPackedState.simulate_pack,←RegistrationNativePlatformInterpret.state_simulate]
  rfl

noncomputable def result (reached :(RegistrationNativePlatformExtractedSdkFinish.BodyResult n KemSK mlSource×P)×List Log) :=
  ((reached.1.1.1.1,(reached.1.1.1.2,reached.2)),(reached.1.1.2,reached.1.2))

theorem sample_source (wire :RegistrationNativeWire.Wire) (note :Stage→Log)
    (pending :registration.BeaconPending) (input :Slice U8) (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes)
    (before :Native) (previous :P) (past :List Log) :
    result <$>RegistrationNativePlatformPublicAdapterFinishLoggedFactor.sample setup wire note coins checks representation created
      pending (packet input) owner scalar before previous past=
      RegistrationNativePlatformPublicAdapterFinishStageCut.logged (implementation coins setup checks representation created)
        (RegistrationNativePlatformPublicAdapterFinishLoggedFactor.body setup wire note pending
          (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)) owner scalar)
        (RegistrationWorldAgreementCompiler.erase before.server.world) past (before,previous) :=by
  unfold RegistrationNativePlatformPublicAdapterFinishStageCut.logged
  rw [free_source]
  unfold RegistrationNativePlatformPublicAdapterFinishLoggedFactor.sample
  have decoded:RegistrationNativePlatformExtractedSdkFinish.decodedPacket (packet input)=
      RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input):=AdapterPublicFinishLifetime.packet_roundtrip input
  rw [decoded]
  simp only [Functor.map_map]
  rfl

theorem sample_cut (wire :RegistrationNativeWire.Wire) (note :Stage→Log) (injective :Function.Injective note)
    (initial :registration.BeaconInitialKdf) (completed :registration.CompletedBeacon)
    (pending :registration.BeaconPending) (input :Slice U8) (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes)
    (before :Native) (previous :P) (past :List Log)
    (reached :(RegistrationNativePlatformExtractedSdkFinish.BodyResult n KemSK mlSource×P)×List Log)
    (supported :reached∈support (RegistrationNativePlatformPublicAdapterFinishLoggedFactor.sample setup wire note coins checks representation created
      pending (packet input) owner scalar before previous past))
    (present :note (.beaconFirstRecord initial (.ok (.Ok completed)))∈reached.2) :
    note (.beaconFirstRecord initial (.ok (.Ok completed)))∈past ∨
      ∃authenticated authenticatedEnv authenticatedState middleEnv middle,
      ((.ok (.Ok authenticated),authenticatedEnv),authenticatedState)∈support
        (RegistrationNativePlatformPublicAdapterFinishStageCut.run (implementation coins setup checks representation created)
          (simulateQ (RegistrationNativeBeaconPhaseCommutation.authentication (source:=mlSource) setup)
            (RegistrationResponseExecutor.begin pending (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input))))
          (RegistrationWorldAgreementCompiler.erase before.server.world) (before,previous)) ∧
      ((.ok (.BeaconComplete initial.agreement),middleEnv),middle)∈support
        (RegistrationNativePlatformPublicAdapterFinishStageCut.run (implementation coins setup checks representation created)
          (simulateQ (RegistrationNativeBeaconPhaseCommutation.agreement setup owner scalar) (RegistrationAgreementExecutor.beacon authenticated)) authenticatedEnv authenticatedState) ∧
      registration.begin_beacon_completion initial.agreement=.ok initial ∧
      ((.ok (.Ok completed),reached.1.1.1.2),(reached.1.1.2,reached.1.2))∈support
        (RegistrationNativePlatformPublicAdapterFinishStageCut.run (implementation coins setup checks representation created)
          (simulateQ (RegistrationNativeBeaconPhaseCommutation.record setup wire) (RegistrationBeaconRecordExecutor.fromInitial initial)) middleEnv middle) ∧
      reached.1.1.1.1=.ok (some completed) :=by
  have logged:(result reached)∈support (RegistrationNativePlatformPublicAdapterFinishStageCut.logged
      (implementation coins setup checks representation created)
      (RegistrationNativePlatformPublicAdapterFinishLoggedFactor.body setup wire note pending
        (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)) owner scalar)
      (RegistrationWorldAgreementCompiler.erase before.server.world) past (before,previous)) :=by
    rw [←sample_source coins setup checks representation created wire note pending input owner scalar before previous past,support_map]
    exact ⟨reached,supported,rfl⟩
  exact RegistrationNativePlatformPublicAdapterFinishStageCut.body_cut (implementation coins setup checks representation created)
    setup wire note injective initial completed pending
    (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)) owner scalar
    (RegistrationWorldAgreementCompiler.erase before.server.world) past (before,previous) (result reached) logged present

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSampleStageCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSampleStageCut.free_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSampleStageCut.free_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSampleStageCut.sample_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSampleStageCut.sample_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSampleStageCut.sample_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSampleStageCut.sample_cut
