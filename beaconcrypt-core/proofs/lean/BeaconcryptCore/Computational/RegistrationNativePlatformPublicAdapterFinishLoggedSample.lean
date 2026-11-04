-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedOutput
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishRunnerSource
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedSample
open BeaconcryptCore.Refinement
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationNativePlatformSdkReification (Backend backend)
open RegistrationNativePlatformExtractedSdkFinish (BodyResult sourceProjection)
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
open AdapterPublicFinishLifetime (packet)
variable {n :Nat} {I KemSK P Log :Type} {base :OracleSpec I} {mlSource :RegistrationNativeMldsa.Source}
variable [material :PublicWrapperPlatform.Material] [ed :AdapterInitEdPrimitive.Operations]
local notation "Native"=>RegistrationNativeExperiment.State n KemSK mlSource

noncomputable def nativeResult (self :beaconcrypt_public_wrapper.beacon.Beacon) (pending :registration.BeaconPending)
    (reached :(BodyResult n KemSK mlSource×P)×List Log) :((RustM AdapterPublicFinishBody.Result×List Log)×Native)×P :=
  ((((sourceProjection self pending reached.1.1).1,reached.2),reached.1.1.2),reached.1.2)

theorem native (coins :QueryImpl unifSpec (StateT P ProbComp))
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (checks :PqxdhServerAuthExperiment.Checks)
    (representation :RegistrationServerRoleBackend.ConvertedIdentity setup) (created :PqxdhLiveServerConstruction.Created Unit)
    (wire :RegistrationNativeWire.Wire) (note :Stage→Log) (self :beaconcrypt_public_wrapper.beacon.Beacon)
    (pending :registration.BeaconPending) (input :Slice U8) (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes)
    (before :Native) (previous :P) (past :List Log) :
    nativeResult self pending <$>
      RegistrationNativePlatformPublicAdapterFinishLoggedFactor.sample setup wire note coins checks representation created
        pending (packet input) owner scalar before previous past=
      (simulateQ coins ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource)
        ((RegistrationNativePlatformPublicAdapterFinishLoggedOutput.program setup wire note self pending input owner scalar).run past)).run before)).run previous :=by
  have sourceLaw:=RegistrationNativePlatformPublicAdapterFinishLoggedOutput.program_projection (n:=n) setup wire note self pending input owner scalar
    (RegistrationWorldAgreementCompiler.erase before.server.world,past)
  have interpreted:=congrArg (fun tree=>(simulateQ coins ((simulateQ
    (RegistrationNativeExperiment.trusted setup checks representation created mlSource) tree).run before)).run previous) sourceLaw
  simp only [simulateQ_map,StateT.run_map] at interpreted
  have decoded:RegistrationNativePlatformExtractedSdkFinish.decodedPacket (packet input)=
      RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input):=
    AdapterPublicFinishLifetime.packet_roundtrip input
  unfold RegistrationNativePlatformPublicAdapterFinishLoggedFactor.sample
  rw [decoded]
  simp only [Functor.map_map]
  exact interpreted.symm

theorem platform (coins :QueryImpl unifSpec (StateT P ProbComp))
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (checks :PqxdhServerAuthExperiment.Checks)
    (representation :RegistrationServerRoleBackend.ConvertedIdentity setup) (created :PqxdhLiveServerConstruction.Created Unit)
    (wire :RegistrationNativeWire.Wire) (note :Stage→Log) (self :beaconcrypt_public_wrapper.beacon.Beacon)
    (pending :registration.BeaconPending) (input :Slice U8) (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes)
    (before :Native) (previous :P) (past :List Log) :
    (Prod.map (Prod.map id backend) id ∘nativeResult self pending) <$>
      RegistrationNativePlatformPublicAdapterFinishLoggedFactor.sample setup wire note coins checks representation created
        pending (packet input) owner scalar before previous past=
      (simulateQ coins ((simulateQ (RegistrationNativePlatformSdkFinishBackend.handler setup checks representation created)
        ((RegistrationNativePlatformPublicAdapterFinishLoggedOutput.program setup wire note self pending input owner scalar).run past)).run (backend before))).run previous :=by
  have first:=congrArg (fun action=>Prod.map (Prod.map id backend) id <$>action)
    (native coins setup checks representation created wire note self pending input owner scalar before previous past)
  simp only [Functor.map_map] at first
  exact first.trans (RegistrationNativePlatformSdkFinishBackend.platform coins setup checks representation created
    ((RegistrationNativePlatformPublicAdapterFinishLoggedOutput.program setup wire note self pending input owner scalar).run past)
    (RegistrationNativePlatformPublicAdapterFinishLoggedOutput.program_safe setup wire note self pending input owner scalar past) before previous)

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedSample

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedSample.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedSample.native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedSample.platform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedSample.platform
