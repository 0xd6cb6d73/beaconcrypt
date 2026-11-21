-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperiment
import BeaconcryptCore.Computational.RegistrationNativeConcreteReaders
import BeaconcryptCore.Refinement.AdapterPublicFinishInactive
/-! The selected dynamic-writer runtime raw finish path uses the concrete source-backed response decoder and exact corrected typed lifecycle. Malformed responses still reach that lifecycle; inactive owners return None with their complete native/platform state unchanged. This instantiates the raw adapter with literal source codecs rather than an assumed reader law. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRawFinish
open BeaconcryptCore.Refinement
open RegistrationNativePlatformMldsaProgram (coins)
variable {n : Nat} {I KemSK E Platform : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

theorem response (bytes : Pqxdh.Bytes) :
    RegistrationNativeWire.readResponse (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire) bytes =
      RegistrationNativeConcreteCodec.wire.decodeResponse bytes := RegistrationNativeConcreteReaders.response bytes

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "impl" => RegistrationNativePlatformOrdinaryExperiment.handler (n := n) setup checks RegistrationNativeConcreteCodec.wire route representation created source credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

theorem typed (index : Nat) (packet : Option registration.ResponsePacket) :
    impl (.inr (.finish index packet)) =
      RegistrationNativePlatformExperiment.liftNative coins
        (RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativePlatformBeaconFinish.finish setup source
            (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire) index packet)) := rfl

theorem raw (index : Nat) (input : Slice U8) :
    simulateQ impl (RegistrationNativeRawAdapter.adapter
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire)
      (.inr (.finish index (TranscriptAuthParts.absSlice input)))) =
      RegistrationNativeRawAdapter.resultOption <$>
        RegistrationNativePlatformExperiment.liftNative coins
          (RegistrationNativeExperiment.beacon setup checks representation created
            (RegistrationNativePlatformBeaconFinish.finish setup source
              (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire)
              index (AdapterPublicFinishLifetime.packet input))) := by
  simp only [RegistrationNativeRawAdapter.adapter, simulateQ_map, simulateQ_spec_query,
    typed, response, AdapterPublicFinishLifetime.packet]

theorem inactive (index : Nat) (input : Slice U8) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (selected : before.beacons[index]? = some owner) (inactive : AdapterPublicFinishInactive.Inactive owner) :
    (simulateQ impl (RegistrationNativeRawAdapter.adapter
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire)
      (.inr (.finish index (TranscriptAuthParts.absSlice input))))).run before = pure (none, before) := by
  rw [raw, StateT.run_map]
  change (fun result => (RegistrationNativeRawAdapter.resultOption result.1, result.2)) <$>
    simulateQ coins ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativePlatformBeaconFinish.finish setup source
        (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire)
        index (AdapterPublicFinishLifetime.packet input))).run before) = _
  rw [AdapterPublicFinishInactive.native setup checks representation created _ index owner _ before selected inactive,
    simulateQ_pure, map_pure]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformRawFinish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRawFinish.response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRawFinish.response

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRawFinish.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRawFinish.typed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRawFinish.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRawFinish.raw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRawFinish.inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRawFinish.inactive
