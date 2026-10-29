-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordHiddenPublication

/-! The successful actual native publication and its arbitrary same-run residual keep the selected hidden origin at the returned physical record handle. The full reached cursor, control and private service state are threaded into that residual. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeRecordHiddenPersistence
open PqxdhRecordLiftInterface (WorldSpec Slot effectLift)
open PqxdhRecordLiftProtocol (Control)
variable {n : Nat} {Encoded Reader Response Secret Value : Type}

/-- The actual returned Server peer retains its same hidden slot through every later record or administrative command. -/
theorem server (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (control : pqxdh.ServerState) (slot : Slot n) (published : registration.PublishedServerResponse Encoded)
    (peer : peer.PublishedPeer Encoded) (shell : CborRecordWorldClient.Shell) (before : Control n)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before) (secret : Secret)
    (middle : ((RustM (RegistrationHiddenInstall.Result Encoded) × CborRecordWorldClient.Shell) × Control n) × Secret)
    (supported : middle ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      (simulateQ effectLift (RegistrationHiddenInstall.install control slot published)) shell before secret))
    (successful : middle.1.1.1 = .ok (.Ok peer)) (work : OracleComp (WorldSpec n) Value)
    (result : ((Value × CborRecordWorldClient.Shell) × Control n) × Secret)
    (continued : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route work middle.1.1.2 middle.1.2 middle.2)) :
    PqxdhRecordLiftIdeal.handleSlot result.1.2 (.peer peer.key_id) = some slot := by
  have installed := RegistrationNativeRecordHiddenPublication.server service codec route control slot published peer shell before secret middle supported successful
  have valid := RegistrationNativeRecordHandleSlots.interpreted service codec route _ shell before safe secret middle supported
  exact (RegistrationNativeRecordHandleSlots.interpreted service codec route work middle.1.1.2 middle.1.2 valid.1 middle.2 result continued).2
    (.peer peer.key_id) slot installed

/-- The actual established physical Beacon owner retains its same hidden slot through the original residual execution. -/
theorem beacon (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (owner : Nat) (sender : U64) (slot : Slot n) (prepared : RustM RegistrationBeaconRecordExecutor.Result)
    (completed : RegistrationBeaconSeed.PublicCompleted) (shell : CborRecordWorldClient.Shell) (before : Control n)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before) (secret : Secret)
    (middle : ((RustM RegistrationNativePairedBeaconService.Result × CborRecordWorldClient.Shell) × Control n) × Secret)
    (supported : middle ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      (simulateQ effectLift (RegistrationNativePairedBeaconService.after owner sender (fun _ => .hidden slot) prepared)) shell before secret))
    (successful : middle.1.1.1 = .ok (.Ok completed)) (work : OracleComp (WorldSpec n) Value)
    (result : ((Value × CborRecordWorldClient.Shell) × Control n) × Secret)
    (continued : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route work middle.1.1.2 middle.1.2 middle.2)) :
    PqxdhRecordLiftIdeal.handleSlot result.1.2 (.owner owner) = some slot := by
  have installed := RegistrationNativeRecordHiddenPublication.beacon service codec route owner sender slot prepared completed shell before secret middle supported successful
  have valid := RegistrationNativeRecordHandleSlots.interpreted service codec route _ shell before safe secret middle supported
  exact (RegistrationNativeRecordHandleSlots.interpreted service codec route work middle.1.1.2 middle.1.2 valid.1 middle.2 result continued).2
    (.owner owner) slot installed

end BeaconcryptCore.Computational.RegistrationNativeRecordHiddenPersistence

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordHiddenPersistence.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordHiddenPersistence.server
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordHiddenPersistence.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordHiddenPersistence.beacon
