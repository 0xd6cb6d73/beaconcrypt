-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordHiddenPublication
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconService
/-! The actual failure-aware installation suffixes retain their exact selected hidden slot. The corrected Beacon shell uses its completed assigned identifier. Prefix publication/opening and the external platform remain in their own source interpreter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenPublication
open PqxdhRecordLiftInterface (Slot effectLift)
open PqxdhRecordLiftProtocol (Control)
variable {n : Nat} {Encoded Reader Response Secret : Type}
/-- The literal Server failure-aware insertion continuation installs its returned peer at the same hidden slot. -/
theorem server_after (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
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

/-- The actual successful hidden Beacon continuation installs the same slot at its physical owner handle. -/
theorem beacon (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (owner : Nat) (slot : Slot n) (prepared : RustM RegistrationBeaconRecordExecutor.Result)
    (completed : RegistrationBeaconSeed.PublicCompleted)
    (shell : CborRecordWorldClient.Shell) (before : Control n) (secret : Secret)
    (result : ((RustM RegistrationNativePairedBeaconService.Result × CborRecordWorldClient.Shell) × Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      (RegistrationNativePlatformPairedBeaconService.after effectLift owner (fun _ => .hidden slot) prepared) shell before secret))
    (successful : result.1.1.1 = .ok (.Ok completed)) :
    PqxdhRecordLiftIdeal.handleSlot result.1.2 (.owner owner) = some slot := by
  cases prepared with
  | fail error | div =>
      simp only [RegistrationNativePlatformPairedBeaconService.after,
        CborRawRecordOriginFlatten.interpret_pure, mem_support_pure_iff] at supported
      subst result
      cases successful
  | ok prepared => cases prepared with
    | Err aborted =>
        simp only [RegistrationNativePlatformPairedBeaconService.after,
          CborRawRecordOriginFlatten.interpret_pure, mem_support_pure_iff] at supported
        subst result
        cases successful
    | Ok prepared =>
        simp only [RegistrationNativePlatformPairedBeaconService.after] at supported
        rw [CborRawRecordOriginFlatten.interpret_bind, mem_support_bind_iff] at supported
        obtain ⟨middle, installed, finished⟩ := supported
        rw [CborRawRecordOriginFlatten.interpret_pure, mem_support_pure_iff] at finished
        subst result
        cases selected : middle.1.1.1 with
        | false => simp only [selected, Bool.false_eq_true, ite_false] at successful; cases successful
        | true =>
            exact RegistrationNativeRecordHiddenWorld.beacon service codec route owner
              ⟨prepared.binding.assigned_key_id, prepared.control, prepared.binding.associated_data⟩ slot shell before secret middle installed selected

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenPublication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenPublication.server_after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenPublication.server_after

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenPublication.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenPublication.beacon
