-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordHiddenWorld
import BeaconcryptCore.Computational.RegistrationNativePairedBeaconService

/-! Successful actual native publication continuations install their same hidden reference. The Server receipt uses the returned native peer key ID, and the Beacon receipt uses its actual physical owner index. All cursor, control and private poststates are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRecordHiddenPublication
open PqxdhRecordLiftInterface (Slot effectLift)
open PqxdhRecordLiftProtocol (Control)
variable {n : Nat} {Encoded Reader Response Secret : Type}

/-- The actual successful hidden peer-insertion continuation installs the slot at exactly its returned key ID. -/
theorem server (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (control : pqxdh.ServerState) (slot : Slot n) (published : registration.PublishedServerResponse Encoded)
    (peer : peer.PublishedPeer Encoded) (shell : CborRecordWorldClient.Shell) (before : Control n) (secret : Secret)
    (result : ((RustM (RegistrationHiddenInstall.Result Encoded) × CborRecordWorldClient.Shell) × Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      (simulateQ effectLift (RegistrationHiddenInstall.install control slot published)) shell before secret))
    (successful : result.1.1.1 = .ok (.Ok peer)) :
    PqxdhRecordLiftIdeal.handleSlot result.1.2 (.peer peer.key_id) = some slot := by
  obtain ⟨prepared, prepareRun, _retained⟩ := BeaconcryptCore.Refinement.PeerOwnership.peer_insert_begin_retains control published
  cases prepared with
  | Err previous =>
      simp only [RegistrationHiddenInstall.install, prepareRun] at supported
      change result ∈ support (pure (((.ok (.Err previous), shell), before), secret)) at supported
      rw [mem_support_pure_iff] at supported
      subst result
      cases successful
  | Ok pending =>
      rw [RegistrationHiddenInstall.install_native control slot published pending prepareRun] at supported
      simp only [simulateQ_bind, simulateQ_pure] at supported
      rw [CborRawRecordOriginFlatten.interpret_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, installed, finished⟩ := supported
      rw [CborRawRecordOriginFlatten.interpret_pure, mem_support_pure_iff] at finished
      subst result
      cases selected : middle.1.1.1 with
      | false =>
          simp only [selected, BeaconcryptCore.Refinement.PeerOwnership.publication_finish] at successful
          cases successful
      | true =>
          have origin := RegistrationNativeRecordHiddenWorld.server service codec route
            pending.peer.binding.assigned_key_id (PqxdhRecordLiftInterface.PeerBinding.ofSession pending.peer.binding)
            slot shell before secret middle installed selected
          simp only [selected, BeaconcryptCore.Refinement.PeerOwnership.publication_finish,
            ite_true, RustM.ok.injEq, core.result.Result.Ok.injEq] at successful
          have key : peer.key_id = pending.peer.binding.assigned_key_id :=
            (congrArg (fun value : beaconcrypt_core.peer.PublishedPeer Encoded => value.key_id) successful).symm
          rw [key]
          exact origin

/-- The actual successful hidden Beacon continuation installs the same slot at its physical owner handle. -/
theorem beacon (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (owner : Nat) (sender : U64) (slot : Slot n) (prepared : RustM RegistrationBeaconRecordExecutor.Result)
    (completed : RegistrationBeaconSeed.PublicCompleted)
    (shell : CborRecordWorldClient.Shell) (before : Control n) (secret : Secret)
    (result : ((RustM RegistrationNativePairedBeaconService.Result × CborRecordWorldClient.Shell) × Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      (simulateQ effectLift (RegistrationNativePairedBeaconService.after owner sender (fun _ => .hidden slot) prepared)) shell before secret))
    (successful : result.1.1.1 = .ok (.Ok completed)) :
    PqxdhRecordLiftIdeal.handleSlot result.1.2 (.owner owner) = some slot := by
  cases prepared with
  | fail error | div =>
      simp only [RegistrationNativePairedBeaconService.after, simulateQ_pure,
        CborRawRecordOriginFlatten.interpret_pure, mem_support_pure_iff] at supported
      subst result
      cases successful
  | ok prepared => cases prepared with
    | Err aborted =>
        simp only [RegistrationNativePairedBeaconService.after, simulateQ_pure,
          CborRawRecordOriginFlatten.interpret_pure, mem_support_pure_iff] at supported
        subst result
        cases successful
    | Ok prepared =>
        simp only [RegistrationNativePairedBeaconService.after, simulateQ_bind,
          simulateQ_spec_query, simulateQ_pure] at supported
        rw [CborRawRecordOriginFlatten.interpret_bind, mem_support_bind_iff] at supported
        obtain ⟨middle, installed, finished⟩ := supported
        rw [CborRawRecordOriginFlatten.interpret_pure, mem_support_pure_iff] at finished
        subst result
        cases selected : middle.1.1.1 with
        | false => simp only [selected, Bool.false_eq_true, ite_false] at successful; cases successful
        | true =>
            exact RegistrationNativeRecordHiddenWorld.beacon service codec route owner
              ⟨sender, prepared.control, prepared.binding.associated_data⟩ slot shell before secret middle installed selected

end BeaconcryptCore.Computational.RegistrationNativeRecordHiddenPublication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordHiddenPublication.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordHiddenPublication.server
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordHiddenPublication.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordHiddenPublication.beacon
