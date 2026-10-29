-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSigningView

/-! Actual first-record response completion, signing and peer installation observe no omitted private accounting fields. Complete response results and reached operational state remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeCompletionView
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationWorldAgreement (State)
open RegistrationServerRecordWorldSource (project)
open RegistrationStateView (Stable)
variable {n : Nat} {Auxiliary Encoded ι KemSK Reader Response : Type} {base : OracleSpec ι}

/-- Actual peer insertion retains each gate, source-selected identifier and installed full kernel. -/
theorem install_input (control : pqxdh.ServerState) (published : registration.PublishedServerResponse Encoded) :
    Stable (project (n := n) (Auxiliary := Auxiliary)) (RegistrationWorldServerCompletion.install control published) := by
  cases prepared : peer.begin_peer_insert control published with
  | fail error | div =>
      simp only [RegistrationWorldServerCompletion.install, prepared]
      exact RegistrationStateView.pure_stable _ RegistrationNativeLocalView.project_idempotent _
  | ok outcome =>
      cases outcome with
      | Err previous =>
          simp only [RegistrationWorldServerCompletion.install, prepared]
          exact RegistrationStateView.pure_stable _ RegistrationNativeLocalView.project_idempotent _
      | Ok pending =>
          rw [RegistrationWorldServerCompletion.install_native control published pending prepared]
          apply RegistrationStateView.bind_stable
          · exact RegistrationNativeLocalView.capability_input _
          · intro inserted
            exact RegistrationStateView.pure_stable _ RegistrationNativeLocalView.project_idempotent _

/-- Publication retains failed signing and packing state before any successful peer installation. -/
theorem publish_input
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded) (control : pqxdh.ServerState)
    (pending : registration.ServerResponseHash) :
    Stable (project (n := n) (Auxiliary := Auxiliary))
      (RegistrationWorldServerCompletion.publish sign encode control pending) := by
  unfold RegistrationWorldServerCompletion.publish
  apply RegistrationStateView.bind_stable
  · exact RegistrationNativeSigningView.signing_input sign encode pending
  · intro published
    cases published with
    | fail error | div => exact RegistrationStateView.pure_stable _ RegistrationNativeLocalView.project_idempotent _
    | ok outcome => cases outcome with
      | Err previous => exact RegistrationStateView.pure_stable _ RegistrationNativeLocalView.project_idempotent _
      | Ok published => exact install_input control published

/-- The entire actual initial-record controller preserves optional failures, AD, ciphertext and consumed kernel. -/
theorem initial_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded) (control : pqxdh.ServerState)
    (pending : registration.ServerInitialKdf) :
    Stable (project (n := n) (Auxiliary := Auxiliary))
      (RegistrationWorldServerCompletion.fromInitial setup codec sign encode control pending) := by
  unfold RegistrationWorldServerCompletion.fromInitial
  apply RegistrationStateView.bind_stable
  · exact RegistrationNativeLocalView.record_program setup codec _
  · intro record
    cases record with
    | fail error | div => exact RegistrationStateView.pure_stable _ RegistrationNativeLocalView.project_idempotent _
    | ok outcome => cases outcome with
      | Err previous => exact RegistrationStateView.pure_stable _ RegistrationNativeLocalView.project_idempotent _
      | Ok pending => exact publish_input sign encode control pending

end BeaconcryptCore.Computational.RegistrationNativeCompletionView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCompletionView.install_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCompletionView.install_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCompletionView.publish_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCompletionView.publish_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCompletionView.initial_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCompletionView.initial_input
