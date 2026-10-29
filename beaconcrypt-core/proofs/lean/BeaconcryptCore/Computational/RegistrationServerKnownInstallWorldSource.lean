-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerPublicationWorldCompiler
import BeaconcryptCore.Computational.RegistrationWorldServerCompletion
import BeaconcryptCore.Computational.RegistrationNativePairedServerService

/-! Source peer insertion transfers exactly the completed native kernel through the same known-install Env capability. Every native allocator/pin failure and final publication decision is preserved before the SDK commit wrapper. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerKnownInstallWorldSource
open RegistrationServerPublicationWorldCompiler (effect)
variable {n : Nat} {Auxiliary Encoded : Type}

/-- Native source insertion is precisely the actual known-kernel installation program on the same current World. -/
theorem install (control : pqxdh.ServerState) (published : registration.PublishedServerResponse Encoded) :
    RegistrationWorldServerCompletion.install (n := n) (Auxiliary := Auxiliary) control published =
      simulateQ effect (RegistrationNativePairedServerService.knownInstall control published) := by
  cases prepared : peer.begin_peer_insert control published with
  | fail error =>
      simp only [RegistrationWorldServerCompletion.install, RegistrationNativePairedServerService.knownInstall, prepared]
      rfl
  | div =>
      simp only [RegistrationWorldServerCompletion.install, RegistrationNativePairedServerService.knownInstall, prepared]
      rfl
  | ok answer =>
      cases answer with
      | Err previous =>
          simp only [RegistrationWorldServerCompletion.install, RegistrationNativePairedServerService.knownInstall, prepared]
          rfl
      | Ok pending =>
          rw [RegistrationWorldServerCompletion.install_native control published pending prepared,
            RegistrationNativePairedServerService.knownInstall_native control published pending prepared]
          simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
          rfl

/-- The actual finite post-publication branch runs that same known insertion and preserves every failure outcome. -/
theorem after (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded)) :
    simulateQ (effect (n := n) (Auxiliary := Auxiliary))
        (RegistrationNativePairedServerService.knownAfter control published) =
      (match published with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok (.Err previous) => pure (.ok (.Err previous))
      | .ok (.Ok value) => RegistrationWorldServerCompletion.install control value) := by
  cases published with
  | fail error => rfl
  | div => rfl
  | ok answer =>
      cases answer with
      | Err previous => rfl
      | Ok value => exact (install control value).symm

end BeaconcryptCore.Computational.RegistrationServerKnownInstallWorldSource

/-- info: 'BeaconcryptCore.Computational.RegistrationServerKnownInstallWorldSource.install' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerKnownInstallWorldSource.install
/-- info: 'BeaconcryptCore.Computational.RegistrationServerKnownInstallWorldSource.after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerKnownInstallWorldSource.after
