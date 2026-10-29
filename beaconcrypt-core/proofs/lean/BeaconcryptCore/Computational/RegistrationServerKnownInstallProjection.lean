-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerKnownInstallWorldSource

/-! The actual known Server insertion ignores only the explicitly omitted proof counters/log. Actual peer vacancy, full binding/kernel transfer and final publication success or failure are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerKnownInstallProjection
open RegistrationServerRecordWorldSource (project)
variable {n : Nat} {Auxiliary Encoded : Type}

/-- The actual current-World known insertion capability preserves the whole local source view. -/
theorem capability (keyId : U64) (identity : PqxdhRecordLiftInterface.PeerBinding)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id project <$>
      (RegistrationWorldServerCompletion.capability (.installServer keyId identity (.known kernel))).run before =
      (RegistrationWorldServerCompletion.capability (.installServer keyId identity (.known kernel))).run (project before) := by
  have source := congrArg (fun distribution => (fun result => (result.1,
    { project before with world := (result.2, before.world.2) })) <$> distribution)
    (RegistrationServerWorldInstallSource.install keyId identity kernel before.world.1)
  simpa only [RegistrationWorldServerCompletion.capability, StateT.run, Functor.map_map,
    Prod.map_def, id_eq, project] using source

/-- The complete native peer-insertion controller retains the same full published peer and actual install decision. -/
theorem install (control : pqxdh.ServerState) (published : registration.PublishedServerResponse Encoded)
    (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id project <$> (RegistrationWorldServerCompletion.install control published).run before =
      (RegistrationWorldServerCompletion.install control published).run (project before) := by
  cases prepared : peer.begin_peer_insert control published with
  | fail error =>
      simp only [RegistrationWorldServerCompletion.install, prepared]
      rfl
  | div =>
      simp only [RegistrationWorldServerCompletion.install, prepared]
      rfl
  | ok result =>
      cases result with
      | Err previous =>
          simp only [RegistrationWorldServerCompletion.install, prepared]
          rfl
      | Ok pending =>
          rw [RegistrationWorldServerCompletion.install_native control published pending prepared]
          simp only [bind_pure_comp]
          have source := congrArg (fun distribution => (fun result =>
            ((⟨pending.previous, pending.next, pending.peer.binding.assigned_key_id, pending.encoded⟩ :
              peer.PublicationFinish Encoded).finish result.1, result.2)) <$> distribution)
            (capability pending.peer.binding.assigned_key_id
              (PqxdhRecordLiftInterface.PeerBinding.ofSession pending.peer.binding)
              pending.peer.ratchet before)
          simpa only [StateT.run_map, Functor.map_map, Prod.map_def, id_eq] using source

noncomputable def after (control : pqxdh.ServerState) :
    RustM (RegistrationWorldServerPublication.Result Encoded) →
      StateT (RegistrationWorldAgreement.State n Auxiliary) ProbComp
        (RustM (RegistrationWorldServerCompletion.Result Encoded))
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err previous) => pure (.ok (.Err previous))
  | .ok (.Ok published) => RegistrationWorldServerCompletion.install control published

/-- Every native publication outcome resumes exactly the same source-view insertion or failure branch. -/
theorem after_project (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded))
    (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id project <$> (after control published).run before = (after control published).run (project before) := by
  cases published with
  | fail error => rfl
  | div => rfl
  | ok result =>
      cases result with
      | Err previous => rfl
      | Ok value => exact install control value before

end BeaconcryptCore.Computational.RegistrationServerKnownInstallProjection

/-- info: 'BeaconcryptCore.Computational.RegistrationServerKnownInstallProjection.capability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerKnownInstallProjection.capability
/-- info: 'BeaconcryptCore.Computational.RegistrationServerKnownInstallProjection.install' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerKnownInstallProjection.install
/-- info: 'BeaconcryptCore.Computational.RegistrationServerKnownInstallProjection.after_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerKnownInstallProjection.after_project
