-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenWorldInstall
import BeaconcryptCore.Computational.RegistrationNativePairedServerService

/-! Actual Server peer insertion has the same complete semantic World outcome under a canonical known kernel and its cached unused hidden reference. The binding, assigned identifier, native live-counter gate and publication finish are the real extracted continuations. Publication support derives the whole consumed kernel; the cached/unused receipts remain explicit local inputs until the global service/alias coupling supplies them. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3ServerInsertion
open PqxdhRecordLiftInterface (EnvEffects Slot PeerBinding)
open RegistrationNativeHiddenWorldInstall (view)
variable {n : Nat} {Encoded : Type}

/-- The actual source allocator gate and peer-publication finish agree in both kernel representations, including native insertion failure. -/
theorem install (control : pqxdh.ServerState) (slot : Slot n)
    (published : registration.PublishedServerResponse Encoded) (seed : PqxdhRecordLiftSeed.Seed)
    (canonical : published.kernel = PqxdhRecordLiftWorld.kernel .server seed)
    (before : PqxdhRecordLiftWorld.State n) (cached : before.seeds.1 slot = some seed)
    (unused : before.used slot .server = false) :
    Prod.map id view <$>
      (simulateQ PqxdhRecordLiftWorld.effects (RegistrationNativePairedServerService.knownInstall control published)).run before =
      Prod.map id view <$>
        (simulateQ PqxdhRecordLiftWorld.effects (RegistrationHiddenInstall.install control slot published)).run before := by
  obtain ⟨result, prepared, retained⟩ := BeaconcryptCore.Refinement.PeerOwnership.peer_insert_begin_retains control published
  cases result with
  | Err previous =>
      simp only [RegistrationNativePairedServerService.knownInstall, RegistrationHiddenInstall.install, prepared]
      rfl
  | Ok pending =>
      have kernel := retained.2.2.2.1
      rw [RegistrationNativePairedServerService.knownInstall_native control published pending prepared,
        RegistrationHiddenInstall.install_native control slot published pending prepared]
      have actual := RegistrationNativeHiddenWorldInstall.server_effect pending.peer.binding.assigned_key_id
        (PeerBinding.ofSession pending.peer.binding) slot seed before cached unused
      have mapped := congrArg (fun work => (fun result =>
        (((⟨pending.previous, pending.next, pending.peer.binding.assigned_key_id, pending.encoded⟩ :
          peer.PublicationFinish Encoded).finish result.1), result.2)) <$> work) actual.symm
      rw [kernel, canonical]
      let finish : Bool → RustM (RegistrationNativePairedServerService.Result Encoded) :=
        (⟨pending.previous, pending.next, pending.peer.binding.assigned_key_id, pending.encoded⟩ :
          peer.PublicationFinish Encoded).finish
      let known : OracleComp (EnvEffects n) Bool := (EnvEffects n).query
        (.inr (.installServer pending.peer.binding.assigned_key_id (PeerBinding.ofSession pending.peer.binding)
          (.known (PqxdhRecordLiftWorld.kernel .server seed))))
      let hidden : OracleComp (EnvEffects n) Bool := (EnvEffects n).query
        (.inr (.installServer pending.peer.binding.assigned_key_id (PeerBinding.ofSession pending.peer.binding) (.hidden slot)))
      change Prod.map id view <$> (simulateQ PqxdhRecordLiftWorld.effects (known >>= fun inserted => pure (finish inserted))).run before =
        Prod.map id view <$> (simulateQ PqxdhRecordLiftWorld.effects (hidden >>= fun inserted => pure (finish inserted))).run before
      rw [bind_pure_comp, bind_pure_comp]
      simp only [known, hidden, finish, simulateQ_map, simulateQ_spec_query, StateT.run_map,
        Functor.map_map, Prod.map_def, id_eq] at mapped ⊢
      convert mapped using 1 <;> rfl

/-- Every supported native publication result reaches the same real insertion behavior; encoding/signing rejection remains rejection. -/
theorem after_publication (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (slot : Slot n) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (material : PqxdhDeploymentHiddenLayout.Material) (seed : PqxdhRecordLiftSeed.Seed)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded))
    (supported : published ∈ support (RegistrationBoundPublication.program encode initial
      (PqxdhDeploymentHiddenLayout.joinOutput material seed)))
    (before : PqxdhRecordLiftWorld.State n) (cached : before.seeds.1 slot = some seed)
    (unused : before.used slot .server = false) :
    Prod.map id view <$>
      (simulateQ PqxdhRecordLiftWorld.effects (RegistrationNativePairedServerService.knownAfter control published)).run before =
      Prod.map id view <$>
        (simulateQ PqxdhRecordLiftWorld.effects (RegistrationHiddenInstall.after control slot published)).run before := by
  cases published with
  | fail error => rfl
  | div => rfl
  | ok result =>
      cases result with
      | Err previous => rfl
      | Ok published =>
          exact install control slot published seed
            (RegistrationBoundPublication.published_kernel encode initial material seed published supported) before cached unused

end BeaconcryptCore.Computational.RegistrationNativeG3ServerInsertion

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3ServerInsertion.install' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3ServerInsertion.install
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3ServerInsertion.after_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3ServerInsertion.after_publication
