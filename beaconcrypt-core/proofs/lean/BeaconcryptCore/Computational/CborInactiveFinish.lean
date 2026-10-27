-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborTaggedFinish

/-! Missing and non-InitSent owners reject every raw finish input before any native callback. These equalities include fresh owners and preserve the complete scheduler and deployment state, so the public response tag is irrelevant outside an active finish. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborInactiveFinish
open PqxdhServerAuthExperiment PqxdhRegistrationSchedule

theorem native_inactive {I D K X Response : Type} (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : RawCtxBeaconLifecycle.State I D K)
    (inactive : ∀ control prekey oneTime kem, state.beacon.phase ≠ .initSent control prekey oneTime kem) :
    PqxdhBeaconPhase2Publication.nativeOwner (X := X) (Response := Response) decode raw state =
      pure (none, state) := by
  rw [PqxdhBeaconPhase2Publication.nativeOwner,
    PqxdhBeaconPhase2Publication.owner_inactive decode raw state inactive]
  simp only [simulateQ_pure]

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

theorem schedule_inactive (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (raw : Pqxdh.Bytes) (state : PqxdhRegistrationSchedule.State KemSK) (owner : Owner KemSK)
    (found : state.owners[index]? = some owner)
    (inactive : ∀ control prekey oneTime kem, owner.beacon.phase ≠ .initSent control prekey oneTime kem) :
    PqxdhRegistrationSchedule.finish setup codec index raw state = pure (none, state) := by
  rw [finish_source setup codec index raw state owner found,
    native_inactive codec.frameRead raw owner inactive]
  simp only [simulateQ_pure, StateT.run_pure, map_pure]
  obtain ⟨bound, atIndex⟩ := List.getElem?_eq_some_iff.mp found
  rw [← atIndex, List.set_getElem_self bound]

theorem schedule_no_active (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (raw : Pqxdh.Bytes) (state : PqxdhRegistrationSchedule.State KemSK)
    (inactive : ∀ owner, state.owners[index]? = some owner →
      ∀ control prekey oneTime kem, owner.beacon.phase ≠ .initSent control prekey oneTime kem) :
    PqxdhRegistrationSchedule.finish setup codec index raw state = pure (none, state) := by
  cases found : state.owners[index]?
  case some owner => exact schedule_inactive setup codec index raw state owner found (inactive owner found)
  exact finish_missing setup codec index raw state found

theorem deployment_inactive (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder) (seed : PqxdhJointIdentity.IdentitySeed)
    (index : Nat) (raw : Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK)
    (inactive : ∀ owner, state.native.owners[index]? = some owner →
      ∀ control prekey oneTime kem, owner.beacon.phase ≠ .initSent control prekey oneTime kem) :
    (PqxdhDeploymentNative.handler setup codec checks route seed (.inr (.finish index raw))).run state =
      pure (none, state) := by
  simp only [PqxdhDeploymentNative.handler, PqxdhRegistrationSchedule.handler,
    PqxdhDeploymentNative.onNative, StateT.run, schedule_no_active setup codec index raw state.native inactive,
    map_pure]

end BeaconcryptCore.Computational.CborInactiveFinish

/-- info: 'BeaconcryptCore.Computational.CborInactiveFinish.native_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborInactiveFinish.native_inactive
/-- info: 'BeaconcryptCore.Computational.CborInactiveFinish.schedule_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborInactiveFinish.schedule_inactive
/-- info: 'BeaconcryptCore.Computational.CborInactiveFinish.schedule_no_active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborInactiveFinish.schedule_no_active
/-- info: 'BeaconcryptCore.Computational.CborInactiveFinish.deployment_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborInactiveFinish.deployment_inactive
