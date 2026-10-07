-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftInterface

/-! The exact ordinary-record quotient of the source Beacon. Inactive registration fields are erased because record dispatch never reads them; established sender, control, AD and complete kernel remain. No dummy private key or control value is constructed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftBeacon
open PqxdhRecordLiftInterface (BeaconShell InactivePhase)
variable {Identity DhPair KemPair : Type}

/-- Inactive source phase tags are enough for rejection and later administrative checks. -/
inductive Phase where
  | inactive (phase : InactivePhase)
  | established (shell : BeaconShell) (kernel : ConcreteRatchetKernel)

/-- The raw-attempt ghost remains separate from the source's native fields. -/
structure State where
  phase : Phase
  rawAttempts : Nat

/-- Only established record dispatch reads the outer sender, control and stored AD. -/
def projectPhase (beacon : RawCtxBeaconLifecycle.Beacon Identity DhPair KemPair) : Phase :=
  match beacon.phase with
  | .fresh _ _ _ => .inactive .fresh
  | .freshWithCoins _ _ _ _ => .inactive .freshWithCoins
  | .initSent _ _ _ _ => .inactive .initSent
  | .aborted _ => .inactive .aborted
  | .established control associatedData kernel =>
      .established ⟨beacon.identityKeyId, control, associatedData⟩ kernel

/-- No source private field is fabricated when taking this view. -/
def project (state : RawCtxBeaconLifecycle.State Identity DhPair KemPair) : State :=
  ⟨projectPhase state.beacon, state.rawAttempts⟩

/-- Put an ordinary-record result back into the original full source frame. Registration fields and inactive payloads always remain the original values. -/
def putback (before : RawCtxBeaconLifecycle.State Identity DhPair KemPair) (after : State) :
    RawCtxBeaconLifecycle.State Identity DhPair KemPair :=
  match before.beacon.phase, after.phase with
  | .established control associatedData _, .established _ kernel =>
      ⟨{ before.beacon with phase := .established control associatedData kernel }, after.rawAttempts⟩
  | _, _ => { before with rawAttempts := after.rawAttempts }

/-- The same native inactive reply and separate raw counter update. -/
def rejected (query : RawCtxMixedOwner.SourceSpec.Domain) (state : State) :
    RawCtxMixedOwner.SourceSpec.Range query × State :=
  match query with
  | .inl _ => (none, state)
  | .inr _ => (.None, { state with rawAttempts := state.rawAttempts + 1 })

/-- Established requests reuse the unchanged whole-owner handler and its exact optional reply. -/
noncomputable def handler (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl RawCtxMixedOwner.SourceSpec (StateT State (OracleComp RawCtxMixedOwner.NativeSpec)) :=
  fun query state =>
    match state.phase with
    | .inactive _ => pure (rejected query state)
    | .established shell kernel => do
        let result ← (RawCtxMixedOwner.ownerImpl shell.identityKeyId decode query).run
          ⟨⟨kernel, shell.control.server_binding.identity_key_id,
            PqxdhRefinement.absBytes shell.associatedData, ()⟩, state.rawAttempts⟩
        pure (result.1, ⟨.established shell result.2.owner.kernel, result.2.rawAttempts⟩)

/-- Projecting the actual source step equals the minimal handler, with every primitive effect retained. -/
theorem step_project (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : RawCtxBeaconLifecycle.State Identity DhPair KemPair) :
    Prod.map id project <$> (RawCtxBeaconLifecycle.beaconImpl decode query).run state =
      (handler decode query).run (project state) := by
  cases phase : state.beacon.phase
  all_goals simp only [RawCtxBeaconLifecycle.beaconImpl, StateT.run, phase,
    project, projectPhase, handler, map_pure, bind_pure_comp, Functor.map_map,
    RawCtxBeaconLifecycle.selected, RawCtxBeaconLifecycle.reinstall, Prod.map]
  all_goals cases query <;> simp only [RawCtxBeaconLifecycle.rejected, rejected,
    phase, id_eq]

/-- Putting an unchanged projection back preserves every full source field. -/
theorem putback_project (state : RawCtxBeaconLifecycle.State Identity DhPair KemPair) :
    putback state (project state) = state := by
  cases phase : state.beacon.phase <;> simp only [putback, project, projectPhase, phase]
  rw [← phase]

/-- Reinstalling one minimal step in its original source frame is exactly the native step. -/
theorem step_putback (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : RawCtxBeaconLifecycle.State Identity DhPair KemPair) :
    Prod.map id (putback state) <$> (handler decode query).run (project state) =
      (RawCtxBeaconLifecycle.beaconImpl decode query).run state := by
  cases phase : state.beacon.phase
  all_goals simp only [RawCtxBeaconLifecycle.beaconImpl, StateT.run, phase,
    project, projectPhase, handler, map_pure, bind_pure_comp, Functor.map_map,
    RawCtxBeaconLifecycle.selected, RawCtxBeaconLifecycle.reinstall, Prod.map, putback]
  all_goals cases query <;> simp only [RawCtxBeaconLifecycle.rejected, rejected, id_eq]

/-- Actual deployment logging and any primitive interpreter retain the exact native result after put-back, including failed-writer frames and the complete primitive poststate. -/
theorem logged_putback {PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxMixedOwner.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : RawCtxBeaconLifecycle.State Identity DhPair KemPair) (primitive : PrimitiveState) :
    (fun result => (((result.1.1.1, putback state result.1.1.2), result.1.2), result.2)) <$>
      (simulateQ impl (PqxdhDeploymentNative.logged ((handler decode query).run (project state)))).run primitive =
      (simulateQ impl (PqxdhDeploymentNative.logged
        ((RawCtxBeaconLifecycle.beaconImpl decode query).run state))).run primitive := by
  have same := congrArg (fun work => (simulateQ impl (PqxdhDeploymentNative.logged work)).run primitive)
    (step_putback decode query state)
  simpa only [PqxdhDeploymentNative.logged_map, simulateQ_map, StateT.run_map, Prod.map, id_eq] using same

/-- Put-back never replaces outer identity, sender or pin, even for arbitrary projected values. -/
theorem putback_fields (before : RawCtxBeaconLifecycle.State Identity DhPair KemPair) (after : State) :
    (putback before after).beacon.identity = before.beacon.identity ∧
      (putback before after).beacon.identityKeyId = before.beacon.identityKeyId ∧
      (putback before after).beacon.serverIdentity = before.beacon.serverIdentity ∧
      (putback before after).rawAttempts = after.rawAttempts := by
  cases hb : before.beacon.phase <;> cases ha : after.phase <;> simp only [putback, hb, ha, and_self]

/-- Every minimal state has the exact source service bound, without fabricating a full native owner. -/
theorem handler_bound (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : State) (kind : RawCtxMixedOwner.CallKind) :
    ((handler decode query).run state).IsQueryBoundP
      (fun request => RawCtxMixedOwner.callKind request = kind)
      (match query with
       | .inl _ => RawCtxMixedOwner.sendCost kind
       | .inr _ => RawCtxMixedOwner.receiveCost kind) := by
  cases phase : state.phase
  all_goals simp only [handler, StateT.run, phase, isQueryBoundP_pure,
    bind_pure_comp, isQueryBoundP_map_iff]
  cases query with
  | inl plaintext => exact RawCtxMixedOwner.send_bounds _ _ _ _ _
  | inr raw => exact RawCtxMixedOwner.receive_bounds _ _ _ _ _

/-- The quotient preserves the existing native primitive budget for every source state. -/
theorem step_bound (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : RawCtxBeaconLifecycle.State Identity DhPair KemPair) (kind : RawCtxMixedOwner.CallKind) :
    ((handler decode query).run (project state)).IsQueryBoundP
      (fun request => RawCtxMixedOwner.callKind request = kind)
      (match query with
       | .inl _ => RawCtxMixedOwner.sendCost kind
       | .inr _ => RawCtxMixedOwner.receiveCost kind) := by
  rw [← step_project, isQueryBoundP_map_iff]
  exact RawCtxBeaconLifecycle.step_bound decode query state kind

end BeaconcryptCore.Computational.PqxdhRecordLiftBeacon

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftBeacon.step_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftBeacon.step_project
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftBeacon.putback_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftBeacon.putback_project
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftBeacon.step_putback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftBeacon.step_putback
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftBeacon.putback_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftBeacon.putback_fields
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftBeacon.step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftBeacon.step_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftBeacon.handler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftBeacon.handler_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftBeacon.logged_putback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftBeacon.logged_putback
