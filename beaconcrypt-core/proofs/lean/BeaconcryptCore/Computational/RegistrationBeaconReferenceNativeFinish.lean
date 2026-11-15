-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativePhase
import BeaconcryptCore.Computational.RegistrationBeaconResponseMetadata

/-! The actual terminal owner consumption and incoming response authentication precede the composed native agreement/record phase. The source controller uses the private scalar only in its interpreter; the executable reference controller does not carry it. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeFinish
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationBeaconReferenceCompiler (SelectedOwner eraseOwner Spec effect)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceNativeInterpreter (State implementation)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

private theorem state_bind_apply {m : Type → Type} [Monad m] {S A B : Type}
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

private theorem state_lift_apply {m : Type → Type} [Monad m] {S A : Type}
    (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (do let value ← work; pure (value, before)) := rfl

private theorem state_pure_apply {m : Type → Type} [Monad m] {S A : Type}
    (value : A) (before : S) : (pure value : StateT S m A) before = pure (value, before) := rfl

noncomputable def incoming (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) :
    RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := RegistrationServerRoleBackend.State)
      source (RustM (Option Pqxdh.Bytes)) := do
  let owner ← get
  match owner.phase with
  | .initSent pending oneTime => match pending.aborted_state with
    | .fail error => pure (.fail error)
    | .div => pure .div
    | .ok aborted => do
        modify fun current => { current with phase := .aborted aborted }
        let authenticated ← StateT.lift (StateT.lift (simulateQ effect
          (simulateQ (RegistrationAuthenticationCompiler.callbacks setup.source.crypto source.verify)
            (RegistrationResponseExecutor.begin pending (match packet with | none => .None | some value => .Some value)))))
        match authenticated with
        | .fail error => RegistrationBeaconReferenceFinish.abort owner *> pure (.fail error)
        | .div => RegistrationBeaconReferenceFinish.abort owner *> pure .div
        | .ok (.Err _) => RegistrationBeaconReferenceFinish.abort owner *> pure (.ok none)
        | .ok (.Ok accepted) => RegistrationBeaconReferenceNativePhase.phase setup owner oneTime accepted
  | _ => pure (.ok none)

/-- Factoring response authentication leaves the exact consumed owner phase and the same public prepare/material continuation. -/
theorem reference_factor (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) :
    RegistrationBeaconReferenceFinish.finish (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup source packet =
      incoming setup source packet := by
  apply StateT.ext
  intro owner
  apply StateT.ext
  intro env
  cases phase : owner.phase with
  | fresh | freshWithCoins scalar | established completed | aborted aborted =>
      simp only [RegistrationBeaconReferenceFinish.finish, incoming, StateT.run_bind, StateT.run_get,
        pure_bind, phase, StateT.run_pure]
  | initSent pending oneTime =>
      simp only [RegistrationBeaconReferenceFinish.finish, incoming, StateT.run_bind, StateT.run_get,
        pure_bind, phase]
      cases moved : pending.aborted_state with
      | fail error | div => rfl
      | ok aborted =>
          simp only [RegistrationBeaconReferenceCompiler.finishPreparation, StateT.run_bind,
            StateT.run_get, pure_bind, phase, moved, StateT.run_set, StateT.run_modify,
            StateT.run_lift, bind_pure_comp, bind_map_left, bind_assoc]
          apply bind_congr
          intro authenticated
          cases authenticated with
          | fail error | div => rfl
          | ok result => cases result with
            | Err error => rfl
            | Ok accepted =>
                simp only [RegistrationBeaconReferenceNativePhase.phase, StateT.run_bind,
                  StateT.run_lift, bind_pure_comp, StateT.run_map, bind_map_left]
                apply bind_congr
                rintro ⟨result, afterEnv⟩
                cases result with
                | fail error | div => rfl
                | ok ready => cases ready <;> rfl

private theorem effects_actual (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) :
    RegistrationNativeExperiment.trusted (n := n) setup checks representation created mlSource ∘ₛ
      RegistrationBeaconReferenceNativeRecord.environment =
      RegistrationBeaconReferenceNativeEffects.native setup checks representation created := by
  funext query
  simp only [QueryImpl.apply_compose, RegistrationBeaconReferenceNativeRecord.environment,
    simulateQ_spec_query, RegistrationBeaconReferenceNativeEffects.native]

private theorem authentication_actual (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) :
    RegistrationNativeExperiment.trusted (n := n) setup checks representation created mlSource ∘ₛ
      (RegistrationBeaconReferenceNativeRecord.environment ∘ₛ
        RegistrationAuthenticationCompiler.callbacks setup.source.crypto mlSource.verify) =
      RegistrationBeaconReferenceNativeEffects.native setup checks representation created ∘ₛ
        RegistrationAuthenticationCompiler.callbacks setup.source.crypto mlSource.verify := by
  funext query
  simp only [QueryImpl.apply_compose, ← QueryImpl.simulateQ_compose, effects_actual]

/-- The complete scalar-free finishing controller executes the actual incoming verifier, native root phase and consumed-kernel completion on the same World. Coherence and the private source scalar identify the retained native capability. -/
theorem finish_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (owner : Owner mlSource) (packet : Option registration.ResponsePacket)
    (env : EnvState RegistrationServerRoleBackend.State) (before : State n KemSK mlSource)
    (sameScalar : owner.prekeyScalar = scalar)
    (coherent : ∀ pending oneTime, owner.phase = .initSent pending oneTime →
      pending.control.expected_server_binding = pending.binding.server_pin.binding)
    (erased : Std.Array U8 227#usize) :
    RegistrationBeaconReferenceNativeCompletion.drop <$>
      (simulateQ (implementation setup checks wire representation created scalar credential)
        (((RegistrationBeaconReferenceFinish.finish setup mlSource packet :
          RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK)
            (Auxiliary := RegistrationServerRoleBackend.State) mlSource (RustM (Option Pqxdh.Bytes))).run (eraseOwner owner)).run
              (RegistrationBeaconReferenceNativeRecord.erase env))).run before =
      Prod.map RegistrationBeaconReferenceNativeContinuation.view id <$>
        (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource)
          (((RegistrationBeaconReferenceNativeOwner.finish setup mlSource wire packet :
            RegistrationBeaconReferenceNativeOwner.M n KemSK RegistrationServerRoleBackend.State mlSource
              (RustM (Option Pqxdh.Bytes))).run owner).run env)).run before.2.2 := by
  rw [reference_factor]
  have phaseView : (eraseOwner owner).phase = owner.phase := rfl
  cases phase : owner.phase with
  | fresh | freshWithCoins scalar | established completed | aborted aborted =>
      simp only [incoming, RegistrationBeaconReferenceNativeOwner.finish, StateT.run_bind, StateT.run_get,
        pure_bind, phaseView, phase, StateT.run_pure, simulateQ_pure, map_pure,
        RegistrationBeaconReferenceNativeCompletion.drop, Prod.map_def, id_eq,
        RegistrationBeaconReferenceNativeContinuation.view]
  | initSent pending oneTime =>
      simp only [incoming, RegistrationBeaconReferenceNativeOwner.finish, StateT.run_bind, StateT.run_get,
        pure_bind, phaseView, phase]
      cases moved : pending.aborted_state with
      | fail error | div =>
          simp only [StateT.run_pure, simulateQ_pure, map_pure,
            RegistrationBeaconReferenceNativeCompletion.drop, Prod.map_def, id_eq,
            RegistrationBeaconReferenceNativeContinuation.view]
      | ok aborted =>
          simp only [StateT.run_modify, pure_bind, StateT.run_bind, StateT.run_lift,
            bind_pure_comp, simulateQ_bind, map_bind, bind_map_left,
            RegistrationBeaconReferenceNativeOwner.authentication]
          rw [RegistrationBeaconReferenceNativeMaterial.effects_program]
          simp only [← QueryImpl.simulateQ_compose, authentication_actual, bind_map_left]
          apply bind_congr_of_forall_mem_support
          rintro ⟨authenticated, afterNative⟩ supported
          cases authenticated with
          | fail error | div =>
              exact RegistrationBeaconReferenceNativeContinuation.abort_owner_source setup checks wire representation created scalar credential
                owner { owner with phase := .aborted aborted } env _ (before.1, (before.2.1, afterNative))
          | ok result => cases result with
            | Err error =>
                exact RegistrationBeaconReferenceNativeContinuation.abort_owner_source setup checks wire representation created scalar credential
                  owner { owner with phase := .aborted aborted } env _ (before.1, (before.2.1, afterNative))
            | Ok accepted =>
                have retained : RegistrationBeaconResponseMetadata.Retained pending accepted := by
                  cases packet with
                  | none =>
                      apply RegistrationBeaconResponseMetadata.simulated_metadata
                        (RegistrationBeaconReferenceNativeEffects.native setup checks representation created ∘ₛ
                          RegistrationAuthenticationCompiler.callbacks setup.source.crypto mlSource.verify)
                        pending .None accepted before.2.2 afterNative
                      simpa only [QueryImpl.simulateQ_compose] using supported
                  | some value =>
                      apply RegistrationBeaconResponseMetadata.simulated_metadata
                        (RegistrationBeaconReferenceNativeEffects.native setup checks representation created ∘ₛ
                          RegistrationAuthenticationCompiler.callbacks setup.source.crypto mlSource.verify)
                        pending (.Some value) accepted before.2.2 afterNative
                      simpa only [QueryImpl.simulateQ_compose] using supported
                have correct : accepted.control.expected_server_binding = accepted.binding.server_pin.binding := by
                  rw [retained.1, retained.2.1]
                  exact coherent pending oneTime phase
                have actual := RegistrationBeaconReferenceNativePhase.phase_full_source setup checks wire representation created scalar credential
                  owner { owner with phase := .aborted aborted } oneTime env accepted correct erased
                  (before.1, (before.2.1, afterNative))
                rw [← RegistrationBeaconReferenceNativeCallbacks.lower_program] at actual
                simp only [RegistrationBeaconReferenceNativeStage.lower, simulateQ_bind, StateT.run, state_bind_apply,
                  state_lift_apply, state_pure_apply, pure_bind, bind_assoc, sameScalar,
                  map_bind, bind_map_left, RegistrationBeaconReferenceNativeContinuation.sourceAfter,
                  RegistrationBeaconReferenceNativeKnown.postRoot] at actual ⊢
                convert actual using 1 <;> rfl

end BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeFinish

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeFinish.reference_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeFinish.reference_factor
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeFinish.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeFinish.finish_source
