-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconRelatedRoot

/-! The whole authenticated Beacon agreement reaches the existing native Phase2 preparation and root continuation, with selected prekey DH implemented at its two original source positions. No successful preparation or opening is assumed. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.Computational.RegistrationBeaconPreparationInterpreter

open RegistrationAgreementExecutor
open PqxdhJointIdentity PqxdhJointGapDh
open PqxdhBeaconPhase2Preparation (Word32)
open RegistrationBeaconAgreementRoot (callbacks)
open RegistrationBeaconRootInterpreter (sumCallbacks auxImpl sourceImpl)

theorem prepare_sum (authenticated : registration.AuthenticatedResponse) :
    simulateQ (callbacks authenticated)
      (PqxdhBeaconPhase2Preparation.prepare (completedBinding := authenticated.binding) authenticated.control () false true () []) =
    simulateQ (sumCallbacks authenticated)
      (PqxdhBeaconPhase2Preparation.prepare (completedBinding := authenticated.binding) authenticated.control () (.inl ()) (.inr ()) () []) := by
  simp only [PqxdhBeaconPhase2Preparation.prepare, simulateQ_bind,
    RegistrationBeaconRootInterpreter.collect_sum]
  congr 1
  funext result
  cases result with
  | none => simp only [simulateQ_pure]
  | some input =>
      simp only [PqxdhBeaconPhase2Preparation.afterInputs, simulateQ_bind,
        simulateQ_spec_query, simulateQ_pure, sumCallbacks, callbacks, pure_bind]

theorem prepare_source {m : Type → Type} [Monad m] [LawfulMonad m]
    {joint : Primitives} (dh : DhInterface joint) (scalar : ScalarBytes)
    (backend : QueryImpl Spec m) (visit : Word32 → m Unit)
    (authenticated : registration.AuthenticatedResponse) :
    simulateQ (sourceImpl dh scalar backend visit)
      (simulateQ (callbacks authenticated)
        (PqxdhBeaconPhase2Preparation.prepare (completedBinding := authenticated.binding) authenticated.control () false true () [])) =
    simulateQ (PqxdhPhase2GapDhSource.nativeImpl dh scalar (auxImpl backend authenticated) visit)
      (PqxdhBeaconPhase2Preparation.prepare (completedBinding := authenticated.binding) authenticated.control () (.inl ()) (.inr ()) () []) := by
  rw [prepare_sum, ← QueryImpl.simulateQ_compose]
  have equal : sourceImpl dh scalar backend visit ∘ₛ sumCallbacks authenticated =
      PqxdhPhase2GapDhSource.nativeImpl dh scalar (auxImpl backend authenticated) visit := by
    funext query
    exact RegistrationBeaconRootInterpreter.callbacks_source dh scalar backend visit authenticated query
  rw [equal]

theorem after_source {m : Type → Type} [Monad m] [LawfulMonad m]
    {joint : Primitives} (dh : DhInterface joint) (scalar : ScalarBytes)
    (backend : QueryImpl Spec m) (visit : Word32 → m Unit)
    (authenticated : registration.AuthenticatedResponse)
    (result : Option (PqxdhBeaconPhase2Preparation.Prepared registration.AuthenticatedResponse)) :
    simulateQ (sourceImpl dh scalar backend visit) (RegistrationBeaconRootPreparation.afterPrepared authenticated result) =
      simulateQ backend (RegistrationBeaconRootPreparation.afterPrepared authenticated result) := by
  cases result with
  | none => simp only [RegistrationBeaconRootPreparation.afterPrepared, simulateQ_pure]
  | some original =>
      have requested : (⟨.Beacon original.candidate authenticated.binding authenticated.packet.application⟩ : agreement.RootKdfPending).request =
          .ok ⟨original.candidate.root_key_input.bytes, pqxdh.PQXDH_INFO⟩ := by
        simp only [agreement.RootKdfPending.request, pqxdh.BeaconRegistrationCandidate.impl.root_key_input,
          pqxdh.RootKeyInput.as_bytes, bind_tc_ok]
      simp only [RegistrationBeaconRootPreparation.afterPrepared]
      rw [RegistrationBeaconRelatedRoot.root_step_two _ _ requested]
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, sourceImpl]

theorem beacon_source {m : Type → Type} [Monad m] [LawfulMonad m]
    {joint : Primitives} (dh : DhInterface joint) (scalar : ScalarBytes)
    (backend : QueryImpl Spec m) (visit : Word32 → m Unit)
    (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.control.expected_server_binding = authenticated.binding.server_pin.binding) :
    simulateQ (sourceImpl dh scalar backend visit) (beacon authenticated) = (do
      let result ← (simulateQ (PqxdhPhase2GapDhSource.nativeImpl dh scalar (auxImpl backend authenticated) visit)
        (PqxdhBeaconPhase2Preparation.prepare (completedBinding := authenticated.binding) authenticated.control () (.inl ()) (.inr ()) () []))
      simulateQ backend (RegistrationBeaconRootPreparation.afterPrepared authenticated result)) := by
  rw [RegistrationBeaconAgreementRoot.beacon_normalized authenticated coherent,
    RegistrationBeaconRootPreparation.normalized_prepared]
  simp only [RegistrationBeaconRootPreparation.prepared, simulateQ_bind, prepare_source, after_source]

end BeaconcryptCore.Computational.RegistrationBeaconPreparationInterpreter

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconPreparationInterpreter.prepare_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconPreparationInterpreter.prepare_sum

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconPreparationInterpreter.prepare_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconPreparationInterpreter.prepare_source

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconPreparationInterpreter.after_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconPreparationInterpreter.after_source

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconPreparationInterpreter.beacon_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconPreparationInterpreter.beacon_source
