-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconInitExecutor
import BeaconcryptCore.Computational.RegistrationBeaconInitPin

/-! Actual outgoing native control retains its original expected Server binding through all signing and hashing stages, independent of their replies. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationBeaconInitPinSource
open RegistrationBeaconInitExecutor
attribute [local irreducible] registration.BeaconInitHash.resume
variable {Encoded : Type} {expected : pqxdh.ServerBinding}
private theorem continueWith_support {Input : Type} (action : RustM Input)
    (next : Input → OracleComp Spec (RustM (Result Encoded))) (published : registration.PublishedBeaconInit Encoded)
    (supported : .ok (.Ok published) ∈ support (continueWith action next)) :
    ∃ value, action = .ok value ∧ .ok (.Ok published) ∈ support (next value) := by
  cases action <;> simp_all [continueWith]

theorem ready_coherent (encode : registration.InitView → core.option.Option Encoded)
    (pending : registration.BeaconInitReady) (published : registration.PublishedBeaconInit Encoded)
    (coherent : RegistrationBeaconInitPin.Coherent expected (.Ready pending)) (supported : .ok (.Ok published) ∈ support (ready encode pending)) :
    published.pending.control.expected_server_binding = expected := by
  obtain ⟨view, _requested, continued⟩ := continueWith_support pending.message _ published supported
  simp only [support_pure, Set.mem_singleton_iff] at continued
  exact RegistrationBeaconInitPin.publish_coherent pending (encode view)
    published coherent continued.symm

theorem hash_coherent (encode : registration.InitView → core.option.Option Encoded)
    (pending : registration.BeaconInitHash) (published : registration.PublishedBeaconInit Encoded)
    (coherent : RegistrationBeaconInitPin.StateCoherent expected pending.state) (supported : .ok (.Ok published) ∈ support (fromHash encode pending)) :
    published.pending.control.expected_server_binding = expected := by
  obtain ⟨request, _requested, called⟩ := continueWith_support pending.request _ published supported
  simp only [mem_support_bind_iff] at called
  obtain ⟨digest, _hashed, continued⟩ := called
  obtain ⟨effect, resumed, continued⟩ := continueWith_support
    (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest))) _ published continued
  have kept := RegistrationBeaconInitPin.hash_coherent pending _ effect coherent resumed
  cases effect with
  | Ready selected => exact ready_coherent encode selected published kept continued
  | _ => simp at continued

theorem ed_coherent (encode : registration.InitView → core.option.Option Encoded)
    (pending : registration.BeaconEd25519Signing) (published : registration.PublishedBeaconInit Encoded)
    (coherent : RegistrationBeaconInitPin.StateCoherent expected pending.state) (supported : .ok (.Ok published) ∈ support (fromEd encode pending)) :
    published.pending.control.expected_server_binding = expected := by
  rw [fromEd.eq_def] at supported
  obtain ⟨request, _requested, called⟩ := continueWith_support pending.request _ published supported
  simp only [mem_support_bind_iff] at called
  obtain ⟨reply, _signed, continued⟩ := called
  cases actual : pending.resume reply with
  | fail error => rw [actual] at continued; simp at continued
  | div => rw [actual] at continued; simp at continued
  | ok effect =>
      have kept := RegistrationBeaconInitPin.ed_coherent pending reply effect coherent actual
      cases effect with
      | Ed25519SigningRequested next =>
          rw [actual] at continued
          exact ed_coherent encode next published kept continued
      | HashRequested selected =>
          rw [actual] at continued
          exact hash_coherent encode selected published kept continued
      | _ => rw [actual] at continued; simp at continued
termination_by edRank pending
decreasing_by exact ed_rank pending reply next actual

/-- Published control/binding coherence is derived from the actual begin gate and all reached native continuations. -/
theorem begin_coherent (encode : registration.InitView → core.option.Option Encoded)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin)
    (published : registration.PublishedBeaconInit Encoded)
    (supported : .ok (.Ok published) ∈ support (begin encode control inputs coins pin)) :
    published.pending.control.expected_server_binding = control.expected_server_binding := by
  obtain ⟨effect, actual, continued⟩ := continueWith_support
    (registration.begin_beacon_init control inputs coins pin) _ published supported
  have kept := RegistrationBeaconInitPin.begin_coherent
    control inputs coins pin effect actual
  cases effect with
  | Ed25519SigningRequested selected => exact ed_coherent encode selected published kept continued
  | _ => simp at continued

theorem simulated_coherent {State : Type} (implementation : QueryImpl Spec (StateT State ProbComp))
    (encode : registration.InitView → core.option.Option Encoded)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin)
    (published : registration.PublishedBeaconInit Encoded) (before after : State)
    (supported : (.ok (.Ok published), after) ∈ support
      ((simulateQ implementation (begin encode control inputs coins pin)).run before)) :
    published.pending.control.expected_server_binding = control.expected_server_binding := by
  apply begin_coherent encode control inputs coins pin published
  apply OracleComp.support_simulateQ_run'_subset implementation (begin encode control inputs coins pin) before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst supported

end BeaconcryptCore.Computational.RegistrationBeaconInitPinSource

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitPinSource.ready_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitPinSource.ready_coherent


/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitPinSource.hash_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitPinSource.hash_coherent


/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitPinSource.ed_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitPinSource.ed_coherent

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitPinSource.begin_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitPinSource.begin_coherent

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitPinSource.simulated_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitPinSource.simulated_coherent
