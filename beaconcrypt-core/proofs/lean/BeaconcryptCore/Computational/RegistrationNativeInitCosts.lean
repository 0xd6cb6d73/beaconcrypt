-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconInitExecutor

/-! The actual outgoing Init controller has at most four primitive callbacks on every typed reply path: up to three attached Ed signatures followed by the retained Init request hash. Failed getters, signatures and encoding retain their original short-circuit positions. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.RegistrationNativeInitCosts
open RegistrationBeaconInitExecutor
variable {Encoded Input : Type}
attribute [local irreducible] registration.BeaconInitHash.resume

private theorem continue_bound (action : RustM Input)
    (next : Input → OracleComp Spec (RustM (Result Encoded))) (count : Nat)
    (bounded : ∀ value, (next value).IsTotalQueryBound count) :
    (continueWith action next).IsTotalQueryBound count := by
  cases action with
  | ok value => exact bounded value
  | fail error => trivial
  | div => trivial

private theorem ready_bound (encode : registration.InitView → core.option.Option Encoded)
    (pending : registration.BeaconInitReady) : (ready encode pending).IsTotalQueryBound 0 := by
  unfold ready
  exact continue_bound _ _ _ (fun _ => by trivial)

private theorem hash_bound (encode : registration.InitView → core.option.Option Encoded)
    (pending : registration.BeaconInitHash) : (fromHash encode pending).IsTotalQueryBound 1 := by
  unfold fromHash
  apply continue_bound
  intro request
  rw [isTotalQueryBound_query_bind_iff]
  refine ⟨by decide, fun digest => ?_⟩
  apply continue_bound
  intro effect
  cases effect with
  | Ready selected => exact ready_bound encode selected
  | _ => trivial

/-- The original attached-signing rank bounds every actual outgoing prefix, without assuming replies succeed. -/
theorem ed_bound (encode : registration.InitView → core.option.Option Encoded)
    (pending : registration.BeaconEd25519Signing) : (fromEd encode pending).IsTotalQueryBound (edRank pending + 1) := by
  rw [fromEd.eq_def]
  apply continue_bound
  intro request
  rw [isTotalQueryBound_query_bind_iff]
  refine ⟨by omega, fun reply => ?_⟩
  cases actual : pending.resume reply with
  | fail error => trivial
  | div => trivial
  | ok effect =>
      cases effect with
      | Ed25519SigningRequested next => exact (ed_bound encode next).mono (by have := ed_rank pending reply next actual; omega)
      | HashRequested selected =>
          apply (hash_bound encode selected).mono
          have positive : 1 ≤ edRank pending := by cases stage : pending.stage <;> simp [edRank, stage]
          omega
      | _ => trivial
termination_by edRank pending
decreasing_by exact ed_rank pending reply next actual

attribute [local irreducible] registration.begin_beacon_init

/-- The literal native begin gate has the four-callback allowance on all error and optional-failure branches. -/
theorem begin_bound (encode : registration.InitView → core.option.Option Encoded)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) :
    (begin encode control inputs coins pin).IsTotalQueryBound 4 := by
  unfold begin
  apply continue_bound
  intro effect
  cases effect with
  | Ed25519SigningRequested pending =>
      apply (ed_bound encode pending).mono
      cases stage : pending.stage <;> simp [edRank, stage]
  | _ => trivial

end BeaconcryptCore.Computational.RegistrationNativeInitCosts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitCosts.ed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitCosts.ed_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitCosts.begin_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitCosts.begin_bound
