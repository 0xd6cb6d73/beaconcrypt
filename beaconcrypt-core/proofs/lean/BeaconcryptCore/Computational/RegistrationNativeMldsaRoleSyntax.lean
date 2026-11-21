-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconInitExecutor

/-! The actual outgoing Beacon Init controller emits no ML signing request. The property is syntactic over all primitive replies, including failed signing or publication, and does not assume authentication or source security. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaRoleSyntax
open RegistrationBeaconInitExecutor
variable {Encoded : Type}
attribute [local irreducible] registration.BeaconInitHash.resume registration.begin_beacon_init

def NoMldsa : Spec.Domain → Prop
  | .inl (.sign _ _ _) => False
  | _ => True

private theorem continue_all {Input : Type} (action : RustM Input)
    (next : Input → OracleComp Spec (RustM (Result Encoded)))
    (all : ∀ value, AllQueriesSatisfy (next value) NoMldsa) : AllQueriesSatisfy (continueWith action next) NoMldsa := by
  cases action with
  | ok value => exact all value
  | fail error | div => trivial

private theorem ready_all (encode : registration.InitView → core.option.Option Encoded)
    (pending : registration.BeaconInitReady) : AllQueriesSatisfy (ready encode pending) NoMldsa := by
  unfold ready
  exact continue_all _ _ (fun _ => by trivial)

theorem hash_all (encode : registration.InitView → core.option.Option Encoded)
    (pending : registration.BeaconInitHash) : AllQueriesSatisfy (fromHash encode pending) NoMldsa := by
  unfold fromHash
  apply continue_all
  intro request
  rw [allQueriesSatisfy_query_bind_iff]
  refine ⟨trivial, fun _ => ?_⟩
  apply continue_all
  intro effect
  cases effect with
  | Ready selected => exact ready_all encode selected
  | _ => trivial

theorem ed_all (encode : registration.InitView → core.option.Option Encoded)
    (pending : registration.BeaconEd25519Signing) : AllQueriesSatisfy (fromEd encode pending) NoMldsa := by
  rw [fromEd.eq_def]
  apply continue_all
  intro request
  rw [allQueriesSatisfy_query_bind_iff]
  refine ⟨trivial, fun reply => ?_⟩
  cases resumed : pending.resume reply with
  | fail error | div => trivial
  | ok effect => cases effect with
    | Ed25519SigningRequested next => exact ed_all encode next
    | HashRequested selected => exact hash_all encode selected
    | _ => trivial
termination_by edRank pending
decreasing_by exact ed_rank pending reply next resumed

/-- No complete outgoing Init source branch contains an ML signing request. -/
theorem begin_all (encode : registration.InitView → core.option.Option Encoded)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) :
    AllQueriesSatisfy (begin encode control inputs coins pin) NoMldsa := by
  unfold begin
  apply continue_all
  intro effect
  cases effect with
  | Ed25519SigningRequested selected => exact ed_all encode selected
  | _ => trivial

end BeaconcryptCore.Computational.RegistrationNativeMldsaRoleSyntax

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaRoleSyntax.hash_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaRoleSyntax.hash_all

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaRoleSyntax.ed_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaRoleSyntax.ed_all

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaRoleSyntax.begin_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaRoleSyntax.begin_all
