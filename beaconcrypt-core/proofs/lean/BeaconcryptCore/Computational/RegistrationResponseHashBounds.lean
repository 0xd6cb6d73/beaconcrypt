-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationResponseExecutor

/-! The actual mandatory response controller has three callback positions: response transcript hash, pinned Server ML verification, then record-AD hash. Only the two hash positions enter the shared hash bill. Every optional refusal and core rejection retains its reached prefix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationResponseHashBounds
variable {Input : Type}

def IsHash : RegistrationAuthenticationExecutor.Request → Prop
  | .hash _ => True
  | _ => False
instance : DecidablePred IsHash := fun query => by cases query <;> dsimp [IsHash] <;> infer_instance

private theorem continue_bound (selected : RegistrationAuthenticationExecutor.Request → Prop)
    [DecidablePred selected] (action : RustM Input)
    (next : Input → OracleComp RegistrationAuthenticationExecutor.Spec (RustM RegistrationResponseExecutor.ResponseResult))
    (count : Nat) (bounded : ∀ value, (next value).IsQueryBoundP selected count) :
    (RegistrationAuthenticationExecutor.continueWith action next).IsQueryBoundP selected count := by
  cases action with
  | ok value => exact bounded value
  | fail error | div => trivial

private theorem result_bound (selected : RegistrationAuthenticationExecutor.Request → Prop)
    [DecidablePred selected] (action : RustM (core.result.Result Input pqxdh.BeaconAborted))
    (next : Input → OracleComp RegistrationAuthenticationExecutor.Spec (RustM RegistrationResponseExecutor.ResponseResult))
    (count : Nat) (bounded : ∀ value, (next value).IsQueryBoundP selected count) :
    (RegistrationResponseExecutor.continueResult action next).IsQueryBoundP selected count := by
  cases action with
  | ok result => cases result with
    | Ok value => exact bounded value
    | Err error => trivial
  | fail error | div => trivial

/-- All three reached primitive callback positions are counted, including rejected replies. -/
theorem begin_total_bound (pending : registration.BeaconPending) (packet : core.option.Option registration.ResponsePacket) :
    (RegistrationResponseExecutor.begin pending packet).IsTotalQueryBound 3 := by
  apply (isQueryBoundP_true_iff _ _).mp
  unfold RegistrationResponseExecutor.begin
  apply result_bound (fun _ => True)
  intro hashing
  apply continue_bound (fun _ => True)
  intro hashRequest
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨by decide, fun digest => ?_⟩
  apply result_bound (fun _ => True)
  intro verification
  apply continue_bound (fun _ => True)
  intro verifyRequest
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨by decide, fun verified => ?_⟩
  apply result_bound (fun _ => True)
  intro adState
  apply continue_bound (fun _ => True)
  intro adRequest
  rw [isQueryBoundP_query_bind_iff]
  exact ⟨by decide, fun _ => by trivial⟩

/-- Only the response transcript and exact record-AD preimage occupy hash positions. -/
theorem begin_hash_bound (pending : registration.BeaconPending) (packet : core.option.Option registration.ResponsePacket) :
    (RegistrationResponseExecutor.begin pending packet).IsQueryBoundP IsHash 2 := by
  unfold RegistrationResponseExecutor.begin
  apply result_bound IsHash
  intro hashing
  apply continue_bound IsHash
  intro hashRequest
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr (by decide), fun digest => ?_⟩
  apply result_bound IsHash
  intro verification
  apply continue_bound IsHash
  intro verifyRequest
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (by simp [IsHash]), fun verified => ?_⟩
  apply result_bound IsHash
  intro adState
  apply continue_bound IsHash
  intro adRequest
  rw [isQueryBoundP_query_bind_iff]
  exact ⟨Or.inr (by simp [IsHash]), fun _ => by trivial⟩
end BeaconcryptCore.Computational.RegistrationResponseHashBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationResponseHashBounds.begin_total_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationResponseHashBounds.begin_total_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationResponseHashBounds.begin_hash_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationResponseHashBounds.begin_hash_bound
