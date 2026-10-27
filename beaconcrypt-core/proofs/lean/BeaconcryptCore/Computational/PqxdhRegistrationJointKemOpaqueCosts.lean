-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume

/-! Count the private compiler requests separately from the primitive work performed by their actual interpreters. Erasure and bookkeeping are explicit requests, and the current ROM backend retains its original possible 64-byte draw; no ambient source work is declared free. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueCosts
open PqxdhRegistrationJointKemOpaqueClient
open PqxdhRegistrationJointKemOpaqueSuffix
open PqxdhServerAuthNative PqxdhSecretInputKdf
variable {Reader KemSK : Type}

def IsRoot : (PqxdhRegistrationJointKemOpaqueClient.Spec Reader).Domain → Prop
  | .inl _ => True
  | .inr _ => False
instance (query : (PqxdhRegistrationJointKemOpaqueClient.Spec Reader).Domain) : Decidable (IsRoot query) :=
  by cases query <;> simp only [IsRoot] <;> infer_instance

/-- At most one private root request is made through every typed callback, including every actual rejection branch. -/
theorem client_root (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding) (input : Input Reader) :
    (client control binding input).IsQueryBoundP IsRoot 1 := by
  unfold client
  cases PqxdhRegistrationJointKemOpaqueCore.accept control binding input with
  | fail error => simp [IsRoot]
  | div => simp [IsRoot]
  | ok result =>
      cases result <;> simp [isQueryBoundP_query_bind_iff, IsRoot]

/-- The marker client has at most four internal requests: erase-shared, root, erase-input and consume. This is not a claim that a root implementation costs one primitive query. -/
theorem client_calls (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding) (input : Input Reader) :
    (client control binding input).IsQueryBoundP (fun _ => True) 4 := by
  unfold client
  cases PqxdhRegistrationJointKemOpaqueCore.accept control binding input with
  | fail error => simp
  | div => simp
  | ok result =>
      cases result <;> simp [isQueryBoundP_query_bind_iff]

/-- The interpreted current native client retains the existing 64-byte uniform allowance for its restricted-ROM root. Erasure, consumption, all histories and caches remain present. -/
theorem client_uniform (hmac : HmacSha512) (index : Nat)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (input : Input Reader)
    (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding) (state : NativeState KemSK) :
    ((simulateQ (romImpl KemSK hmac index candidate) (client control binding input)).run state).IsTotalQueryBound 64 := by
  rw [PqxdhRegistrationJointKemOpaqueClient.client_native]
  exact PqxdhRegistrationSchedule.server_client_uniform hmac index control binding _ state

/-- Allocation and optional publication add at most two bookkeeping requests to the four-request client, with all typed root replies covered. -/
theorem tail_calls (serverKeyId : U64) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (state : PqxdhServerAuthExperiment.GameState KemSK)
    (collected : Option (Input Reader) × List Pqxdh.Bytes) :
    (PqxdhRegistrationJointKemOpaqueTail.tail serverKeyId publicIdentity state collected).IsQueryBoundP
      (fun _ => True) 6 := by
  unfold PqxdhRegistrationJointKemOpaqueTail.tail
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr (by decide), fun ignored => ?_⟩
  cases collected.1 with
  | none => exact isQueryBoundP_pure _ _ _
  | some input =>
      apply isQueryBoundP_bind (n := 4) (m := 1)
      · apply RawCtxSourceOpen.simulate_bound _ (fun _ => True) (fun _ => True) _ 4
          (client_calls state.server.control _ input)
        intro query
        simp [PqxdhRegistrationJointKemOpaqueTail.forward]
      · intro returned _
        cases returned with
        | fail error => exact isQueryBoundP_pure _ _ _
        | div => exact isQueryBoundP_pure _ _ _
        | ok result => cases result <;> simp

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueCosts

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueCosts.client_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueCosts.client_root

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueCosts.client_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueCosts.client_calls

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueCosts.client_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueCosts.client_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueCosts.tail_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueCosts.tail_calls
