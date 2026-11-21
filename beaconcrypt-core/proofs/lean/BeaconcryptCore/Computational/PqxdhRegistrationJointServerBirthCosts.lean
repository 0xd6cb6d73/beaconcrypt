-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedPrefix

/-! All-reply constructor capability accounting separates the initialization callback, ordinary generated creation and deterministic caller-known import. These are logical caps; the complete evaluated initialization/scalar/KEM/base randomness is accounted for by initialized_uniform. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointServerBirthCosts
open PqxdhRegistrationJointServerBirth
variable {KemSK P : Type}

inductive Kind where
  | initialize | create | importSeed | other
  deriving DecidableEq

def classify : (Spec KemSK).Domain → Kind
  | .inr .initialize => .initialize
  | .inr (.importSeed _) => .importSeed
  | .inl (.inl (.inr .create)) => .create
  | _ => .other

def cap (supplied : Option Pqxdh.Bytes) : Kind → Nat
  | .initialize => 1
  | .create => if supplied.isNone then 1 else 0
  | .importSeed => if supplied.isSome then 1 else 0
  | .other => 0

set_option backward.isDefEq.respectTransparency false in
/-- The actual constructor has one initialization allowance and at most one request of its chosen origin. The statement covers every typed reply, including initialization rejection and invalid imported lengths. -/
theorem client_bound (sender : Std.U64) (supplied : Option Pqxdh.Bytes) (kind : Kind) :
    (client (KemSK := KemSK) (P := P) sender supplied).IsQueryBoundP
      (fun request => classify (KemSK := KemSK) request = kind) (cap supplied kind) := by
  cases kind <;> cases supplied <;>
    simp [client, cap, classify, isQueryBoundP_query_bind_iff]
  all_goals split <;> simp [isQueryBoundP_query_iff]

end BeaconcryptCore.Computational.PqxdhRegistrationJointServerBirthCosts

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerBirthCosts.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerBirthCosts.client_bound
