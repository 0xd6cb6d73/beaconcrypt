-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefix
import BeaconcryptCore.Computational.PqxdhServerRootQueryBounds

/-! The actual indexed Server prefix emits at most one joint identity-DH request, at most twenty-one retained native auxiliary callbacks, and no other private capability. These are all-reply logical bounds; the complete evaluated scalar/KEM/base uniform bill remains in prefix_uniform. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefixCosts
open PqxdhRegistrationJointServerPrefix
variable {KemSK Reader Result : Type}

inductive Kind where
  | staticDh | auxiliary | other
  deriving DecidableEq

def classify : (Spec KemSK Reader).Domain → Kind
  | .inl (.inl (.inr (.service _ (.staticDh _)))) => .staticDh
  | .inr _ => .auxiliary
  | _ => .other

def cap : Kind → Nat
  | .staticDh => 1 | .auxiliary => 21 | .other => 0

def charged (kind : Kind) (query : (NativeSpec Reader).Domain) : Prop :=
  (kind = .staticDh ∧ PqxdhServerRootQueryBounds.selected query = true) ∨
    (kind = .auxiliary ∧ PqxdhServerRootQueryBounds.selected query = false)

instance (kind : Kind) : DecidablePred (charged (Reader := Reader) kind) := fun _ => inferInstanceAs (Decidable (_ ∨ _))

set_option backward.isDefEq.respectTransparency false in
/-- Every compiler callback emits its own one logical request, retaining all optional typed replies and excluding unrelated capabilities. -/
theorem compiler_step (identityIndex : Nat) (query : (NativeSpec Reader).Domain) (kind : Kind) :
    (compiler (KemSK := KemSK) identityIndex query).IsQueryBoundP
      (fun request => classify (KemSK := KemSK) request = kind) (if charged kind query then 1 else 0) := by
  cases query <;> cases kind <;> simp [compiler, charged, classify, PqxdhServerRootQueryBounds.selected, isQueryBoundP_query_iff]

/-- This compiler cannot create or disclose identities, sign, decapsulate, create KEM keys or make any other private request. -/
theorem other_free (identityIndex : Nat) (program : OracleComp (NativeSpec Reader) Result) :
    (simulateQ (compiler (KemSK := KemSK) identityIndex) program).IsQueryBoundP
      (fun request => classify (KemSK := KemSK) request = .other) 0 := by
  induction program using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      apply isQueryBoundP_bind (n := 0) (m := 0)
      · simpa [charged] using compiler_step (KemSK := KemSK) identityIndex query .other
      · exact fun reply _ => ih reply

/-- The complete raw prefix counts every permitted logical attempt, including all early rejection paths, before any primitive interpretation. -/
theorem prefix_bound (identityIndex : Nat) (raw : Pqxdh.Bytes) (kind : Kind) :
    (clientPrefix (KemSK := KemSK) (Reader := Reader) identityIndex raw).IsQueryBoundP
      (fun request => classify (KemSK := KemSK) request = kind) (cap kind) := by
  cases kind
  case other => exact other_free identityIndex _
  case staticDh =>
    apply (PqxdhServerRootQueryBounds.collect_class (Reader := Reader) (E := PqxdhJointGapDh.ScalarBytes)
      (Shared := PqxdhBeaconPhase2Preparation.Word32) true raw).simulateQ_of_step
    · intro query selected
      simpa [charged, selected] using compiler_step (KemSK := KemSK) identityIndex query .staticDh
    · intro query absent
      simpa [charged, absent] using compiler_step (KemSK := KemSK) identityIndex query .staticDh
  case auxiliary =>
    apply (PqxdhServerRootQueryBounds.collect_class (Reader := Reader) (E := PqxdhJointGapDh.ScalarBytes)
      (Shared := PqxdhBeaconPhase2Preparation.Word32) false raw).simulateQ_of_step
    · intro query selected
      simpa [charged, selected] using compiler_step (KemSK := KemSK) identityIndex query .auxiliary
    · intro query absent
      simpa [charged, absent] using compiler_step (KemSK := KemSK) identityIndex query .auxiliary

end BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefixCosts

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefixCosts.compiler_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefixCosts.compiler_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefixCosts.other_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefixCosts.other_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefixCosts.prefix_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefixCosts.prefix_bound
