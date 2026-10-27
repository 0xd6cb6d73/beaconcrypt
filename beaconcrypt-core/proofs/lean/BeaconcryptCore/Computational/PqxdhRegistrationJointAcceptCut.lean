-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutBounds
import BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginUniform

/-! Suspend the actual adaptive source14 program immediately before a selected raw accept attempt. Every preceding command and every original continuation remain intact. The position counts raw attempts, including rejected ones, rather than successful encapsulations. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCut
open PqxdhRegistrationJointRevealSchedule (Spec)
variable {KemSK Result : Type}

/-- The exact caller-supplied request and continuation are retained without inspecting any private source state. -/
inductive Cut (KemSK Result : Type) where
  | complete (result : Result)
  | pending (raw : Pqxdh.Bytes) (next : Option Nat → OracleComp (Spec KemSK) Result)

/-- Count every raw accept request. All other replies are forwarded unchanged to the same original continuation. -/
noncomputable def scan (work : OracleComp (Spec KemSK) Result) : Nat → OracleComp (Spec KemSK) (Cut KemSK Result) :=
  OracleComp.recOn work
    (fun result _ => pure (.complete result))
    (fun query next recurse index => match query with
      | .inl (.inr (.accept raw)) => match index with
        | 0 => pure (.pending raw next)
        | index + 1 => do
          let answer ← (Spec KemSK).query (.inl (.inr (.accept raw)))
          recurse answer index
      | query => do
        let answer ← (Spec KemSK).query query
        recurse answer index)

/-- Resuming executes the literal suspended request and its original adaptive remainder. -/
noncomputable def finish : Cut KemSK Result → OracleComp (Spec KemSK) Result
  | .complete result => pure result
  | .pending raw next => (Spec KemSK).query (.inl (.inr (.accept raw))) >>= next

/-- Scanning and resuming recover the entire original program under any later interpreter, including all native state and private histories. -/
theorem scan_finish (work : OracleComp (Spec KemSK) Result) (index : Nat) :
    (scan work index >>= finish) = work := by
  induction work using OracleComp.inductionOn generalizing index with
  | pure result => rfl
  | query_bind query next ih =>
    rcases query with (coin | request) | read
    · change ((((Spec KemSK).query (.inl (.inl coin)) : OracleComp (Spec KemSK) _) >>= fun answer => scan (next answer) index) >>= finish) = _
      simp only [bind_assoc, ih]
    · cases request
      all_goals first
        | change ((((Spec KemSK).query _ : OracleComp (Spec KemSK) _) >>= fun answer => scan (next answer) index) >>= finish) = _
          simp only [bind_assoc, ih]
        | skip
      cases index with
      | zero => rfl
      | succ index =>
        change ((((Spec KemSK).query _ : OracleComp (Spec KemSK) _) >>= fun answer => scan (next answer) index) >>= finish) = _
        simp only [bind_assoc, ih]
    · change ((((Spec KemSK).query (.inr read) : OracleComp (Spec KemSK) _) >>= fun answer => scan (next answer) index) >>= finish) = _
      simp only [bind_assoc, ih]

/-- Suspending retains the original all-reply allowance for every source predicate; omitted continuation work is never charged as extra or used to cancel earlier calls. -/
theorem scan_bound (work : OracleComp (Spec KemSK) Result) (index : Nat)
    (predicate : (Spec KemSK).Domain → Prop) [DecidablePred predicate] (cap : Nat)
    (bounded : work.IsQueryBoundP predicate cap) : (scan work index).IsQueryBoundP predicate cap := by
  apply PqxdhRegistrationJointKemCutBounds.bind_prefix _ finish
  rw [scan_finish]
  exact bounded

/-- The caller-supplied public owner address and the original raw bytes are packaged as the existing native-origin reduction's final choice type. Early completion returns only the fixed public fallback, without examining native state. -/
def choice (owner : Nat) (fallback : Pqxdh.Bytes) : Cut KemSK Result → PqxdhRegistrationJointFinalCandidate.Choice
  | .complete _ => (owner, fallback)
  | .pending raw _ => (owner, raw)

noncomputable def selected (work : OracleComp (Spec KemSK) Result) (index owner : Nat) (fallback : Pqxdh.Bytes) :
    OracleComp (Spec KemSK) PqxdhRegistrationJointFinalCandidate.Choice := choice owner fallback <$> scan work index

/-- The selected original-accept prefix keeps every query cap of the complete program, so each of the fourteen source caps applies to it. Supplying these caps to the initialized authentication reduction is part of the open join. -/
theorem selected_bound (work : OracleComp (Spec KemSK) Result) (index owner : Nat) (fallback : Pqxdh.Bytes)
    (predicate : (Spec KemSK).Domain → Prop) [DecidablePred predicate] (cap : Nat)
    (bounded : work.IsQueryBoundP predicate cap) : (selected work index owner fallback).IsQueryBoundP predicate cap := by
  exact (isQueryBoundP_map_iff _ _ _).mpr (scan_bound work index predicate cap bounded)

end BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCut

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCut.scan_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCut.scan_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCut.scan_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCut.scan_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCut.selected_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCut.selected_bound
