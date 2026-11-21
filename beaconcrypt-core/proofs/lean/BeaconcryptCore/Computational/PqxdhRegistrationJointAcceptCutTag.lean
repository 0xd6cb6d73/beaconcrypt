-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCut

/-! Record the selected raw accept of the actual adaptive source14 program without changing the program. The tagged program issues exactly the original requests in the original order and additionally returns the selected raw bytes and the public reply of that accept. The raw-accept ordinal counts every raw accept request, including rejected attempts, and is distinct from the encapsulation ordinal of `PqxdhRegistrationJointKemCut`. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutTag
open PqxdhRegistrationJointRevealSchedule (Spec)
open PqxdhRegistrationJointAcceptCut (Cut scan finish)
variable {KemSK Result : Type}

/-- The selected raw bytes with the public reply of that accept, or `none` when the program completes before the selected accept. -/
abbrev Tag := Option (Pqxdh.Bytes × Option Nat)

/-- Resume a raw cut exactly as `AcceptCut.finish` does, and also return the suspended raw bytes and the public reply that the resumed accept received. -/
noncomputable def tagFinish : Cut KemSK Result → OracleComp (Spec KemSK) (Result × Tag)
  | .complete result => pure (result, none)
  | .pending raw next => do
    let answer ← (Spec KemSK).query (.inl (.inr (.accept raw)))
    (fun result => (result, some (raw, answer))) <$> next answer

/-- The original program, suspended before its raw accept at zero-based position `index` and resumed with the recording finish. -/
noncomputable def tag (work : OracleComp (Spec KemSK) Result) (index : Nat) :
    OracleComp (Spec KemSK) (Result × Tag) :=
  scan work index >>= tagFinish

/-- The selected accept was reached and its public reply is a session index. -/
def accepted : Tag → Bool
  | some (_, some _) => true
  | _ => false

/-- An adversary decision on the original result, counted only when the selected accept returned a session. -/
def decideTag (decision : Result → Bool) (output : Result × Tag) : Bool :=
  decision output.1 && accepted output.2

/-- A Boolean client on the tagged program. It reads only the original result and the public reply of the selected accept. -/
noncomputable def decisionClient (decision : Result → Bool) (work : OracleComp (Spec KemSK) Result) (index : Nat) :
    OracleComp (Spec KemSK) Bool :=
  decideTag decision <$> tag work index

/-- The tagged program is literally the raw-accept scan followed by the recording finish, so it can be split at the cut. -/
theorem tag_split (work : OracleComp (Spec KemSK) Result) (index : Nat) :
    tag work index = scan work index >>= tagFinish := rfl

/-- Forgetting the record turns the recording finish into the original finish. -/
theorem finish_erase (cut : Cut KemSK Result) : Prod.fst <$> tagFinish cut = finish cut := by
  cases cut with
  | complete result => rfl
  | pending raw next =>
    simp only [tagFinish, finish, map_bind, Functor.map_map, id_map']

/-- Forgetting the record recovers the entire original program, so the tag adds no request and changes no reply. -/
theorem tag_erase (work : OracleComp (Spec KemSK) Result) (index : Nat) :
    Prod.fst <$> tag work index = work := by
  rw [tag, map_bind]
  simp only [finish_erase]
  exact PqxdhRegistrationJointAcceptCut.scan_finish work index

/-- The tagged program keeps every all-reply cap of the original program. -/
theorem tag_bound (work : OracleComp (Spec KemSK) Result) (index : Nat)
    (predicate : (Spec KemSK).Domain → Prop) [DecidablePred predicate] (cap : Nat)
    (bounded : work.IsQueryBoundP predicate cap) : (tag work index).IsQueryBoundP predicate cap := by
  apply (isQueryBoundP_map_iff (tag work index) Prod.fst cap).mp
  rw [tag_erase]
  exact bounded

/-- The decision client keeps every all-reply cap of the original program. -/
theorem decision_bound (decision : Result → Bool) (work : OracleComp (Spec KemSK) Result) (index : Nat)
    (predicate : (Spec KemSK).Domain → Prop) [DecidablePred predicate] (cap : Nat)
    (bounded : work.IsQueryBoundP predicate cap) :
    (decisionClient decision work index).IsQueryBoundP predicate cap :=
  (isQueryBoundP_map_iff _ _ _).mpr (tag_bound work index predicate cap bounded)

/-- A reached pending raw cut lies strictly below the all-reply raw-accept cap. Rejected earlier accepts are counted like successful ones, so this bounds the raw-accept ordinal, not the encapsulation ordinal. -/
theorem accept_lt (work : OracleComp (Spec KemSK) Result) (index cap : Nat)
    (bounded : work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = .inl 3) cap)
    (raw : Pqxdh.Bytes) (next : Option Nat → OracleComp (Spec KemSK) Result)
    (reached : Cut.pending raw next ∈ support (scan work index)) : index < cap := by
  induction work using OracleComp.inductionOn generalizing index cap with
  | pure result =>
    change _ ∈ support (pure (Cut.complete result) : OracleComp (Spec KemSK) _) at reached
    simp at reached
  | query_bind query continuation ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    rcases query with (coin | request) | read
    · change _ ∈ support ((((Spec KemSK).query (.inl (.inl coin)) : OracleComp (Spec KemSK) _) >>= fun answer =>
        scan (continuation answer) index)) at reached
      rw [mem_support_bind_iff] at reached
      obtain ⟨answer, _, reached⟩ := reached
      have remaining := bounded.2 answer
      rw [ite_eq_right (by simp [PqxdhRegistrationJointRevealCosts.sourceKind, PqxdhRegistrationSchedule.sourceKind])]
        at remaining
      exact ih answer index cap remaining reached
    · cases request
      case accept raw' =>
        have positive : 0 < cap := bounded.1.resolve_left (fun absurd => absurd rfl)
        cases index with
        | zero => exact positive
        | succ index =>
          change _ ∈ support ((((Spec KemSK).query (.inl (.inr (.accept raw'))) : OracleComp (Spec KemSK) _) >>=
            fun answer => scan (continuation answer) index)) at reached
          rw [mem_support_bind_iff] at reached
          obtain ⟨answer, _, reached⟩ := reached
          have remaining := bounded.2 answer
          rw [ite_eq_left (show PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK)
            (.inl (.inr (.accept raw'))) = .inl 3 from rfl)] at remaining
          have earlier := ih answer index (cap - 1) remaining reached
          omega
      all_goals
        change _ ∈ support ((((Spec KemSK).query _ : OracleComp (Spec KemSK) _) >>= fun answer =>
          scan (continuation answer) index)) at reached
        rw [mem_support_bind_iff] at reached
        obtain ⟨answer, _, reached⟩ := reached
        have remaining := bounded.2 answer
        rw [ite_eq_right (by simp [PqxdhRegistrationJointRevealCosts.sourceKind, PqxdhRegistrationSchedule.sourceKind])]
          at remaining
        exact ih answer index cap remaining reached
    · change _ ∈ support ((((Spec KemSK).query (.inr read) : OracleComp (Spec KemSK) _) >>= fun answer =>
        scan (continuation answer) index)) at reached
      rw [mem_support_bind_iff] at reached
      obtain ⟨answer, _, reached⟩ := reached
      have remaining := bounded.2 answer
      rw [ite_eq_right (by simp [PqxdhRegistrationJointRevealCosts.sourceKind])] at remaining
      exact ih answer index cap remaining reached

/-- Every reached pending raw cut of a source14 program with certified budget has ordinal below `qAccept`, the raw-accept budget `budget (.inl 3)`. This bounds the finite family of raw-accept handles; it charges no selection loss. -/
theorem accept_source (work : OracleComp (Spec KemSK) Result) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (raw : Pqxdh.Bytes) (next : Option Nat → OracleComp (Spec KemSK) Result)
    (reached : Cut.pending raw next ∈ support (scan work index)) : index < budget (.inl 3) :=
  accept_lt work index (budget (.inl 3)) (certified (.inl 3)) raw next reached

end BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutTag

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutTag.tag_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutTag.tag_split

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutTag.finish_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutTag.finish_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutTag.tag_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutTag.tag_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutTag.tag_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutTag.tag_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutTag.decision_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutTag.decision_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutTag.accept_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutTag.accept_lt

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutTag.accept_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutTag.accept_source
