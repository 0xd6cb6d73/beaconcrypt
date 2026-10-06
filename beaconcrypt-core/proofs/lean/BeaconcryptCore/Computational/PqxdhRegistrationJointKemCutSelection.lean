-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemReductionBills

/-! Actual pending encapsulation cuts lie within the source's finite qAccept occurrence range. This identifies the finite index set for later target selection; it does not assert that a selected key is an honest owner or charge a selection loss prematurely. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutSelection
open PqxdhRegistrationJointKemEncapsulation PqxdhRegistrationJointKemCut PqxdhRegistrationJointKemExposedCounts
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Result Reader Response : Type}

set_option backward.isDefEq.respectTransparency false in
/-- A reached actual encapsulation occurrence has an index strictly below the original all-reply encapsulation cap. Repeated equal keys and earlier failed replies still consume their own occurrence. -/
theorem occurrence_lt (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (work : OracleComp (Spec KemSK) Result) (index cap : Nat)
    (bounded : work.IsQueryBoundP (IsEncapsulation (KemSK := KemSK)) cap)
    (request : Request) (next : Reply → OracleComp (Spec KemSK) Result)
    (reached : Cut.pending request next ∈ support (scan setup work index)) : index < cap := by
  induction work using OracleComp.inductionOn generalizing index cap with
  | pure result =>
    change Cut.pending request next ∈ support
      (pure (Cut.complete result) : OracleComp (PqxdhLiveKemBirth.Spec KemSK) _) at reached
    simp at reached
  | query_bind query continuation ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    cases query with
    | inl query =>
      rw [scan_other, mem_support_bind_iff] at reached
      obtain ⟨answer, _, reached⟩ := reached
      exact ih answer index cap (by simpa only [IsEncapsulation, ite_false] using bounded.2 answer) reached
    | inr input =>
      have positive : 0 < cap := by simpa only [IsEncapsulation, not_true_eq_false, false_or] using bounded.1
      cases index with
      | zero => exact positive
      | succ index =>
        rw [scan_prior, mem_support_bind_iff] at reached
        obtain ⟨answer, _, reached⟩ := reached
        have earlier := ih answer index (cap - 1)
          (by simpa only [IsEncapsulation, ite_true] using bounded.2 answer) reached
        omega

/-- Every source14 pending cut belongs to the qAccept-sized occurrence family derived from actual source requests. There is no successful-accept, key-origin or public-key-injectivity premise. -/
theorem source_occurrence (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (identityIndex : Nat) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (work : OracleComp (PqxdhRegistrationJointKemCommands.SourceSpec KemSK) Result)
    (budget : PqxdhRegistrationJointKemCommands.Budget)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (state : PqxdhServerAuthNative.NativeState KemSK)
    (index : Nat) (request : Request)
    (next : Reply → OracleComp (Spec KemSK) (PqxdhRegistrationJointKemCommands.Outcome KemSK Result))
    (reached : Cut.pending request next ∈ support
      (scan setup (commands setup codec checks identityIndex publicIdentity work owners state) index)) :
    index < budget (.inl 3) :=
  occurrence_lt setup _ index _
    (command_bound setup codec checks identityIndex publicIdentity work budget certified owners state) request next reached

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutSelection

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutSelection.occurrence_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutSelection.occurrence_lt

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutSelection.source_occurrence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutSelection.source_occurrence
