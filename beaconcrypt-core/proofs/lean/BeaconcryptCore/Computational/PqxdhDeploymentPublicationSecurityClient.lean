-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityReduction

/-! Public terminal reports for the actual original and publication-suppressed source clients. Reports add no source primitive request, preserve the complete source result, and turn every accepted candidate with an unissued field into the existing ordinary joint-use weak-EUF endpoint. -/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityClient
open PqxdhJointIdentity PqxdhDynamicIdentityPool PqxdhDynamicIdentityRouting PqxdhDynamicIdentityReports
open PqxdhJointPhase1Reports (ProtocolSpec SourceClass sourceImpl)
open PqxdhDeploymentProvenance (announceAll acceptedCandidates)
open PqxdhDeploymentPublicationSecurityReduction (reduction)
variable {Reader Response Result : Type}

/-- Execute the full source client, then report its actual accepted candidates at every generated identity position. The complete source result remains the returned value. -/
noncomputable def terminal (codec : PqxdhServerAuthExperiment.Codec Reader Response) (count : Nat)
    (transcript : Result → List PqxdhDeploymentInterface.Entry) (source : OracleComp ProtocolSpec Result) :
    OracleComp ProtocolSpec Result := do
  let outcome ← source
  announceAll count (acceptedCandidates codec (transcript outcome))
  pure outcome

/-- Terminal reports add zero queries of every original source class. -/
theorem terminal_class_bound (codec : PqxdhServerAuthExperiment.Codec Reader Response) (count : Nat)
    (transcript : Result → List PqxdhDeploymentInterface.Entry) (source : OracleComp ProtocolSpec Result)
    (predicate : DynamicSpec.Domain → Prop) [DecidablePred predicate] (bound : Nat)
    (bounded : source.IsQueryBoundP (SourceClass predicate) bound) :
    (terminal codec count transcript source).IsQueryBoundP (SourceClass predicate) bound := by
  have result := isQueryBoundP_bind (ob := fun outcome => do
      announceAll count (acceptedCandidates codec (transcript outcome))
      pure outcome) (m := 0) bounded fun outcome _ =>
    isQueryBoundP_bind (m := 0) (n := 0)
      (PqxdhDeploymentProvenance.announceAll_bound count (acceptedCandidates codec (transcript outcome)) predicate)
      fun _ _ => isQueryBoundP_pure (SourceClass predicate) outcome 0
  simpa only [terminal, Nat.add_zero] using result

/-- Complete execution of the source followed by its real terminal report batches, retaining the reached full interpreter state. -/
theorem terminal_run (joint : Primitives) (codec : PqxdhServerAuthExperiment.Codec Reader Response) (count : Nat)
    (transcript : Result → List PqxdhDeploymentInterface.Entry) (source : OracleComp ProtocolSpec Result) :
    PqxdhJointPhase1Reports.run joint count (terminal codec count transcript source) =
      PqxdhJointPhase1Reports.run joint count source >>= fun reached =>
        (fun after => (reached.1, after.2)) <$> (simulateQ (sourceImpl joint count)
          (announceAll count (acceptedCandidates codec (transcript reached.1)))).run reached.2 := by
  simp only [PqxdhJointPhase1Reports.run, terminal, simulateQ_bind, StateT.run_bind, simulateQ_pure,
    StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def]

/-- A fresh field of an actual accepted raw candidate in the source client's final transcript. -/
def Eligible (joint : Primitives) (codec : PqxdhServerAuthExperiment.Codec Reader Response) {count : Nat}
    (transcript : Result → List PqxdhDeploymentInterface.Entry)
    (reached : Result × (PqxdhJointPhase1Reports.Monitor count × ReportingState count)) : Prop :=
  ∃ target candidate, candidate ∈ acceptedCandidates codec (transcript reached.1) ∧
    PqxdhJointPhase1Reports.FieldOriginFailure joint ⟨target, candidate⟩ reached.2.1.snapshot

/-- Every eligible final source candidate raises the sticky monitor through the actual terminal batches. No source result, callback or probability mass is discarded. -/
theorem eligible_terminal (joint : Primitives) (codec : PqxdhServerAuthExperiment.Codec Reader Response) (count : Nat)
    (transcript : Result → List PqxdhDeploymentInterface.Entry) (source : OracleComp ProtocolSpec Result) :
    Pr{let reached ← PqxdhJointPhase1Reports.run joint count source}[Eligible joint codec transcript reached] ≤
      Pr{let final ← PqxdhJointPhase1Reports.run joint count (terminal codec count transcript source)}[final.2.1.occurred = true] := by
  classical
  rw [terminal_run]
  have compared := prEvent_bind_mono_of_forall_le_of_support
    (PqxdhJointPhase1Reports.run joint count source)
    (fun reached => (pure (decide (Eligible joint codec transcript reached)) : ProbComp Bool))
    (fun reached => (fun after => after.2.1.occurred) <$> (simulateQ (sourceImpl joint count)
      (announceAll count (acceptedCandidates codec (transcript reached.1)))).run reached.2)
    (fun value : Bool => value = true) (fun value : Bool => value = true) (fun reached _ => ?_)
  · simpa only [map_bind, Functor.map_map, bind_pure_comp, prEvent_map, decide_eq_true_eq] using compared
  · by_cases happened : Eligible joint codec transcript reached
    · simp only [prEvent_pure, decide_eq_true_eq, happened, ite_true]
      apply le_of_eq
      symm
      apply OracleComp.prEvent_eq_one_of_forall_mem_support
      intro value supported
      rw [support_map] at supported
      obtain ⟨after, afterMember, rfl⟩ := supported
      obtain ⟨target, candidate, member, failure⟩ := happened
      exact PqxdhDeploymentPublishedTuple.announceAll_detects joint count target _ candidate member reached.2 failure
        after afterMember
    · simp only [prEvent_pure, decide_eq_true_eq, happened, ite_false, zero_le]

/-- Eligible candidate probability is bounded by genuine ordinary joint-use reductions of this very source client with its terminal reports. -/
theorem eligible_bound (joint : Primitives) (codec : PqxdhServerAuthExperiment.Codec Reader Response) (count : Nat)
    (transcript : Result → List PqxdhDeploymentInterface.Entry) (source : OracleComp ProtocolSpec Result)
    (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    (creates : source.IsQueryBoundP (SourceClass IsCreate) (count + 1)) :
    Pr{let reached ← PqxdhJointPhase1Reports.run joint (count + 1) source}[Eligible joint codec transcript reached] ≤
      ∑ target : Fin (count + 1), advantage joint
        (reduction joint count (terminal codec (count + 1) transcript source) fallback ordinaryFallback target) :=
  (eligible_terminal joint codec (count + 1) transcript source).trans
    (PqxdhDeploymentPublicationSecurityReduction.report_bound joint count _ fallback ordinaryFallback
      (terminal_class_bound codec (count + 1) transcript source IsCreate (count + 1) creates))

/-- The exact source signing, converted-DH and uniform caps survive terminal reporting and the ordinary generated-identity reduction. -/
theorem terminal_bills (joint : Primitives) (codec : PqxdhServerAuthExperiment.Codec Reader Response) (count : Nat)
    (transcript : Result → List PqxdhDeploymentInterface.Entry) (source : OracleComp ProtocolSpec Result)
    (fallback : DynamicForgery) (ordinaryFallback : Forgery) (qSign qDh qUniform : Nat)
    (signBound : source.IsQueryBoundP (SourceClass (dynamicClass (PqxdhJointIdentityFamily.IsClass .sign))) qSign)
    (dhBound : source.IsQueryBoundP (SourceClass (dynamicClass (PqxdhJointIdentityFamily.IsClass .staticDh))) qDh)
    (uniformBound : source.IsQueryBoundP (SourceClass (dynamicClass (PqxdhJointIdentityFamily.IsClass .uniform))) qUniform)
    (target : Fin (count + 1)) :
    PqxdhDeploymentPublicationSecurityReduction.Bills joint count (terminal codec (count + 1) transcript source)
      fallback ordinaryFallback qSign qDh qUniform target :=
  PqxdhDeploymentPublicationSecurityReduction.bills joint count _ fallback ordinaryFallback qSign qDh qUniform
    (terminal_class_bound codec (count + 1) transcript source _ _ signBound)
    (terminal_class_bound codec (count + 1) transcript source _ _ dhBound)
    (terminal_class_bound codec (count + 1) transcript source _ _ uniformBound) target

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityClient

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityClient.terminal_class_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityClient.terminal_class_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityClient.terminal_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityClient.terminal_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityClient.eligible_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityClient.eligible_terminal

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityClient.eligible_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityClient.eligible_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityClient.terminal_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityClient.terminal_bills
