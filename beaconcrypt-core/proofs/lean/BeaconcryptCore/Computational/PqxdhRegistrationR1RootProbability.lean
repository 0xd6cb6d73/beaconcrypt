-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationR1RootSurface
import BeaconcryptCore.Computational.PqxdhServerAuthCommonProbability

/-! Unconditional generated-target probability transport through the actual constructor and initialization refusals. The source's generator order is retained; no conditional uniformity assertion is used. -/

open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationR1RootProbability
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment
open PqxdhRegistrationR1RootAudit PqxdhRegistrationR1RootSurface
variable {ι KemSK Reader Response Result A : Type} {baseSpec : OracleSpec ι}

/-- A refused Beacon creation has no target event. Successful creation observes the retained same-run source outcome. -/
def prefixDecision (observe : PqxdhServerAuthRootExecution.Outcome KemSK → Bool) : PrefixOutcome KemSK Result → Bool
  | .rejected _ => false
  | .created audit => observe audit.2

/-- Server-constructor refusal also has no target event. This never conditions the experiment on creation or success. -/
def laneDecision (observe : PqxdhServerAuthRootExecution.Outcome KemSK → Bool)
    (result : Option (PqxdhLiveServerConstruction.Created Unit × PrefixOutcome KemSK Result) × A) : Bool :=
  match result.1 with
  | none => false
  | some (_, outcome) => prefixDecision observe outcome

/-- Dropping only the second initialization gate can increase a target-event probability. The refused missing-owner tail is still executed on the left, with all of its possible failures and optional replies. -/
theorem prefix_probability (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (origin : PqxdhLiveServerConstruction.Origin)
    (ensureInit : StateT A ProbComp Bool) (work : AuthInput → OracleComp ServerAuthSpec Result)
    (runtime : A) (observe : PqxdhServerAuthRootExecution.Outcome KemSK → Bool) :
    𝒟[(fun result => prefixDecision observe result.1) <$>
      rootPrefix setup codec checks serverSeed origin ensureInit (fun _ => work) runtime] {true} ≤
    𝒟[(fun audit => observe audit.2) <$> rootAudited setup codec checks serverSeed
      (fun published => work ⟨setup.joint.publicKeys serverSeed, setup.serverKeyId, published, none⟩)] {true} := by
  simp only [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map, Function.comp_def]
  unfold rootPrefix
  refine probEvent_bind_le_of_forall_le fun initialized _ => ?_
  cases initialized.1 <;> simp only [Bool.false_eq_true, ite_false, ite_true, probEvent_map, prefixDecision]
  all_goals simp [Function.comp_def]

/-- The target event of the actual generated-Server experiment is bounded by the existing ordered authentication experiment. Both initialization gates are dropped only by probability monotonicity, with their runtime-dependent refusal tails intact on the source side. -/
theorem generated_probability (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (work : AuthInput → OracleComp ServerAuthSpec Result)
    (runtime : A) (observe : PqxdhServerAuthRootExecution.Outcome KemSK → Bool) :
    𝒟[laneDecision observe <$> rootExperiment setup codec checks ensureInit none (fun _ => work) runtime] {true} ≤
      𝒟[observe <$> PqxdhServerAuthRootObserved.orderedGame setup codec checks false
        (fun input => (fun _ => ()) <$> work input)] {true} := by
  rw [← generated_order setup codec checks work]
  simp only [rootExperiment, PqxdhLiveServerConstruction.construct, StateT.run, map_bind,
    bind_assoc, Functor.map_map, evalDist_apply_singleton, ← probEvent_eq_eq_probOutput]
  refine probEvent_bind_le_of_forall_le fun initialized _ => ?_
  cases initialized.1 <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_bind,
    map_pure, laneDecision, probEvent_pure, zero_le, bind_map_left, Functor.map_map]
  refine probEvent_bind_mono fun seed _ => ?_
  simpa only [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput,
    PqxdhLiveServerConstruction.initialized] using
    prefix_probability setup codec checks seed .generated ensureInit work initialized.2 observe

/-- The actual common session/record failure is tested on the retained outcome; every constructor-refusal branch is false. The supplied-seed experiment is defined operationally but has no security conclusion here. -/
noncomputable def laneFailure (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) :
    (Option (PqxdhLiveServerConstruction.Created Unit × PrefixOutcome KemSK Result) × A) → Bool :=
  laneDecision (PqxdhServerAuthCommonProbability.decision setup codec checks)

/-- The source's unconditional generated-target common-authentication failure has no extra selection or probability loss from its constructor gates. No uniformity conditional on successful creation is asserted. -/
theorem generated_failure_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (work : AuthInput → OracleComp ServerAuthSpec Result) (runtime : A) :
    𝒟[laneFailure setup codec checks <$>
      rootExperiment setup codec checks ensureInit none (fun _ => work) runtime] {true} ≤
      𝒟[PqxdhServerAuthCommonProbability.decision setup codec checks <$>
        PqxdhServerAuthRootObserved.orderedGame setup codec checks false
          (fun input => (fun _ => ()) <$> work input)] {true} :=
  generated_probability setup codec checks ensureInit work runtime
    (PqxdhServerAuthCommonProbability.decision setup codec checks)

end BeaconcryptCore.Computational.PqxdhRegistrationR1RootProbability

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1RootProbability.prefix_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1RootProbability.prefix_probability
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1RootProbability.generated_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1RootProbability.generated_probability
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1RootProbability.generated_failure_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1RootProbability.generated_failure_le
