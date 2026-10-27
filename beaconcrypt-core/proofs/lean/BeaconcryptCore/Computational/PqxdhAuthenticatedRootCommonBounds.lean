import BeaconcryptCore.Computational.PqxdhAuthenticatedRootExperiment
import BeaconcryptCore.Computational.PqxdhGeneratedBeaconQueryBounds
import BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverResources

/-!
The common and rejected branches retain the original unblocked source scheduler. Their conservative structural bill includes every attempted native finish, original record/public/reveal request and builder callback. The ordinary source interpreter charges identity creation separately at thirty-two uniform calls; no arbitrary common continuation or primitive effect is treated as free. These bounds use the actual compiler before evaluation and never infer costs from distribution equality.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAuthenticatedRootCommonBounds
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhPhase2GeneratedDriver PqxdhGeneratedBeaconState PqxdhAuthenticatedRootExperiment
open PqxdhPrivateAcceptedRoot PqxdhKemIndCca PqxdhInitializerSecrecy
open PqxdhCorrelatedRootQueryBounds PqxdhChallengeSecretQueryBounds PqxdhPrivateAcceptedRootBounds
open PqxdhPhase2SourceSchedulerBounds
variable {ι : Type} {baseSpec : OracleSpec ι} {M P I K X Response A : Type} {S B : Nat}

set_option backward.isDefEq.respectTransparency false in
/-- The original source lifting preserves its complete query count. -/
theorem selectorLift_total {Result : Type} (client : OracleComp (SelectorSpec baseSpec) Result)
    (q : Nat) (bounded : client.IsTotalQueryBound q) :
    (simulateQ selectorLift client).IsTotalQueryBound q := by
  induction client using OracleComp.inductionOn generalizing q with
  | pure value => trivial
  | query_bind query next ih =>
    rw [isTotalQueryBound_query_bind_iff] at bounded
    cases query <;> simp only [simulateQ_bind, simulateQ_spec_query, selectorLift]
    all_goals
      rw [isTotalQueryBound_query_bind_iff]
      exact ⟨bounded.1, fun answer => ih answer _ (bounded.2 answer)⟩

set_option backward.isDefEq.respectTransparency false in
/-- The common source lifting cannot issue an opaque target-root request. -/
theorem selectorLift_roots {Result : Type} (client : OracleComp (SelectorSpec baseSpec) Result) :
    (simulateQ selectorLift client).IsQueryBoundP
      (LocalClass (baseSpec := baseSpec) IsPrivateRoot) 0 := by
  induction client using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    cases query <;> simp only [simulateQ_bind, simulateQ_spec_query, selectorLift]
    all_goals
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp [LocalClass, IsPrivateRoot]), fun answer => ih answer⟩

set_option backward.isDefEq.respectTransparency false in
/-- Native builder coins keep their exact structural cost. -/
theorem coins_total {Result : Type} (client : ProbComp Result) (q : Nat)
    (bounded : client.IsTotalQueryBound q) :
    (PqxdhProtocolRegistration.coins (baseSpec := baseSpec) client).IsTotalQueryBound q := by
  induction client using OracleComp.inductionOn generalizing q with
  | pure value => trivial
  | query_bind query next ih =>
    rw [isTotalQueryBound_query_bind_iff] at bounded
    simp only [PqxdhProtocolRegistration.coins, simulateQ_bind, simulateQ_spec_query]
    rw [isTotalQueryBound_query_bind_iff]
    exact ⟨bounded.1, fun answer => ih answer _ (bounded.2 answer)⟩

set_option backward.isDefEq.respectTransparency false in
/-- Builder coins cannot issue opaque target-root requests. -/
theorem coins_roots {Result : Type} (client : ProbComp Result) :
    (PqxdhProtocolRegistration.coins (baseSpec := baseSpec) client).IsQueryBoundP
      (LocalClass (baseSpec := baseSpec) IsPrivateRoot) 0 := by
  induction client using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [PqxdhProtocolRegistration.coins, simulateQ_bind, simulateQ_spec_query]
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [LocalClass, IsPrivateRoot]), fun answer => ih answer⟩

/-- The original native builder and the complete common scheduler have an explicit conservative structural bill. -/
def commonBill (qLocal qAux : Nat) (budget : Budget) : Nat := (64 + 5 * qAux) + bill qLocal budget

variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (qLocal : Nat) (localBound : ∀ query state, ((env.localImpl query).run state).IsTotalQueryBound qLocal)
    (budget : Budget) (postBound : ∀ choice response, Bounded (post choice response) budget)
    (qAux : Nat)

include localBound postBound in
/-- Rejected registration resumes the complete original common scheduler, including every attempted finish. -/
theorem completed_total
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome
      (PqxdhPrivatePhase1Prefix.Retained setup Unit (driver env.toDriverEnvironment program).State)))
    (execution : PqxdhSourceAuthenticatedRoot.ServerExecution) :
    ((commonObserver env program post).completed output execution).IsTotalQueryBound (commonBill qLocal qAux budget) := by
  cases output with
  | none => trivial
  | some output =>
    apply selectorLift_total
    apply IsTotalQueryBound.mono (n₁ := bill qLocal budget)
    · simpa only [IsTotalQueryBound, isQueryBound_map_iff] using
        compiler_total env.source env.recordWriter env.senderId env.route env.decode env.localImpl qLocal localBound
          (post output.context.selection.1 (.ok none)) budget (postBound _ _) output.context.selection.2
    · exact Nat.le_add_left _ _

include localBound postBound in
/-- Accepted common candidates pay the actual builder cost before their full adaptive scheduler. -/
theorem accepted_total
    (auxBound : ∀ query state, ((env.aux query).run state).IsTotalQueryBound qAux)
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome
      (PqxdhPrivatePhase1Prefix.Retained setup Unit (driver env.toDriverEnvironment program).State)))
    (execution : Ready) :
    ((commonObserver env program post).accepted output execution).IsTotalQueryBound (commonBill qLocal qAux budget) := by
  cases output with
  | none => trivial
  | some output =>
    apply isTotalQueryBound_bind
      (coins_total _ _ (PqxdhProtocolQueryBounds.build_uniform env.source env.recordWriter env.aux qAux auxBound
        env.senderId env.index env.metadata execution output.context.selection.2))
    intro result
    apply selectorLift_total
    simpa only [IsTotalQueryBound, isQueryBound_map_iff] using
      compiler_total env.source env.recordWriter env.senderId env.route env.decode env.localImpl qLocal localBound
        (post output.context.selection.1 result.1) budget (postBound _ _) result.2

/-- Rejection runs only original source operations; it cannot enter the opaque target-root channel. -/
theorem completed_roots
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome
      (PqxdhPrivatePhase1Prefix.Retained setup Unit (driver env.toDriverEnvironment program).State)))
    (execution : PqxdhSourceAuthenticatedRoot.ServerExecution) :
    ((commonObserver env program post).completed output execution).IsQueryBoundP
      (LocalClass (baseSpec := baseSpec) IsPrivateRoot) 0 := by
  cases output with
  | none => trivial
  | some output => exact selectorLift_roots _

/-- Arbitrary accepted common candidates likewise retain the unblocked original source channel. -/
theorem accepted_roots
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome
      (PqxdhPrivatePhase1Prefix.Retained setup Unit (driver env.toDriverEnvironment program).State)))
    (execution : Ready) :
    ((commonObserver env program post).accepted output execution).IsQueryBoundP
      (LocalClass (baseSpec := baseSpec) IsPrivateRoot) 0 := by
  cases output with
  | none => trivial
  | some output => exact isQueryBoundP_bind (coins_roots _) (fun _ _ => selectorLift_roots _)

include localBound postBound in
/-- Every common completed observer class is bounded by the explicit structural bill, with zero opaque roots. -/
theorem completed_bounds
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome
      (PqxdhPrivatePhase1Prefix.Retained setup Unit (driver env.toDriverEnvironment program).State)))
    (execution : PqxdhSourceAuthenticatedRoot.ServerExecution) :
    let total := commonBill qLocal qAux budget
    ObserverBounds ((commonObserver env program post).completed output execution) total total total total total 0 := by
  have bounded := completed_total env program post qLocal localBound budget postBound qAux output execution
  exact ⟨bounded.isQueryBoundP, bounded.isQueryBoundP, bounded.isQueryBoundP, bounded.isQueryBoundP,
    bounded.isQueryBoundP, completed_roots env program post output execution⟩

include localBound postBound in
/-- Every common accepted observer class includes the complete native builder and original source schedule. -/
theorem accepted_bounds
    (auxBound : ∀ query state, ((env.aux query).run state).IsTotalQueryBound qAux)
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome
      (PqxdhPrivatePhase1Prefix.Retained setup Unit (driver env.toDriverEnvironment program).State)))
    (execution : Ready) :
    let total := commonBill qLocal qAux budget
    ObserverBounds ((commonObserver env program post).accepted output execution) total total total total total 0 := by
  have bounded := accepted_total env program post qLocal localBound budget postBound qAux auxBound output execution
  exact ⟨bounded.isQueryBoundP, bounded.isQueryBoundP, bounded.isQueryBoundP, bounded.isQueryBoundP,
    bounded.isQueryBoundP, accepted_roots env program post output execution⟩

end BeaconcryptCore.Computational.PqxdhAuthenticatedRootCommonBounds

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootCommonBounds.selectorLift_total' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootCommonBounds.selectorLift_total

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootCommonBounds.selectorLift_roots' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootCommonBounds.selectorLift_roots

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootCommonBounds.coins_total' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootCommonBounds.coins_total

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootCommonBounds.coins_roots' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootCommonBounds.coins_roots

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootCommonBounds.completed_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootCommonBounds.completed_total

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootCommonBounds.accepted_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootCommonBounds.accepted_total

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootCommonBounds.completed_roots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootCommonBounds.completed_roots

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootCommonBounds.accepted_roots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootCommonBounds.accepted_roots

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootCommonBounds.completed_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootCommonBounds.completed_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootCommonBounds.accepted_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootCommonBounds.accepted_bounds
