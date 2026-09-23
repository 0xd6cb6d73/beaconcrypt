import BeaconcryptCore.Computational.PqxdhInitialAliasEvent
import BeaconcryptCore.Computational.PqxdhInitialObserverBudgets

/-! Every value-consistent initializer call retains its original uniform sampling cost. Recording the private candidate list is pure bookkeeping; cache misses still pay32 and all ordinary client coins remain charged. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialAliasQueryBounds
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhInitialRootAliases PqxdhInitialObserverCallbackBudgets PqxdhCorrelatedExpandHybrid
variable {Result : Type}
variable (source : FixedHkdfSha512NoSaltSource) (selected : Message) (target : RootOutput)
  (response : PqxdhInitialRootLabelService.Response)

noncomputable def label : QueryImpl PqxdhInitialLabelCompiler.Spec
    (StateT (RootOracle.QueryCache × List RootOutput) ProbComp) :=
  RawCtxSelectedQueryTrace.recorded (consistent source target response) inputs ∘ₛ compiler selected response

/-- Known and selected roots are pure; every nonselected initializer cache miss pays32 and every client coin pays one. -/
theorem step (query : PqxdhInitialLabelCompiler.Spec.Domain) (state : RootOracle.QueryCache × List RootOutput) :
    ((label source selected target response query).run state).IsTotalQueryBound
      ((if IsCoin query then 1 else 0) + (if IsService query then 32 else 0)) := by
  cases query with
  | inl coin =>
    change ((unifSpec.query coin : ProbComp _) >>= fun value => pure (value, state)).IsTotalQueryBound 1
    exact ⟨Nat.zero_lt_succ 0, fun _ => True.intro⟩
  | inr request =>
    simp only [IsCoin, IsService, if_true, if_false, Nat.zero_add]
    cases request with
    | known root =>
      simp only [label, QueryImpl.apply_compose, compiler, simulateQ_spec_query,
        RawCtxSelectedQueryTrace.recorded, StateT.run, consistent, RawCtxSelectedAliasCoupling.routed, inputs]
      split <;> trivial
    | family message =>
      by_cases same : message = selected
      · simp only [label, QueryImpl.apply_compose, compiler, same, if_true, simulateQ_pure, StateT.run_pure]
        trivial
      · simp only [label, QueryImpl.apply_compose, compiler, same, if_false,
          simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
        have rootBound : ((RawCtxSelectedQueryTrace.recorded (consistent source target response) inputs
          (.inr (.inl message))).run state).IsTotalQueryBound 32 := by
          simp only [RawCtxSelectedQueryTrace.recorded, consistent, RawCtxSelectedAliasCoupling.routed, inputs, List.not_mem_nil, if_false, handler, StateT.run, bind_pure_comp, List.append_nil]
          change ((fun result => (result.1, (result.2, state.2))) <$> (uniformImpl (.inr message)).run state.1).IsTotalQueryBound 32
          apply (isQueryBound_map_iff _ _ _ _ _).2
          exact PqxdhCorrelatedExpandQueryBounds.cached_step ($ᵗ RootOutput) 32
            (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32) (.inr message) state.1
        simpa only [Nat.add_zero] using isTotalQueryBound_bind rootBound (n₂ := 0) (fun result => by
          simp only [RawCtxSelectedQueryTrace.recorded, StateT.run, consistent, RawCtxSelectedAliasCoupling.routed, inputs]
          split <;> trivial)

/-- The value-consistent interpreter charges all ordinary coins and each actual initializer attempt, including failed and repeated source branches. -/
theorem program (client : OracleComp PqxdhInitialLabelCompiler.Spec Result)
    (u r : Nat) (coins : client.IsQueryBoundP IsCoin u) (services : client.IsQueryBoundP IsService r)
    (state : RootOracle.QueryCache × List RootOutput) :
    ((simulateQ (label source selected target response) client).run state).IsTotalQueryBound (u + 32 * r) := by
  induction client using OracleComp.inductionOn generalizing u r state with
  | pure value => trivial
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at coins services
    rw [simulateQ_query_bind, StateT.run_bind]
    apply (isTotalQueryBound_bind (step source selected target response query state)
      (fun answer => ih answer.1 _ _ (coins.2 answer.1) (services.2 answer.1) answer.2)).mono
    have hu := coins.1
    have hr := services.1
    split_ifs at * <;> simp_all only [not_true_eq_false, false_or] <;> omega

end BeaconcryptCore.Computational.PqxdhInitialAliasQueryBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialAliasQueryBounds.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialAliasQueryBounds.step

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialAliasQueryBounds.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialAliasQueryBounds.program
