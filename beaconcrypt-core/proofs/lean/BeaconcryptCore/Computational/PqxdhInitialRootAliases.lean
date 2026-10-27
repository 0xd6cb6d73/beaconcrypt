import BeaconcryptCore.Computational.PqxdhInitialLegalObserver
import BeaconcryptCore.Computational.RawCtxSelectedAliasInitial

/-!
Expose the actual nonselected root-cache reply only inside the private initializer interpreter, then record that same root before the real64-byte evaluation. Selected-coordinate requests use the supplied response without a root argument. This representation preserves repeated/cached requests and permits a value-consistent selected response to be compared with the coordinate-selected response under an explicit candidate event. Public HKDF remains the original real code.
-/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialRootAliases
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid
open PqxdhCorrelatedExtractFamily PqxdhInitialRootLabelService
variable {Result : Type}

abbrev Expanded := unifSpec + (RootOracle + (RootOutput →ₒ PqxdhInitialRootLabelService.Response))

noncomputable def compiler (selected : Message) (response : PqxdhInitialRootLabelService.Response) :
    QueryImpl PqxdhInitialLabelCompiler.Spec (OracleComp Expanded)
  | .inl coin => Expanded.query (.inl coin)
  | .inr (.known root) => Expanded.query (.inr (.inr root))
  | .inr (.family message) =>
      if message = selected then pure response else do
        let root ← Expanded.query (.inr (.inl message))
        Expanded.query (.inr (.inr root))

noncomputable def handler (fixed : FixedHkdfSha512NoSaltSource) :
    QueryImpl Expanded (StateT RootOracle.QueryCache ProbComp)
  | .inl coin => (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT RootOracle.QueryCache ProbComp) coin
  | .inr (.inl message) => uniformImpl (.inr message)
  | .inr (.inr root) => pure (realInitial fixed root)

/-- Splitting the original private callback at its actual root-cache reply preserves the same reply and complete cache state. -/
theorem source_step (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (response : PqxdhInitialRootLabelService.Response) (query : PqxdhInitialLabelCompiler.Spec.Domain)
    (cache : RootOracle.QueryCache) :
    (simulateQ (handler fixed) (compiler selected response query)).run cache =
      (labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected response query).run cache := by
  cases query with
  | inl coin => rfl
  | inr request =>
      cases request with
      | known root => rfl
      | family message =>
          by_cases same : message = selected
          · subst message
            simp [compiler, labelledFull, labelled]
          · simp [compiler, same, labelledFull, labelled, native, handler, OracleSpec.query, StateT.run]
            exact StateT.run_map (realInitial fixed) (uniformImpl (.inr message)) cache

/-- The exact entire adaptive initializer observer survives this private expansion with all original root-cache correlations. -/
theorem source_program (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (response : PqxdhInitialRootLabelService.Response) (client : OracleComp PqxdhInitialLabelCompiler.Spec Result)
    (cache : RootOracle.QueryCache) :
    (simulateQ (handler fixed) (simulateQ (compiler selected response) client)).run cache =
      (simulateQ (labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected response) client).run cache := by
  have same : handler fixed ∘ₛ compiler selected response =
      labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected response := by
    funext query state
    exact source_step fixed selected response query state
  rw [← QueryImpl.simulateQ_compose, same]

def inputs : Expanded.Domain → List RootOutput
  | .inr (.inr root) => [root]
  | _ => []

noncomputable def traced (fixed : FixedHkdfSha512NoSaltSource) :=
  RawCtxSelectedQueryTrace.recorded (handler fixed) inputs

/-- Erasing the complete actual root-candidate log recovers the original adaptive labelled initializer observer, including the entire root cache. -/
theorem trace_source (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (response : PqxdhInitialRootLabelService.Response) (client : OracleComp PqxdhInitialLabelCompiler.Spec Result)
    (state : RootOracle.QueryCache × List RootOutput) :
    Prod.map id Prod.fst <$>
      (simulateQ (traced fixed) (simulateQ (compiler selected response) client)).run state =
      (simulateQ (labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected response) client).run state.1 := by
  rw [traced, RawCtxSelectedQueryTrace.complete, source_program]

noncomputable def alternate (fixed : FixedHkdfSha512NoSaltSource) (response : PqxdhInitialRootLabelService.Response) :
    QueryImpl Expanded (StateT RootOracle.QueryCache ProbComp)
  | .inl coin => handler fixed (.inl coin)
  | .inr (.inl message) => handler fixed (.inr (.inl message))
  | .inr (.inr _) => pure response

noncomputable def consistent (fixed : FixedHkdfSha512NoSaltSource)
    (target : RootOutput) (response : PqxdhInitialRootLabelService.Response) :=
  RawCtxSelectedAliasCoupling.routed (handler fixed) (alternate fixed response) inputs target

/-- Every equal-byte known root or nonselected cached/generated root receives the same selected response; unequal roots keep the actual real initializer. -/
theorem consistent_initial (fixed : FixedHkdfSha512NoSaltSource) (target root : RootOutput)
    (response : PqxdhInitialRootLabelService.Response) (cache : RootOracle.QueryCache) :
    (consistent fixed target response (.inr (.inr root))).run cache =
      pure ((if root = target then response else realInitial fixed root), cache) := by
  simp [consistent, RawCtxSelectedAliasCoupling.routed, inputs, handler, alternate, eq_comm]
  split <;> rfl

/-- Equal-value alias routing is an exact identity in the real initializer world, so no real-world alias probability is needed for this service comparison. -/
theorem consistent_real (fixed : FixedHkdfSha512NoSaltSource) (target : RootOutput) :
    consistent fixed target (realInitial fixed target) = handler fixed := by
  funext query state
  cases query with
  | inl coin => rfl
  | inr privateQuery =>
      cases privateQuery with
      | inl message => rfl
      | inr root =>
          rw [show (consistent fixed target (realInitial fixed target) (.inr (.inr root))) state =
            (consistent fixed target (realInitial fixed target) (.inr (.inr root))).run state from rfl,
            consistent_initial]
          by_cases same : root = target <;> simp [same, handler] <;> rfl

/-- The complete adaptive result, root cache and candidate log differ only when the original actual trace evaluates an initializer at the selected root bytes. -/
theorem distance (fixed : FixedHkdfSha512NoSaltSource) (selected : Message) (target : RootOutput)
    (response : PqxdhInitialRootLabelService.Response) (client : OracleComp PqxdhInitialLabelCompiler.Spec Result)
    (state : RootOracle.QueryCache × List RootOutput) :
    discreteDistance ((simulateQ (traced fixed) (simulateQ (compiler selected response) client)).run state)
      ((simulateQ (RawCtxSelectedQueryTrace.recorded (consistent fixed target response) inputs)
        (simulateQ (compiler selected response) client)).run state) ≤
      Pr{let result ← (simulateQ (traced fixed) (simulateQ (compiler selected response) client)).run state}[target ∈ result.2.2].toReal :=
  RawCtxSelectedAliasInitial.recorded_distance_initial (handler fixed) (alternate fixed response) inputs target _ state

def IsInitializer (query : PqxdhInitialLabelCompiler.Spec.Domain) : Prop := query.isRight = true
def IsEvaluation : Expanded.Domain → Prop
  | .inr (.inr _) => True
  | _ => False
instance : DecidablePred IsInitializer := fun query => inferInstanceAs (Decidable (query.isRight = true))
instance : DecidablePred IsEvaluation
  | .inl _ => isFalse id
  | .inr (.inl _) => isFalse id
  | .inr (.inr _) => isTrue trivial

/-- Each original private initializer request contributes at most one known-root evaluation; selected coordinates contribute none. -/
theorem compiler_evaluations (selected : Message) (response : PqxdhInitialRootLabelService.Response)
    (query : PqxdhInitialLabelCompiler.Spec.Domain) :
    (compiler selected response query).IsQueryBoundP IsEvaluation (if IsInitializer query then 1 else 0) := by
  cases query with
  | inl coin =>
      apply (isQueryBoundP_query_iff (spec := Expanded) (p := IsEvaluation) (.inl coin) 0).mpr
      simp [IsEvaluation]
  | inr request =>
      cases request with
      | known root =>
          apply (isQueryBoundP_query_iff (spec := Expanded) (p := IsEvaluation) (.inr (.inr root)) 1).mpr
          simp
      | family message =>
          simp only [compiler, IsInitializer, Sum.isRight_inr, ite_true]
          split
          · trivial
          · rw [isQueryBoundP_query_bind_iff (spec := Expanded)]
            refine ⟨Or.inl (by simp [IsEvaluation]), fun root => ?_⟩
            apply (isQueryBoundP_query_iff (spec := Expanded) (p := IsEvaluation) (.inr (.inr root)) 1).mpr
            simp

/-- All-reply source initializer caps are inherited by the actual expanded known-root evaluation program. -/
theorem program_evaluations (selected : Message) (response : PqxdhInitialRootLabelService.Response)
    (client : OracleComp PqxdhInitialLabelCompiler.Spec Result) (budget : Nat)
    (bounded : client.IsQueryBoundP IsInitializer budget) :
    (simulateQ (compiler selected response) client).IsQueryBoundP IsEvaluation budget := by
  exact RawCtxSourceOpen.simulate_bound (compiler selected response) IsInitializer IsEvaluation
    client budget bounded (compiler_evaluations selected response)

/-- Every supported original adaptive run retains the entire previous candidate list and appends at most one actual root per original initializer request. -/
theorem trace_length (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (response : PqxdhInitialRootLabelService.Response) (client : OracleComp PqxdhInitialLabelCompiler.Spec Result)
    (budget : Nat) (bounded : client.IsQueryBoundP IsInitializer budget)
    (state : RootOracle.QueryCache × List RootOutput) (result : Result × (RootOracle.QueryCache × List RootOutput))
    (supported : result ∈ support ((simulateQ (traced fixed) (simulateQ (compiler selected response) client)).run state)) :
    result.2.2.length ≤ state.2.length + budget := by
  apply RawCtxSelectedQueryTrace.length_bound (handler fixed) inputs IsEvaluation
    (fun query => by cases query with
      | inl _ => simp [inputs, IsEvaluation]
      | inr query => cases query <;> simp [inputs, IsEvaluation])
    _ budget (program_evaluations selected response client budget bounded) state result supported

end BeaconcryptCore.Computational.PqxdhInitialRootAliases

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootAliases.source_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootAliases.source_step

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootAliases.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootAliases.source_program

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootAliases.trace_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootAliases.trace_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootAliases.consistent_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootAliases.consistent_initial

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootAliases.consistent_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootAliases.consistent_real

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootAliases.distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootAliases.distance

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootAliases.compiler_evaluations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootAliases.compiler_evaluations

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootAliases.program_evaluations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootAliases.program_evaluations

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootAliases.trace_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootAliases.trace_length
