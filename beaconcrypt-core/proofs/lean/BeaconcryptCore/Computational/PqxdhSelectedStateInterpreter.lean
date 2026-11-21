import BeaconcryptCore.Computational.PqxdhSelectedCallbackCompiler

/-!
Flattening the local source state and the component interpreter preserves the complete adaptive continuation. This is a monadic execution equality; it neither erases private state nor changes the source/random query accounting.
-/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhSelectedStateInterpreter
variable {ι κ Local Component Result Value : Type} {spec : OracleSpec ι} {input : OracleSpec κ}

def pair (result : (Result × Local) × Component) : Result × (Local × Component) :=
  (result.1.1, (result.1.2, result.2))

noncomputable def evaluate (impl : QueryImpl spec (StateT Component ProbComp))
    (work : StateT Local (OracleComp spec) Result) : StateT (Local × Component) ProbComp Result :=
  fun state => pair <$> (simulateQ impl (work.run state.1)).run state.2

/-- Pure source work retains both full states. -/
theorem pure_evaluate (impl : QueryImpl spec (StateT Component ProbComp)) (value : Result) :
    evaluate impl (pure value : StateT Local (OracleComp spec) Result) = pure value := by
  funext state
  simp only [evaluate, StateT.run_pure, simulateQ_pure, map_pure, pair]
  rfl

/-- Flattening commutes with every complete continuation, including adaptive replies and state effects. -/
theorem bind_evaluate (impl : QueryImpl spec (StateT Component ProbComp))
    (work : StateT Local (OracleComp spec) Result) (next : Result → StateT Local (OracleComp spec) Value) :
    evaluate impl (work >>= next) = evaluate impl work >>= fun result => evaluate impl (next result) := by
  funext state
  change pair <$> (simulateQ impl ((work >>= next).run state.1)).run state.2 =
    (do let result ← pair <$> (simulateQ impl (work.run state.1)).run state.2
        pair <$> (simulateQ impl ((next result.1).run result.2.1)).run result.2.2)
  simp only [StateT.run_bind, simulateQ_bind, map_bind, bind_map_left, pair]

/-- The entire adaptive source program executes through the same component interpreter after lowering, retaining both states and every reply. -/
theorem program (impl : QueryImpl spec (StateT Component ProbComp))
    (compiler : QueryImpl input (StateT Local (OracleComp spec)))
    (work : OracleComp input Result) :
    evaluate impl (simulateQ compiler work) = simulateQ (fun query => evaluate impl (compiler query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, pure_evaluate]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, bind_evaluate, ih]

/-- A component program keeps the full local state while the component interpreter retains its own exact poststate. -/
theorem lift_evaluate (impl : QueryImpl spec (StateT Component ProbComp)) (work : OracleComp spec Result) :
    evaluate impl (fun state : Local => (fun reply => (reply, state)) <$> work) =
      (fun state => (fun result => (result.1, (state.1, result.2))) <$> (simulateQ impl work).run state.2) := by
  funext state
  change pair <$> (simulateQ impl ((fun reply => (reply, state.1)) <$> work)).run state.2 = _
  rw [simulateQ_map, StateT.run_map]
  simp only [Functor.map_map, pair]

end BeaconcryptCore.Computational.PqxdhSelectedStateInterpreter

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedStateInterpreter.pure_evaluate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedStateInterpreter.pure_evaluate
/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedStateInterpreter.bind_evaluate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedStateInterpreter.bind_evaluate

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedStateInterpreter.program' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedStateInterpreter.program

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedStateInterpreter.lift_evaluate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedStateInterpreter.lift_evaluate
