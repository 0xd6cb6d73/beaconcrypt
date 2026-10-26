import BeaconcryptCore.Computational.PqxdhLaterChallengeMarkerPrefix
import BeaconcryptCore.Computational.PqxdhRecordConfidentialityTrace
/-! An exact private-monitor annotation of the unchanged native source interpreter and its actual adaptive prefixes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeSourceMonitor
open PqxdhSecretInputKdf PqxdhFirstRecordConfidentiality
variable {ι M P I D K A N C Native Result : Type} {extra : OracleSpec ι} {S B : Nat}

/-- The full wrapper and native source state, with only the private monitor added. -/
abbrev State (Native : Type) := (PqxdhRecordConfidentialityChallenge.State × Native) × Option Bool

/-- Reassociate the original wrapper with its original source interpreter. -/
noncomputable def original (impl : QueryImpl (ConfPostSpec extra S B) (StateT Native ProbComp))
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool) :
    QueryImpl (AdvSpec extra S B) (StateT (PqxdhRecordConfidentialityChallenge.State × Native) ProbComp) :=
  fun query before => (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ impl ((PqxdhRecordConfidentialityChallenge.handler owner number bit query).run before.1)).run before.2

/-- Apply the existing monitor at the actual request state, then return the unchanged source result and complete state. -/
noncomputable def annotated (impl : QueryImpl (ConfPostSpec extra S B) (StateT Native ProbComp))
    (view : Native → InsState M P I D K A N C S B) (target : RootOutput)
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool) :
    QueryImpl (AdvSpec extra S B) (StateT (State Native) ProbComp) :=
  fun query before => (fun result => (result.1, (result.2,
    PqxdhLaterChallengeMonitor.record target owner query before.1.1 (view before.1.2, before.2)))) <$>
      (original impl owner number bit query).run before.1

/-- Erasing the private marker preserves the complete original source query distribution. -/
theorem query_source (impl : QueryImpl (ConfPostSpec extra S B) (StateT Native ProbComp))
    (view : Native → InsState M P I D K A N C S B) (target : RootOutput)
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (query : (AdvSpec extra S B).Domain) (before : State Native) :
    Prod.map id Prod.fst <$> (annotated impl view target owner number bit query).run before =
      (original impl owner number bit query).run before.1 := by
  simp only [annotated, StateT.run, Functor.map_map, Prod.map_def, id_eq]
  exact id_map _

/-- Marker erasure preserves the complete adaptive source execution, not merely returned-value marginals. -/
theorem program_source (impl : QueryImpl (ConfPostSpec extra S B) (StateT Native ProbComp))
    (view : Native → InsState M P I D K A N C S B) (target : RootOutput)
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (client : OracleComp (AdvSpec extra S B) Result) (before : State Native) :
    Prod.map id Prod.fst <$> (simulateQ (annotated impl view target owner number bit) client).run before =
      (simulateQ (original impl owner number bit) client).run before.1 := by
  exact map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (query_source impl view target owner number bit) client before

/-- The reassociated interpreter is exactly the original nested wrapper and source program. -/
theorem original_program (impl : QueryImpl (ConfPostSpec extra S B) (StateT Native ProbComp))
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (client : OracleComp (AdvSpec extra S B) Result)
    (current : PqxdhRecordConfidentialityChallenge.State) (native : Native) :
    (simulateQ (original impl owner number bit) client).run (current, native) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ impl ((simulateQ (PqxdhRecordConfidentialityChallenge.handler owner number bit) client).run current)).run native := by
  induction client using OracleComp.inductionOn generalizing current native with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      simp only [original, StateT.run, bind_map_left]
      exact bind_congr fun reply => ih reply.1.1 reply.1.2 reply.2

/-- An actual finite prefix of the annotated interpreter, retaining every source state and complete adaptive remainder. -/
inductive Reaches (impl : QueryImpl (ConfPostSpec extra S B) (StateT Native ProbComp))
    (view : Native → InsState M P I D K A N C S B) (target : RootOutput)
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool) :
    OracleComp (AdvSpec extra S B) Result → State Native → OracleComp (AdvSpec extra S B) Result → State Native → Prop where
  | here (client : OracleComp (AdvSpec extra S B) Result) (before : State Native) :
      Reaches impl view target owner number bit client before client before
  | later (query : (AdvSpec extra S B).Domain)
      (next : (AdvSpec extra S B).Range query → OracleComp (AdvSpec extra S B) Result)
      (before : State Native) (step : (AdvSpec extra S B).Range query × State Native)
      (rest : OracleComp (AdvSpec extra S B) Result) (after : State Native)
      (actual : step ∈ support ((annotated impl view target owner number bit query).run before))
      (tail : Reaches impl view target owner number bit (next step.1) step.2 rest after) :
      Reaches impl view target owner number bit ((AdvSpec extra S B).query query >>= next) before rest after

/-- A supported source callback ending unused preserves its incoming private marker. -/
theorem query_unmarked (impl : QueryImpl (ConfPostSpec extra S B) (StateT Native ProbComp))
    (view : Native → InsState M P I D K A N C S B) (target : RootOutput)
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (query : (AdvSpec extra S B).Domain) (before : State Native)
    (result : (AdvSpec extra S B).Range query × State Native)
    (supported : result ∈ support ((annotated impl view target owner number bit query).run before))
    (unused : result.2.1.1.pair = none) : before.1.1.pair = none ∧ result.2.2 = before.2 := by
  simp only [annotated, original, StateT.run, Functor.map_map, support_map, Set.mem_image] at supported
  obtain ⟨step, actual, rfl⟩ := supported
  apply PqxdhLaterChallengeMarkerPrefix.callback_unmarked target owner number bit query before.1.1 (view before.1.2) before.2 step.1 _ unused
  apply support_simulateQ_run'_subset impl _ before.1.2
  simp only [StateT.run'_eq, support_map, Set.mem_image]
  exact ⟨step, actual, rfl⟩

/-- An actual annotated prefix ending unused could not have set the monitor along the way. -/
theorem Reaches.unmarked {impl : QueryImpl (ConfPostSpec extra S B) (StateT Native ProbComp)}
    {view : Native → InsState M P I D K A N C S B} {target : RootOutput}
    {owner : RawCtxProtocolReveals.Owner S B} {number : Std.U64} {bit : Bool}
    {client rest : OracleComp (AdvSpec extra S B) Result} {before after : State Native}
    (reached : Reaches impl view target owner number bit client before rest after)
    (unused : after.1.1.pair = none) : before.1.1.pair = none ∧ after.2 = before.2 := by
  induction reached with
  | here client before => exact ⟨unused, rfl⟩
  | later query next before step rest after actual tail ih =>
      have later := ih unused
      have first := query_unmarked impl view target owner number bit query before step actual later.1
      exact ⟨first.1, later.2.trans first.2⟩

/-- Every actual native source prefix lifts to this exact annotation with the same replies, source state and remainder. -/
theorem source_reaches (impl : QueryImpl (ConfPostSpec extra S B) (StateT Native ProbComp))
    (view : Native → InsState M P I D K A N C S B) (target : RootOutput)
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (client rest : OracleComp (AdvSpec extra S B) Result)
    (before after : PqxdhRecordConfidentialityChallenge.State) (native finalNative : Native)
    (reached : PqxdhRecordConfidentialityTrace.Reaches impl owner number bit client before native rest after finalNative)
    (choice : Option Bool) :
    ∃ finalChoice, Reaches impl view target owner number bit client ((before, native), choice) rest ((after, finalNative), finalChoice) := by
  induction reached generalizing choice with
  | here client before native => exact ⟨choice, .here _ _⟩
  | later query next before native step rest after finalNative actual tail ih =>
      obtain ⟨finalChoice, later⟩ := ih (PqxdhLaterChallengeMonitor.record target owner query before (view native, choice))
      refine ⟨finalChoice, .later query next ((before, native), choice) (step.1.1, ((step.1.2, step.2), PqxdhLaterChallengeMonitor.record target owner query before (view native, choice))) rest _ ?_ later⟩
      simp only [annotated, original, StateT.run, Functor.map_map, support_map, Set.mem_image]
      exact ⟨step, actual, rfl⟩

/-- An actual source prefix ending unused retains any incoming marker, including the literal initial none. -/
theorem source_unused (impl : QueryImpl (ConfPostSpec extra S B) (StateT Native ProbComp))
    (view : Native → InsState M P I D K A N C S B) (target : RootOutput)
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (client rest : OracleComp (AdvSpec extra S B) Result)
    (before after : PqxdhRecordConfidentialityChallenge.State) (native finalNative : Native)
    (reached : PqxdhRecordConfidentialityTrace.Reaches impl owner number bit client before native rest after finalNative)
    (choice : Option Bool) (unused : after.pair = none) :
    Reaches impl view target owner number bit client ((before, native), choice) rest ((after, finalNative), choice) := by
  obtain ⟨finalChoice, annotated⟩ := source_reaches impl view target owner number bit client rest before after native finalNative reached choice
  have same : finalChoice = choice := (annotated.unmarked unused).2
  simpa only [same] using annotated

end BeaconcryptCore.Computational.PqxdhLaterChallengeSourceMonitor

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSourceMonitor.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSourceMonitor.query_source

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSourceMonitor.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSourceMonitor.program_source

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSourceMonitor.original_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSourceMonitor.original_program

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSourceMonitor.query_unmarked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSourceMonitor.query_unmarked

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSourceMonitor.Reaches.unmarked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSourceMonitor.Reaches.unmarked

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSourceMonitor.source_reaches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSourceMonitor.source_reaches

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSourceMonitor.source_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSourceMonitor.source_unused
