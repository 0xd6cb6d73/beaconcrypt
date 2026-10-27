-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeSourceMonitor
import BeaconcryptCore.Computational.PqxdhLaterChallengeMonitorSource

/-! Extract the designation from the same complete annotated source path that produced the final target event. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedTrace
open PqxdhSecretInputKdf PqxdhFirstRecordConfidentiality PqxdhLaterChallengeSourceMonitor
variable {ι Native Result : Type} {extra : OracleSpec ι} {S B : Nat}
variable (impl : QueryImpl (ConfPostSpec extra S B) (StateT Native ProbComp))
    (selected : Native → Prop)
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)

/-- Run the unchanged original source callback and record only the actual pre-request predicate. The predicate does not alter source acceptance, replies or private state. -/
noncomputable def annotated : QueryImpl (AdvSpec extra S B) (StateT (State Native) ProbComp) :=
  fun query before => (fun result => (result.1, (result.2,
    PqxdhLaterChallengeMonitorSource.record selected query (before.1.1, (before.1.2, before.2))))) <$>
      (original impl owner number bit query).run before.1

/-- The actual annotated prefix retains the complete source state and adaptive remainder. -/
inductive Reaches : OracleComp (AdvSpec extra S B) Result → State Native →
    OracleComp (AdvSpec extra S B) Result → State Native → Prop where
  | here (client : OracleComp (AdvSpec extra S B) Result) (before : State Native) :
      Reaches client before client before
  | later (query : (AdvSpec extra S B).Domain)
      (next : (AdvSpec extra S B).Range query → OracleComp (AdvSpec extra S B) Result)
      (before : State Native) (step : (AdvSpec extra S B).Range query × State Native)
      (rest : OracleComp (AdvSpec extra S B) Result) (after : State Native)
      (actual : step ∈ support ((annotated impl selected owner number bit query).run before))
      (tail : Reaches (next step.1) step.2 rest after) :
      Reaches ((AdvSpec extra S B).query query >>= next) before rest after

/-- Erasing the annotation from an actual prefix gives the same original source prefix with every intermediate native state retained. -/
theorem Reaches.source {client rest : OracleComp (AdvSpec extra S B) Result} {before after : State Native}
    (reached : Reaches impl selected owner number bit client before rest after) :
    PqxdhRecordConfidentialityTrace.Reaches impl owner number bit client before.1.1 before.1.2 rest after.1.1 after.1.2 := by
  induction reached with
  | here client before => exact .here client before.1.1 before.1.2
  | later query next before step rest after actual tail ih =>
    simp only [annotated, original, StateT.run, Functor.map_map, support_map, Set.mem_image] at actual
    obtain ⟨head, returned, rfl⟩ := actual
    exact .later query next before.1.1 before.1.2 head rest after.1.1 after.1.2 returned ih

/-- Erasing the annotation preserves the complete original execution distribution. -/
theorem program_source (client : OracleComp (AdvSpec extra S B) Result) (before : State Native) :
    Prod.map id Prod.fst <$> (simulateQ (annotated impl selected owner number bit) client).run before =
      (simulateQ (original impl owner number bit) client).run before.1 := by
  apply map_run_simulateQ_eq_of_query_map_eq
  intro query state
  simp only [annotated, StateT.run, Functor.map_map, Prod.map_def, id_eq]
  exact id_map _

/-- Removing only the marker recovers the original nested wrapper and source distribution with their literal tuple association. -/
theorem program_nested (client : OracleComp (AdvSpec extra S B) Result) (before : State Native) :
    (fun result => ((result.1, result.2.1.1), result.2.1.2)) <$>
      (simulateQ (annotated impl selected owner number bit) client).run before =
      (simulateQ impl ((simulateQ (PqxdhRecordConfidentialityChallenge.handler owner number bit) client).run before.1.1)).run before.1.2 := by
  have erased := congrArg (fun work => (fun result => ((result.1, result.2.1), result.2.2)) <$> work)
    (program_source impl selected owner number bit client before)
  simp only [Functor.map_map, Prod.map_def, id_eq] at erased
  rw [original_program impl owner number bit client before.1.1 before.1.2] at erased
  simpa only [Functor.map_map, id_map'] using erased

/-- Once designated, the complete annotation carries the same marker through every source reply and entire adaptive remainder, with the full source distribution unchanged. -/
theorem recorded (client : OracleComp (AdvSpec extra S B) Result)
    (before : PqxdhRecordConfidentialityChallenge.State × Native) (value : Bool) :
    (simulateQ (annotated impl selected owner number bit) client).run (before, some value) =
      (fun result => (result.1, (result.2, some value))) <$>
        (simulateQ (original impl owner number bit) client).run before := by
  induction client using OracleComp.inductionOn generalizing before with
  | pure result => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    simp only [annotated, StateT.run, PqxdhLaterChallengeMonitorSource.record, bind_map_left]
    exact bind_congr fun result => ih result.1 result.2

/-- Every supported annotated outcome projects to the complete nested original source execution, with the same result, wrapper state and native poststate. -/
theorem original_supported (client : OracleComp (AdvSpec extra S B) Result)
    (before : State Native) (result : Result × State Native)
    (supported : result ∈ support ((simulateQ (annotated impl selected owner number bit) client).run before)) :
    ((result.1, result.2.1.1), result.2.1.2) ∈ support ((simulateQ impl
      ((simulateQ (PqxdhRecordConfidentialityChallenge.handler owner number bit) client).run before.1.1)).run before.1.2) := by
  have actual : (result.1, result.2.1) ∈ support
      ((simulateQ (original impl owner number bit) client).run before.1) := by
    rw [← program_source impl selected owner number bit client before, support_map]
    exact ⟨result, supported, rfl⟩
  rw [original_program, support_map] at actual
  obtain ⟨⟨⟨value, current⟩, native⟩, member, same⟩ := actual
  exact (congrArg (fun value => ((value.1, value.2.1), value.2.2)) same) ▸ member

/-- Every actual complete suffix beginning with a designation retains exactly that designation. -/
theorem recorded_support (client : OracleComp (AdvSpec extra S B) Result)
    (before : PqxdhRecordConfidentialityChallenge.State × Native) (value : Bool)
    (result : Result × State Native)
    (supported : result ∈ support ((simulateQ (annotated impl selected owner number bit) client).run (before, some value))) :
    result.2.2 = some value := by
  rw [recorded, support_map] at supported
  obtain ⟨outcome, _, rfl⟩ := supported
  rfl

/-- The admitted challenge lies on this very annotated execution: both its complete prefix and reply-dependent suffix retain the original native states, and the final designation is its actual pre-request condition. -/
def Origin (client : OracleComp (AdvSpec extra S B) Result)
    (before : PqxdhRecordConfidentialityChallenge.State × Native) (result : Result × State Native) : Prop :=
  ∃ (left right : Pqxdh.Bytes) (next : Option RawCtxSourceSend.Encrypted → OracleComp (AdvSpec extra S B) Result)
      (current : PqxdhRecordConfidentialityChallenge.State) (reached after : Native) (record : RawCtxSourceSend.Encrypted),
    Reaches impl selected owner number bit client (before, none)
      ((AdvSpec extra S B).query (.inr (left, right)) >>= next) ((current, reached), none) ∧
    current.pair = none ∧ left.length = right.length ∧ current.otherTarget = false ∧
    (some record, after) ∈ support ((simulateQ impl
      (PqxdhRecordConfidentialityChallenge.send owner (if bit then right else left))).run reached) ∧
    result ∈ support ((simulateQ (annotated impl selected owner number bit) (next (some record))).run
      (({ current with pair := some (left, right), reply := some (some record) }, after),
        some (@decide (selected reached) (Classical.propDecidable _)))) ∧
    record.sequence = number ∧
    result.2.2 = some (@decide (selected reached) (Classical.propDecidable _))

/-- A final target event from an unused annotated source wrapper identifies the literal challenge on the same complete execution, including its exact final private designation. -/
theorem origin (client : OracleComp (AdvSpec extra S B) Result)
    (before : PqxdhRecordConfidentialityChallenge.State × Native) (result : Result × State Native)
    (supported : result ∈ support ((simulateQ (annotated impl selected owner number bit) client).run (before, none)))
    (unused : before.1.pair = none) (accepted : PqxdhRecordConfidentialityChallenge.Target number result.2.1.1) :
    Origin impl selected owner number bit client before result := by
  induction client using OracleComp.inductionOn generalizing before result
  case query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨step, actual, later⟩ := supported
    have extend (unmarked : step.2.2 = none) : Origin impl selected owner number bit (next step.1) step.2.1 result →
        Origin impl selected owner number bit ((AdvSpec extra S B).query query >>= next) before result := by
      rintro ⟨left, right, continuation, current, reached, after, record, path, remaining⟩
      exact ⟨left, right, continuation, current, reached, after, record,
        .later query next (before, none) step _ ((current, reached), none) actual
          (by simpa only [← unmarked] using path), remaining⟩
    rcases query with request | ⟨left, right⟩
    case inr =>
      by_cases equal : left.length = right.length
      case pos =>
        simp only [annotated, original, StateT.run, Functor.map_map, support_map, Set.mem_image] at actual
        obtain ⟨head, returned, rfl⟩ := actual
        change head ∈ support ((simulateQ impl ((PqxdhRecordConfidentialityChallenge.handler owner number bit (.inr (left, right))).run before.1)).run before.2) at returned
        rw [PqxdhRecordConfidentialityChallenge.challenge_step owner number bit left right equal before.1 unused] at returned
        simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at returned
        obtain ⟨⟨reply, after⟩, sent, rfl⟩ := returned
        simp only [PqxdhLaterChallengeMonitorSource.record, unused, Option.isSome_none, Bool.false_eq_true, equal, ne_eq, not_true_eq_false, or_self, ite_false] at later
        have tail := PqxdhRecordConfidentialityTrace.run_trace impl owner number bit (next reply) _ after _
          (original_supported impl selected owner number bit (next reply) _ result later)
        have kept := tail.kept.1 (by rfl)
        obtain ⟨record, returned, sequence⟩ := accepted.2.1
        rw [kept.2] at returned
        have same : reply = some record := Option.some.inj returned
        subst reply
        exact ⟨left, right, next, before.1, before.2, after, record, .here _ (before, none),
          unused, equal, tail.kept.2 accepted.2.2, sent, later, sequence,
          recorded_support impl selected owner number bit (next (some record)) _ _ result later⟩
      case neg =>
        simp only [annotated, original, StateT.run, PqxdhRecordConfidentialityChallenge.handler, equal, ne_eq, not_false_eq_true, or_true, ite_true, simulateQ_pure, PqxdhLaterChallengeMonitorSource.record] at actual
        change step ∈ support ((fun result => (result.1.1, ((result.1.2, result.2), none))) <$> (pure ((none, before.1), before.2) : ProbComp _)) at actual
        simp only [map_pure, mem_support_pure_iff] at actual
        subst step
        exact extend rfl (ih none before result later unused accepted)
    case inl =>
      simp only [annotated, original, StateT.run, PqxdhRecordConfidentialityChallenge.handler, bind_pure_comp, simulateQ_map, simulateQ_spec_query, Functor.map_map, support_map, Set.mem_image, PqxdhLaterChallengeMonitorSource.record] at actual
      obtain ⟨head, returned, rfl⟩ := actual
      change head ∈ support (((fun value => (PqxdhRecordConfidentialityChallenge.screen before.1 request value,
        PqxdhRecordConfidentialityChallenge.observe owner number before.1 request value)) <$> impl request).run before.2) at returned
      rw [StateT.run_map, support_map] at returned
      obtain ⟨⟨reply, after⟩, _, rfl⟩ := returned
      exact extend rfl (ih _ _ result later unused accepted)
  case pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    simp only [PqxdhRecordConfidentialityChallenge.Target, unused, Option.isSome_none, Bool.false_eq_true, false_and] at accepted

/-- Specializing the predicate to the compiled role view is literally the maintained executable annotation; this generalization adds no new source operation. -/
theorem annotated_view {M P I D K A N C : Type}
    (view : Native → InsState M P I D K A N C S B) (target : RootOutput) :
    annotated impl (fun state => PqxdhLaterChallengeMonitor.Selected target owner (view state)) owner number bit =
      PqxdhLaterChallengeSourceMonitor.annotated impl view target owner number bit := by
  rfl

end BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedTrace

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedTrace.Reaches.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedTrace.Reaches.source

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedTrace.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedTrace.program_source

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedTrace.program_nested' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedTrace.program_nested

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedTrace.recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedTrace.recorded

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedTrace.original_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedTrace.original_supported

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedTrace.recorded_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedTrace.recorded_support

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedTrace.origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedTrace.origin

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedTrace.annotated_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedTrace.annotated_view
