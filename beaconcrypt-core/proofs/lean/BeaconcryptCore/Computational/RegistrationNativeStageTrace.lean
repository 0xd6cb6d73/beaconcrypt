-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeServerIssuance
import BeaconcryptCore.Computational.PqxdhRecordLiftFlat

/-! A private source journal retains complete pre/post callback states in one execution. Its exact erasure leaves original adaptive source semantics unchanged. The chronological path witnesses each callback at its actual earlier leading; this journal is mathematical analysis state and is never an adversary interface. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeStageTrace
variable {Query S V : Type} {spec : OracleSpec Query}

structure Call (spec : OracleSpec Query) (S : Type) where
  query : spec.Domain
  before : S
  reply : spec.Range query
  after : S

def Executed (implementation : QueryImpl spec (StateT S ProbComp)) (call : Call spec S) : Prop :=
  (call.reply, call.after) ∈ support ((implementation call.query).run call.before)

inductive Path (implementation : QueryImpl spec (StateT S ProbComp)) : S → List (Call spec S) → S → Prop where
  | nil (state : S) : Path implementation state [] state
  | cons (call : Call spec S) (called : Executed implementation call) (rest : List (Call spec S)) (last : S)
      (following : Path implementation call.after rest last) : Path implementation call.before (call :: rest) last

/-- Source paths compose with their actual intermediate complete state. -/
theorem Path.append {implementation : QueryImpl spec (StateT S ProbComp)} {first middle last : S}
    {leading trailing : List (Call spec S)} (before : Path implementation first leading middle)
    (after : Path implementation middle trailing last) : Path implementation first (leading ++ trailing) last := by
  induction before with
  | nil => exact after
  | cons call called rest last following ih => exact .cons call called _ _ (ih after)

noncomputable def handler (implementation : QueryImpl spec (StateT S ProbComp)) :
    QueryImpl spec (StateT (S × List (Call spec S)) ProbComp) := fun query before =>
  (fun result => (result.1, (result.2, before.2 ++ [⟨query, before.1, result.1, result.2⟩]))) <$>
    (implementation query).run before.1

/-- Erasing only the journal retains the complete original adaptive source execution and every private state coordinate. -/
theorem erase (implementation : QueryImpl spec (StateT S ProbComp)) (work : OracleComp spec V)
    (before : S × List (Call spec S)) :
    Prod.map id Prod.fst <$> (simulateQ (handler implementation) work).run before = (simulateQ implementation work).run before.1 := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query current
  simp only [handler, StateT.run, Functor.map_map, Prod.map, id_eq]
  exact id_map _

private theorem step_path (implementation : QueryImpl spec (StateT S ProbComp)) (initial : S)
    (query : spec.Domain) (before : S × List (Call spec S)) (prior : Path implementation initial before.2 before.1)
    (result : spec.Range query × (S × List (Call spec S)))
    (supported : result ∈ support ((handler implementation query).run before)) : Path implementation initial result.2.2 result.2.1 := by
  simp only [handler, StateT.run, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  cases same
  exact prior.append (.cons ⟨query, before.1, inner.1, inner.2⟩ called [] inner.2 (.nil inner.2))

/-- Every supported complete journal execution derives its exact chronological source path. -/
theorem path (implementation : QueryImpl spec (StateT S ProbComp)) (work : OracleComp spec V) (before : S)
    (result : V × (S × List (Call spec S)))
    (supported : result ∈ support ((simulateQ (handler implementation) work).run (before, []))) :
    Path implementation before result.2.2 result.2.1 :=
  PqxdhRecordLiftFlat.support_keep_oracle (handler implementation)
    (fun current => Path implementation before current.2 current.1)
    (step_path implementation before) work (before, []) (.nil before) result supported

/-- Every retained journal member has its actual earlier source leading, supported callback and actual later trailing in that same execution. -/
theorem Path.member {implementation : QueryImpl spec (StateT S ProbComp)} {first last : S} {calls : List (Call spec S)}
    (actual : Path implementation first calls last) (call : Call spec S) (member : call ∈ calls) :
    ∃ leading trailing, calls = leading ++ call :: trailing ∧ Path implementation first leading call.before ∧
      Executed implementation call ∧ Path implementation call.after trailing last := by
  induction actual with
  | nil => cases member
  | cons head called rest last following ih =>
      rcases List.mem_cons.mp member with same | later
      · subst call
        exact ⟨[], rest, rfl, .nil _, called, following⟩
      · obtain ⟨leading, trailing, split, before, middle, after⟩ := ih later
        exact ⟨head :: leading, trailing, by rw [split]; rfl, .cons head called _ _ before, middle, after⟩

end BeaconcryptCore.Computational.RegistrationNativeStageTrace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStageTrace.Path.append' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStageTrace.Path.append

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStageTrace.erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStageTrace.erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStageTrace.path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStageTrace.path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStageTrace.Path.member' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStageTrace.Path.member
