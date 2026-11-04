-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleBoundaryPair
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorCanonicalJournal
/-! A complete same-run bundle suffix retains its literal first reply and full poststate jointly with the public before-accept journal observation. Only unused later execution is integrated out by losslessness. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleRetainedJournal
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeStageTrace (Call)
open RegistrationNativeIdentityCensorVisitorJournal (full fold visit)
variable {S A : Type}
private theorem prepend (implementation : QueryImpl TypedSpec (StateT S ProbComp)) (work : OracleComp TypedSpec A)
    (before : S) (leading : List (Call TypedSpec S)) :
    (fun result => (result.1,(result.2.1,leading++result.2.2))) <$> full implementation work before =
      (simulateQ (RegistrationNativeStageTrace.handler implementation) work).run (before,leading) := by
  have law := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (RegistrationNativeStageTrace.handler implementation) (RegistrationNativeStageTrace.handler implementation)
    (fun current => (current.1,leading++current.2)) (fun query current => by
      simp only [RegistrationNativeStageTrace.handler,StateT.run,Functor.map_map,Prod.map_def,id_eq,List.append_assoc]) work (before,[])
  simpa only [full,List.append_nil,Prod.map_def,id_eq] using law

theorem full_step (implementation : QueryImpl TypedSpec (StateT S ProbComp)) (query : TypedSpec.Domain)
    (next : TypedSpec.Range query → OracleComp TypedSpec A) (before : S) :
    full implementation (TypedSpec.query query >>= next) before = (do
      let reached ← (implementation query).run before
      let result ← full implementation (next reached.1) reached.2
      pure (result.1,(result.2.1,(⟨query,before,reached.1,reached.2⟩ : Call TypedSpec S)::result.2.2))) := by
  unfold full
  rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
  simp only [RegistrationNativeStageTrace.handler,StateT.run,bind_map_left,List.nil_append]
  apply bind_congr
  intro reached
  have law := (prepend implementation (next reached.1) reached.2 [⟨query,before,reached.1,reached.2⟩]).symm
  simpa only [full,StateT.run,map_eq_bind_pure_comp,Function.comp_def,List.singleton_append] using law


noncomputable def complete (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (index : Nat) (next : TypedSpec.Range (.inr (.bundle index)) → OracleComp TypedSpec A) (before : S) := do
  let kept ← (implementation (.inr (.bundle index))).run before
  let final ← full implementation (next kept.1) kept.2
  pure (kept,final)

def observe (target : S → Option Pqxdh.Bytes)
    (published : (query : TypedSpec.Domain) → TypedSpec.Range query → S → Bool)
    (accept cursor index : Nat)
    (result : (TypedSpec.Range (.inr (.bundle index)) × S) × (A × (S × List (Call TypedSpec S)))) :=
  if published (.inr (.bundle index)) result.1.1 result.1.2 then none else
    some (result.1,fold target published accept cursor result.2.2.2)

noncomputable def retained (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (target : S → Option Pqxdh.Bytes)
    (published : (query : TypedSpec.Domain) → TypedSpec.Range query → S → Bool)
    (accept cursor index : Nat) (next : TypedSpec.Range (.inr (.bundle index)) → OracleComp TypedSpec A) (before : S) := do
  let kept ← (implementation (.inr (.bundle index))).run before
  if published (.inr (.bundle index)) kept.1 kept.2 then pure none else
    (fun found=>some (kept,found)) <$> visit implementation target published accept (next kept.1) kept.2 cursor

/-- The full same-run first bundle and its later journal fold have precisely the retained stopped-observation distribution. -/
theorem source (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (target : S → Option Pqxdh.Bytes)
    (published : (query : TypedSpec.Domain) → TypedSpec.Range query → S → Bool)
    (accept cursor index : Nat) (next : TypedSpec.Range (.inr (.bundle index)) → OracleComp TypedSpec A) (before : S) :
    observe target published accept cursor index <$>complete implementation index next before =ᵈ
      retained implementation target published accept cursor index next before := by
  unfold complete retained
  simp only [map_bind,bind_pure_comp]
  apply EvalDistEq.bind_right
  intro kept
  simp only [Functor.map_map]
  change (fun final=>if published (.inr (.bundle index)) kept.1 kept.2 then none else some (kept,fold target published accept cursor final.2.2)) <$>
    full implementation (next kept.1) kept.2 =ᵈ
      (if published (.inr (.bundle index)) kept.1 kept.2 then pure none else
        (fun found=>some (kept,found)) <$>visit implementation target published accept (next kept.1) kept.2 cursor)
  cases stopped : published (.inr (.bundle index)) kept.1 kept.2 with
  | true=>
    simp only [ite_true]
    exact EvalDistEq.map_const _ none
  | false=>
    simp only [Bool.false_eq_true,ite_false]
    have law := RegistrationNativeIdentityCensorVisitorJournal.source implementation target published accept (next kept.1) kept.2 cursor
    have mapped := law.map (fun found=>some (kept,found))
    simpa only [Functor.map_map] using mapped

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleRetainedJournal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleRetainedJournal.full_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleRetainedJournal.full_step
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleRetainedJournal.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleRetainedJournal.source
