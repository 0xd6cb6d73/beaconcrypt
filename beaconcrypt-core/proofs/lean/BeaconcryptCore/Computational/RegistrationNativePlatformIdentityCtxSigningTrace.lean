-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningLog
/-! Public all-attempt bundle markers wrap the literal typed callback tree. Analysis logging records the same indexed request/reply while the original source state, persistent P, primitive query order and callback replies survive exact erasure. The marker is independent of private acceptance events. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningTrace
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxSigningLog (Trace Receipt Valid logging)
open RegistrationNativePlatformIdentityCtxSignScope (Allowed)
variable {S A : Type}

def IsBundle : TypedSpec.Domain → Prop
  | .inr (.bundle _) => True
  | _ => False
instance : DecidablePred IsBundle := fun query => by
  unfold IsBundle
  split <;> infer_instance

def mark (query : TypedSpec.Domain) (before : Trace) : Option Nat × Trace :=
  if IsBundle query then (some before.nextBundle, { before with nextBundle := before.nextBundle + 1 })
  else (none, before)

def wrap (handler : QueryImpl TypedSpec (StateT S (OracleComp Spec))) :
    QueryImpl TypedSpec (StateT (S × Trace) (OracleComp Spec)) := fun query before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (logging (mark query before.2).1) ((handler query).run before.1)).run (mark query before.2).2

private theorem wrap_run (handler : QueryImpl TypedSpec (StateT S (OracleComp Spec))) (query : TypedSpec.Domain)
    (before : S × Trace) : (wrap handler query).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (logging (mark query before.2).1) ((handler query).run before.1)).run (mark query before.2).2 := rfl

/-- Removing the analysis counter/log restores the complete literal source callback state and exact reply. -/
theorem query_erasure (handler : QueryImpl TypedSpec (StateT S (OracleComp Spec))) (query : TypedSpec.Domain) (before : S × Trace) :
    Prod.map id Prod.fst <$> (wrap handler query).run before = (handler query).run before.1 := by
  simpa only [wrap_run, Functor.map_map, Prod.map_def, id_eq] using
    RegistrationNativePlatformIdentityCtxSigningLog.erase (mark query before.2).1 ((handler query).run before.1) (mark query before.2).2

/-- Erasure retains every original adaptive reply and full source/P poststate through all later callbacks. -/
theorem program_erasure (handler : QueryImpl TypedSpec (StateT S (OracleComp Spec)))
    (work : OracleComp TypedSpec A) (before : S × Trace) :
    Prod.map id Prod.fst <$> (simulateQ (wrap handler) work).run before = (simulateQ handler work).run before.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst (query_erasure handler) work before

private theorem mark_next (query : TypedSpec.Domain) (before : Trace) :
    (mark query before).2.nextBundle = before.nextBundle + if IsBundle query then 1 else 0 := by
  by_cases selected : IsBundle query
  · simp only [mark, selected, ite_true]
  · simp only [mark, selected, ite_false, Nat.add_zero]

/-- Every attempted public bundle debits exactly once before its callback, including invalid handles and failed writers. -/
theorem query_counter (handler : QueryImpl TypedSpec (StateT S (OracleComp Spec))) (query : TypedSpec.Domain)
    (before : S × Trace) (result : TypedSpec.Range query × (S × Trace))
    (supported : result ∈ support ((wrap handler query).run before)) :
    result.2.2.nextBundle = before.2.nextBundle + if IsBundle query then 1 else 0 := by
  rw [wrap_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact (RegistrationNativePlatformIdentityCtxSigningLog.next_unchanged _ _ _ inner reached).trans (mark_next query before.2)

private theorem mark_valid (query : TypedSpec.Domain) (before : Trace) (valid : Valid before) : Valid (mark query before).2 := by
  by_cases selected : IsBundle query
  · simp only [mark, selected, ite_true]
    intro receipt member
    obtain ⟨ordinal, tagged, bounded⟩ := valid receipt member
    exact ⟨ordinal, tagged, Nat.lt_trans bounded (Nat.lt_succ_self _)⟩
  · simpa only [mark, selected, ite_false] using valid

private theorem query_valid (handler : QueryImpl TypedSpec (StateT S (OracleComp Spec))) (query : TypedSpec.Domain)
    (before : S × Trace) (result : TypedSpec.Range query × (S × Trace))
    (valid : Valid before.2) (quiet : ¬ IsBundle query → ((handler query).run before.1).AllQueriesSatisfy Allowed)
    (supported : result ∈ support ((wrap handler query).run before)) : Valid result.2.2 := by
  rw [wrap_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  by_cases selected : IsBundle query
  · exact RegistrationNativePlatformIdentityCtxSigningLog.valid _ _ _ inner (mark_valid query before.2 valid)
      ⟨before.2.nextBundle, by simp only [mark, selected, ite_true], by simp only [mark, selected, ite_true]; omega⟩ reached
  · rw [RegistrationNativePlatformIdentityCtxSigningLog.no_sign _ _ (quiet selected), support_map] at reached
    obtain ⟨returned, _source, same⟩ := reached
    cases same
    exact mark_valid query before.2 valid

/-- The public typed bundle budget bounds the actual marker counter; source primitive loops do not consume extra callback ordinals. -/
theorem counter_budget (handler : QueryImpl TypedSpec (StateT S (OracleComp Spec)))
    (work : OracleComp TypedSpec A) (budget : Nat) (bounded : work.IsQueryBoundP IsBundle budget)
    (before : S × Trace) (result : A × (S × Trace))
    (supported : result ∈ support ((simulateQ (wrap handler) work).run before)) :
    result.2.2.nextBundle ≤ before.2.nextBundle + budget := by
  induction work using OracleComp.inductionOn generalizing budget before result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    exact Nat.le_add_right _ _
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, first, last⟩ := supported
    have step := query_counter handler query before middle first
    have later := ih middle.1 _ (bounded.2 middle.1) middle.2 result last
    rw [step] at later
    by_cases selected : IsBundle query
    · have positive := bounded.1.resolve_left (fun impossible => impossible selected)
      simp only [selected, ite_true] at later
      omega
    · simp only [selected, ite_false, Nat.add_zero] at later
      exact later
/-- The actual private identity/hash interpreter retains its entire source pool, cache, journal and counted replies after only analysis-log erasure. -/
theorem source_erasure (joint : PqxdhJointIdentity.Primitives)
    (handler : QueryImpl TypedSpec (StateT S (OracleComp Spec))) (work : OracleComp TypedSpec A)
    (before : S × Trace) (privateBefore : RegistrationNativePlatformIdentityCtxSource.State) :
    Prod.map (Prod.map id Prod.fst) id <$>
      (simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation joint)
        ((simulateQ (wrap handler) work).run before)).run privateBefore =
      (simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation joint)
        ((simulateQ handler work).run before.1)).run privateBefore := by
  have equation := congrArg (fun tree => (simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation joint) tree).run privateBefore)
    (program_erasure handler work before)
  simpa only [simulateQ_map, StateT.run_map, Prod.map_def, id_eq] using equation

section Actual
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "actual" => RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation created credential
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "SourceState" => RegistrationNativeIdentityMain.State n KemSK source × Platform

/-- The literal corrected typed source handler supplies the non-bundle restriction, so every reached signing receipt has a genuine public bundle ordinal. -/
theorem handler_valid (query : TypedSpec.Domain) (before : SourceState × Trace)
    (result : TypedSpec.Range query × (SourceState × Trace)) (prior : Valid before.2)
    (supported : result ∈ support ((wrap actual query).run before)) : Valid result.2.2 := by
  apply query_valid actual query before result prior ?_ supported
  intro noBundle
  apply RegistrationNativePlatformIdentityCtxSignScope.handler_safe setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer query ?_ before.1
  intro index same
  apply noBundle
  cases same
  exact True.intro

/-- Every later source callback executes and every actual receipt retains a valid public all-attempt ordinal. -/
theorem program_valid (work : OracleComp TypedSpec A) (before : SourceState × Trace)
    (result : A × (SourceState × Trace)) (prior : Valid before.2)
    (supported : result ∈ support ((simulateQ (wrap actual) work).run before)) : Valid result.2.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    exact prior
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, called, continued⟩ := supported
    exact ih middle.1 middle.2 result (handler_valid setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query before middle prior called) continued

/-- From the empty analysis trace, every actual successful OR failed signing request has an ordinal below the original public typed bundle allowance. -/
theorem receipt_budget (work : OracleComp TypedSpec A) (budget : Nat) (bounded : work.IsQueryBoundP IsBundle budget)
    (before : SourceState) (result : A × (SourceState × Trace))
    (supported : result ∈ support ((simulateQ (wrap actual) work).run (before, {})))
    (receipt : Receipt) (member : receipt ∈ result.2.2.log) :
    ∃ ordinal, receipt.bundle = some ordinal ∧ ordinal < budget := by
  have initial : Valid ({} : Trace) := by
    intro entry impossible
    cases impossible
  have retained := program_valid setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer work (before, {}) result initial supported
  obtain ⟨ordinal, tagged, less⟩ := retained receipt member
  have total := counter_budget actual work budget bounded (before, {}) result supported
  refine ⟨ordinal, tagged, Nat.lt_of_lt_of_le less ?_⟩
  simpa only [Nat.zero_add] using total

/-- The same ordinal bound holds on every reached outcome of the actual private source backend, retaining all private and P coordinates. -/
theorem source_receipt_budget (work : OracleComp TypedSpec A) (budget : Nat) (bounded : work.IsQueryBoundP IsBundle budget)
    (before : SourceState) (privateBefore : RegistrationNativePlatformIdentityCtxSource.State)
    (result : (A × (SourceState × Trace)) × RegistrationNativePlatformIdentityCtxSource.State)
    (supported : result ∈ support ((simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation setup.joint)
      ((simulateQ (wrap actual) work).run (before, {}))).run privateBefore))
    (receipt : Receipt) (member : receipt ∈ result.1.2.2.log) :
    ∃ ordinal, receipt.bundle = some ordinal ∧ ordinal < budget := by
  apply receipt_budget setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer work budget bounded before result.1 ?_ receipt member
  apply support_simulateQ_run'_subset (RegistrationNativePlatformIdentityCtxSource.implementation setup.joint) _ privateBefore
  rw [StateT.run'_eq, support_map]
  exact ⟨result, supported, rfl⟩
end Actual
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningTrace.query_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningTrace.query_erasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningTrace.program_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningTrace.program_erasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningTrace.query_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningTrace.query_counter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningTrace.counter_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningTrace.counter_budget

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningTrace.source_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningTrace.source_erasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningTrace.handler_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningTrace.handler_valid

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningTrace.program_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningTrace.program_valid

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningTrace.receipt_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningTrace.receipt_budget

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningTrace.source_receipt_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningTrace.source_receipt_budget
