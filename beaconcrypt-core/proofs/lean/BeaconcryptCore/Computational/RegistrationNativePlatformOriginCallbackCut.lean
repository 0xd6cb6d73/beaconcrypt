-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeStageTrace
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackCut
variable {Q S A : Type} {spec : OracleSpec Q}
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p
structure Cut (spec : OracleSpec Q) (S A : Type) where
  query : spec.Domain
  next : spec.Range query → OracleComp spec A
  state : S
abbrev Outcome (spec : OracleSpec Q) (S A : Type) := (A × S) ⊕ Cut spec S A

noncomputable def scan (counted : spec.Domain → Prop) (implementation : QueryImpl spec (StateT S ProbComp))
    (work : OracleComp spec A) : Nat → S → ProbComp (Outcome spec S A) := by
  classical
  exact OracleComp.recOn work
    (fun value _ state=>pure (.inl (value,state)))
    (fun query next recurse index state=>
      if counted query then match index with
      | 0=>pure (.inr ⟨query,next,state⟩)
      | index+1=>do
        let reply←(implementation query).run state
        recurse reply.1 index reply.2
      else do
        let reply←(implementation query).run state
        recurse reply.1 index reply.2)

noncomputable def resume (implementation : QueryImpl spec (StateT S ProbComp)) : Outcome spec S A → ProbComp (A × S)
  | .inl result=>pure result
  | .inr cut=>do
    let reply←(implementation cut.query).run cut.state
    (simulateQ implementation (cut.next reply.1)).run reply.2

/-- Every counted callback attempt has its ordinal before the actual optional reply is sampled. -/
theorem scan_query (counted : spec.Domain → Prop) (implementation : QueryImpl spec (StateT S ProbComp))
    (query : spec.Domain) (next : spec.Range query → OracleComp spec A) (index : Nat) (state : S) :
    scan counted implementation (spec.query query >>=next) index state =
      if counted query then match index with
      | 0=>pure (.inr ⟨query,next,state⟩)
      | index+1=>(implementation query).run state >>=fun reply=>scan counted implementation (next reply.1) index reply.2
      else (implementation query).run state >>=fun reply=>scan counted implementation (next reply.1) index reply.2 := by
  classical
  rfl

/-- Resuming the suspended actual callback reconstructs the entire original adaptive execution, including early completion and all failed replies. -/
theorem scan_resume (counted : spec.Domain → Prop) (implementation : QueryImpl spec (StateT S ProbComp))
    (work : OracleComp spec A) (index : Nat) (state : S) :
    (scan counted implementation work index state >>=resume implementation)=(simulateQ implementation work).run state := by
  classical
  induction work using OracleComp.inductionOn generalizing index state with
  | pure value=>
    change (pure (.inl (value,state)) >>=resume implementation)=pure (value,state)
    rw [pure_bind]
    rfl
  | query_bind query next ih=>
    rw [scan_query]
    split
    · cases index with
      | zero=>simp only [pure_bind,resume,simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
      | succ index=>simp only [bind_assoc,ih,simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    · simp only [bind_assoc,ih,simulateQ_bind,simulateQ_spec_query,StateT.run_bind]

/-- The selected result retains the same literal current query/reply and complete source pre/post state beside its original final value. -/
noncomputable def markedResume (implementation : QueryImpl spec (StateT S ProbComp)) :
    Outcome spec S A → ProbComp (Option (RegistrationNativeStageTrace.Call spec S) × (A × S))
  | .inl result=>pure (none,result)
  | .inr cut=>do
    let reply←(implementation cut.query).run cut.state
    let result←(simulateQ implementation (cut.next reply.1)).run reply.2
    pure (some ⟨cut.query,cut.state,reply.1,reply.2⟩,result)

/-- Dropping only the current-callback certificate gives the same original continuation, with no change to any public or private reply. -/
theorem marked_erase (implementation : QueryImpl spec (StateT S ProbComp)) (outcome : Outcome spec S A) :
    Prod.snd <$>markedResume implementation outcome=resume implementation outcome := by
  cases outcome with
  | inl result=>simp only [markedResume,resume,map_pure]
  | inr cut=>simp only [markedResume,resume,map_bind,map_pure,bind_pure]
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackCut.scan_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackCut.scan_query


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackCut.scan_resume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackCut.scan_resume


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackCut.marked_erase' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackCut.marked_erase
