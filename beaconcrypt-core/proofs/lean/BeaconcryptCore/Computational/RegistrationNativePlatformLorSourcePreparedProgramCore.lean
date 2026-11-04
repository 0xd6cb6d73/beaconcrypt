-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedPrefix
/-! Supported callback decomposition transports an operational invariant to each literal query reached by a sequential source compiler. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedProgramCore
open RegistrationNativePlatformOriginCallbackCut (Prefix)
variable {I J Front Private Message A : Type} {spec : OracleSpec I} {word : OracleSpec J}
variable (implementation : QueryImpl word (StateT Private ProbComp))
    (controller : QueryImpl spec (StateT Front (OracleComp word)))
    (invariant : Front → Private → Prop) (prepared : Message → Private → Prop) (demand : Message → word.Domain)
variable (keeps : ∀ query front before value after,
    (value,after)∈support ((simulateQ implementation ((controller query).run front)).run before) →
    invariant front before →invariant value.2 after)
variable (localPrepared : ∀ query front before message tail after,
    invariant front before →
    Prefix implementation ((controller query).run front) before ((word.query (demand message)) >>=tail) after →
    prepared message after)
include keeps localPrepared in
/-- Literal source prefixes retain the actual states of completed callbacks before entering adaptive continuations. -/
theorem program (work : OracleComp spec A) (front : Front) (before : Private) (message : Message)
    (tail : word.Range (demand message) →OracleComp word (A × Front)) (after : Private)
    (held : invariant front before)
    (path : Prefix implementation ((simulateQ controller work).run front) before (word.query (demand message) >>=tail) after) :
    prepared message after := by
  induction work using OracleComp.inductionOn generalizing front before with
  | pure value=>
    simp only [simulateQ_pure,StateT.run_pure] at path
    exact (RegistrationNativePlatformLorSourcePreparedPrefix.query_allowed implementation (fun _=>False) _ (by trivial)
      before _ tail after path).elim
  | query_bind query next ih=>
    rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind] at path
    rcases RegistrationNativePlatformLorSourcePreparedPrefix.bind_query_cases implementation ((controller query).run front)
      (fun result=>(simulateQ controller (next result.1)).run result.2) before _ tail after path with during|completed
    · obtain ⟨firstTail,earlier⟩ := during
      exact localPrepared query front before message firstTail after held earlier
    · obtain ⟨value,middle,called,later⟩ := completed
      exact ih value.1 value.2 middle (keeps query front before value middle called held) later
end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedProgramCore
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedProgramCore.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedProgramCore.program
