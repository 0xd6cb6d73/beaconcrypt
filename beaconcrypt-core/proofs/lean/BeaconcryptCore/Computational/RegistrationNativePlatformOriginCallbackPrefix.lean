-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackCut
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackCut
variable {Q S A : Type} {spec : OracleSpec Q}
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p
/-- The stopped callback is reached through actual unchanged earlier callback replies. -/
inductive Prefix (implementation : QueryImpl spec (StateT S ProbComp)) (initial : OracleComp spec A) (start : S) :
    OracleComp spec A → S → Prop
  | initial : Prefix implementation initial start initial start
  | step {query : spec.Domain} {next : spec.Range query → OracleComp spec A} {state : S}
      {reply : spec.Range query × S}
      (before : Prefix implementation initial start (spec.query query >>=next) state)
      (called : reply∈support ((implementation query).run state)) :
      Prefix implementation initial start (next reply.1) reply.2

theorem Prefix.trans (implementation : QueryImpl spec (StateT S ProbComp))
    {initial middle rest : OracleComp spec A} {start between finish : S}
    (first : Prefix implementation initial start middle between)
    (later : Prefix implementation middle between rest finish) : Prefix implementation initial start rest finish := by
  induction later with
  | initial=>exact first
  | step before called ih=>exact .step ih called

/-- Prefix support is derived before the selected callback reply, and includes unsuccessful earlier calls. -/
theorem scan_prefix (counted : spec.Domain → Prop) (implementation : QueryImpl spec (StateT S ProbComp))
    (work : OracleComp spec A) (index : Nat) (state : S) (cut : Cut spec S A)
    (supported : Sum.inr cut∈support (scan counted implementation work index state)) :
    Prefix implementation work state (spec.query cut.query >>=cut.next) cut.state ∧counted cut.query := by
  classical
  induction work using OracleComp.inductionOn generalizing index state cut with
  | pure value=>
    change Sum.inr cut∈support (pure (.inl (value,state)) :ProbComp _) at supported
    simp only [mem_support_pure_iff] at supported
    cases supported
  | query_bind query next ih=>
    rw [scan_query] at supported
    split at supported
    · rename_i hit
      cases index with
      | zero=>
        simp only [mem_support_pure_iff] at supported
        cases supported
        exact ⟨.initial,hit⟩
      | succ index=>
        simp only [mem_support_bind_iff] at supported
        obtain ⟨reply,called,later⟩ :=supported
        obtain ⟨prefixPath,chosen⟩ := ih reply.1 index reply.2 cut later
        exact ⟨Prefix.trans implementation (.step .initial called) prefixPath,chosen⟩
    · simp only [mem_support_bind_iff] at supported
      obtain ⟨reply,called,later⟩ :=supported
      obtain ⟨prefixPath,chosen⟩ := ih reply.1 index reply.2 cut later
      exact ⟨Prefix.trans implementation (.step .initial called) prefixPath,chosen⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackCut.Prefix.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackCut.Prefix.trans

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackCut.scan_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackCut.scan_prefix
