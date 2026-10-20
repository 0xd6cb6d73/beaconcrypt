import BeaconcryptCore.Computational.RawCtxFlaggedQueryTrace
import BeaconcryptCore.Computational.StatefulGoodEvent

/-!
Masking a query-derived disclosure preserves the unconditioned final good event when its original complete callback is unchanged outside that disclosure. Both candidate history and disclosure history remain in the same result. The callback equation is an operational premise discharged by the actual optional-read implementation; it is not a security premise or a bound on disclosure probability.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxFlaggedQueryAgreement
open PqxdhSecretInputKdf RawCtxFlaggedQueryTrace

/-- Each supported callback retains the original flag or marks the current disclosure, independently of its actual reply. -/
theorem flag_step {ι State : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT State ProbComp)) (record : spec.Domain → List RootOutput)
    (direct : spec.Domain → Bool) (query : spec.Domain) (state : (State × List RootOutput) × Bool)
    (result : spec.Range query × ((State × List RootOutput) × Bool))
    (supported : result ∈ support ((trace handler record direct query).run state)) :
    result.2.2 = (state.2 || direct query) := by
  simp only [trace, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨_, _, rfl⟩ := supported
  rfl

/-- The original disclosure flag is sticky for every supported callback result. -/
theorem sticky {ι State : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT State ProbComp)) (record : spec.Domain → List RootOutput)
    (direct : spec.Domain → Bool) (query : spec.Domain) (state : (State × List RootOutput) × Bool)
    (bad : state.2 = true) (result : spec.Range query × ((State × List RootOutput) × Bool))
    (supported : result ∈ support ((trace handler record direct query).run state)) : result.2.2 = true := by
  simpa only [bad, Bool.true_or] using flag_step handler record direct query state result supported

/-- Complete good transitions agree when the original callbacks agree outside the explicitly marked query. -/
theorem agree_good {ι State : Type} {spec : OracleSpec ι}
    (left right : QueryImpl spec (StateT State ProbComp)) (record : spec.Domain → List RootOutput)
    (direct : spec.Domain → Bool)
    (safe : ∀ query, direct query = false → left query = right query)
    (query : spec.Domain) (state : State × List RootOutput) (reply : spec.Range query) (next : State × List RootOutput) :
    Pr[= (reply, (next, false)) | (trace left record direct query).run (state, false)] =
      Pr[= (reply, (next, false)) | (trace right record direct query).run (state, false)] := by
  by_cases hit : direct query = true
  · have zero (handler : QueryImpl spec (StateT State ProbComp)) :
        Pr[= (reply, (next, false)) | (trace handler record direct query).run (state, false)] = 0 := by
      apply probOutput_eq_zero_of_not_mem_support
      exact fun supported => Bool.false_ne_true (by simpa only [hit, Bool.or_true] using
        (flag_step handler record direct query (state, false) (reply, (next, false)) supported))
    rw [zero, zero]
  · simp only [trace, StateT.run, safe query (by simpa using hit)]

/-- The same full adaptive event restricted to the original good flag has exactly the same unconditioned probability, including prior exposure. -/
theorem event_good {ι State Result : Type} {spec : OracleSpec ι}
    (left right : QueryImpl spec (StateT State ProbComp)) (record : spec.Domain → List RootOutput)
    (direct : spec.Domain → Bool)
    (safe : ∀ query, direct query = false → left query = right query)
    (client : OracleComp spec Result) (state : (State × List RootOutput) × Bool)
    (event : Result × ((State × List RootOutput) × Bool) → Prop) :
    Pr[fun result => event result ∧ result.2.2 = false | (simulateQ (trace left record direct) client).run state] =
      Pr[fun result => event result ∧ result.2.2 = false | (simulateQ (trace right record direct) client).run state] := by
  exact StatefulGoodEvent.event_good_vcvioLegacy _ _ (agree_good left right record direct safe)
    (sticky left record direct) (sticky right record direct) client state event

end BeaconcryptCore.Computational.RawCtxFlaggedQueryAgreement

/-- info: 'BeaconcryptCore.Computational.RawCtxFlaggedQueryAgreement.flag_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFlaggedQueryAgreement.flag_step
/-- info: 'BeaconcryptCore.Computational.RawCtxFlaggedQueryAgreement.sticky' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFlaggedQueryAgreement.sticky
/-- info: 'BeaconcryptCore.Computational.RawCtxFlaggedQueryAgreement.agree_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFlaggedQueryAgreement.agree_good
/-- info: 'BeaconcryptCore.Computational.RawCtxFlaggedQueryAgreement.event_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFlaggedQueryAgreement.event_good
