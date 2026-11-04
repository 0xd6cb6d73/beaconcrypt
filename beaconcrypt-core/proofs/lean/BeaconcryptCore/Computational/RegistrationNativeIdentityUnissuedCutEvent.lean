-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutTrace
/-! Any event of the original packet and its own pre-accept state is transferred to a fixed public acceptance cutoff. The event may inspect private analysis state, while the stopping code uses only the public ordinal. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutEvent
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeStageTrace (Call)
open RegistrationNativeIdentityUnissuedAcceptCut (Cut stop resume)
open RegistrationNativeIdentityUnissuedCutTrace (count accepted)
variable {A S : Type}
abbrev Packet := beaconcrypt_core.registration.InitPacket
abbrev State (S : Type) := S × List (Call TypedSpec S)

def At (bad : Packet → S → Prop) (accept : Nat) (result : A × State S) : Prop :=
  ∃ packet before, (accepted result.2.2)[accept]? = some (packet,before) ∧ bad packet before

def AtCut (bad : Packet → S → Prop) (result : Cut A × State S) : Prop :=
  match result.1 with
  | .returned _ => False
  | .accept packet _ => bad packet result.2.1

noncomputable def coupled (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (accept : Nat) (work : OracleComp TypedSpec A) (before : S) : ProbComp ((Cut A × State S) × (A × State S)) := do
  let cut ← (simulateQ (RegistrationNativeStageTrace.handler implementation) (stop accept work 0)).run (before,[])
  let result ← (simulateQ (RegistrationNativeStageTrace.handler implementation) (resume cut.1)).run cut.2
  pure (cut,result)

/-- The selected entry in the original complete journal has precisely the same packet and pre-call state as its fixed public cutoff. -/
theorem contains (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (accept : Nat) (work : OracleComp TypedSpec A) (before : S) (bad : Packet → S → Prop)
    (cut : Cut A × State S)
    (reached : cut ∈ support ((simulateQ (RegistrationNativeStageTrace.handler implementation) (stop accept work 0)).run (before,[])))
    (result : A × State S)
    (continued : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler implementation) (resume cut.1)).run cut.2))
    (failed : At bad accept result) : AtCut bad cut := by
  have ordinal := RegistrationNativeIdentityUnissuedCutTrace.prefix_status implementation accept work before cut reached
  rcases cut with ⟨cut,initial,calls⟩
  cases cut with
  | returned value =>
      simp only [resume,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at continued
      cases continued
      obtain ⟨packet,previous,selected,_bad⟩ := failed
      have length : (accepted calls).length ≤ accept := by
        rw [RegistrationNativeIdentityUnissuedCutTrace.accepted_length]
        exact ordinal
      rw [List.getElem?_eq_none (by omega)] at selected
      cases selected
  | accept packet next =>
      have selected := RegistrationNativeIdentityUnissuedCutTrace.resumed_at implementation packet next initial calls accept ordinal result continued
      obtain ⟨other,previous,found,badAt⟩ := failed
      have same := Option.some.inj (selected.symm.trans found)
      cases same
      exact badAt

/-- Forgetting the private fixed-cut receipt restores the complete original execution and journal exactly. -/
theorem full_marginal (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (accept : Nat) (work : OracleComp TypedSpec A) (before : S) :
    Prod.snd <$> coupled implementation accept work before =
      (simulateQ (RegistrationNativeStageTrace.handler implementation) work).run (before,[]) := by
  simp only [coupled,map_bind,map_pure,bind_pure]
  exact (RegistrationNativeIdentityUnissuedAcceptCut.execution accept 0
    (RegistrationNativeStageTrace.handler implementation) work (before,[])).symm

/-- The receipt retained at the public cutoff has the exact prefix distribution, even while every original later callback runs. -/
theorem prefix_marginal (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (accept : Nat) (work : OracleComp TypedSpec A) (before : S) :
    Prod.fst <$> coupled implementation accept work before =ᵈ
      (simulateQ (RegistrationNativeStageTrace.handler implementation) (stop accept work 0)).run (before,[]) := by
  have law := EvalDistEq.bind_right
    ((simulateQ (RegistrationNativeStageTrace.handler implementation) (stop accept work 0)).run (before,[]))
    (fun cut => EvalDistEq.bind_const
      ((simulateQ (RegistrationNativeStageTrace.handler implementation) (resume cut.1)).run cut.2) (pure cut))
  simpa only [coupled,map_bind,map_pure,bind_pure] using law

/-- Every private event of the original selected packet and its own earlier state is bounded by the same fixed public cutoff event, with no private stopping monitor. -/
theorem bound (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (accept : Nat) (work : OracleComp TypedSpec A) (before : S) (bad : Packet → S → Prop) :
    Pr{let result ← ((simulateQ (RegistrationNativeStageTrace.handler implementation) work).run (before,[]))}[At bad accept result] ≤
      Pr{let cut ← ((simulateQ (RegistrationNativeStageTrace.handler implementation) (stop accept work 0)).run (before,[]))}[AtCut bad cut] := by
  rw [←full_marginal implementation accept work before,prEvent_map]
  calc
    Pr{let result ← coupled implementation accept work before}[At bad accept result.2] ≤
        Pr{let result ← coupled implementation accept work before}[AtCut bad result.1] := by
      apply prEvent_mono_of_support
      intro result supported failed
      simp only [coupled,mem_support_bind_iff,mem_support_pure_iff] at supported
      obtain ⟨cut,reached,final,continued,rfl⟩ := supported
      exact contains implementation accept work before bad cut reached final continued failed
    _ = _ := by
      have equal := (prefix_marginal implementation accept work before).prEvent_eq (AtCut bad)
      simpa only [prEvent_map] using equal

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutEvent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutEvent.contains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutEvent.contains

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutEvent.full_marginal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutEvent.full_marginal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutEvent.prefix_marginal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutEvent.prefix_marginal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutEvent.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutEvent.bound
