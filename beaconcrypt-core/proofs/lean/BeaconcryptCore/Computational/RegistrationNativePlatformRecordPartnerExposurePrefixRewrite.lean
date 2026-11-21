-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackPrefix
/-! Rewriting the exact callbacks at the supported original prefixes preserves the full adaptive result and state. This transports source-derived readiness into the checked material dictionary without changing any original trace or failed callback outcome. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePrefixRewrite
open RegistrationNativePlatformOriginCallbackCut (Prefix)
variable {Q S A : Type} {spec : OracleSpec Q}

/-- Only actually reached original callback states are required when replacing the same adaptive source dictionary. -/
theorem run (original changed : QueryImpl spec (StateT S ProbComp)) (work : OracleComp spec A) (before : S)
    (compatible : ∀query next current,Prefix original work before ((spec.query query : OracleComp spec (spec.Range query)) >>=next) current →
      (original query).run current=(changed query).run current) :
    (simulateQ original work).run before=(simulateQ changed work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value=>simp only [simulateQ_pure,StateT.run_pure]
  | query_bind query next ih=>
    have head := compatible query next before .initial
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    rw [←head]
    apply OracleComp.bind_congr_of_forall_mem_support
    intro reached called
    apply ih reached.1 reached.2
    intro later tail current path
    exact compatible later tail current (Prefix.trans original (.step .initial called) path)


/-- Source-derived local query projection at every reached original prefix lifts to the full adaptive execution, retaining the original result. -/
theorem map_run {T : Type} (original : QueryImpl spec (StateT S ProbComp))
    (changed : QueryImpl spec (StateT T ProbComp)) (project : S →T) (invariant : S →Prop)
    (work : OracleComp spec A) (before : S) (held : invariant before)
    (compatible : ∀query next current,Prefix original work before ((spec.query query : OracleComp spec (spec.Range query)) >>=next) current →
      invariant current → Prod.map id project <$> (original query).run current=(changed query).run (project current))
    (keeps : ∀query next current result,Prefix original work before ((spec.query query : OracleComp spec (spec.Range query)) >>=next) current →
      invariant current → result∈support ((original query).run current) → invariant result.2) :
    Prod.map id project <$> (simulateQ original work).run before=(simulateQ changed work).run (project before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value=>simp only [simulateQ_pure,StateT.run_pure,map_pure,Prod.map_apply,id_eq]
  | query_bind query next ih=>
    have head := compatible query next before .initial held
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
    rw [←head,bind_map_left]
    apply OracleComp.bind_congr_of_forall_mem_support
    intro reached called
    apply ih reached.1 reached.2 (keeps query next before reached .initial held called)
    · intro later tail current path valid
      exact compatible later tail current (Prefix.trans original (.step .initial called) path) valid
    · intro later tail current result path valid member
      exact keeps later tail current result (Prefix.trans original (.step .initial called) path) valid member

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePrefixRewrite
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePrefixRewrite.run' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePrefixRewrite.run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePrefixRewrite.map_run' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePrefixRewrite.map_run
