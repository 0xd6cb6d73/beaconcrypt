-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClient
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureFirstHit
/-! Ordinary recovery closes the actual candidate-free physical client by retaining its complete cache and World state. Only product association changes in this execution correspondence. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientExecution
open RegistrationNativeSecretWord (Cache)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSuffixKeyPrf (Secret)
open RegistrationNativePlatformRecordPartnerExposureClient (Shared ambient)
variable {n : Nat} {Physical A : Type}
variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (candidate : Secret)
local notation "recovery"=>RegistrationNativeSecretWordRecoveryCompiler.closed source candidate

private theorem coin_query (query : unifSpec.Domain) (cache : Cache) :
    (recovery (.inl (.inl query))).run cache=(fun value=>(value,cache)) <$>
      (unifSpec.query query : ProbComp (unifSpec.Range query)) := by
  change ((unifSpec.query query : ProbComp (unifSpec.Range query)) >>=fun value=>pure (value,cache))=_
  exact bind_pure_comp _ _

/-- Actual ordinary recovery coins keep their original replies and do not change the private key cache. -/
theorem coins (work : ProbComp A) (cache : Cache) :
    (simulateQ recovery (simulateQ RegistrationNativeSecretWordService.coins work)).run cache=
      (fun value=>(value,cache)) <$>work := by
  induction work using OracleComp.inductionOn with
  | pure value=>simp only [simulateQ_pure,StateT.run_pure,map_pure]
  | query_bind query next ih=>
    simp only [simulateQ_bind,simulateQ_spec_query,RegistrationNativeSecretWordService.coins,
      StateT.run_bind,map_bind]
    rw [coin_query source candidate query cache,bind_map_left]
    exact bind_congr fun reply=>ih reply

private theorem coins_apply (work : ProbComp A) (cache : Cache) :
    simulateQ recovery (simulateQ RegistrationNativeSecretWordService.coins work) cache=
      (fun value=>(value,cache)) <$>work := by
  simpa only [StateT.run] using coins source candidate work cache

noncomputable def interpreted (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp)) :=
  (QueryImpl.mapStateTBase recovery (ambient physical)).flattenStateT

variable (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
/-- Closing one actual ambient query retains the same recovery cache and physical state up to their named product swap. -/
theorem query (request : (Shared n).Domain) (before : Physical) (cache : Cache) :
    Prod.map id Prod.swap <$> (interpreted source candidate physical request).run (before,cache)=
      (RegistrationNativePlatformRecordPartnerExposureRootRecovery.close source candidate physical request).run (cache,before) := by
  rw [interpreted,QueryImpl.flattenStateT_mapStateTBase_apply_run]
  cases request with
  | inl query=>
    simp only [ambient,StateT.run_lift,bind_pure_comp,simulateQ_map,simulateQ_spec_query,StateT.run_map,
      RegistrationNativePlatformRecordPartnerExposureRootRecovery.close,Functor.map_map]
    rfl
  | inr query=>
    simp only [ambient,StateT.run,coins_apply,RegistrationNativePlatformRecordPartnerExposureRootRecovery.close,
      Functor.map_map]
    rfl

/-- The same actual shared-oracle tree commutes with ordinary recovery, retaining its full physical and recovery state. -/
theorem program (work : OracleComp (Shared n) A) (before : Physical) (cache : Cache) :
    Prod.map id Prod.swap <$> (simulateQ (interpreted source candidate physical) work).run (before,cache)=
      (simulateQ (RegistrationNativePlatformRecordPartnerExposureRootRecovery.close source candidate physical) work).run (cache,before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.swap (fun request state=>query source candidate physical request state.1 state.2) work (before,cache)


/-- The staged actual physical interpreter closes to the same shared recovery execution with both reached state components retained. -/
theorem ambient_program (work : OracleComp (Shared n) A) (before : Physical) (cache : Cache) :
    (simulateQ recovery ((simulateQ (ambient physical) work).run before)).run cache=
      (fun result=>((result.1,result.2.2),result.2.1)) <$>
        (simulateQ (RegistrationNativePlatformRecordPartnerExposureRootRecovery.close source candidate physical) work).run (cache,before) := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  have observed := congrArg (Functor.map (fun result=>((result.1,result.2.2),result.2.1)))
    (program source candidate physical work before cache)
  simpa only [Functor.map_map,Prod.map_def,Prod.swap,id_eq,interpreted] using observed

/-- The root-level open closing is the same actual stateful interpreter after a product reassociation. -/
theorem closing_eq (input : RegistrationNativeSecretWordMessage.Message →Option RegistrationNativeSecretWord.Key)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix →Bool) (operand : RegistrationNativeSecretWordMessage.Message →RegistrationNativeSecretWordMessage.Message) :
    (QueryImpl.mapStateTBase (RegistrationNativePlatformRecordPartnerExposureRootRecovery.close source candidate physical)
      (RegistrationNativePlatformRecordPartnerExposureClient.closing (n := n) source input inside operand)).flattenStateT=
      RegistrationNativePlatformRecordPartnerExposureFirstHit.closing source candidate physical input inside operand := by
  funext request before
  rcases before with ⟨roots,cache,physicalBefore⟩
  change ((QueryImpl.mapStateTBase (RegistrationNativePlatformRecordPartnerExposureRootRecovery.close source candidate physical)
    (RegistrationNativePlatformRecordPartnerExposureClient.closing source input inside operand)).flattenStateT request).run (roots,(cache,physicalBefore))=_
  rw [QueryImpl.flattenStateT_mapStateTBase_apply_run]
  rcases request with ambient|(message|message)
  · simp only [RegistrationNativePlatformRecordPartnerExposureClient.closing,StateT.run_lift,bind_pure_comp,
      simulateQ_map,simulateQ_spec_query,StateT.run_map,RegistrationNativePlatformRecordPartnerExposureFirstHit.closing,Functor.map_map]
    rfl
  · rfl
  · rfl

/-- Any complete open source tree runs through the identical literal root/recovery/physical closing. -/
theorem root_program (input : RegistrationNativeSecretWordMessage.Message →Option RegistrationNativeSecretWord.Key)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix →Bool) (operand : RegistrationNativeSecretWordMessage.Message →RegistrationNativeSecretWordMessage.Message)
    (work : OracleComp (RegistrationNativePlatformLorOpenDictionary.Spec n) A)
    (roots : RegistrationNativePlatformRecordPartnerExposureSlots.State n) (cache : Cache) (before : Physical) :
    (simulateQ (RegistrationNativePlatformRecordPartnerExposureRootRecovery.close source candidate physical)
      ((simulateQ (RegistrationNativePlatformRecordPartnerExposureClient.closing source input inside operand) work).run roots)).run (cache,before)=
      (fun result=>((result.1,result.2.1),result.2.2)) <$>
        (simulateQ (RegistrationNativePlatformRecordPartnerExposureFirstHit.closing source candidate physical input inside operand) work).run (roots,(cache,before)) := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT,closing_eq]

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientExecution
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientExecution.coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientExecution.coins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientExecution.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientExecution.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientExecution.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientExecution.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientExecution.ambient_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientExecution.ambient_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientExecution.closing_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientExecution.closing_eq

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientExecution.root_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientExecution.root_program
