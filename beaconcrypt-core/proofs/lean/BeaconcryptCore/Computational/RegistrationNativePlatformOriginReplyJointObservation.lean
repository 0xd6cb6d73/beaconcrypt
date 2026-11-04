-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginResumedCallback
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginReplyObservation
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginReplyJointObservation
open PqxdhRecordLiftIdeal (CtxPrivate)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordFactsOriginMuteAdaptive (marked)
open PqxdhRecordFactsOriginMuteUntilBad (serviceBad)
open RegistrationNativePlatformOriginReserveContinuationBound (continued)
open RegistrationNativePlatformOriginResumedCallback (prefixWork)
variable {n : Nat} {Platform Failure A X : Type}
private theorem quiet_program {A : Type} (target : Label n) (decode : AdaptiveCtxReceive.RawDecoder)
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (work : OracleComp (ServiceSpec n) A)
    (quiet : work.AllQueriesSatisfy (fun query => ∀state,serviceBad target decode query state=false))
    (before : CtxPrivate n) (flag : Bool) :
    (simulateQ (marked target decode service) work).run (before,flag)=
      (fun result => (result.1,(result.2,flag))) <$> (simulateQ service work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure,StateT.run_pure,map_pure]
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at quiet
    simp only [simulateQ_bind,simulateQ_spec_query]
    change ((marked target decode service query >>= fun reply => simulateQ (marked target decode service) (next reply)).run (before,flag)) =
      (fun result => (result.1,(result.2,flag))) <$> ((service query >>= fun reply => simulateQ service (next reply)).run before)
    simp only [StateT.run_bind]
    change ((do let result ← (service query).run before; pure (result.1,(result.2,flag || serviceBad target decode query before))) >>= _) = _
    simp only [bind_assoc,pure_bind,map_bind]
    apply bind_congr
    intro result
    simpa only [pure_bind,quiet.1 before,Bool.or_false] using ih result.1 (quiet.2 result.1) result.2

private theorem coins_quiet {A : Type} (target : Label n) (decode : AdaptiveCtxReceive.RawDecoder) (work : ProbComp A) :
    (simulateQ RegistrationNativePlatformOriginGateSource.coins work).AllQueriesSatisfy
      (fun query => ∀state,serviceBad target decode query state=false) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,RegistrationNativePlatformOriginGateSource.coins,bind_assoc,
      allQueriesSatisfy_query_bind_iff]
    exact ⟨fun _ => rfl,fun _ => ⟨fun _ => rfl,fun reply => ih reply⟩⟩

private theorem prefix_quiet
    (target : Label n) (decode : AdaptiveCtxReceive.RawDecoder)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (before : Platform) (tag : PqxdhDeploymentInterface.FrameTag) (reply : Option RawCtxSourceSend.Encrypted) :
    (prefixWork reserve before tag reply).AllQueriesSatisfy
      (fun query => ∀state,serviceBad target decode query state=false) := by
  simp only [prefixWork,allQueriesSatisfy_query_bind_iff]
  exact ⟨fun _ => rfl,fun _ => coins_quiet target decode _⟩

variable (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (after : Option RawCtxSourceSend.Encrypted → Platform → A)
    (future : A → OracleComp (ServiceSpec n) X) (beforeP : Platform) (tag : PqxdhDeploymentInterface.FrameTag)
    (target : Label n) (decode : AdaptiveCtxReceive.RawDecoder)
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (before : CtxPrivate n) (pending : PqxdhRecordLiftProtocol.Sealing n)

/-- The actual prefix only publishes and draws charged reserve coins; its marked interpreter retains the same gate result and physical state before the genuine continuation. -/
theorem continued_form {Y : Type} (next : Option RawCtxSourceSend.Encrypted → Platform → OracleComp (ServiceSpec n) Y)
    (reply : Option RawCtxSourceSend.Encrypted) (state : CtxPrivate n) :
    (simulateQ (marked target decode service) (continued reserve next beforeP tag reply)).run (state,false) =
    (do let gated ← (simulateQ service (prefixWork reserve beforeP tag reply)).run state
        (simulateQ (marked target decode service) (next gated.1.1 gated.1.2)).run (gated.2,false)) := by
  have ast : continued reserve next beforeP tag reply=prefixWork reserve beforeP tag reply >>=fun gated=>next gated.1 gated.2 := by
    simp only [continued,prefixWork,bind_assoc]
  rw [ast,simulateQ_bind,StateT.run_bind,quiet_program target decode service _ (prefix_quiet target decode reserve beforeP tag reply) state false]
  simp only [bind_map_left]

noncomputable def joint : ProbComp (((A × CtxPrivate n) × (X × CtxPrivate n)) × Bool) := do
  let sealed ← (service (.sealing pending)).run before
  let gated ← (simulateQ service (prefixWork reserve beforeP tag sealed.1)).run sealed.2
  let finished ← (simulateQ (marked target decode service) (future (after gated.1.1 gated.1.2))).run (gated.2,false)
  pure (((after gated.1.1 gated.1.2,gated.2),(finished.1,finished.2.1)),gated.1.1.isNone &&finished.2.2)

/-- Erasing only the refusal/match flag retains the SAME body reply/poststate jointly with its actual continued execution. -/
theorem erase :
    Prod.fst <$>joint reserve after future beforeP tag target decode service before pending =
    (do let body ← (simulateQ service
          (((ServiceSpec n).query (.sealing pending) : OracleComp (ServiceSpec n) _) >>=continued reserve (fun output reachedP=>pure (after output reachedP)) beforeP tag)).run before
        let finished ← (simulateQ service (future body.1)).run body.2
        pure (body,finished)) := by
  simp only [joint,map_bind,map_pure,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,bind_assoc]
  apply bind_congr
  intro sealed
  have ast : continued (n := n) reserve (fun output reachedP=>pure (after output reachedP)) beforeP tag sealed.1=
      (fun gated=>after gated.1 gated.2) <$>prefixWork reserve beforeP tag sealed.1 := by
    simp only [continued,prefixWork,bind_pure_comp,map_bind]
  rw [ast]
  simp only [simulateQ_map,StateT.run_map,bind_map_left]
  apply bind_congr
  intro gated
  have erased := PqxdhRecordFactsOriginMuteAdaptive.complete_erase target decode service (future (after gated.1.1 gated.1.2)) (gated.2,false)
  have same := congrArg (Functor.map (fun result => ((after gated.1.1 gated.1.2,gated.2),result))) erased
  simpa only [Functor.map_map,bind_pure_comp,Prod.map_def,id_eq] using same

/-- Dropping only the retained body coordinate recovers the existing guarded sealing observation exactly. -/
theorem project :
    (fun result=>(result.1.2,result.2)) <$>joint reserve after future beforeP tag target decode service before pending =
      RegistrationNativePlatformOriginResumedCallback.sealingObservation reserve
        (fun output reachedP=>future (after output reachedP)) beforeP tag target decode service before pending := by
  simp only [joint,RegistrationNativePlatformOriginResumedCallback.sealingObservation,map_bind,map_pure]
  apply bind_congr
  intro sealed
  unfold RegistrationNativePlatformOriginResumedCallback.observation
  rw [continued_form]
  simp only [map_bind,simulateQ_map,StateT.run_map,Functor.map_map,bind_pure_comp]

/-- Every supported joint outcome exposes its same actual seal, gate and marked future replies and complete intermediate states. -/
theorem cases_source (result : ((A × CtxPrivate n) × (X × CtxPrivate n)) × Bool)
    (supported : result∈support (joint reserve after future beforeP tag target decode service before pending)) :
    ∃sealed gated finished,
      sealed∈support ((service (.sealing pending)).run before) ∧
      gated∈support ((simulateQ service (prefixWork reserve beforeP tag sealed.1)).run sealed.2) ∧
      finished∈support ((simulateQ (marked target decode service) (future (after gated.1.1 gated.1.2))).run (gated.2,false)) ∧
      result=(((after gated.1.1 gated.1.2,gated.2),(finished.1,finished.2.1)),gated.1.1.isNone &&finished.2.2) := by
  simp only [joint,mem_support_bind_iff,mem_support_pure_iff] at supported
  obtain ⟨sealed,called,gated,gate,finished,final,equal⟩ := supported
  exact ⟨sealed,gated,finished,called,gate,final,equal⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginReplyJointObservation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReplyJointObservation.continued_form' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReplyJointObservation.continued_form
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReplyJointObservation.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReplyJointObservation.erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReplyJointObservation.project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReplyJointObservation.project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReplyJointObservation.cases_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReplyJointObservation.cases_source
