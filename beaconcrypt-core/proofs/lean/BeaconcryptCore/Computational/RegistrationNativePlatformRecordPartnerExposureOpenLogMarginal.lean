-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureOpenMarginal
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureOpenLogMarginal
open LazyOracleDiscard (LawEq)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSuffixKeyPrf (Secret)
open RegistrationNativePlatformRecordPartnerExposureDictionarySource (NoAmbient)
variable {n : Nat} {Physical A : Type}
variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (candidate : Secret)
    (filler : PqxdhServerAuthKeySchedule.Output)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
    (input : Message →Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix →Bool) (operand : Message →Message)
local notation "original"=>RegistrationNativePlatformRecordPartnerExposureFirstHit.closing source candidate physical input inside operand
local notation "direct"=>RegistrationNativePlatformRecordPartnerExposureOpenMarginal.direct source candidate filler physical input inside operand
local notation "literals"=>RegistrationNativePlatformRecordPartnerExposureFirstHit.literals (n:=n) input inside

def drop (before : RegistrationNativePlatformRecordPartnerExposureFirstHit.Private n Physical×List Secret) :=
  (RegistrationNativePlatformRecordPartnerExposureOpenMarginal.drop before.1,before.2)

/-- Recording actual input literals commutes with dropping only the recovery cache at each allowed Open query. -/
theorem query (request : (RegistrationNativePlatformLorOpenDictionary.Spec n).Domain) (allowed : NoAmbient request)
    (before : RegistrationNativePlatformRecordPartnerExposureFirstHit.Private n Physical×List Secret) :
    LawEq (Prod.map id drop <$> (RawCtxSelectedQueryTrace.recorded original literals request).run before)
      ((RawCtxSelectedQueryTrace.recorded direct literals request).run (drop before)) := by
  have same := (RegistrationNativePlatformRecordPartnerExposureOpenMarginal.query source candidate filler physical input inside operand request allowed before.1).map
    (fun result=>(result.1,(result.2,before.2++literals request)))
  simpa only [RawCtxSelectedQueryTrace.recorded,StateT.run,map_bind,map_pure,bind_pure_comp,
    Functor.map_map,drop,Prod.map_def,id_eq] using same

/-- The complete same-run input log and every original return/root/physical coordinate survive cache marginalization. -/
theorem program (work : OracleComp (RegistrationNativePlatformLorOpenDictionary.Spec n) A)
    (allowed : work.AllQueriesSatisfy NoAmbient)
    (before : RegistrationNativePlatformRecordPartnerExposureFirstHit.Private n Physical×List Secret) :
    LawEq (Prod.map id drop <$> (simulateQ (RawCtxSelectedQueryTrace.recorded original literals) work).run before)
      ((simulateQ (RawCtxSelectedQueryTrace.recorded direct literals) work).run (drop before)) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value=>exact LawEq.of_eq (by simp only [simulateQ_pure,StateT.run_pure,map_pure,Prod.map_apply,id_eq])
  | query_bind request next ih=>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
    refine (LazyOracleDiscard.LawEq.bind (LawEq.refl _) (fun result :
      (RegistrationNativePlatformLorOpenDictionary.Spec n).Range request ×
        (RegistrationNativePlatformRecordPartnerExposureFirstHit.Private n Physical×List Secret)=>
          ih result.1 (allowed.2 result.1) result.2)).trans ?_
    have first := LazyOracleDiscard.LawEq.bind
      (query source candidate filler physical input inside operand request allowed.1 before)
      (fun result : (RegistrationNativePlatformLorOpenDictionary.Spec n).Range request ×
        ((RegistrationNativePlatformRecordPartnerExposureSlots.State n×Physical)×List Secret)=>LawEq.refl
          ((simulateQ (RawCtxSelectedQueryTrace.recorded direct literals) (next result.1)).run result.2))
    simpa only [bind_map_left,Prod.map_def,id_eq] using first

/-- Protected literal hit probability is unchanged by the actual recovery-cache marginal, with arbitrary prior log and warm state. -/
theorem hit_probability (work : OracleComp (RegistrationNativePlatformLorOpenDictionary.Spec n) A)
    (allowed : work.AllQueriesSatisfy NoAmbient)
    (before : RegistrationNativePlatformRecordPartnerExposureFirstHit.Private n Physical×List Secret) :
    Pr{let result←(simulateQ (RawCtxSelectedQueryTrace.recorded original literals) work).run before}[candidate∈result.2.2]=
      Pr{let result←(simulateQ (RawCtxSelectedQueryTrace.recorded direct literals) work).run (drop before)}[candidate∈result.2.2] := by
  let : MeasurableSpace (A×((RegistrationNativePlatformRecordPartnerExposureSlots.State n×Physical)×List Secret)):=⊤
  have same := program source candidate filler physical input inside operand work allowed before
    _ (fun result=>pure result)
  simp only [bind_pure] at same
  have equal := (EvalDistEq.of_evalDist_eq same) (fun result=>candidate∈result.2.2)
  simpa only [prEvent_map,Prod.map_def,drop,id_eq] using equal

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureOpenLogMarginal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureOpenLogMarginal.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureOpenLogMarginal.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureOpenLogMarginal.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureOpenLogMarginal.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureOpenLogMarginal.hit_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureOpenLogMarginal.hit_probability
