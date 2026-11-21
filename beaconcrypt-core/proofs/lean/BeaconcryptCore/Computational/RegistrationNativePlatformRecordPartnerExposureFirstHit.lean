-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootRecovery
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureNormalize
import BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling
/-! The normalized private root operand and candidate-independent recovery dictionary are identical until the first protected candidate-equal literal demand. Their full first-hit masses therefore agree, with every cache and physical transition retained. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureFirstHit
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key Word Cache)
open RegistrationNativeSuffixKeyPrf (Secret)
open RegistrationNativePlatformRecordPartnerExposureSlots (State)
variable {n : Nat} {I KemSK Physical A : Type} {base : OracleSpec I}
abbrev Private (n : Nat) (Physical : Type) := State n ×(Cache ×Physical)

def literals (input : Message →Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix →Bool) :
    (RegistrationNativePlatformLorOpenDictionary.Spec n).Domain →List Secret
  | .inr (.inr message)=>match input message with
    | none=>[]
    | some key=>if inside key.head then match key.word with | .atom=>[] | .literal value=>[value] else []
  | _=>[]

noncomputable def closing (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (candidate : Secret)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
    (input : Message →Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix →Bool) (operand : Message →Message) :
    QueryImpl (RegistrationNativePlatformLorOpenDictionary.Spec n) (StateT (Private n Physical) ProbComp)
  | .inl query=>fun before=>(fun result=>(result.1,(before.1,result.2))) <$>
      (RegistrationNativePlatformRecordPartnerExposureRootRecovery.close source candidate physical query).run before.2
  | .inr (.inl message)=>fun before=>(fun result=>(result.1.1,(result.1.2,result.2))) <$>
      (simulateQ (RegistrationNativePlatformRecordPartnerExposureRootRecovery.close source candidate physical)
        ((RegistrationNativePlatformRecordPartnerExposureRoot.handler source input inside (.inl message)).run before.1)).run before.2
  | .inr (.inr message)=>fun before=>(fun result=>(result.1.1,(result.1.2,result.2))) <$>
      (simulateQ (RegistrationNativePlatformRecordPartnerExposureRootRecovery.close source candidate physical)
        ((RegistrationNativePlatformRecordPartnerExposureRoot.handler source input inside (.inr (operand message))).run before.1)).run before.2

private theorem same_input (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message →Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix →Bool)
    (first second : Message) (equal : input first=input second) (before : State n) :
    (RegistrationNativePlatformRecordPartnerExposureRoot.demand source input inside first).run before=
      (RegistrationNativePlatformRecordPartnerExposureRoot.demand source input inside second).run before := by
  simp only [RegistrationNativePlatformRecordPartnerExposureRoot.demand,StateT.run,equal]

private theorem map_apply {S X Y : Type} {m : Type →Type} [Monad m] [LawfulMonad m]
    (f : X →Y) (work : StateT S m X) (before : S) :
    (f <$>work) before=Prod.map f id <$>work before := StateT.run_map _ _ _

private theorem pure_apply {S X : Type} {m : Type →Type} [Monad m] (value : X) (before : S) :
    (pure value : StateT S m X) before=pure (value,before) := rfl

variable (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : Secret) (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
local notation "Input"=>RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
local notation "inside"=>RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))
local notation "normalize"=>RegistrationNativePlatformRecordPartnerExposureNormalize.message candidate
local notation "close"=>RegistrationNativePlatformRecordPartnerExposureRootRecovery.close setup.source candidate physical

/-- Before a protected candidate-equal literal, actual normalized and independent demand callbacks retain the same complete closed state. -/
theorem demand (message : Message) (before : State n) (cache : Cache) (physicalBefore : Physical)
    (safe : ∀key,Input message=some key →inside key.head=true →key.word≠.literal candidate) :
    (simulateQ close ((RegistrationNativePlatformRecordPartnerExposureRoot.demand setup.source Input inside (normalize message)).run before)).run (cache,physicalBefore)=
      (simulateQ close ((RegistrationNativePlatformRecordPartnerExposureRoot.demand setup.source Input inside message).run before)).run (cache,physicalBefore) := by
  cases formed : Input message with
  | none=>
    have same : Input (normalize message)=Input message := by
      rw [RegistrationNativePlatformRecordPartnerExposureNormalize.input,formed,Option.map_none]
    rw [same_input setup.source Input inside _ _ same]
  | some key=>
    have normalized : Input (normalize message)=some (RegistrationNativeSecretWord.normalize candidate key) := by
      rw [RegistrationNativePlatformRecordPartnerExposureNormalize.input,formed,Option.map_some]
    by_cases different : key.word≠.literal candidate
    · have sameKey : RegistrationNativeSecretWord.normalize candidate key=key := by
        simp only [RegistrationNativeSecretWord.normalize,ite_eq_right different]
      have same : Input (normalize message)=Input message := by rw [normalized,sameKey,formed]
      rw [same_input setup.source Input inside _ _ same]
    · have literal : key.word=.literal candidate := not_not.mp different
      have outside : inside key.head=false := Bool.eq_false_of_not_eq_true (fun protectedInput=>safe key formed protectedInput literal)
      simp only [RegistrationNativePlatformRecordPartnerExposureRoot.demand,StateT.run,formed,normalized,
        RegistrationNativeSecretWord.normalize,literal,ite_true,outside,Bool.false_eq_true,ite_false]
      simp only [simulateQ_map,simulateQ_spec_query,RegistrationNativePlatformRecordPartnerExposureRootRecovery.close,
        RegistrationNativeSecretWordRecoveryCompiler.closed,StateT.run,map_apply,map_pure,simulateQ_pure,pure_apply,Prod.map_apply,id_eq]


/-- Every nonmatching open source query retains the same full root, recovery-cache and physical transition. -/
theorem query (request : (RegistrationNativePlatformLorOpenDictionary.Spec n).Domain) (before : Private n Physical)
    (safe : candidate∉literals Input inside request) :
    (closing setup.source candidate physical Input inside normalize request).run before=
      (closing setup.source candidate physical Input inside id request).run before := by
  rcases request with ambient|(message|message)
  · rfl
  · rfl
  · have safeDemand : ∀key,Input message=some key →inside key.head=true →key.word≠.literal candidate := by
      intro key formed protectedInput literal
      apply safe
      simp only [literals,formed,protectedInput,ite_true,literal,List.mem_singleton]
    have same := demand setup seed scalar candidate physical message before.1 before.2.1 before.2.2 safeDemand
    exact congrArg (Functor.map (fun result=>(result.1.1,(result.1.2,result.2)))) same

private theorem routed :
    RawCtxSelectedAliasCoupling.routed
      (closing setup.source candidate physical Input inside id)
      (closing setup.source candidate physical Input inside normalize) (literals Input inside) candidate=
      closing setup.source candidate physical Input inside normalize := by
  funext request before
  by_cases hit : candidate∈literals Input inside request
  · simp only [RawCtxSelectedAliasCoupling.routed,ite_eq_left hit]
  · simp only [RawCtxSelectedAliasCoupling.routed,ite_eq_right hit]
    exact (query setup seed scalar candidate physical request before hit).symm

/-- The normalized and candidate-independent full open-source executions have exactly the same first protected-literal hit probability. -/
theorem hit_probability (work : OracleComp (RegistrationNativePlatformLorOpenDictionary.Spec n) A) (before : Private n Physical) :
    Pr{let result←(simulateQ (RawCtxSelectedQueryTrace.recorded
      (closing setup.source candidate physical Input inside id) (literals Input inside)) work).run (before,[])}[candidate∈result.2.2]=
    Pr{let result←(simulateQ (RawCtxSelectedQueryTrace.recorded
      (closing setup.source candidate physical Input inside normalize) (literals Input inside)) work).run (before,[])}[candidate∈result.2.2] := by
  have same := StatefulGoodEvent.bad_probability_eq
    (RawCtxSelectedAliasCoupling.marked (closing setup.source candidate physical Input inside id) (literals Input inside) candidate)
    (RawCtxSelectedAliasCoupling.marked (RawCtxSelectedAliasCoupling.routed (closing setup.source candidate physical Input inside id)
      (closing setup.source candidate physical Input inside normalize) (literals Input inside) candidate) (literals Input inside) candidate)
    (RawCtxSelectedAliasCoupling.agree_good (closing setup.source candidate physical Input inside id)
      (closing setup.source candidate physical Input inside normalize) (literals Input inside) candidate)
    (RawCtxSelectedAliasCoupling.marked_sticky _ _ _) (RawCtxSelectedAliasCoupling.marked_sticky _ _ _) work ((before,[]),false)
  rw [routed] at same
  simpa only [RawCtxSelectedAliasCoupling.bad_probability] using same

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureFirstHit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureFirstHit.demand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureFirstHit.demand

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureFirstHit.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureFirstHit.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureFirstHit.hit_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureFirstHit.hit_probability
