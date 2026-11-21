-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceFormBound
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackFreeStop
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackCut
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackJoint
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhRecordLiftIdeal (CtxPrivate)
open PqxdhRecordLiftWorldCompiler (Label)
open RegistrationNativePlatformOriginSourceSendSyntax (Reply)
open RegistrationNativePlatformOriginCallbackCut (Cut markedResume)
open RegistrationNativePlatformOriginCallbackFreeStop (PublicCall publicCall)
open RegistrationNativeStageTrace (Call)
variable {n : Nat} {Q S A X : Type} {spec : OracleSpec Q}

/-- The complete actual callback witness is retained jointly with a pure public certificate/final-state projection; no private state is read by the free client. -/
def project (finish : PublicCall spec → A × S → X)
    (result : Option (Call spec (S × CtxPrivate n)) × (A × (S × CtxPrivate n))) :
    Option (Call spec (S × CtxPrivate n) × (X × CtxPrivate n)) :=
  result.1.map (fun current=>(current,(finish (publicCall current) (result.2.1,result.2.2.1),result.2.2.2)))

/-- The selected closed callback and its original adaptive continuation have exactly the SAME free-source body-poststate/future joint law, including every optional failure reply. -/
theorem source (front : QueryImpl spec (StateT S (OracleComp (ServiceSpec n))))
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (finish : PublicCall spec → A × S → X) (cut : Cut spec (S × CtxPrivate n) A) :
    project finish <$>markedResume (QueryImpl.Stateful.link front service) (.inr cut)=
      (fun result=>some
        (⟨cut.query,cut.state,result.1.1.1,(result.1.1.2,result.1.2)⟩,
          result.2)) <$>
        RegistrationNativePlatformOriginSourceFormBound.run service ((front cut.query).run cut.state.1)
          (fun returned=>(finish ⟨cut.query,returned.1⟩) <$>(simulateQ front (cut.next returned.1)).run returned.2)
          cut.state.2 := by
  have linked (query : spec.Domain) (before : S × CtxPrivate n) :
      (QueryImpl.Stateful.link front service query).run before=
        (fun result=>(result.1.1,(result.1.2,result.2))) <$>
          (simulateQ service ((front query).run before.1)).run before.2 := by
    rw [QueryImpl.Stateful.link_impl_apply_run]
    rfl
  have client (work : OracleComp spec A) (before : S × CtxPrivate n) :
      (simulateQ (QueryImpl.Stateful.link front service) work).run before=
        (fun result=>(result.1.1,(result.1.2,result.2))) <$>
          (simulateQ service ((simulateQ front work).run before.1)).run before.2 := by
    rw [QueryImpl.Stateful.simulateQ_link_run]
    rfl
  simp only [markedResume,RegistrationNativePlatformOriginSourceFormBound.run,map_bind,bind_map_left,
    simulateQ_map,StateT.run_map,project,Option.map_some,map_pure]
  rw [linked]
  simp only [bind_map_left]
  apply bind_congr
  intro returned
  rw [client]
  simp only [bind_map_left]
  apply bind_congr
  intro finished
  rfl

def Event (read : (query : spec.Domain) →spec.Range query →Reply)
    (accepts : Label n → X × CtxPrivate n →Prop) (finish : PublicCall spec →A × S →X)
    (current : Call spec (S × CtxPrivate n)) (final : A × (S × CtxPrivate n)) : Prop :=
  read current.query current.reply=none ∧∃label,
    RegistrationNativePlatformOriginSourceFormBound.Acquired current.before.2 current.after.2 label ∧
      accepts label (finish (publicCall current) (final.1,final.2.1),final.2.2)

local instance : MeasurableSpace (Option (Call spec (S × CtxPrivate n)) × (A × (S × CtxPrivate n))) := ⊤
local instance : DiscreteMeasurableSpace (Option (Call spec (S × CtxPrivate n)) × (A × (S × CtxPrivate n))) := ⟨fun _=>trivial⟩
local instance : MeasurableSpace (Option (Call spec (S × CtxPrivate n) × (X × CtxPrivate n))) := ⊤
local instance : DiscreteMeasurableSpace (Option (Call spec (S × CtxPrivate n) × (X × CtxPrivate n))) := ⟨fun _=>trivial⟩
local instance (Y : Type) : MeasurableSpace (RegistrationNativePlatformOriginSourceFormBound.Joint n Y X) := ⊤
local instance (Y : Type) : DiscreteMeasurableSpace (RegistrationNativePlatformOriginSourceFormBound.Joint n Y X) := ⟨fun _=>trivial⟩

/-- The actual marked callback event has exactly the direct body/future-joint probability; full intermediate private snapshots are coupled rather than inferred from a projected event. -/
theorem probability (front : QueryImpl spec (StateT S (OracleComp (ServiceSpec n))))
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (finish : PublicCall spec → A × S → X) (cut : Cut spec (S × CtxPrivate n) A)
    (read : (query : spec.Domain) →spec.Range query →Reply)
    (accepts : Label n →X × CtxPrivate n →Prop) :
    𝒟[markedResume (QueryImpl.Stateful.link front service) (.inr cut)]
      {result|RegistrationNativePlatformOriginCallbackProbability.SelectedEvent (Event read accepts finish) result}=
    𝒟[RegistrationNativePlatformOriginSourceFormBound.run service ((front cut.query).run cut.state.1)
      (fun returned=>(finish ⟨cut.query,returned.1⟩) <$>(simulateQ front (cut.next returned.1)).run returned.2) cut.state.2]
      {result|RegistrationNativePlatformOriginSourceFormBound.Bad
        (fun returned=>read cut.query returned.1) accepts cut.state.2 result} := by
  let predicate : Option (Call spec (S × CtxPrivate n) × (X × CtxPrivate n)) →Prop:=fun result=>
    match result with
    |none=>False
    |some (current,final)=>read current.query current.reply=none ∧∃label,
      RegistrationNativePlatformOriginSourceFormBound.Acquired current.before.2 current.after.2 label ∧accepts label final
  have first : 𝒟[project finish <$>markedResume (QueryImpl.Stateful.link front service) (.inr cut)] {result|predicate result}=
      𝒟[markedResume (QueryImpl.Stateful.link front service) (.inr cut)]
        {result|RegistrationNativePlatformOriginCallbackProbability.SelectedEvent (Event read accepts finish) result} := by
    rw [←prEvent_eq_evalDist_of_discrete,←prEvent_eq_evalDist_of_discrete,prEvent_map]
    have predicates : (fun result=>predicate (project finish result))=
        (fun result=>RegistrationNativePlatformOriginCallbackProbability.SelectedEvent (Event read accepts finish) result) := by
      funext result
      rcases result with ⟨current,final⟩
      cases current <;>rfl
    rw [predicates]
  rw [←first,source]
  rw [←prEvent_eq_evalDist_of_discrete,←prEvent_eq_evalDist_of_discrete,prEvent_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackJoint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackJoint.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackJoint.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackJoint.probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackJoint.probability
