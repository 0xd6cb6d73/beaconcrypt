-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTraceCore
/-! The literal native preparation flag follows the same prior symbolic prepare tags. Aliased complete native addresses retain a valid flag because input validity is constant on address evaluation. The proof is per-query and retains every actual stateful outcome. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedCore
open RegistrationNativeSecretWordInterface (Spec)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWordFrontendTrace (State Event begin finish)
open RegistrationNativePlatformLorSourcePreparedTraceCore (Prepared)
open RegistrationNativePlatformOriginCallbackCut (Prefix)
variable {n : Nat} {KemSK Private Address A : Type}

noncomputable def next (input : Message →Bool) (evaluate : Message →Address)
    (query : (Spec n KemSK).Domain) (flags : Address →Bool) : Address →Bool := by
  classical
  exact match query with
  | .inl (.inl message)=>Function.update flags (evaluate message) (input message)
  | _=>flags

def Good (input : Message →Bool) (evaluate : Message →Address) (flags : Address →Bool) (trace : State) : Prop :=
  ∀message,input message=true →Prepared message trace →flags (evaluate message)=true

private theorem prepared_step (query : (Spec n KemSK).Domain) (reply : (Spec n KemSK).Range query)
    (before : State) (message : Message) :
    Prepared message (finish query reply (begin query before)) →
      Prepared message before ∨query=.inl (.inl message) := by
  rcases query with (prepared|(demand|(publication|environment))|kem)|record
  · simp only [Prepared,finish,begin,List.mem_append,List.mem_singleton,Event.prepare.injEq]
    intro occurs
    rcases occurs with old|equal
    · exact Or.inl old
    · exact Or.inr (congrArg (fun m=>Sum.inl (Sum.inl m)) equal.symm)
  · simp only [Prepared,finish,begin,List.mem_append,List.mem_singleton,reduceCtorEq,or_false]
    exact Or.inl
  · exact Or.inl
  · rcases environment with coin|capability
    · exact Or.inl
    · cases capability
      case installServer key binding kernel=>
        cases current : before.current <;> cases reply <;>
          simp [Prepared,finish,begin,RegistrationNativeSecretWordFrontendTrace.attempt,
            RegistrationNativeSecretWordFrontendTrace.installed,current,List.mem_append]
      case installBeacon owner shell kernel=>
        cases current : before.current <;> cases reply <;>
          simp [Prepared,finish,begin,RegistrationNativeSecretWordFrontendTrace.attempt,
            RegistrationNativeSecretWordFrontendTrace.installed,current,List.mem_append]
      all_goals exact Or.inl
  · rcases kem with (other|key)|pool|key
    · exact Or.inl
    · simp only [Prepared,finish,begin,List.mem_append,List.mem_singleton,reduceCtorEq,or_false]
      exact Or.inl
    · cases pool <;> exact Or.inl
    · simp only [Prepared,finish,begin,List.mem_append,List.mem_singleton,reduceCtorEq,or_false]
      exact Or.inl
  · exact Or.inl

variable (input : Message →Bool) (evaluate : Message →Address)
    (valid : ∀first second,evaluate first=evaluate second →input first=input second)

include valid
/-- The actual single-query trace update retains native preparation at every valid previously prepared descriptor. -/
theorem step (query : (Spec n KemSK).Domain) (reply : (Spec n KemSK).Range query)
    (before : State) (flags : Address →Bool) (good : Good input evaluate flags before) :
    Good input evaluate (next input evaluate query flags) (finish query reply (begin query before)) := by
  classical
  intro message available occurred
  rcases prepared_step query reply before message occurred with old|new
  · have retained := good message available old
    rcases query with (prepared|(demand|(publication|environment))|kem)|record
    · change Function.update flags (evaluate prepared) (input prepared) (evaluate message)=true
      by_cases equal : evaluate message=evaluate prepared
      · rw [equal,Function.update_self,←valid message prepared equal]
        exact available
      · rw [Function.update_of_ne equal]
        exact retained
    all_goals exact retained
  · subst query
    simpa only [next,Function.update_self] using available

variable (implementation : QueryImpl (Spec n KemSK) (StateT Private ProbComp))
    (flags : Private →Address →Bool)
    (fields : ∀query before result,result∈support ((implementation query).run before) →
      flags result.2=next input evaluate query (flags before))
local notation "actual" => RegistrationNativePlatformLorStatefulSupport.trace implementation

include valid fields
/-- Individual native flag updates and the literal trace handler preserve the reached preparation relation. -/
theorem query (request : (Spec n KemSK).Domain) (before : State ×Private)
    (result : (Spec n KemSK).Range request ×(State ×Private))
    (good : Good input evaluate (flags before.2) before.1)
    (supported : result∈support ((actual request).run before)) :
    Good input evaluate (flags result.2.2) result.2.1 := by
  have original := RegistrationNativePlatformLorSourceKemTrace.query_support implementation request before result supported
  have updated := fields request before.2 (result.1,result.2.2) original
  have traced := RegistrationNativePlatformLorStatefulSupport.trace_support implementation
    ((Spec n KemSK).query request) before result (by simpa only [simulateQ_spec_query] using supported)
  simp only [simulateQ_spec_query,RegistrationNativeSecretWordFrontendTrace.handler,StateT.run,support_map] at traced
  obtain ⟨reply,_called,equal⟩ := traced
  have stateEq := congrArg Prod.snd equal
  change finish request reply (begin request before.1)=result.2.1 at stateEq
  rw [updated,←stateEq]
  exact step input evaluate valid request reply before.1 (flags before.2) good

/-- Every reached original prefix retains its same-cache preparation flags and full symbolic chronology. -/
theorem at_prefix {work rest : OracleComp (Spec n KemSK) A} {before after : State ×Private}
    (path : Prefix actual work before rest after) (good : Good input evaluate (flags before.2) before.1) :
    Good input evaluate (flags after.2) after.1 := by
  induction path with
  | initial=>exact good
  | step earlier called ih=>exact query input evaluate valid implementation flags fields _ _ _ ih called

omit valid fields in
/-- An empty original trace needs no assumed preparation relationship. -/
theorem empty (flags : Address →Bool) (current : Option Message) :
    Good input evaluate flags ⟨current,[]⟩ := by
  intro message _ occurred
  exact False.elim (List.not_mem_nil occurred)

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedCore
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedCore.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedCore.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedCore.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedCore.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedCore.at_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedCore.at_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedCore.empty' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedCore.empty
