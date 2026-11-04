-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKemTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackPrefix
/-! Genuine symbolic trace queries append their actual events and preserve every earlier preparation, under any persistent source interpretation. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTraceCore
open RegistrationNativeSecretWordInterface (Spec)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWordFrontendTrace (State Event begin finish attempt installed)
open RegistrationNativePlatformOriginCallbackCut (Prefix)
variable {n : Nat} {KemSK Private A : Type}

def Prepared (message : Message) (before : State) : Prop := Event.prepare message∈before.events

/-- Every literal trace update only appends its own actual chronological events. -/
theorem update_suffix (query : (Spec n KemSK).Domain) (reply : (Spec n KemSK).Range query) (before : State) :
    ∃added,(finish query reply (begin query before)).events=before.events++added := by
  rcases query with (prepared|(demand|(publication|environment))|kem)|record
  · exact ⟨[.prepare prepared],rfl⟩
  · exact ⟨[.demand demand],rfl⟩
  · exact ⟨[],(List.append_nil _).symm⟩
  · rcases environment with coin|capability
    · exact ⟨[],(List.append_nil _).symm⟩
    · cases capability
      case installServer keyId binding kernel=>
        cases current : before.current <;> cases reply <;>
          simp [begin,finish,attempt,installed,current,List.append_assoc]
      case installBeacon owner shell kernel=>
        cases current : before.current <;> cases reply <;>
          simp [begin,finish,attempt,installed,current,List.append_assoc]
      all_goals exact ⟨[],(List.append_nil _).symm⟩
  · rcases kem with (other|key)|pool|key
    · exact ⟨[],(List.append_nil _).symm⟩
    · exact ⟨[.encapsulate false key reply.1 reply.2],rfl⟩
    · cases pool <;> exact ⟨[],(List.append_nil _).symm⟩
    · exact ⟨[.encapsulate true key reply.1 reply.2],rfl⟩
  · exact ⟨[],(List.append_nil _).symm⟩

variable (implementation : QueryImpl (Spec n KemSK) (StateT Private ProbComp))
local notation "actual" => RegistrationNativePlatformLorStatefulSupport.trace implementation

/-- A reached traced callback has the same appended chronology, regardless of any actual source failure. -/
theorem query_suffix (query : (Spec n KemSK).Domain) (before : State × Private)
    (result : (Spec n KemSK).Range query × (State × Private))
    (supported : result∈support ((actual query).run before)) :
    ∃added,result.2.1.events=before.1.events++added := by
  have free := RegistrationNativePlatformLorStatefulSupport.trace_support implementation ((Spec n KemSK).query query) before result
    (by simpa only [simulateQ_spec_query] using supported)
  simp only [simulateQ_spec_query,RegistrationNativeSecretWordFrontendTrace.handler,StateT.run,support_map] at free
  obtain ⟨reply,_reached,equal⟩ := free
  have traceEq := congrArg Prod.snd equal
  change finish query reply (begin query before.1)=result.2.1 at traceEq
  rw [←traceEq]
  exact update_suffix query reply before.1

/-- The actual preparation callback records its own requested descriptor before any later material demand. -/
theorem prepare_recorded (message : Message) (before : State × Private)
    (result : Option Message × (State × Private))
    (supported : result∈support ((actual (.inl (.inl message))).run before)) : Prepared message result.2.1 := by
  have free := RegistrationNativePlatformLorStatefulSupport.trace_support implementation
    ((Spec n KemSK).query (.inl (.inl message))) before result (by simpa only [simulateQ_spec_query] using supported)
  simp only [simulateQ_spec_query,RegistrationNativeSecretWordFrontendTrace.handler,StateT.run,support_map] at free
  obtain ⟨reply,_reached,equal⟩ := free
  have traceEq := congrArg Prod.snd equal
  change (⟨none,before.1.events++[.prepare message]⟩ : State)=result.2.1 at traceEq
  rw [←traceEq]
  exact List.mem_append_right _ (List.mem_singleton_self _)

/-- Complete adaptive source work preserves every earlier trace event in order. -/
theorem program_suffix (work : OracleComp (Spec n KemSK) A) (before : State × Private)
    (result : A × (State × Private)) (supported : result∈support ((simulateQ actual work).run before)) :
    ∃added,result.2.1.events=before.1.events++added := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value=>
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    exact ⟨[],(List.append_nil _).symm⟩
  | query_bind query next ih=>
    rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,later⟩ := supported
    obtain ⟨first,head⟩ := query_suffix implementation query before middle called
    obtain ⟨last,tail⟩ := ih middle.1 middle.2 result later
    exact ⟨first++last,by rw [tail,head,List.append_assoc]⟩

/-- A previously executed preparation remains strictly in the past at every later actual query prefix. -/
theorem prefix_keeps (message : Message) {work rest : OracleComp (Spec n KemSK) A}
    {before after : State × Private} (prefixPath : Prefix actual work before rest after)
    (prepared : Prepared message before.1) : Prepared message after.1 := by
  induction prefixPath with
  | initial=>exact prepared
  | step earlier called ih=>
    obtain ⟨added,appended⟩ := query_suffix implementation _ _ _ called
    dsimp only [Prepared] at ih ⊢
    rw [appended]
    exact List.mem_append_left _ ih
end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTraceCore
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTraceCore.update_suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTraceCore.update_suffix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTraceCore.query_suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTraceCore.query_suffix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTraceCore.program_suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTraceCore.program_suffix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTraceCore.prefix_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTraceCore.prefix_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTraceCore.prepare_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTraceCore.prepare_recorded
