-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureDictionarySource
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureFirstHit
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendTrace
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureQueryLog
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (WorldSpec)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSuffixKeyPrf (Secret)
variable {n : Nat} {I KemSK A Private : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (input : Message →Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix →Bool)
    (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK)
local notation "handler" => RegistrationNativePlatformLorOpenDictionary.handler setup wire sign input inside provider
local notation "literals" => RegistrationNativePlatformRecordPartnerExposureFirstHit.literals (n:=n) input inside
abbrev Nonroot := RegistrationNativePlatformRecordPartnerExposureDictionarySource.Nonroot (n:=n) (KemSK:=KemSK)

def wordLiterals : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain →List Secret
  | .inl (.inr (.inl (.inl message))) =>literals (.inr (.inr message))
  | _ =>[]

def traceLiterals (events : List RegistrationNativeSecretWordFrontendTrace.Event) : List Secret :=
  events.flatMap (fun event =>match event with | .demand message =>literals (.inr (.inr message)) | _=>[])

private theorem world_form (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (quiet : Nonroot query) (before : RegistrationNativeSecretWordInterpreter.State n KemSK) :
    ∃body : OracleComp (WorldSpec n) ((RegistrationNativeSecretWordInterface.Spec n KemSK).Range query ×RegistrationNativeSecretWordInterpreter.State n KemSK),
      (handler query).run before=simulateQ RegistrationNativePlatformLorOpenDictionary.embed
        (simulateQ RegistrationNativePlatformLorWorldDictionary.world body) := by
  rcases query with (prepare | (demand | common) | routed) | record
  · exact quiet.elim
  · exact quiet.elim
  · rcases common with publication | effect
    · refine ⟨(fun result => (result.1,{before with ordinary:={before.ordinary with receipts:=result.2}})) <$>
        simulateQ PqxdhRecordLiftInterface.effectLift
          ((RegistrationBoundSourceCompiler.compiler setup.source (RegistrationNativeWire.ledgerCodec wire).frameWrite sign publication).run before.ordinary.receipts),?_⟩
      simp only [RegistrationNativePlatformLorOpenDictionary.handler,QueryImpl.mapStateTBase,
        RegistrationNativePlatformLorWorldDictionary.handler,RegistrationNativePlatformLorWorldDictionary.common,
        RegistrationNativePlatformLorWorldDictionary.publication,StateT.run,simulateQ_map,←QueryImpl.simulateQ_compose]
      rfl
    · refine ⟨(fun reply => (reply,before)) <$>PqxdhRecordLiftInterface.effectLift effect,?_⟩
      simp only [RegistrationNativePlatformLorOpenDictionary.handler,QueryImpl.mapStateTBase,
        RegistrationNativePlatformLorWorldDictionary.handler,RegistrationNativePlatformLorWorldDictionary.common,
        RegistrationNativePlatformLorWorldDictionary.effect,StateT.run_mk,StateT.run_lift,bind_pure_comp,simulateQ_map,
        PqxdhRecordLiftInterface.effectLift,simulateQ_spec_query]
  · refine ⟨(fun result => (result.1,{before with kem:=result.2})) <$>
      simulateQ PqxdhRecordLiftInterface.coinLift ((provider routed).run before.kem),?_⟩
    simp only [RegistrationNativePlatformLorOpenDictionary.handler,QueryImpl.mapStateTBase,
      RegistrationNativePlatformLorWorldDictionary.handler,RegistrationNativePlatformLorWorldDictionary.routed,
      StateT.run,simulateQ_map,RegistrationNativePlatformLorWorldDictionary.coins,←QueryImpl.simulateQ_compose]
    rfl
  · refine ⟨(fun reply => (reply,before)) <$>((WorldSpec n).query (.inr (.inr record)) :OracleComp (WorldSpec n) _),?_⟩
    simp only [RegistrationNativePlatformLorOpenDictionary.handler,QueryImpl.mapStateTBase,StateT.run_mk,
      RegistrationNativePlatformLorWorldDictionary.record_run,simulateQ_map,simulateQ_spec_query]
    rfl


private theorem quiet_log {ι : Type} {spec : OracleSpec ι}
    (close : QueryImpl spec (StateT Private ProbComp)) (record : spec.Domain →List Secret)
    (work : OracleComp spec A) (quiet : work.AllQueriesSatisfy (fun query=>record query=[]))
    (before : Private×List Secret) (result : A×(Private×List Secret))
    (supported : result∈support ((simulateQ (RawCtxSelectedQueryTrace.recorded close record) work).run before)) :
    result.2.2=before.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    rfl
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at quiet
    simp only [simulateQ_bind,simulateQ_spec_query] at supported
    change result∈support (((RawCtxSelectedQueryTrace.recorded close record query).run before) >>=fun reply=>
      (simulateQ (RawCtxSelectedQueryTrace.recorded close record) (next reply.1)).run reply.2) at supported
    simp only [RawCtxSelectedQueryTrace.recorded,StateT.run,bind_assoc,pure_bind,quiet.1,List.append_nil] at supported
    rw [mem_support_bind_iff] at supported
    obtain ⟨reply,_called,tailSupport⟩:=supported
    exact ih reply.1 (quiet.2 reply.1) (reply.2,before.2) result tailSupport

private theorem world_quiet (work : OracleComp (WorldSpec n) A) :
    (simulateQ RegistrationNativePlatformLorOpenDictionary.embed
      (simulateQ RegistrationNativePlatformLorWorldDictionary.world work)).AllQueriesSatisfy
        (fun query=>literals query=[]) := by
  induction work using OracleComp.inductionOn with
  | pure value =>trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,RegistrationNativePlatformLorWorldDictionary.world,
      RegistrationNativePlatformLorOpenDictionary.embed,allQueriesSatisfy_query_bind_iff]
    exact ⟨rfl,ih⟩

/-- The recorder appends exactly the protected literal of this Word demand; every other source callback adds nothing. -/
theorem query
    (close : QueryImpl (RegistrationNativePlatformLorOpenDictionary.Spec n) (StateT Private ProbComp))
    (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (wordBefore : RegistrationNativeSecretWordInterpreter.State n KemSK) (before : Private×List Secret)
    (result : ((RegistrationNativeSecretWordInterface.Spec n KemSK).Range query×RegistrationNativeSecretWordInterpreter.State n KemSK)×(Private×List Secret))
    (supported : result∈support ((simulateQ (RawCtxSelectedQueryTrace.recorded close literals)
      ((handler query).run wordBefore)).run before)) :
    result.2.2=before.2++wordLiterals input inside query := by
  rcases query with (prepare | (demand | common) | routed) | record
  · rw [RegistrationNativePlatformLorOpenDictionary.prepare_run] at supported
    simp only [RegistrationNativePlatformLorOpenDictionary.root,simulateQ_bind,simulateQ_spec_query] at supported
    change result∈support (((RawCtxSelectedQueryTrace.recorded close literals (.inr (.inl prepare))).run before) >>=fun reply=>
      pure (((input prepare).map (fun _=>prepare),{wordBefore with flags:=Function.update wordBefore.flags prepare (input prepare).isSome}),reply.2)) at supported
    simp only [RawCtxSelectedQueryTrace.recorded,StateT.run,bind_assoc,pure_bind] at supported
    rw [mem_support_bind_iff] at supported
    obtain ⟨reply,_called,returned⟩:=supported
    rw [mem_support_pure_iff] at returned
    cases returned
    rfl
  · rw [RegistrationNativePlatformLorOpenDictionary.demand_run] at supported
    simp only [simulateQ_map,RegistrationNativePlatformLorOpenDictionary.root,simulateQ_spec_query] at supported
    rw [StateT.run_map] at supported
    simp only [RawCtxSelectedQueryTrace.recorded,StateT.run,bind_pure_comp,Functor.map_map,support_map] at supported
    obtain ⟨reply,_called,rfl⟩:=supported
    rfl
  · obtain ⟨body,bodyEq⟩:=world_form setup wire sign input inside provider (.inl (.inr (.inl (.inr common)))) (by trivial) wordBefore
    rw [bodyEq] at supported
    simpa only [wordLiterals,List.append_nil] using
      quiet_log close literals _ (world_quiet input inside body) before result supported
  · obtain ⟨body,bodyEq⟩:=world_form setup wire sign input inside provider (.inl (.inr (.inr routed))) (by trivial) wordBefore
    rw [bodyEq] at supported
    simpa only [wordLiterals,List.append_nil] using
      quiet_log close literals _ (world_quiet input inside body) before result supported
  · obtain ⟨body,bodyEq⟩:=world_form setup wire sign input inside provider (.inr record) (by trivial) wordBefore
    rw [bodyEq] at supported
    simpa only [wordLiterals,List.append_nil] using
      quiet_log close literals _ (world_quiet input inside body) before result supported



/-- The symbolic trace records the same literal suffix on each callback, irrespective of its optional reply. -/
theorem trace_step (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (reply : (RegistrationNativeSecretWordInterface.Spec n KemSK).Range query)
    (before : RegistrationNativeSecretWordFrontendTrace.State) :
    traceLiterals (n:=n) input inside
      (RegistrationNativeSecretWordFrontendTrace.finish query reply
        (RegistrationNativeSecretWordFrontendTrace.begin query before)).events=
      traceLiterals (n:=n) input inside before.events++wordLiterals input inside query := by
  rcases query with (prepare | (demand | common) | routed) | record
  · simp [RegistrationNativeSecretWordFrontendTrace.begin,RegistrationNativeSecretWordFrontendTrace.finish,
      traceLiterals,wordLiterals,List.flatMap_append]
  · simp [RegistrationNativeSecretWordFrontendTrace.begin,RegistrationNativeSecretWordFrontendTrace.finish,
      traceLiterals,wordLiterals,List.flatMap_append]
  · rcases common with publication | effect
    · simp [RegistrationNativeSecretWordFrontendTrace.begin,RegistrationNativeSecretWordFrontendTrace.finish,
        traceLiterals,wordLiterals]
    · rcases effect with coin | capability
      · simp [RegistrationNativeSecretWordFrontendTrace.begin,RegistrationNativeSecretWordFrontendTrace.finish,
          traceLiterals,wordLiterals]
      · cases capability <;>
          simp [RegistrationNativeSecretWordFrontendTrace.begin,RegistrationNativeSecretWordFrontendTrace.finish,
            RegistrationNativeSecretWordFrontendTrace.attempt,RegistrationNativeSecretWordFrontendTrace.installed,
            traceLiterals,wordLiterals] <;>
          cases held : before.current <;> cases reply <;>
            simp_all [List.flatMap_append]
  · rcases routed with (other | key) | (pool | key)
    · simp [RegistrationNativeSecretWordFrontendTrace.begin,RegistrationNativeSecretWordFrontendTrace.finish,
        traceLiterals,wordLiterals]
    · simp [RegistrationNativeSecretWordFrontendTrace.begin,RegistrationNativeSecretWordFrontendTrace.finish,
        traceLiterals,wordLiterals,List.flatMap_append]
    · simp [RegistrationNativeSecretWordFrontendTrace.begin,RegistrationNativeSecretWordFrontendTrace.finish,
        traceLiterals,wordLiterals]
    · simp [RegistrationNativeSecretWordFrontendTrace.begin,RegistrationNativeSecretWordFrontendTrace.finish,
        traceLiterals,wordLiterals,List.flatMap_append]
  · simp [RegistrationNativeSecretWordFrontendTrace.begin,RegistrationNativeSecretWordFrontendTrace.finish,
      traceLiterals,wordLiterals]


noncomputable abbrev recordedWord
    (close : QueryImpl (RegistrationNativePlatformLorOpenDictionary.Spec n) (StateT Private ProbComp)) :=
  QueryImpl.flattenStateT (QueryImpl.mapStateTBase (RawCtxSelectedQueryTrace.recorded close literals) handler)

noncomputable abbrev traced
    (close : QueryImpl (RegistrationNativePlatformLorOpenDictionary.Spec n) (StateT Private ProbComp)) :=
  QueryImpl.flattenStateT (QueryImpl.mapStateTBase (recordedWord setup wire sign input inside provider close)
    (RegistrationNativeSecretWordFrontendTrace.handler (n:=n) (KemSK:=KemSK)))

private theorem traced_query
    (close : QueryImpl (RegistrationNativePlatformLorOpenDictionary.Spec n) (StateT Private ProbComp))
    (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (before : RegistrationNativeSecretWordFrontendTrace.State×(RegistrationNativeSecretWordInterpreter.State n KemSK×(Private×List Secret)))
    (past : List Secret) (aligned : before.2.2.2=past++traceLiterals (n:=n) input inside before.1.events)
    (result : (RegistrationNativeSecretWordInterface.Spec n KemSK).Range query×
      (RegistrationNativeSecretWordFrontendTrace.State×(RegistrationNativeSecretWordInterpreter.State n KemSK×(Private×List Secret))))
    (supported : result∈support ((traced setup wire sign input inside provider close query).run before)) :
    result.2.2.2.2=past++traceLiterals (n:=n) input inside result.2.1.events := by
  rw [traced,QueryImpl.flattenStateT_mapStateTBase_apply_run] at supported
  simp only [RegistrationNativeSecretWordFrontendTrace.handler,StateT.run,simulateQ_map,simulateQ_spec_query] at supported
  change result∈support ((fun value=>(value.1.1,(value.1.2,value.2))) <$>
    (((fun reply=>(reply,RegistrationNativeSecretWordFrontendTrace.finish query reply
      (RegistrationNativeSecretWordFrontendTrace.begin query before.1))) <$>
      recordedWord setup wire sign input inside provider close query).run before.2)) at supported
  rw [StateT.run_map,recordedWord,QueryImpl.flattenStateT_mapStateTBase_apply_run] at supported
  simp only [Functor.map_map,support_map] at supported
  obtain ⟨inner,called,rfl⟩:=supported
  change inner.2.2=past++traceLiterals (n:=n) input inside
    (RegistrationNativeSecretWordFrontendTrace.finish query inner.1.1
      (RegistrationNativeSecretWordFrontendTrace.begin query before.1)).events
  rw [trace_step,←List.append_assoc,←aligned]
  exact RegistrationNativePlatformRecordPartnerExposureQueryLog.query setup wire sign input inside provider
    close query before.2.1 before.2.2 inner called


/-- The complete traced Word program retains exact agreement between its genuine demand trace and the Open input recorder. -/
theorem program
    (close : QueryImpl (RegistrationNativePlatformLorOpenDictionary.Spec n) (StateT Private ProbComp))
    (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) A)
    (before : RegistrationNativeSecretWordFrontendTrace.State×(RegistrationNativeSecretWordInterpreter.State n KemSK×(Private×List Secret)))
    (past : List Secret) (aligned : before.2.2.2=past++traceLiterals (n:=n) input inside before.1.events)
    (result : A×(RegistrationNativeSecretWordFrontendTrace.State×(RegistrationNativeSecretWordInterpreter.State n KemSK×(Private×List Secret))))
    (supported : result∈support ((simulateQ (traced setup wire sign input inside provider close) work).run before)) :
    result.2.2.2.2=past++traceLiterals (n:=n) input inside result.2.1.events := by
  exact OracleComp.simulateQ_run_preservesInv (traced setup wire sign input inside provider close)
    (fun state=>state.2.2.2=past++traceLiterals (n:=n) input inside state.1.events)
    (fun query state held out called=>traced_query setup wire sign input inside provider close query state past held out called)
    work before aligned result supported

/-- Running the literal open dictionary and recorder on the actual symbolic trace produces exactly that trace's protected demand literals. -/
theorem source
    (close : QueryImpl (RegistrationNativePlatformLorOpenDictionary.Spec n) (StateT Private ProbComp))
    (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) A)
    (trace : RegistrationNativeSecretWordFrontendTrace.State)
    (wordBefore : RegistrationNativeSecretWordInterpreter.State n KemSK) (before : Private×List Secret)
    (past : List Secret) (aligned : before.2=past++traceLiterals (n:=n) input inside trace.events)
    (result : ((A×RegistrationNativeSecretWordFrontendTrace.State)×RegistrationNativeSecretWordInterpreter.State n KemSK)×(Private×List Secret))
    (supported : result∈support ((simulateQ (RawCtxSelectedQueryTrace.recorded close literals)
      ((simulateQ handler ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler work).run trace)).run wordBefore)).run before)) :
    result.2.2=past++traceLiterals (n:=n) input inside result.1.1.2.events := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT] at supported
  rw [support_map] at supported
  obtain ⟨middle,called,rfl⟩:=supported
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT] at called
  rw [support_map] at called
  obtain ⟨last,reached,rfl⟩:=called
  exact program setup wire sign input inside provider close work (trace,(wordBefore,before)) past aligned last reached


private theorem literal_mem (candidate : Secret) (message : Message) :
    candidate∈literals (.inr (.inr message)) ↔
      ∃key,input message=some key ∧inside key.head=true ∧key.word=.literal candidate := by
  cases formed : input message with
  | none=>simp [RegistrationNativePlatformRecordPartnerExposureFirstHit.literals,formed]
  | some key=>
    cases word : key.word <;>cases insideHeld : inside key.head <;>
      simp only [RegistrationNativePlatformRecordPartnerExposureFirstHit.literals,formed,insideHeld,word,
        Bool.false_eq_true,ite_false,ite_true,List.not_mem_nil,List.mem_singleton,Option.some.injEq,
        exists_eq_left',false_and,true_and,reduceCtorEq,and_false]
    simp only [eq_comm,RegistrationNativeSecretWord.Word.literal.injEq]

/-- Membership in the recorded literal list is exactly a genuine protected literal demand in the same source trace. -/
theorem mem_trace (candidate : Secret) (events : List RegistrationNativeSecretWordFrontendTrace.Event) :
    candidate∈traceLiterals (n:=n) input inside events ↔
      ∃message key,RegistrationNativeSecretWordFrontendTrace.Event.demand message∈events ∧
        input message=some key ∧inside key.head=true ∧key.word=.literal candidate := by
  simp only [traceLiterals,List.mem_flatMap]
  constructor
  · rintro ⟨event,present,member⟩
    cases event with
    | demand message=>
      obtain ⟨key,formed,insideHeld,word⟩:=(literal_mem input inside candidate message).mp member
      exact ⟨message,key,present,formed,insideHeld,word⟩
    | _=>simp only [List.not_mem_nil] at member
  · rintro ⟨message,key,present,formed,insideHeld,word⟩
    exact ⟨.demand message,present,(literal_mem input inside candidate message).mpr ⟨key,formed,insideHeld,word⟩⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureQueryLog

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureQueryLog.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureQueryLog.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureQueryLog.trace_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureQueryLog.trace_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureQueryLog.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureQueryLog.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureQueryLog.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureQueryLog.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureQueryLog.mem_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureQueryLog.mem_trace
