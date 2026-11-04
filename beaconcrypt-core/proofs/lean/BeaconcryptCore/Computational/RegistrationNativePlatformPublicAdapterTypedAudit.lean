-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeStageTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterReply
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected
/-! One private annotation retains the typed callback journal and protected-origin flag on the same SDK packet. It preserves the original source object call and public result. The concrete dispatcher supplies its existing unmapped typed factory, not a new sampling operation or a whole audit correspondence premise. -/
open CoreModels OracleComp OracleSpec Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit
open RegistrationNativePlatformExtractedSdkPublic (TotalStep returned store)
open RegistrationNativeStageTrace (Call)
variable {I S A B : Type} {spec : OracleSpec I}

structure Audit (spec : OracleSpec I) (S : Type) where
  calls : List (Call spec S)
  bad : Bool

def empty : Audit spec S :=⟨[],false⟩

noncomputable def update (failure : ∀query,spec.Range query→S→Prop)
    (query : spec.Domain) (before : S) (reply : spec.Range query) (after : S) (prior : Audit spec S) : Audit spec S :=by
  classical
  exact ⟨prior.calls++[⟨query,before,reply,after⟩],prior.bad ||decide (failure query reply before)⟩

noncomputable def handler (implementation : QueryImpl spec (StateT S ProbComp))
    (failure : ∀query,spec.Range query→S→Prop) :QueryImpl spec (StateT (S×Audit spec S) ProbComp) :=
  fun query before=>(fun result=>(result.1,(result.2,update failure query before.1 result.1 result.2 before.2))) <$>
    (implementation query).run before.1

def journal (state : S×Audit spec S) : S×List (Call spec S) :=(state.1,state.2.calls)
def flag (state : S×Audit spec S) : S×Bool :=(state.1,state.2.bad)

noncomputable def badHandler (implementation : QueryImpl spec (StateT S ProbComp))
    (failure : ∀query,spec.Range query→S→Prop) :QueryImpl spec (StateT (S×Bool) ProbComp) :=by
  classical
  exact fun query before=>(fun result=>(result.1,(result.2,before.2 ||decide (failure query result.1 before.1)))) <$>
    (implementation query).run before.1

theorem journal_query (implementation : QueryImpl spec (StateT S ProbComp))
    (failure : ∀query,spec.Range query→S→Prop) (query : spec.Domain) (before : S×Audit spec S) :
    Prod.map id journal <$> (handler implementation failure query).run before=
      (RegistrationNativeStageTrace.handler implementation query).run (journal before) :=by
  simp only [handler,RegistrationNativeStageTrace.handler,StateT.run,Functor.map_map]
  rfl

theorem flag_query (implementation : QueryImpl spec (StateT S ProbComp))
    (failure : ∀query,spec.Range query→S→Prop) (query : spec.Domain) (before : S×Audit spec S) :
    Prod.map id flag <$> (handler implementation failure query).run before=
      (badHandler implementation failure query).run (flag before) :=by
  simp only [handler,badHandler,StateT.run,Functor.map_map]
  rfl

theorem journal_program (implementation : QueryImpl spec (StateT S ProbComp))
    (failure : ∀query,spec.Range query→S→Prop) (work : OracleComp spec A) (before : S×Audit spec S) :
    Prod.map id journal <$> (simulateQ (handler implementation failure) work).run before=
      (simulateQ (RegistrationNativeStageTrace.handler implementation) work).run (journal before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ journal (journal_query implementation failure) work before

theorem flag_program (implementation : QueryImpl spec (StateT S ProbComp))
    (failure : ∀query,spec.Range query→S→Prop) (work : OracleComp spec A) (before : S×Audit spec S) :
    Prod.map id flag <$> (simulateQ (handler implementation failure) work).run before=
      (simulateQ (badHandler implementation failure) work).run (flag before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ flag (flag_query implementation failure) work before

theorem native_program (implementation : QueryImpl spec (StateT S ProbComp))
    (failure : ∀query,spec.Range query→S→Prop) (work : OracleComp spec A) (before : S×Audit spec S) :
    Prod.map id Prod.fst <$> (simulateQ (handler implementation failure) work).run before=
      (simulateQ implementation work).run before.1 :=by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query current
  simp only [handler,StateT.run,Functor.map_map]
  exact id_map _

abbrev Private (objects : S→Type) (state : S×Audit spec S) :=objects state.1

noncomputable def lift (implementation : QueryImpl spec (StateT S ProbComp))
    (failure : ∀query,spec.Range query→S→Prop) (objects : S→Type)
    (query : spec.Domain) (before : S) (prior : Audit spec S)
    (call : TotalStep objects ((implementation query).run before)) :
    TotalStep (Private (spec:=spec) objects) ((handler implementation failure query).run (before,prior)) :={
  step:={
    Packet:=call.step.Packet
    sample:=call.step.sample
    sourceType:=call.step.sourceType
    sourceReply:=call.step.sourceReply
    sourceState:=fun packet=>(call.step.sourceState packet,
      update failure query before (call.step.native packet).1 (call.step.native packet).2 prior)
    sourceCall:=(fun packet=>(call.step.sourceReply packet,(call.step.sourceState packet,
      update failure query before (call.step.native packet).1 (call.step.native packet).2 prior))) <$>call.step.sample
    source_exact:=rfl
    native:=fun packet=>((call.step.native packet).1,((call.step.native packet).2,
      update failure query before (call.step.native packet).1 (call.step.native packet).2 prior))
    native_exact:=by
      have mapped:=congrArg (fun work=>(fun result=>(result.1,(result.2,update failure query before result.1 result.2 prior))) <$>work) call.step.native_exact
      simp only [Functor.map_map] at mapped
      exact mapped
    store:=call.step.store }
  observe:=call.observe
  normal:=call.normal
  reply:=call.reply }

theorem source_erasure (implementation : QueryImpl spec (StateT S ProbComp))
    (failure : ∀query,spec.Range query→S→Prop) (objects : S→Type)
    (query : spec.Domain) (before : S) (prior : Audit spec S)
    (call : TotalStep objects ((implementation query).run before)) :
    Prod.map id Prod.fst <$> (lift implementation failure objects query before prior call).step.sourceCall=call.step.sourceCall :=by
  simp only [lift,Functor.map_map,Prod.map,id_eq]
  exact call.step.source_exact

theorem store_base (implementation : QueryImpl spec (StateT S ProbComp))
    (failure : ∀query,spec.Range query→S→Prop) (objects : S→Type)
    (query : spec.Domain) (before : S) (prior : Audit spec S)
    (call : TotalStep objects ((implementation query).run before))
    (packet : {value //value∈support call.step.sample}) :
    store (lift implementation failure objects query before prior call) packet=store call packet :=rfl

noncomputable def silent (objects : S→Type) (prior : Audit spec S)
    {model : ProbComp (A×S)} (call : TotalStep objects model) :
    TotalStep (Private (spec:=spec) objects) ((fun result=>(result.1,(result.2,prior))) <$>model) :={
  step:={
    Packet:=call.step.Packet
    sample:=call.step.sample
    sourceType:=call.step.sourceType
    sourceReply:=call.step.sourceReply
    sourceState:=fun packet=>(call.step.sourceState packet,prior)
    sourceCall:=Prod.map id (fun state=>(state,prior)) <$>call.step.sourceCall
    source_exact:=by
      have mapped:=congrArg (fun work=>Prod.map id (fun state=>(state,prior)) <$>work) call.step.source_exact
      simp only [Functor.map_map] at mapped
      exact mapped
    native:=fun packet=>((call.step.native packet).1,((call.step.native packet).2,prior))
    native_exact:=by
      have mapped:=congrArg (fun work=>(fun result=>(result.1,(result.2,prior))) <$>work) call.step.native_exact
      simp only [Functor.map_map] at mapped
      exact mapped
    store:=call.step.store }
  observe:=call.observe
  normal:=call.normal
  reply:=call.reply }

theorem silent_source (objects : S→Type) (prior : Audit spec S)
    {model : ProbComp (A×S)} (call : TotalStep objects model) :
    Prod.map id Prod.fst <$> (silent objects prior call).step.sourceCall=call.step.sourceCall :=by
  simp only [silent,Functor.map_map,Prod.map,id_eq,Prod.eta]
  exact id_map _

noncomputable def transport {objects : S→Type} {left right : ProbComp (A×S)}
    (same : left=right) (call : TotalStep objects left) :TotalStep objects right :=same ▸call

theorem path (implementation : QueryImpl spec (StateT S ProbComp))
    (failure : ∀query,spec.Range query→S→Prop) (work : OracleComp spec A) (before : S)
    (result : A×(S×Audit spec S))
    (supported : result∈support ((simulateQ (handler implementation failure) work).run (before,empty))) :
    RegistrationNativeStageTrace.Path implementation before result.2.2.calls result.2.1 :=by
  have mapped : Prod.map id journal result∈support
      (Prod.map id journal <$> (simulateQ (handler implementation failure) work).run (before,empty)) :=
    by
      rw [support_map]
      exact Set.mem_image_of_mem (Prod.map id journal) supported
  rw [journal_program] at mapped
  exact RegistrationNativeStageTrace.path implementation work before (Prod.map id journal result) mapped

variable [material : BeaconcryptCore.Refinement.PublicWrapperPlatform.Material]
variable [platform : BeaconcryptCore.Refinement.PublicWrapperPlatform.Platform]
variable [ed : BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]
variable {n : Nat} {KemSK R P : Type}

theorem physical (implementation : QueryImpl spec (StateT S ProbComp))
    (failure : ∀query,spec.Range query→S→Prop) (objects : S→Type)
    (query : spec.Domain) (before : S) (prior : Audit spec S)
    (call : TotalStep objects ((implementation query).run before))
    (observe : spec.Range query→B)
    (project : ∀current,objects current→RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw (fun current held=>project current.1 held)
      (RegistrationNativePlatformPublicAdapterReply.map observe (lift implementation failure objects query before prior call))=
      RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw project (RegistrationNativePlatformPublicAdapterReply.map observe call) :=rfl

theorem physical_silent (objects : S→Type) (prior : Audit spec S)
    {model : ProbComp (A×S)} (call : TotalStep objects model) (observe : A→B)
    (project : ∀current,objects current→RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw (fun current held=>project current.1 held)
      (RegistrationNativePlatformPublicAdapterReply.map observe (silent objects prior call))=
      RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw project (RegistrationNativePlatformPublicAdapterReply.map observe call) :=rfl

theorem physical_transport {objects : S→Type} {left right : ProbComp (A×S)}
    (same : left=right) (call : TotalStep objects left) (observe : A→B)
    (project : ∀current,objects current→RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw project (RegistrationNativePlatformPublicAdapterReply.map observe (transport same call))=
      RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw project (RegistrationNativePlatformPublicAdapterReply.map observe call) :=by
  cases same
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit.journal_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit.journal_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit.flag_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit.flag_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit.native_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit.lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit.lift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit.source_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit.source_erasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit.store_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit.store_base

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit.silent' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit.silent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit.silent_source' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit.silent_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit.path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit.physical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit.physical

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit.physical_silent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit.physical_silent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit.physical_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit.physical_transport
