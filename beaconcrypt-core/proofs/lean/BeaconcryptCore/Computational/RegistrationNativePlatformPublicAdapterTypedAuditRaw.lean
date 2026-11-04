-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAudit
import BeaconcryptCore.Computational.RegistrationNativeFullCompiler
/-! Raw parsing is an exact zero-or-one typed-query adapter. Malformed constructor pins and Init bytes produce no typed audit entry, while build conversion refusal and every finish parse result still execute their actual typed lifecycle query. Both audit projections follow that same adapter and full secrecy-ledger compilation. -/
open CoreModels OracleComp OracleSpec Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw
open RegistrationNativePlatformPublicAdapterTypedAudit (Audit handler journal flag badHandler)
open RegistrationNativeRawAdapter (TypedSpec resultOption responseOption)
variable {I S A : Type} {spec : OracleSpec I}

inductive Form (spec : OracleSpec I) (A : Type) where
  | pure (value : A)
  | query (selected : spec.Domain) (observe : spec.Range selected→A)

def Form.program (form : Form spec A) : OracleComp spec A :=
  match form with
  | .pure value=>Pure.pure value
  | .query selected observe=>observe <$>spec.query selected

def form (wire : RegistrationNativeWire.Wire) (query : RegistrationNativeInterface.Spec.Domain) :
    Form TypedSpec (RegistrationNativeInterface.Spec.Range query) :=
  match query with
  | .inl coin=>.query (.inl coin) id
  | .inr (.create edPin mlPin keyId)=>
    match PqxdhDeploymentInterface.parsePin edPin,RegistrationNativeWire.parseMldsaPin mlPin with
    | some edPin,some mlPin=>.query (.inr (.create edPin mlPin keyId)) resultOption
    | _,_=>.pure none
  | .inr (.bundle owner)=>.query (.inr (.bundle owner)) resultOption
  | .inr (.accept bytes)=>
    match RegistrationNativeWire.readInit wire bytes with
    | none=>.pure none
    | some packet=>.query (.inr (.accept packet)) resultOption
  | .inr (.build session payload)=>.query (.inr (.build session (RegistrationNativeRawAdapter.application payload))) responseOption
  | .inr (.finish owner bytes)=>.query (.inr (.finish owner (RegistrationNativeWire.readResponse wire bytes))) resultOption
  | .inr (.hmac key message)=>.query (.inr (.hmac key message)) id
  | .inr (.hash bytes)=>.query (.inr (.hash bytes)) id
  | .inr (.serverSend key plaintext)=>.query (.inr (.serverSend key plaintext)) id
  | .inr (.serverRaw bytes)=>.query (.inr (.serverRaw bytes)) id
  | .inr (.beaconSend owner plaintext)=>.query (.inr (.beaconSend owner plaintext)) id
  | .inr (.beaconRaw owner bytes)=>.query (.inr (.beaconRaw owner bytes)) id

theorem form_source (wire : RegistrationNativeWire.Wire) (query : RegistrationNativeInterface.Spec.Domain) :
    (form wire query).program=RegistrationNativeRawAdapter.adapter wire query :=by
  cases query with
  | inl coin=>rfl
  | inr command=>
    cases command with
    | create edPin mlPin keyId=>
      cases edParsed:PqxdhDeploymentInterface.parsePin edPin <;>cases mlParsed:RegistrationNativeWire.parseMldsaPin mlPin <;>
        simp only [form,RegistrationNativeRawAdapter.adapter,edParsed,mlParsed,Form.program]
    | accept bytes=>cases parsed:RegistrationNativeWire.readInit wire bytes <;>
        simp only [form,RegistrationNativeRawAdapter.adapter,parsed,Form.program]
    | _=>rfl

theorem accept_malformed (wire : RegistrationNativeWire.Wire) (bytes : Pqxdh.Bytes)
    (malformed : RegistrationNativeWire.readInit wire bytes=none) :
    form wire (.inr (.accept bytes))=.pure none :=by
  simp only [form,malformed]

theorem create_malformed (wire : RegistrationNativeWire.Wire) (edPin mlPin : Pqxdh.Bytes) (key : U64)
    (malformed : PqxdhDeploymentInterface.parsePin edPin=none ∨RegistrationNativeWire.parseMldsaPin mlPin=none) :
    form wire (.inr (.create edPin mlPin key))=.pure none :=by
  rcases malformed with bad | bad
  · simp only [form,bad]
  · simp only [form,bad]
    cases PqxdhDeploymentInterface.parsePin edPin <;>rfl

theorem build_single (wire : RegistrationNativeWire.Wire) (session : Nat) (payload : Option Pqxdh.Bytes) :
    form wire (.inr (.build session payload))=
      .query (.inr (.build session (RegistrationNativeRawAdapter.application payload))) responseOption :=rfl

theorem finish_single (wire : RegistrationNativeWire.Wire) (owner : Nat) (bytes : Pqxdh.Bytes) :
    form wire (.inr (.finish owner bytes))=
      .query (.inr (.finish owner (RegistrationNativeWire.readResponse wire bytes))) resultOption :=rfl

theorem query (wire : RegistrationNativeWire.Wire) (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (failure : ∀query,TypedSpec.Range query→S→Prop) (selected : RegistrationNativeInterface.Spec.Domain)
    (before : S×Audit TypedSpec S) :
    (RegistrationNativeRawAdapter.handler wire (handler implementation failure) selected).run before=
      match form wire selected with
      | .pure value=>pure (value,before)
      | .query typed observe=>Prod.map observe id <$> (handler implementation failure typed).run before :=by
  unfold RegistrationNativeRawAdapter.handler
  rw [QueryImpl.apply_compose]
  rw [←form_source wire selected]
  cases chosen:form wire selected <;>
    simp only [Form.program,simulateQ_pure,simulateQ_map,simulateQ_spec_query,StateT.run_pure,StateT.run_map]
  rfl

theorem journal_program (wire : RegistrationNativeWire.Wire) (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (failure : ∀query,TypedSpec.Range query→S→Prop) (work : OracleComp RegistrationNativeInterface.Spec A)
    (before : S×Audit TypedSpec S) :
    Prod.map id journal <$>
      (simulateQ (RegistrationNativeRawAdapter.handler wire (handler implementation failure)) work).run before=
      (simulateQ (RegistrationNativeStageTrace.handler implementation) (RegistrationNativeRawAdapter.compile wire work)).run (journal before) :=by
  rw [RegistrationNativeRawAdapter.program_native,RegistrationNativePlatformPublicAdapterTypedAudit.journal_program]

theorem flag_program (wire : RegistrationNativeWire.Wire) (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (failure : ∀query,TypedSpec.Range query→S→Prop) (work : OracleComp RegistrationNativeInterface.Spec A)
    (before : S×Audit TypedSpec S) :
    Prod.map id flag <$>
      (simulateQ (RegistrationNativeRawAdapter.handler wire (handler implementation failure)) work).run before=
      (simulateQ (badHandler implementation failure) (RegistrationNativeRawAdapter.compile wire work)).run (flag before) :=by
  rw [RegistrationNativeRawAdapter.program_native,RegistrationNativePlatformPublicAdapterTypedAudit.flag_program]

theorem path (wire : RegistrationNativeWire.Wire) (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (failure : ∀query,TypedSpec.Range query→S→Prop) (work : OracleComp RegistrationNativeInterface.Spec A) (before : S)
    (result : A×(S×Audit TypedSpec S))
    (supported : result∈support ((simulateQ (RegistrationNativeRawAdapter.handler wire (handler implementation failure)) work).run
      (before,RegistrationNativePlatformPublicAdapterTypedAudit.empty))) :
    RegistrationNativeStageTrace.Path implementation before result.2.2.calls result.2.1 :=by
  rw [RegistrationNativeRawAdapter.program_native] at supported
  exact RegistrationNativePlatformPublicAdapterTypedAudit.path implementation failure
    (RegistrationNativeRawAdapter.compile wire work) before result supported

theorem journal_full (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (failure : ∀query,TypedSpec.Range query→S→Prop) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : S×Audit TypedSpec S) :
    (fun result=>(result.1,(result.2.1,journal result.2.2))) <$>
      RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds (handler implementation failure) mode work before=
      RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds (RegistrationNativeStageTrace.handler implementation)
        mode work (journal before) :=by
  rw [RegistrationNativeFullCompiler.compile_run,RegistrationNativeFullCompiler.compile_run,Functor.map_map]
  have mapped:=congrArg (fun tree=>(fun result=>(result.1.1,(result.1.2,result.2))) <$>tree)
    (RegistrationNativePlatformPublicAdapterTypedAudit.journal_program implementation failure
      (RegistrationNativeFullCompiler.compile crypto wire serverKeyId bounds mode work) before)
  simp only [Functor.map_map] at mapped
  exact mapped

theorem flag_full (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (failure : ∀query,TypedSpec.Range query→S→Prop) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : S×Audit TypedSpec S) :
    (fun result=>(result.1,(result.2.1,flag result.2.2))) <$>
      RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds (handler implementation failure) mode work before=
      RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds (badHandler implementation failure)
        mode work (flag before) :=by
  rw [RegistrationNativeFullCompiler.compile_run,RegistrationNativeFullCompiler.compile_run,Functor.map_map]
  have mapped:=congrArg (fun tree=>(fun result=>(result.1.1,(result.1.2,result.2))) <$>tree)
    (RegistrationNativePlatformPublicAdapterTypedAudit.flag_program implementation failure
      (RegistrationNativeFullCompiler.compile crypto wire serverKeyId bounds mode work) before)
  simp only [Functor.map_map] at mapped
  exact mapped

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw.form_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw.form_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw.accept_malformed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw.accept_malformed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw.create_malformed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw.create_malformed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw.build_single' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw.build_single

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw.finish_single' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw.finish_single

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw.journal_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw.journal_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw.flag_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw.flag_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw.path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw.journal_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw.journal_full

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw.flag_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw.flag_full
