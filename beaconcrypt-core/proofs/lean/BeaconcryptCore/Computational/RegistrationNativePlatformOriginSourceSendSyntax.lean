-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerSendSyntax
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeCoin
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedFields
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceSendSyntax
open PqxdhRecordLiftProtocol (ServiceSpec Control)
open PqxdhRecordLiftInterface (Environment)
open PqxdhServerAuthExperiment (Codec)
open RegistrationNativePlatformOriginReserveContinuationBound (continued)
open RegistrationNativePlatformOriginNativeTails (source ReplyEnvelope)
variable {n : Nat} {Platform Failure Reader Response A B : Type}
abbrev Reply := Option RawCtxSourceSend.Encrypted

inductive Form (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure)) (read : A → Reply) :
    OracleComp (ServiceSpec n) A → Prop
  | quiet (work : OracleComp (ServiceSpec n) A)
      (noSeal : work.AllQueriesSatisfy RegistrationNativePlatformOriginErasedFields.BaseOnly) : Form reserve read work
  | hidden (pending : PqxdhRecordLiftProtocol.Sealing n) (tag : PqxdhDeploymentInterface.FrameTag)
      (beforeP : Platform) (after : Reply → Platform → A) (same : ∀output state,read (after output state)=output) :
      Form reserve read (do
        let _←((ServiceSpec n).query (.lookup pending.material) :OracleComp (ServiceSpec n) _)
        let output←((ServiceSpec n).query (.sealing pending) :OracleComp (ServiceSpec n) _)
        continued reserve (fun output state=>pure (after output state)) beforeP tag output)
  | coin (amount : Nat) (next : Fin (amount+1) → OracleComp (ServiceSpec n) A)
      (later : ∀value,Form reserve read (next value)) :
      Form reserve read (RegistrationNativePlatformOriginGateSource.coins amount >>=next)

/-- Pure result transport retains the same literal hidden-send reply and every independent experiment coin. -/
theorem Form.map {reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure)} {read : A → Reply}
    {work : OracleComp (ServiceSpec n) A} (form : Form reserve read work)
    (change : A → B) (afterRead : B → Reply) (same : ∀value,afterRead (change value)=read value) :
    Form reserve afterRead (change <$>work) := by
  induction form with
  | quiet work noSeal=>exact .quiet _ (by simpa only [AllQueriesSatisfy,isQueryBound_map_iff] using noSeal)
  | hidden pending tag beforeP after observed=>
    have equal : change <$> (do
      let _←((ServiceSpec n).query (.lookup pending.material) :OracleComp (ServiceSpec n) _)
      let output←((ServiceSpec n).query (.sealing pending) :OracleComp (ServiceSpec n) _)
      continued reserve (fun output state=>pure (after output state)) beforeP tag output) =
      (do let _←((ServiceSpec n).query (.lookup pending.material) :OracleComp (ServiceSpec n) _)
          let output←((ServiceSpec n).query (.sealing pending) :OracleComp (ServiceSpec n) _)
          continued reserve (fun output state=>pure (change (after output state))) beforeP tag output) := by
      simp only [continued,map_bind,map_pure]
    rw [equal]
    exact .hidden pending tag beforeP _ (fun output state=>(same _).trans (observed output state))
  | coin amount next _later ih=>
    rw [map_bind]
    exact .coin amount _ ih

private theorem source_pure (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure)) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (value : A) (beforeP : Platform)
    (shell : CborRecordWorldClient.Shell) (control : Control n) :
    source env reserve codec route (pure value) beforeP shell control=pure (((value,beforeP),shell),control) := by
  simp only [source,simulateQ_pure,StateT.run_pure]

private theorem source_bind (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure)) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp PqxdhDeploymentInterface.Spec A)
    (next : A → OracleComp PqxdhDeploymentInterface.Spec B) (beforeP : Platform)
    (shell : CborRecordWorldClient.Shell) (control : Control n) :
    source env reserve codec route (work >>=next) beforeP shell control=
      (do let result←source env reserve codec route work beforeP shell control
          source env reserve codec route (next result.1.1.1) result.1.1.2 result.1.2 result.2) := by
  simp only [source,simulateQ_bind,StateT.run_bind]

private theorem source_map (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure)) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (change : A → B) (work : OracleComp PqxdhDeploymentInterface.Spec A)
    (beforeP : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n) :
    source env reserve codec route (change <$>work) beforeP shell control=
      (fun result=>(((change result.1.1.1,result.1.1.2),result.1.2),result.2)) <$>
        source env reserve codec route work beforeP shell control := by
  simp only [source,simulateQ_map,StateT.run_map]

private theorem weighted_zero {J X : Type} {spec : OracleSpec J} (cost : J → Nat)
    (work : OracleComp spec X) (bounded : PqxdhRecordLiftCtxProgramBounds.Weighted cost work 0) :
    work.AllQueriesSatisfy (fun query=>cost query=0) := by
  induction work using OracleComp.inductionOn with
  | pure value=>trivial
  | query_bind query next ih=>
    rw [PqxdhRecordLiftCtxProgramBounds.Weighted,isQueryBound_query_bind_iff] at bounded
    rw [allQueriesSatisfy_query_bind_iff]
    refine ⟨by omega,?_⟩
    intro reply
    apply ih reply
    change (next reply).IsQueryBound 0 (fun query available=>cost query≤available) (fun query available=>available-cost query)
    simpa only [Nat.zero_sub] using bounded.2 reply

private theorem raw_bill : (PqxdhRecordLiftCtxBills.worldBill .raw : (PqxdhRecordLiftInterface.WorldSpec n).Domain → Nat)=
    fun query=>if PqxdhRecordLiftBudget.WorldRecord .raw query then 1 else 0 := by
  funext query
  rcases query with created|(effect|record)
  · rfl
  · cases effect <;>rfl
  · rcases record with (send|raw)|⟨owner,plaintext|raw⟩ <;>rfl

private theorem send_no_raw (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure)) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (handle : PqxdhDeploymentInterface.Handle) (message : Pqxdh.Bytes)
    (beforeP : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n) :
    (source env reserve codec route (PqxdhDeploymentSecrecy.send handle message) beforeP shell control).AllQueriesSatisfy
      (fun query=>PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=0) := by
  have first : ((simulateQ (RegistrationNativePlatformGatedRecordInterface.native env reserve)
      (PqxdhDeploymentSecrecy.send handle message)).run beforeP).IsQueryBoundP (PqxdhRecordLiftBudget.WorldRecord .raw) 0 := by
    cases handle with
    | peer keyId=>simpa [PqxdhDeploymentSecrecy.send,PqxdhRecordLiftBudget.NativeRecord,PqxdhDeploymentCompileBudget.commandKind] using RegistrationNativePlatformGatedRecordBounds.native_step env reserve .raw (.inr (.serverSend keyId message)) beforeP
    | owner index=>simpa [PqxdhDeploymentSecrecy.send,PqxdhRecordLiftBudget.NativeRecord,PqxdhDeploymentCompileBudget.commandKind] using RegistrationNativePlatformGatedRecordBounds.native_step env reserve .raw (.inr (.beaconSend index message)) beforeP
  have cursor:=CborRecordWorldClient.client_bound _ (PqxdhRecordLiftBudget.WorldRecord .raw) 0 first shell
  simp only [CborRecordWorldClient.client,isQueryBoundP_map_iff] at cursor
  have weight:=PqxdhRecordLiftCtxProgramBounds.weighted_indicator (PqxdhRecordLiftBudget.WorldRecord .raw) 1 _ 0 cursor
  simp only [Nat.one_mul] at weight
  rw [←raw_bill] at weight
  have compiled:=PqxdhRecordLiftCtxProgramBounds.weighted_run (PqxdhRecordLiftCtxBills.worldBill .raw)
    (PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw) (PqxdhRecordLiftProtocol.handler codec.frameRead route) _ 0 control weight
    (fun request current=>PqxdhRecordLiftCtxBills.handler_categories .raw codec.frameRead route request current)
  exact weighted_zero _ _ compiled

private theorem combine {work : OracleComp (ServiceSpec n) A}
    (quiet : work.AllQueriesSatisfy (fun query=>¬RegistrationNativePlatformOriginSourceTails.Sealing query))
    (noRaw : work.AllQueriesSatisfy (fun query=>PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=0)) :
    work.AllQueriesSatisfy RegistrationNativePlatformOriginErasedFields.BaseOnly := by
  induction work using OracleComp.inductionOn with
  | pure value=>trivial
  | query_bind query next ih=>
    rw [allQueriesSatisfy_query_bind_iff] at quiet noRaw ⊢
    refine ⟨?_,fun reply=>ih reply (quiet.2 reply) (noRaw.2 reply)⟩
    cases query
    all_goals first
      | exact False.elim (quiet.1 ⟨_,rfl⟩)
      | (have zero : (1:Nat)=0:=noRaw.1;omega)
      | trivial

private theorem send (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure)) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (handle : PqxdhDeploymentInterface.Handle) (message : Pqxdh.Bytes)
    (beforeP : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n) :
    Form reserve (fun result=>result.1.1.1)
      (source env reserve codec route (PqxdhDeploymentSecrecy.send handle message) beforeP shell control) := by
  have finish (form : ReplyEnvelope reserve beforeP
      (source env reserve codec route (PqxdhDeploymentSecrecy.send handle message) beforeP shell control)) :
      Form reserve (fun result=>result.1.1.1)
        (source env reserve codec route (PqxdhDeploymentSecrecy.send handle message) beforeP shell control) := by
    obtain ⟨pending,tag,advancedShell,advancedControl,equal⟩ :=form
    rw [equal]
    exact .hidden pending tag beforeP _ (fun _ _=>rfl)
  cases handle with
  | peer keyId=>
    rcases RegistrationNativePlatformOriginNativeTails.server_reply_form env reserve codec route beforeP shell control keyId message with quiet|form
    · exact .quiet _ (combine quiet (send_no_raw env reserve codec route _ _ beforeP shell control))
    · exact finish form
  | owner index=>
    rcases RegistrationNativePlatformOriginNativeTails.beacon_reply_form env reserve codec route beforeP shell control index message with quiet|form
    · exact .quiet _ (combine quiet (send_no_raw env reserve codec route _ _ beforeP shell control))
    · exact finish form

/-- The actual native source of a coin/refusal/single-send tree has only base coin prefixes and the one genuine hidden reserve envelope or a no-seal branch. -/
theorem compile (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure)) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (read : A → Reply) (work : OracleComp PqxdhDeploymentInterface.Spec A)
    (syntaxProof : RegistrationNativePlatformOriginLedgerSendSyntax.SendSyntax read work)
    (beforeP : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n) :
    Form reserve (fun result=>read result.1.1.1) (source env reserve codec route work beforeP shell control) := by
  induction syntaxProof generalizing beforeP shell control with
  | refused value absent=>
    rw [source_pure]
    exact .quiet _ (by trivial)
  | send handle message after same=>
    rw [source_map]
    exact (send env reserve codec route handle message beforeP shell control).map _ _ (fun result=>same result.1.1.1)
  | coin amount next _later ih=>
    rw [source_bind,RegistrationNativePlatformOriginNativeCoin.source,bind_map_left]
    exact .coin amount _ (fun reply=>ih reply beforeP shell control)

/-- Every actual full sending callback, including all test/fresh coins and failed gates, derives this source normal form internally. -/
theorem ledger (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure)) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (crypto : Pqxdh.Crypto) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (query : PqxdhDeploymentInterface.FullSpec.Domain)
    (sending : RegistrationNativePlatformOriginLedgerSendSyntax.Sending query) (before : PqxdhDeploymentSecrecy.Ledger)
    (beforeP : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n) :
    Form reserve (fun result=>RegistrationNativePlatformOriginLedgerSendSyntax.reply query result.1.1.1.1)
      (source env reserve codec route ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKeyId bounds query).run before) beforeP shell control) :=
  compile env reserve codec route _ _ (RegistrationNativePlatformOriginLedgerSendSyntax.ledger_syntax crypto codec serverKeyId bounds query sending before) beforeP shell control
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceSendSyntax

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceSendSyntax.Form.map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceSendSyntax.Form.map

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceSendSyntax.compile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceSendSyntax.compile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceSendSyntax.ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceSendSyntax.ledger
