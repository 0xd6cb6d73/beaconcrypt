-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginInitializedCallback
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedAcceptedCover
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginTrackedProjection
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginStripEvents
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginConcreteCodec
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmSelectedPendingBound
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWarmKeys
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginTrackedEventCover
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftProtocol (ServiceSpec Control)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open RegistrationNativePlatformOriginJournalProgram (Front Calls Client)
variable {n : Nat} {I KemSK Platform Failure Reader Response Value View : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity)
    (env : RegistrationNativeHiddenStartup.Started source → RegistrationNativeEntropyInterface.Environment n Platform)
    (reserve : RegistrationNativeHiddenStartup.Started source → Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (route : RawCtxServerRouting.SenderDecoder)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : RegistrationNativeHiddenStartup.Started source → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (initial : RegistrationNativeHiddenStartup.Started source → Platform)
    (observe : RegistrationNativeHiddenStartup.Started source → Front n Platform → View)
local notation "concrete" => RegistrationNativeWire.ledgerCodec
  (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire)
local notation "compile" => RegistrationNativePlatformOriginStartupTails.compile concrete route
local notation "world" => RegistrationNativePlatformOriginStartupLedgerTails.world setup source ensureInit identityIndex serverKeyId identity env reserve concrete bounds mode work initial
local notation "front(" born ")" => RegistrationNativeObservedStageTrace.handler (observe born)
  (RegistrationNativePlatformOriginFreeFullTrace.frontend (RegistrationNativeEntropyPort.environment (env born))
    (RegistrationNativePlatformGatedNativeEntropy.reserveLift (reserve born)) setup.source.crypto concrete route serverKeyId bounds)
local notation "X" => (Client n Platform Value × Option (Option (RegistrationNativePlatformOriginCallbackFreeStop.PublicCall PqxdhDeploymentInterface.FullSpec) × Value)) × Calls View
local notation "S" => (Front n Platform × Calls View) × CtxPrivate n
local notation "counted" => RegistrationNativePlatformOriginSendCallbackBudget.Sending
local notation "compiled(" born ")" => RegistrationNativePlatformOriginSelectedProgram.compiled source mode work born
local notation "before(" born "," shell "," control "," privateBefore ")" =>
  (((PqxdhDeploymentSecrecy.Ledger.empty,((([],initial born),shell),control)),[]),privateBefore)


/-- A forged restored-ledger receive raises the bounded callback statistic on this exact tracked source run. -/
theorem tracked (modes : Label n→KeyMode) (ideal : ∀label,modes label≠.real) (replace : Pqxdh.Bytes→Pqxdh.Bytes)
    (born : RegistrationNativeHiddenStartup.Started source) (shell : CborRecordWorldClient.Shell)
    (control : Control n) (privateBefore : CtxPrivate n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (empty : ∀label,(privateBefore.keys label).1.successfulSeals=[])
    (result : RegistrationNativePlatformOriginCallbackTrace.Result PqxdhDeploymentInterface.FullSpec S Value)
    (supported : result∈support (RegistrationNativePlatformOriginCallbackTrace.track counted
      (QueryImpl.Stateful.link (front(born)) (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup concrete))
      (compiled(born)) (before(born,shell,control,privateBefore))))
    (consistent : ∀label entry,entry∈(result.2.2.2.keys label).1.successfulSeals→entry.input.context.ad.seq=label.position+1)
    (bad : PqxdhRecordLiftIdeal.UnpublishedAccept concrete route (PqxdhRecordLiftIdeal.ctxView
      (RegistrationNativePlatformOriginJournalProgram.plain born.created (result.2.1,result.2.2.1.1),result.2.2.2))) :
    ∃current∈result.1,RegistrationNativePlatformOriginSelectedPendingBound.event source route born current result.2 := by
  obtain ⟨calls,_actual,projected,filtered⟩:=RegistrationNativePlatformOriginTrackedProjection.tracked
    (RegistrationNativeEntropyPort.environment (env born)) (RegistrationNativePlatformGatedNativeEntropy.reserveLift (reserve born))
    setup.source.crypto concrete route serverKeyId bounds (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup concrete)
    (observe born) counted (compiled(born)) (before(born,shell,control,privateBefore)) result supported
  simp only [PqxdhRecordLiftIdeal.UnpublishedAccept,PqxdhRecordLiftIdeal.ctxView,PqxdhRecordLiftIdeal.viewOf,
    RegistrationNativePlatformOriginJournalProgram.plain,RegistrationNativeRecordPackage.encode,Option.map_some,Option.mem_some_iff] at bad
  obtain ⟨value,rfl,leading,receivedEntry,later,split,forged⟩:=bad
  rw [RegistrationNativeEntropyRestore.ledger_transcript] at split
  obtain ⟨fullLeading,original,fullLater,fullSplit,_beforeMap,_sameReceived,fullForged⟩:=
    RegistrationNativePlatformOriginStripEvents.forged concrete route _ _ leading receivedEntry later split forged
  obtain ⟨label,sealEntry,receiver,raw,opened,handle,received,routed,hidden,direction,position,
    current,pre,post,firstSplit,sending,absent,inserted,refused⟩:=
    RegistrationNativePlatformOriginErasedAcceptedCover.cover modes ideal replace setup concrete route
      RegistrationNativePlatformOriginConcreteCodec.readback
      (RegistrationNativeEntropyPort.environment (env born)) (RegistrationNativePlatformGatedNativeEntropy.reserveLift (reserve born))
      serverKeyId bounds _ _ _ projected safe empty consistent fullLeading original fullLater fullSplit fullForged
  have currentMember : current∈calls.map (RegistrationNativeObservedStageTrace.mapCall RegistrationNativePlatformOriginTrackedProjection.forget) := by
    rw [firstSplit]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self))
  obtain ⟨originalCall,member,same⟩:=List.mem_map.mp currentMember
  subst current
  change counted originalCall.query at sending
  have countedMember : originalCall∈result.1 := by
    rw [←filtered,List.mem_filter]
    exact ⟨member,decide_eq_true sending⟩
  refine ⟨originalCall,countedMember,refused,label,⟨sealEntry,absent,inserted⟩,?_⟩
  change PqxdhRecordFactsOriginResumeConsumer.AcceptedTarget label route
    (RegistrationNativePlatformOriginJournalProgram.plain born.created (result.2.1,result.2.2.1.1),result.2.2.2)
  have originalMember : original∈result.2.2.1.1.1.transcript := by
    rw [fullSplit]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  obtain ⟨decoded,decodedMember,decodedReceived⟩:=RegistrationNativePlatformOriginStripEvents.received _ original originalMember receiver raw opened received
  refine ⟨_,rfl,decoded,?_,receiver,raw,opened,handle,decodedReceived,routed,hidden,direction,position⟩
  change decoded∈(RegistrationNativeEntropyRestore.ledger result.2.2.1.1.1).ledger.transcript
  rw [RegistrationNativeEntropyRestore.ledger_transcript]
  exact decodedMember
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginTrackedEventCover
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginTrackedEventCover.tracked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginTrackedEventCover.tracked
