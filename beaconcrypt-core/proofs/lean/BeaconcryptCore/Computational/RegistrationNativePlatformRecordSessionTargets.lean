-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSessionEvents
import BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonical
import BeaconcryptCore.Computational.RegistrationNativePrekeyEvents
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargets
open PqxdhServerAuthExperiment (Codec)
open PqxdhDeploymentInterface (Handle Entry Budget Mode FreshBounds)
open PqxdhDeploymentHeadlineEvents (Direction)
variable {Reader Response Value State : Type}

inductive Kind where
  | origin (direction : Direction)
  | receiver
  | sender

def publicObservation (value : Value × RegistrationNativeLedger.State)
    (produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame)) :
    PqxdhDeploymentKemTransfer.Observed Value := (value.1,value.2.ledger,produced)

def Witness (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKeyId : U64) (budget : Budget)
    (route : RawCtxServerRouting.SenderDecoder) (kind : Kind)
    (target : Fin budget.accept × Fin budget.capacity) (transcript before : List Entry) (entry : Entry) : Prop :=
  match kind with
  | .origin direction=>RegistrationNativeSessionEvents.ForgedAtCE crypto codec serverKeyId budget route direction target transcript before entry
  | .receiver=>RegistrationNativeSessionEvents.UksReceiverAt crypto codec serverKeyId budget route target transcript entry
  | .sender=>RegistrationNativeSessionEvents.UksSenderAt crypto codec serverKeyId budget route target transcript entry

def Failure (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKeyId : U64) (budget : Budget)
    (route : RawCtxServerRouting.SenderDecoder) (kind : Kind)
    (value : Value × RegistrationNativeLedger.State)
    (produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame)) : Prop :=
  match kind with
  | .origin direction=>RegistrationNativeSessionEvents.OriginFailure crypto codec serverKeyId budget route direction (publicObservation value produced)
  | .receiver=>RegistrationNativeSessionEvents.UksReceiverFailure crypto codec serverKeyId budget route (publicObservation value produced)
  | .sender=>RegistrationNativeSessionEvents.UksSenderFailure crypto codec serverKeyId budget route (publicObservation value produced)

def At (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64) (budget : Budget)
    (route : RawCtxServerRouting.SenderDecoder) (kind : Kind)
    (target : Fin budget.accept × Fin budget.capacity) (value : Value × RegistrationNativeLedger.State) : Prop :=
  ∃before entry after sessionTarget,
    value.2.ledger.transcript=before++entry::after ∧
    Witness crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId budget route kind sessionTarget value.2.ledger.transcript before entry ∧
    sessionTarget.2=target.2 ∧
    RegistrationNativeParsedTargetCanonical.AcceptedAt wire value.2.transcript sessionTarget.1.val target.1.val

open Classical in
noncomputable def event (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64) (budget : Budget)
    (route : RawCtxServerRouting.SenderDecoder) (kind : Kind)
    (target : Fin budget.accept × Fin budget.capacity) (value : Value × RegistrationNativeLedger.State)
    (_produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame))
    (_raw : PqxdhRecordLiftWorld.RawCounters) : Bool :=
  decide (At crypto wire serverKeyId budget route kind target value)

/-- Every original origin/UKS witness retains its actual designated handle and successful session coordinate. -/
theorem witness_designated (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKeyId : U64) (budget : Budget)
    (route : RawCtxServerRouting.SenderDecoder) (kind : Kind)
    (target : Fin budget.accept × Fin budget.capacity) (transcript before : List Entry) (entry : Entry)
    (witness : Witness crypto codec serverKeyId budget route kind target transcript before entry) :
    ∃handle,PqxdhDeploymentTranscript.designateIn crypto codec serverKeyId budget transcript handle=some target := by
  cases kind with
  | origin direction=>
    obtain ⟨receiver,raw,opened,handle,frame,_received,_routed,_direction,designated,_decoded,_unpublished⟩:=witness
    exact ⟨handle,designated⟩
  | receiver=>
    obtain ⟨receiver,raw,opened,keyId,sender,frame,_received,_routed,_decoded,_published,designated,_unrelated⟩:=witness
    exact ⟨.peer keyId,designated⟩
  | sender=>
    obtain ⟨owner,encrypted,frame,_published,_decoded,designated,_other⟩:=witness
    exact ⟨.owner owner,designated⟩

/-- The original corrected public failure has a concrete witness in its SAME complete ledger; no test/fresh eligibility is introduced. -/
theorem failure_witness (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKeyId : U64) (budget : Budget)
    (route : RawCtxServerRouting.SenderDecoder) (kind : Kind)
    (value : Value × RegistrationNativeLedger.State)
    (produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame))
    (failed : Failure crypto codec serverKeyId budget route kind value produced) :
    ∃before entry after target,value.2.ledger.transcript=before++entry::after ∧
      Witness crypto codec serverKeyId budget route kind target value.2.ledger.transcript before entry := by
  cases kind with
  | origin direction=>
    obtain ⟨before,entry,after,split,target,witness⟩:=failed
    exact ⟨before,entry,after,target,split,witness⟩
  | receiver=>
    obtain ⟨entry,member,target,witness⟩:=failed
    obtain ⟨before,after,split⟩:=List.append_of_mem member
    exact ⟨before,entry,after,target,split,witness⟩
  | sender=>
    obtain ⟨entry,member,target,witness⟩:=failed
    obtain ⟨before,after,split⟩:=List.append_of_mem member
    exact ⟨before,entry,after,target,split,witness⟩

/-- Actual canonical public designation determines a bounded parsed-accept selector while preserving the DISTINCT successful session handle and final owner. -/
theorem designated_target (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (bounds : FreshBounds) (typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT State ProbComp))
    (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (bounded : RegistrationNativeInterface.Respects budget work) (before : State)
    (observed : RegistrationNativeEvents.Observed Value State)
    (supported : observed∈support (RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds typed mode work before))
    (handle : Handle) (sessionTarget : Fin budget.accept × Fin budget.capacity)
    (designated : PqxdhDeploymentTranscript.designateIn crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId budget
      observed.2.1.ledger.transcript handle=some sessionTarget) :
    ∃target : Fin budget.accept × Fin budget.capacity,target.2=sessionTarget.2 ∧
      RegistrationNativeParsedTargetCanonical.AcceptedAt wire observed.2.1.transcript sessionTarget.1.val target.1.val := by
  have consistent:=RegistrationNativeFullCompiler.ledger_projection crypto wire serverKeyId bounds typed mode work before observed supported
  have actual:=designated
  rw [consistent] at actual
  obtain ⟨parsed,accepted⟩:=RegistrationNativeParsedTargetCanonical.designated_first crypto wire serverKeyId budget _ handle sessionTarget actual
  have smaller:=RegistrationNativeParsedTargetCaps.accepted_lt wire _ sessionTarget.1.val parsed
    (RegistrationNativeParsedTargetCanonical.accepted_original wire _ sessionTarget.1.val parsed accepted)
  have capped:=RegistrationNativeParsedTargetCaps.run_accepts crypto wire serverKeyId bounds typed mode work budget bounded before observed supported
  exact ⟨(⟨parsed,Nat.lt_of_lt_of_le smaller capped⟩,sessionTarget.2),rfl,accepted⟩

/-- Broad corrected origin and both UKS events are covered by the SAME original parsed-accept times owner product. Every failed history and public alias is retained. -/
theorem selected (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (bounds : FreshBounds) (typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT State ProbComp))
    (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (bounded : RegistrationNativeInterface.Respects budget work) (before : State)
    (observed : RegistrationNativeEvents.Observed Value State)
    (supported : observed∈support (RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds typed mode work before))
    (route : RawCtxServerRouting.SenderDecoder) (kind : Kind)
    (produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame))
    (failed : Failure crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId budget route kind (observed.1,observed.2.1) produced) :
    ∃target : Fin budget.accept × Fin budget.capacity,At crypto wire serverKeyId budget route kind target (observed.1,observed.2.1) := by
  obtain ⟨priorList,entry,suffix,sessionTarget,split,witness⟩:=failure_witness crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId budget route kind _ produced failed
  obtain ⟨handle,designated⟩:=witness_designated crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId budget route kind sessionTarget _ priorList entry witness
  obtain ⟨target,owner,accepted⟩:=designated_target crypto wire serverKeyId bounds typed mode work budget bounded before observed supported handle sessionTarget designated
  exact ⟨target,priorList,entry,suffix,sessionTarget,split,witness,owner.symm,accepted⟩
/-- Regrouping by the parsed selector leaves the original public failure and successful-session counterpart untouched. -/
theorem at_original (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64) (budget : Budget)
    (route : RawCtxServerRouting.SenderDecoder) (kind : Kind)
    (target : Fin budget.accept × Fin budget.capacity) (value : Value × RegistrationNativeLedger.State)
    (produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame))
    (selected : At crypto wire serverKeyId budget route kind target value) :
    Failure crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId budget route kind value produced := by
  obtain ⟨priorList,entry,later,sessionTarget,split,witness,_owner,_accepted⟩:=selected
  have member : entry∈value.2.ledger.transcript:=by
    rw [split]
    exact List.mem_append_right _ (List.mem_cons_self)
  cases kind with
  | origin direction=>exact ⟨priorList,entry,later,split,sessionTarget,witness⟩
  | receiver=>exact ⟨entry,member,sessionTarget,witness⟩
  | sender=>exact ⟨entry,member,sessionTarget,witness⟩

/-- The full original corrected public event uses one parsed-accept by owner sum, with no successful-session/raw-ordinal identification and no eligibility restriction. -/
theorem probability (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (bounds : FreshBounds) (typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT State ProbComp))
    (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (bounded : RegistrationNativeInterface.Respects budget work) (before : State)
    (route : RawCtxServerRouting.SenderDecoder) (kind : Kind) :
    Pr{let observed←RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds typed mode work before}[
      Failure crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId budget route kind (observed.1,observed.2.1) []]≤
      ∑target:Fin budget.accept × Fin budget.capacity,
        Pr{let observed←RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds typed mode work before}[
          At crypto wire serverKeyId budget route kind target (observed.1,observed.2.1)] := by
  classical
  calc
    _≤Pr{let observed←RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds typed mode work before}[
        ∃target∈(Finset.univ:Finset (Fin budget.accept × Fin budget.capacity)),
          At crypto wire serverKeyId budget route kind target (observed.1,observed.2.1)] := by
      apply prEvent_mono_of_support
      intro observed supported failed
      obtain ⟨target,chosen⟩:=selected crypto wire serverKeyId bounds typed mode work budget bounded before observed supported route kind [] failed
      exact ⟨target,Finset.mem_univ _,chosen⟩
    _≤_:=prEvent_exists_finset_le Finset.univ _ _

def claimedHandle (route : RawCtxServerRouting.SenderDecoder) (kind : Kind) (entry : Entry) : Option Handle :=
  match kind with
  | .origin _ | .receiver=>PqxdhDeploymentHeadlineEvents.receivedHandle route entry
  | .sender=>PqxdhDeploymentHeadlineEvents.publishedHandle entry

def PinnedAt (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64) (budget : Budget)
    (route : RawCtxServerRouting.SenderDecoder) (kind : Kind)
    (target : Fin budget.accept × Fin budget.capacity) (value : Value × RegistrationNativeLedger.State) : Prop :=
  ∃priorList entry later sessionTarget,
    value.2.ledger.transcript=priorList++entry::later ∧
    Witness crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId budget route kind sessionTarget value.2.ledger.transcript priorList entry ∧
    sessionTarget.2=target.2 ∧
    RegistrationNativeParsedTargetCanonical.AcceptedAt wire value.2.transcript sessionTarget.1.val target.1.val ∧
    ∀handle,claimedHandle route kind entry=some handle →
      RegistrationNativePrekeyEvents.Pinned crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId value.2.ledger.transcript handle

open Classical in
noncomputable def pinnedEvent (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64) (budget : Budget)
    (route : RawCtxServerRouting.SenderDecoder) (kind : Kind)
    (target : Fin budget.accept × Fin budget.capacity) (value : Value × RegistrationNativeLedger.State)
    (_produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame))
    (_raw : PqxdhRecordLiftWorld.RawCounters) : Bool :=
  decide (PinnedAt crypto wire serverKeyId budget route kind target value)

/-- The public witness itself determines the same claimed handle; no private handle association is supplied. -/
theorem witness_handle (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKeyId : U64) (budget : Budget)
    (route : RawCtxServerRouting.SenderDecoder) (kind : Kind)
    (target : Fin budget.accept × Fin budget.capacity) (transcript priorList : List Entry) (entry : Entry)
    (witness : Witness crypto codec serverKeyId budget route kind target transcript priorList entry) :
    ∃handle,claimedHandle route kind entry=some handle ∧
      PqxdhDeploymentTranscript.designateIn crypto codec serverKeyId budget transcript handle=some target := by
  cases kind with
  | origin direction=>
    obtain ⟨receiver,raw,opened,handle,frame,received,routed,_direction,designated,_decoded,_unpublished⟩:=witness
    exact ⟨handle,by simp only [claimedHandle,PqxdhDeploymentHeadlineEvents.receivedHandle,received,Option.bind_some,routed],designated⟩
  | receiver=>
    obtain ⟨receiver,raw,opened,keyId,sender,frame,received,routed,_decoded,_published,designated,_unrelated⟩:=witness
    exact ⟨.peer keyId,by simp only [claimedHandle,PqxdhDeploymentHeadlineEvents.receivedHandle,received,Option.bind_some,routed],designated⟩
  | sender=>
    obtain ⟨owner,encrypted,frame,published,_decoded,designated,_other⟩:=witness
    exact ⟨.owner owner,by simp only [claimedHandle,PqxdhDeploymentHeadlineEvents.publishedHandle,published,Option.map_some],designated⟩

/-- One same-run changed-prekey alternative covers all public pin failures BEFORE the target union. This is only event algebra; the actual source theorem discharges the per-handle split. -/
theorem pinned_or_changed (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64) (budget : Budget)
    (route : RawCtxServerRouting.SenderDecoder) (kind : Kind)
    (target : Fin budget.accept × Fin budget.capacity) (value : Value × RegistrationNativeLedger.State)
    (selected : At crypto wire serverKeyId budget route kind target value) (changed : Prop)
    (split : ∀handle,RegistrationNativePrekeyEvents.Pinned crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId value.2.ledger.transcript handle ∨changed) :
    PinnedAt crypto wire serverKeyId budget route kind target value ∨changed := by
  obtain ⟨priorList,entry,later,sessionTarget,actual,witness,owner,accepted⟩:=selected
  obtain ⟨handle,claimed,_designated⟩:=witness_handle crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId budget route kind sessionTarget _ priorList entry witness
  rcases split handle with pinned|bad
  · left
    refine ⟨priorList,entry,later,sessionTarget,actual,witness,owner,accepted,?_⟩
    intro other found
    have same:=Option.some.inj (found.symm.trans claimed)
    exact same ▸pinned
  · exact Or.inr bad

/-- The pin-filtered public event still implies the complete original corrected failure. -/
theorem pinned_original (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64) (budget : Budget)
    (route : RawCtxServerRouting.SenderDecoder) (kind : Kind)
    (target : Fin budget.accept × Fin budget.capacity) (value : Value × RegistrationNativeLedger.State)
    (produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame))
    (selected : PinnedAt crypto wire serverKeyId budget route kind target value) :
    Failure crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId budget route kind value produced := by
  obtain ⟨priorList,entry,later,sessionTarget,actual,witness,owner,accepted,_pinned⟩:=selected
  exact at_original crypto wire serverKeyId budget route kind target value produced
    ⟨priorList,entry,later,sessionTarget,actual,witness,owner,accepted⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargets

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargets.witness_designated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargets.witness_designated

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargets.failure_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargets.failure_witness

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargets.designated_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargets.designated_target

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargets.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargets.selected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargets.at_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargets.at_original

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargets.probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargets.probability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargets.witness_handle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargets.witness_handle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargets.pinned_or_changed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargets.pinned_or_changed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargets.pinned_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargets.pinned_original
