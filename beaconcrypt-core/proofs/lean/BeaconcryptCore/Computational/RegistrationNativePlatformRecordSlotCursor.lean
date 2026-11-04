-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotGhost
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealPhysical
import BeaconcryptCore.Computational.RegistrationNativeRecordPackage
/-! Opaque installation annotations are computed after the actual cursor's refusal decision. Full cursor/control/private state erases exactly to the original physical record interpretation; slot-view reconstruction is derived from source replies for any private service. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCursor
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhRecordLiftProtocol (Control ServiceSpec)
open RegistrationNativePlatformRecordSlotGhost (State program slots)
variable {n : Nat} {Reader Response Secret A : Type}
variable (service : QueryImpl (ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

noncomputable def interpret (work : OracleComp (WorldSpec n) A) (ghost : State n)
    (shell : CborRecordWorldClient.Shell) (control : Control n) (secret : Secret) :=
  (simulateQ service ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
    (program ((simulateQ CborRecordWorldClient.handler work).run shell) ghost)).run control)).run secret

/-- Erasing only the computed slot observer restores the original complete physical execution, including the cursor and its actual refused calls. -/
theorem erase (work : OracleComp (WorldSpec n) A) (ghost : State n)
    (shell : CborRecordWorldClient.Shell) (control : Control n) (secret : Secret) :
    (fun result => (((result.1.1.1.1,result.1.1.1.2),result.1.2),result.2)) <$>
      interpret service codec route work ghost shell control secret =
        CborRawRecordOriginFlatten.interpret service codec route work shell control secret := by
  have first := RegistrationNativePlatformRecordSlotGhost.interpreted_erase
    (PqxdhRecordLiftProtocol.handler codec.frameRead route)
    ((simulateQ CborRecordWorldClient.handler work).run shell) ghost control
  have mapped := congrArg (fun tree => (simulateQ service tree).run secret) first
  simpa only [interpret,CborRawRecordOriginFlatten.interpret,simulateQ_map,StateT.run_map] using mapped

/-- The same actual physical result has its slot map computed from opaque installation replies and public handles only. -/
theorem projection (work : OracleComp (WorldSpec n) A) (ghost : State n)
    (shell : CborRecordWorldClient.Shell) (control : Control n)
    (prior : ghost.origins=RegistrationNativePlatformRecordSlotControl.origins control) (secret : Secret)
    (result : (((A × CborRecordWorldClient.Shell) × State n) × Control n) × Secret)
    (supported : result ∈ support (interpret service codec route work ghost shell control secret)) :
    slots result.1.1.2=PqxdhRecordLiftIdeal.handleSlot result.1.2 :=
  RegistrationNativePlatformRecordSlotGhost.interpreted_slots service codec.frameRead route
    ((simulateQ CborRecordWorldClient.handler work).run shell) ghost control prior secret result supported

/-- Cold source control and the transparent analysis observer satisfy the slot relation by construction. -/
theorem cold : (RegistrationNativePlatformRecordSlotGhost.initial (n := n)).origins=
    RegistrationNativePlatformRecordSlotControl.origins PqxdhRecordLiftProtocol.initialControl := by
  apply congrArg₂ PqxdhRecordLiftOrigins.Origins.mk
  · rfl
  · funext index
    simp only [PqxdhRecordLiftProtocolHistory.view,PqxdhRecordLiftProtocol.join,PqxdhRecordLiftProtocol.initialControl,
      PqxdhRecordLiftProtocol.control,PqxdhRecordLiftWorldCompiler.initial,List.getElem?_nil,Option.bind_none]

/-- A genuine fresh source run derives the complete slot projection without a caller slot-map or safety premise and without resetting any private CTX cache. -/
theorem initialized (work : OracleComp (WorldSpec n) A) (shell : CborRecordWorldClient.Shell) (secret : Secret)
    (result : (((A × CborRecordWorldClient.Shell) × State n) × Control n) × Secret)
    (supported : result ∈ support (interpret service codec route work RegistrationNativePlatformRecordSlotGhost.initial
      shell PqxdhRecordLiftProtocol.initialControl secret)) :
    slots result.1.1.2=PqxdhRecordLiftIdeal.handleSlot result.1.2 :=
  projection service codec route work _ shell _ cold secret result supported

section RecordView
variable {E Value : Type}
variable (produced : Secret → List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame))
local notation "Outcome" => RegistrationNativeEntropyRun.Outcome E Value
local notation "TaggedResult" => (((Outcome × CborRecordWorldClient.Shell) × State n) × Control n) × Secret

def view (result : TaggedResult) : RegistrationNativeRecordPackage.View n E Value :=
  ⟨result.1.1.1.1,produced result.2,PqxdhRecordLiftProtocol.rawCounters result.1.2,slots result.1.1.2⟩

/-- The permitted record view is recovered from computed opaque annotations at the same complete source result, not from a slot-map assumption or a replacement run. -/
theorem view_source (work : OracleComp (WorldSpec n) Outcome) (shell : CborRecordWorldClient.Shell) (secret : Secret)
    (result : TaggedResult)
    (supported : result ∈ support (interpret service codec route work RegistrationNativePlatformRecordSlotGhost.initial
      shell PqxdhRecordLiftProtocol.initialControl secret)) :
    view produced result=RegistrationNativeRecordPackage.nativeView (result.1.1.1.1,result.1.2) (produced result.2) := by
  have fields := initialized service codec route work shell secret result supported
  exact congrArg (RegistrationNativeRecordPackage.View.mk result.1.1.1.1 (produced result.2)
    (PqxdhRecordLiftProtocol.rawCounters result.1.2)) fields

/-- Every slot-aware record decision is an exact computable observer extension on the same native value/ledger, produced frames, raw counters and arbitrary reached private cache. -/
theorem event_source (work : OracleComp (WorldSpec n) Outcome) (shell : CborRecordWorldClient.Shell) (secret : Secret)
    (decision : RegistrationNativeRecordPackage.View n E Value → Bool) :
    (fun result => decision (view produced result)) <$>
      interpret service codec route work RegistrationNativePlatformRecordSlotGhost.initial shell PqxdhRecordLiftProtocol.initialControl secret =
        (fun result => decision (RegistrationNativeRecordPackage.nativeView (result.1.1.1,result.1.2) (produced result.2))) <$>
          CborRawRecordOriginFlatten.interpret service codec route work shell PqxdhRecordLiftProtocol.initialControl secret := by
  have erased := congrArg (Functor.map (fun result => decision
    (RegistrationNativeRecordPackage.nativeView (result.1.1.1,result.1.2) (produced result.2))))
    (erase service codec route work RegistrationNativePlatformRecordSlotGhost.initial shell PqxdhRecordLiftProtocol.initialControl secret)
  rw [← erased]
  simp only [Functor.map_map]
  rw [← bind_pure_comp,← bind_pure_comp]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro result supported
  rw [view_source service codec route produced work shell secret result supported]

end RecordView
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCursor
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCursor.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCursor.erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCursor.projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCursor.projection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCursor.cold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCursor.cold

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCursor.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCursor.initialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCursor.view_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCursor.view_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCursor.event_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCursor.event_source
