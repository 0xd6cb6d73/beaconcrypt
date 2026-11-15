-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySendReification
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinarySendOperands
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! Actual ordinary SDK operand samplers commute with removal of administrative instrumentation only. Source results, primitive/cache counters, writer receipts and common platform state remain exact. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySampleReification
open BeaconcryptCore.Refinement
open AdapterPublicWrapperStorage
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformExtractedSdkOrdinaryDriver (M State)
open RegistrationNativePlatformSdkOrdinarySendReification (Compatible)
open RegistrationNativePlatformSdkOrdinaryReification (primitive journal)
variable {n : Nat} {KemSK Platform R I E A B Reader Response Reply PublicReply : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]

omit material platform ed in
private theorem pure_compatible (value : A) : Compatible (pure value :M Platform A) := by
  intro before
  simp only [StateT.run_pure,map_pure]
  rfl

omit material platform ed in
private theorem mapped (observe : A →B) (work : M Platform A) (held : Compatible work) : Compatible (observe <$>work) := by
  intro before
  rw [StateT.run_map,StateT.run_map,←held before,Functor.map_map,Functor.map_map]
  rfl

variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]

omit material platform ed in
theorem send_sample (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (target sender : U64) (associated : Array U8 151#usize)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (bytes : Slice U8) :
    Compatible (RegistrationNativePlatformExtractedSdkOrdinarySendOperands.sample setup codec reserve view failure erased
      target sender associated kernel bytes) := by
  unfold RegistrationNativePlatformExtractedSdkOrdinarySendOperands.sample
  cases AdapterPublicOrdinaryEnvelope.prepareSend bytes target sender associated kernel with
  | fail error | div=>exact pure_compatible _
  | ok optional=>cases optional with
    | none=>exact pure_compatible _
    | some context=>exact RegistrationNativePlatformSdkOrdinarySendReification.send setup codec reserve view failure erased kernel context

omit material platform ed primitives [FrameDispatchFallback.Operations] in
theorem received (setup : Setup base KemSK) (codec : Codec Reader Response)
    (erased : Array U8 227#usize) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (sequence : U64) (payload : Slice U8) (associated : Array U8 151#usize) (sender : U64) :
    Compatible (RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.received (Platform:=Platform) setup codec erased kernel sequence payload associated sender) := by
  intro before
  funext previous
  change (Prod.map id journal <$>
    (RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.received setup codec erased kernel sequence payload associated sender).run before).run previous=
    ((RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.received setup codec erased kernel sequence payload associated sender).run (journal before)).run previous
  rw [StateT.run_map]
  simp only [RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.received,
    RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.lift_run,Functor.map_map]
  have equation:=congrArg (fun distribution=>(fun result=>((result.1,(result.2,before.2)),previous)) <$>distribution)
    (RegistrationNativePlatformSdkOrdinaryReification.receive_program setup codec erased
      (AdapterRecordStatefulReceive.receive kernel sequence payload associated sender).run before.1)
  simp only [Functor.map_map] at equation
  simpa only [RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.receivedPrimitive,Prod.map,id_eq,journal] using equation

omit material platform ed primitives [FrameDispatchFallback.Operations] in
theorem receive_sample (setup : Setup base KemSK) (codec : Codec Reader Response)
    (erased : Array U8 227#usize) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (target : U64) (associated : Array U8 151#usize) (bytes : Slice U8) :
    Compatible (RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon.sample (Platform:=Platform) setup codec erased kernel target associated bytes) := by
  unfold RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon.sample
  cases AdapterPublicOrdinaryEnvelope.prepareReceive bytes target with
  | fail error | div=>exact pure_compatible _
  | ok optional=>cases optional with
    | none=>exact pure_compatible _
    | some frame=>exact received setup codec erased kernel frame.sequence frame.ciphertext associated frame.sender

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySampleReification

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySampleReification.send_sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySampleReification.send_sample

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySampleReification.received' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySampleReification.received

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySampleReification.receive_sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySampleReification.receive_sample
