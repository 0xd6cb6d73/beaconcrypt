-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCursor
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotIdeal
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {I KemSK Reader Response E Value : Type} {base : OracleSpec I}
variable (modes : PqxdhRecordLiftWorldCompiler.Label n → PqxdhRecordLiftIdeal.KeyMode)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
local notation "service" => PqxdhRecordLiftIdeal.ctxInterpreter modes id setup codec

/-- The complete ideal source lift, including physical cache, control, cursor and computed opaque installation receipts. -/
noncomputable def joint (work : OracleComp (WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value)) :=
  RegistrationNativePlatformRecordSlotCursor.interpret service codec route work
    RegistrationNativePlatformRecordSlotGhost.initial CborRecordWorldClient.initial
      PqxdhRecordLiftProtocol.initialControl PqxdhRecordLiftIdeal.CtxPrivate.initial

/-- Attaching the transparent slot ghost leaves the entire original ideal observation unchanged and derives its slot map on the same run. -/
theorem source (work : OracleComp (WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value))
    (decision : RegistrationNativeRecordPackage.View n E Value → Bool) :
    decision <$> RegistrationNativeRecordPackage.ctx modes setup codec route work =
      (fun result => decision (RegistrationNativePlatformRecordSlotCursor.view
        (fun reached => reached.base.produced) result)) <$> joint modes setup codec route work := by
  rw [RegistrationNativeRecordPackage.ctx_source,Functor.map_map]
  exact (RegistrationNativePlatformRecordSlotCursor.event_source service codec route
    (fun reached => reached.base.produced) work CborRecordWorldClient.initial
      PqxdhRecordLiftIdeal.CtxPrivate.initial decision).symm

/-- The same observer extension works at an arbitrary reached private cache and cursor shell, retaining the genuine joint lift. -/
theorem warm_source (work : OracleComp (WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value))
    (shell : CborRecordWorldClient.Shell) (secret : PqxdhRecordLiftIdeal.CtxPrivate n)
    (decision : RegistrationNativeRecordPackage.View n E Value → Bool) :
    (fun result => decision (RegistrationNativeRecordPackage.nativeView (result.1.1.1,result.1.2) result.2.base.produced)) <$>
      CborRawRecordOriginFlatten.interpret service codec route work shell PqxdhRecordLiftProtocol.initialControl secret =
    (fun result => decision (RegistrationNativePlatformRecordSlotCursor.view
      (fun reached => reached.base.produced) result)) <$>
      RegistrationNativePlatformRecordSlotCursor.interpret service codec route work
        RegistrationNativePlatformRecordSlotGhost.initial shell PqxdhRecordLiftProtocol.initialControl secret :=
  (RegistrationNativePlatformRecordSlotCursor.event_source service codec route
    (fun reached => reached.base.produced) work shell secret decision).symm
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotIdeal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotIdeal.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotIdeal.source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotIdeal.warm_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotIdeal.warm_source
