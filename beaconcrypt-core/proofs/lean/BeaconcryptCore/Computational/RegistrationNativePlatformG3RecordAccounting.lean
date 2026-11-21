-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MetricWorld
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldObservation
import BeaconcryptCore.Computational.RegistrationNativeStartupMetricSource
/-! The complete terminal record observation is independent of the three separately billed accounting fields. The actual guarded World and every original result remain literal; this permits the genuine interpreted startup to supply the warm source cut without changing cache, produced frames or raw counters. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordAccounting
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhRecordLiftWorld (State)
open RegistrationNativeG3MetricWorld (mask)
open RegistrationNativePlatformPublicWorldObservation (recordView)
variable {n : Nat} {I KemSK Reader Response Value : Type} {base : OracleSpec I}
private theorem record_mask (before : State n) : recordView (mask before) = recordView before := rfl

/-- Normalizing only the independent accounting coordinates preserves every actual return and the complete record observation. -/
theorem program_input (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) Value) (before : State n) :
    (fun (result : Value × State n) => (result.1,recordView result.2)) <$>
      (simulateQ (CborRecordWorldSimulation.guarded setup codec route) work).run before =
      (fun (result : Value × State n) => (result.1,recordView result.2)) <$>
        (simulateQ (CborRecordWorldSimulation.guarded setup codec route) work).run (mask before) := by
  have first := RegistrationNativeG3MetricWorld.program_source setup codec route work before
  have second := RegistrationNativeG3MetricWorld.program_source setup codec route work (mask before)
  rw [RegistrationNativeG3MetricWorld.mask_idempotent] at second
  have observed := congrArg (Functor.map (fun (result : Value × State n) => (result.1,recordView result.2))) (first.trans second.symm)
  simpa only [Functor.map_map,Prod.map_def,id_eq,record_mask] using observed
/-- The genuine interpreted constructor and actual public startup have the same full record-observed continuation, after only the derived accounting comparison. -/
theorem startup_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64)
    (identity : PqxdhJointIdentity.PublicIdentity)
    (next : Option (RegistrationNativePublicStartup.Started source) → OracleComp (WorldSpec n) Value) (before : State n) :
    (do let initialized ← (simulateQ (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route)
          (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId identity)).run before
        (fun (result : Value × State n) => (result.1,recordView result.2)) <$>
          (simulateQ (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route)
            (next (initialized.1.map RegistrationNativeHiddenStartup.Started.native))).run initialized.2) =
      (do let initialized ← (RegistrationNativePublicStartupFrame.startup setup source ensureInit identityIndex serverKeyId identity).run before
          (fun (result : Value × State n) => (result.1,recordView result.2)) <$>
            (simulateQ (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route)
              (next initialized.1)).run initialized.2) := by
  let continuation := fun (initialized : Option (RegistrationNativePublicStartup.Started source) × State n) =>
    (fun (result : Value × State n) => (result.1,recordView result.2)) <$>
      (simulateQ (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route)
        (next initialized.1)).run initialized.2
  have actual := congrArg (fun distribution => distribution >>= continuation)
    (RegistrationNativeStartupMetric.startup_source setup wire route source ensureInit identityIndex serverKeyId identity before)
  simpa only [continuation,bind_map_left,Prod.map_def,id_eq,← program_input] using actual

end BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordAccounting

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordAccounting.program_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordAccounting.program_input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordAccounting.startup_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordAccounting.startup_source
