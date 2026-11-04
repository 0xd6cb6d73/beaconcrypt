-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterRecordRawContext
import BeaconcryptCore.Computational.RegistrationNativeReceiveLogging

/-! The exact raw-owner model context uses Wire's typed parser and stored AD array around the extracted receive loop. The original frame logger, full owner state and instrumented primitive state are retained jointly. Concrete Rust parsing and outer wrapper correspondence remain separate. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.RegistrationNativeReceiveOwner
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeWire (Wire ledgerCodec)
open BeaconcryptCore.Refinement
variable {ι KemSK Metadata : Type} {base : OracleSpec ι}

noncomputable def raw (setup : Setup base KemSK) (wire : Wire)
    (erased : Array Std.U8 357#usize) (ad : Array Std.U8 281#usize)
    (bytes : Pqxdh.Bytes) (state : RawCtxWholeOwner.OwnerState Metadata) :=
  AdapterRecordRawContext.raw (RegistrationNativeExtractedReceive.primitives setup (ledgerCodec wire))
    erased wire.parseFrame ad bytes state

/-- Literal parser admission, selected sender, complete owner and primitive histories agree with the original native receive model. -/
theorem raw_native (setup : Setup base KemSK) (wire : Wire)
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (erased : Array Std.U8 357#usize) (ad : Array Std.U8 281#usize)
    (bytes : Pqxdh.Bytes) (state : RawCtxWholeOwner.OwnerState Metadata)
    (represented : state.owner.associatedData = PqxdhRefinement.absBytes ad)
    (before : PqxdhRecordLiftWorld.Primitive) :
    (raw setup wire erased ad bytes state).run before =
      (simulateQ (PqxdhRecordLiftWorld.primitives setup (ledgerCodec wire))
        (simulateQ RawCtxMixedOwner.receiveAdapter
          ((RawCtxWholeOwner.rawReceive (ledgerCodec wire).frameRead bytes).run state))).run before := by
  simpa only [raw, RegistrationNativeExtractedReceive.primitives, RawCtxMixedOwner.receiveAdapter,
    QueryImpl.simulateQ_compose, ledgerCodec] using
    AdapterRecordRawContext.raw_native
      (RegistrationNativeExtractedReceive.primitives setup (ledgerCodec wire))
      (RegistrationNativeExtractedReceive.functional setup (ledgerCodec wire) length)
      erased wire.parseFrame ad bytes state represented before

/-- The original receive logger adds no frame, and its complete joint result is the source execution with that unchanged empty receipt list. -/
theorem raw_logged_native (setup : Setup base KemSK) (wire : Wire)
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (erased : Array Std.U8 357#usize) (ad : Array Std.U8 281#usize)
    (bytes : Pqxdh.Bytes) (state : RawCtxWholeOwner.OwnerState Metadata)
    (represented : state.owner.associatedData = PqxdhRefinement.absBytes ad)
    (before : PqxdhRecordLiftWorld.Primitive) :
    (fun result => ((result.1, []), result.2)) <$> (raw setup wire erased ad bytes state).run before =
      (simulateQ (PqxdhRecordLiftWorld.primitives setup (ledgerCodec wire))
        (PqxdhDeploymentNative.logged (simulateQ RawCtxMixedOwner.receiveAdapter
          ((RawCtxWholeOwner.rawReceive (ledgerCodec wire).frameRead bytes).run state)))).run before := by
  rw [RegistrationNativeReceiveLogging.logged_receive, simulateQ_map, StateT.run_map,
    raw_native setup wire length erased ad bytes state represented before]

end BeaconcryptCore.Computational.RegistrationNativeReceiveOwner

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeReceiveOwner.raw_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeReceiveOwner.raw_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeReceiveOwner.raw_logged_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeReceiveOwner.raw_logged_native
