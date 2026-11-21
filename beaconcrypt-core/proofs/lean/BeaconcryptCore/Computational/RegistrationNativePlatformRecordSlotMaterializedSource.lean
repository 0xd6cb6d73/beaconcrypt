-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedWhole
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedProtocol
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterializedTables
import BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedFrontend
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyExecution
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldObservation
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotTranslation
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlotSource
/-! The raw-demand slot snapshot sits below material-reply realization. The literal current frontend supplies source safety and translation internally; the warm World, common platform and actual private backend are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotMaterializedSource
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativeG3MaterializedLocal (handler translate)
open RegistrationNativeG3LocalKeys (State project)
open RegistrationNativeG3LocalMaterialCompletedSource (cache)
open RegistrationNativeG3LocalMaterialCompletion (put)
variable {n : Nat} {I KemSK ProviderState Reader Response A : Type} {base : OracleSpec I}
variable (table : PqxdhRecordLiftInterface.Slot n → PqxdhDeploymentHiddenLayout.Material)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)

theorem raw_source (seeds : Seeds n)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) A)
    (ghost : RegistrationNativePlatformPublicRecordSlots.State n)
    (same : RegistrationNativePlatformPublicRecordSlots.program (simulateQ (translate true seeds) work) ghost =
      RegistrationNativePlatformPublicRecordSlots.program (simulateQ (translate false seeds) work) ghost)
    (before : State n KemSK ProviderState) :
    (fun result => (result.1, RegistrationNativePlatformPublicWorldObservation.recordView result.2.2)) <$>
      (simulateQ (RegistrationNativeG3LocalMaterialCompletion.fixed table setup codec route wire sign seed scalar candidate provider)
        (RegistrationNativePlatformPublicRecordSlots.program (simulateQ (translate true seeds) work) ghost)).run before =
      (fun result => (result.1.1, RegistrationNativePlatformPublicWorldObservation.recordView result.2)) <$>
        (simulateQ (RegistrationNativeG3GuardedMaterializedWorld.source setup codec route seeds)
          ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
            (RegistrationNativePlatformPublicRecordSlots.program work ghost)).run (put before (cache table)).1)).run before.2 := by
  have metric := congrArg (Functor.map (fun result =>
      (result.1, RegistrationNativePlatformPublicWorldObservation.recordView result.2.2)))
    (RegistrationNativeG3MaterializedLocalKeys.fixed_program_project table setup codec route wire sign seed scalar candidate provider
      (RegistrationNativePlatformPublicRecordSlots.program (simulateQ (translate true seeds) work) ghost) before)
  have literal :
      (simulateQ (RegistrationNativeG3LocalMaterialCompletion.fixed table setup codec route wire sign seed scalar candidate provider)
        (RegistrationNativePlatformPublicRecordSlots.program (simulateQ (translate true seeds) work) ghost)).run (project before) =
      (simulateQ (RegistrationNativeG3LocalMaterialCompletion.fixed table setup codec route wire sign seed scalar candidate provider)
        (simulateQ (translate false seeds) (RegistrationNativePlatformPublicRecordSlots.program work ghost))).run (project before) := by
    rw [same,RegistrationNativePlatformRecordSlotTranslation.program]
  have mixed := congrArg (Functor.map (fun result =>
      (result.1, RegistrationNativePlatformPublicWorldObservation.recordView result.2.2))) literal
  simp only [Functor.map_map, Prod.map_def, id_eq,
    project, RegistrationNativePlatformPublicWorldObservation.recordView, RegistrationNativeG3MetricWorld.mask,
    RegistrationNativeWorldView.project, RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin,
    RegistrationNativeKemWorldUniform.mask] at metric mixed
  have actual := congrArg (Functor.map (fun result =>
      (result.1, RegistrationNativePlatformPublicWorldObservation.recordView result.2.2)))
    (RegistrationNativeG3LocalMaterialCompletedSource.world_source table setup codec route wire sign seed scalar candidate provider
      (simulateQ (translate false seeds) (RegistrationNativePlatformPublicRecordSlots.program work ghost)) before)
  have pulled := congrArg (fun program =>
      (fun result => (result.1.1, RegistrationNativePlatformPublicWorldObservation.recordView result.2)) <$>
        (simulateQ (CborRecordWorldSimulation.guarded setup codec route) program).run before.2)
    (RegistrationNativeG3MaterializedSelectivePullback.program_source setup wire sign seed scalar candidate provider seeds (RegistrationNativePlatformPublicRecordSlots.program work ghost)
      (put before (cache table)).1)
  simp only [Functor.map_map, Prod.map_def, id_eq, put, RegistrationNativeG3LocalMaterialFrame.put,
    RegistrationNativePlatformPublicWorldObservation.recordView, RegistrationNativeG3MetricWorld.mask,
    RegistrationNativeWorldView.project, RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin,
    RegistrationNativeKemWorldUniform.mask] at actual
  have joined := metric.trans (mixed.trans (actual.symm.trans pulled.symm))
  have sameRealize : RegistrationNativeG3GuardedMaterializedWorld.realize seeds = RegistrationNativeG3MaterializedWorld.realize seeds := rfl
  simpa only [handler, QueryImpl.simulateQ_compose, RegistrationNativeG3GuardedMaterializedWorld.source,
    sameRealize,
    RegistrationNativePlatformPublicWorldObservation.recordView, PqxdhRecordLiftWorld.rawCounters] using joined


/-- The same raw-demand snapshot is the literal opaque-slot World ghost, before hidden kernels are realized; the complete warm native World and private backend are retained. -/
theorem source (seeds : Seeds n)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) A)
    (safe : RegistrationNativePlatformPublicSlotKind.Safe work)
    (ghost : RegistrationNativePlatformPublicRecordSlots.State n)
    (same : RegistrationNativePlatformPublicRecordSlots.program (simulateQ (translate true seeds) work) ghost =
      RegistrationNativePlatformPublicRecordSlots.program (simulateQ (translate false seeds) work) ghost)
    (before : State n KemSK ProviderState) :
    (fun result => ((result.1.1,result.1.2.snapshot),RegistrationNativePlatformPublicWorldObservation.recordView result.2.2)) <$>
      (simulateQ (RegistrationNativeG3LocalMaterialCompletion.fixed table setup codec route wire sign seed scalar candidate provider)
        (RegistrationNativePlatformPublicRecordSlots.program (simulateQ (translate true seeds) work) ghost)).run before =
    (fun result => ((result.1.1.1,result.1.2),RegistrationNativePlatformPublicWorldObservation.recordView result.2)) <$>
      (simulateQ (RegistrationNativeG3GuardedMaterializedWorld.source setup codec route seeds)
        (RegistrationNativePlatformRecordSlotGhost.program
          ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
            work).run (put before (cache table)).1) ghost.snapshot)).run before.2 := by
  have raw := congrArg (Functor.map (fun result => ((result.1.1,result.1.2.snapshot),result.2)))
    (raw_source table setup codec route wire sign seed scalar candidate provider seeds work ghost same before)
  have ghostLaw := RegistrationNativePlatformPublicRecordSlotSource.source setup wire sign seed scalar candidate provider work safe ghost (put before (cache table)).1
  rw [ghostLaw]
  simpa only [Functor.map_map,simulateQ_map,StateT.run_map] using raw

variable {Platform E : Type}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (checks : PqxdhServerAuthExperiment.Checks) (source : RegistrationNativeMldsa.Source)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))


/-- The literal current raw frontend supplies both observer translation and kind safety internally. No slot-map, callback-equivalence or warm-cache reset is a premise. -/
theorem run (seeds : Seeds n) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (front : RegistrationNativePlatformPublicFrontend.State source Platform)
    (ghost : RegistrationNativePlatformPublicRecordSlots.State n) (before : State n KemSK ProviderState) :
    let canonical := RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
    let tree := RegistrationNativePlatformMaterializedWhole.tree setup wire sign scalar checks source selectedOwner selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front
    (fun result => ((result.1.1,result.1.2.snapshot),RegistrationNativePlatformPublicWorldObservation.recordView result.2.2)) <$>
      (simulateQ (RegistrationNativeG3LocalMaterialCompletion.fixed table setup codec route canonical sign seed scalar candidate provider)
        (RegistrationNativePlatformPublicRecordSlots.program (simulateQ (translate true seeds) tree) ghost)).run before =
    (fun result => ((result.1.1.1,result.1.2),RegistrationNativePlatformPublicWorldObservation.recordView result.2)) <$>
      (simulateQ (RegistrationNativeG3GuardedMaterializedWorld.source setup codec route seeds)
        (RegistrationNativePlatformRecordSlotGhost.program
          ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup canonical sign seed scalar candidate provider)
            tree).run (put before (cache table)).1) ghost.snapshot)).run before.2 := by
  apply RegistrationNativePlatformRecordSlotMaterializedSource.source
  · exact RegistrationNativePlatformPublicSlotSafety.run setup checks wire source sign selectedOwner selectedAccept
      (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front
  · exact RegistrationNativePlatformPublicRecordSlots.run_source setup checks wire source sign selectedOwner selectedAccept
      (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer seeds serverKeyId bounds mode work front ghost

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotMaterializedSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotMaterializedSource.raw_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotMaterializedSource.raw_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotMaterializedSource.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotMaterializedSource.source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotMaterializedSource.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotMaterializedSource.run
