-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3MaterializedTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RepeatRun
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedRetainedLazy
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedProtocol
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordCoupling

/-! The actual corrected traced materialized source equals the known guarded World on that identical request tree while retaining terminal CTX cache, produced frames and raw counters. The explicit accounting projection is discharged by actual fixed-callback non-read laws and is invisible in this record observation. Original replies, ledger and platform state remain joint with the chronology. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordTraceKnown
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeG3AuditTraceRun (cold)
variable {n : Nat} {I KemSK ProviderState Reader Response Platform E A : Type} {base : OracleSpec I}
variable (table : PqxdhRecordLiftInterface.Slot n → PqxdhDeploymentHiddenLayout.Material)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (seeds : RegistrationNativeG3AuditedWorld.Seeds n) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (checks : Checks) (source : RegistrationNativeMldsa.Source) (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (front : RegistrationNativePlatformPublicFrontend.State source Platform)
    (frame : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) (world : PqxdhRecordLiftWorld.State n)
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "tree" => RegistrationNativePlatformMaterializedWhole.tree (n := n) setup wire sign scalar checks source selectedOwner selectedAccept
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front
local notation "tracedTree" => RegistrationNativeG2Trace.program tree

noncomputable def full := (fun result => (result.1, RegistrationNativePlatformPublicWorldObservation.recordView result.2.2)) <$>
  (simulateQ (RegistrationNativeG3MaterializedLocal.handler true table seeds setup codec route canonical sign seed scalar candidate provider)
    tracedTree).run (cold frame ∅, world)

/-- The actual corrected full material source and selective known source retain the same entire native G2 chronology, raw ledger and P. -/
theorem known_source :
    full table setup codec route seeds wire sign seed scalar candidate provider checks source selectedOwner selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front frame world =
      (fun result => (result.1.1, result.2)) <$> RegistrationNativePlatformG3RecordCoupling.known setup codec route seeds
        ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup canonical sign seed scalar candidate provider)
          tracedTree).run (RegistrationNativeG3AuditTraceRun.cold frame (RegistrationNativeG3LocalMaterialCompletedSource.cache table))) world := by
  let before : RegistrationNativeG3LocalKeys.State n KemSK ProviderState := (cold frame ∅, world)
  have mixed := congrArg (fun program => (fun result => (result.1, RegistrationNativePlatformPublicWorldObservation.recordView result.2.2)) <$>
    (simulateQ (RegistrationNativeG3LocalMaterialCompletion.fixed table setup codec route canonical sign seed scalar candidate provider) program).run before)
    (RegistrationNativePlatformG3MaterializedTrace.run_source setup checks wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar)
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer seeds serverKeyId bounds mode work front)
  have actual := congrArg (Functor.map (fun result => (result.1, RegistrationNativePlatformPublicWorldObservation.recordView result.2.2)))
    (RegistrationNativeG3LocalMaterialCompletedSource.world_source table setup codec route canonical sign seed scalar candidate provider
      (simulateQ (RegistrationNativeG3MaterializedLocal.translate false seeds) tracedTree) before)
  have pulled := congrArg (fun actual =>
    (fun result => (result.1.1, RegistrationNativePlatformPublicWorldObservation.recordView result.2)) <$> (simulateQ (CborRecordWorldSimulation.guarded setup codec route) actual).run world)
    (RegistrationNativeG3MaterializedSelectivePullback.program_source setup canonical sign seed scalar candidate provider seeds tracedTree
      (RegistrationNativeG3LocalMaterialCompletion.put before (RegistrationNativeG3LocalMaterialCompletedSource.cache table)).1)
  have record_mask (state : PqxdhRecordLiftWorld.State n) :
      RegistrationNativePlatformPublicWorldObservation.recordView (RegistrationNativeG3MetricWorld.mask state) =
        RegistrationNativePlatformPublicWorldObservation.recordView state := rfl
  simp only [Functor.map_map, Prod.map_def, id_eq, before, record_mask,
    RegistrationNativeG3LocalMaterialCompletion.put, RegistrationNativeG3LocalMaterialFrame.put] at mixed actual
  have normalized := congrArg (Functor.map (fun result => (result.1, RegistrationNativePlatformPublicWorldObservation.recordView result.2.2)))
    (RegistrationNativeG3MaterializedLocalKeys.fixed_program_project table setup codec route canonical sign seed scalar candidate provider
      (simulateQ (RegistrationNativeG3MaterializedLocal.translate false seeds) tracedTree) before)
  simp only [Functor.map_map, Prod.map_def, id_eq, before, RegistrationNativeG3LocalKeys.project, record_mask] at normalized
  have sameRealize : RegistrationNativeG3GuardedMaterializedWorld.realize seeds = RegistrationNativeG3MaterializedWorld.realize seeds := rfl
  have combined := mixed.trans (normalized.trans (actual.symm.trans pulled.symm))
  simpa only [full, RegistrationNativePlatformG3RecordCoupling.known, RegistrationNativeG3GuardedMaterializedWorld.source, sameRealize,
    RegistrationNativeG3MaterializedLocal.handler, QueryImpl.simulateQ_compose,
    RegistrationNativeG3LocalMaterialCompletion.put, RegistrationNativeG3LocalMaterialFrame.put,
    RegistrationNativePlatformMaterializedWhole.tree, before, cold, Functor.map_map, Prod.map_def, id_eq, Function.comp_def] using combined


end BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordTraceKnown

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordTraceKnown.known_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordTraceKnown.known_source
