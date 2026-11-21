-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedRetainedSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldObservation
import BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedWhole
import BeaconcryptCore.Computational.RegistrationNativeOpenRetainedReal
/-! The original retained compiler and its actual provider preserve terminal cache, crypto-produced frames and raw counters through the private materialized interpretation. The equations apply to arbitrary actual frontend trees and retain all common platform outcomes already in their values. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3RetainedRecordSource
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativePlatformPublicWorldObservation (RecordView recordView)
open RegistrationNativeG3RetainedFrontendSource (Frame project handler)
variable {n : Nat} {I KemSK ProviderState A : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (materials : Slot n → Material) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)

noncomputable def client (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) A)
    (before : RegistrationNativeOpenRetainedSource.SourceState n KemSK ProviderState) :
    OracleComp RegistrationNativeRetainedService.Spec (A × RecordView) :=
  (simulateQ (RegistrationNativeOpenRetainedSource.close provider)
    ((fun result => (result.1, recordView result.2.world)) <$>
      (simulateQ (RegistrationNativeOpenRetained.compiler setup wire route sign) work).run
        (RegistrationNativeOpenRetained.mask before.1))).run' (before.1.pool, before.2)

private theorem record_mask (before : RegistrationNativePublicInterpreter.State n KemSK) :
    recordView (RegistrationNativeOpenRetained.mask before).world = recordView before.world := rfl

/-- The actual direct material service retains the complete terminal record-data observation of the same open retained computation. -/
theorem retained_source (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) A)
    (before : Frame n KemSK ProviderState) :
    (fun result => (result.1, recordView result.2.2)) <$>
      (simulateQ (RegistrationNativeG3MaterializedDirectFrontend.handler materials setup (RegistrationNativeWire.ledgerCodec wire)
        route wire sign seed scalar candidate provider seeds) work).run (project before) =
    (simulateQ (RegistrationNativeG3RetainedCallbacks.keys setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate materials seeds)
      (client setup wire route sign provider work before.1)).run' before.2 := by
  have same := congrArg (Functor.map (fun result => (result.1, recordView result.2.2)))
    (RegistrationNativeG3RetainedFrontendRun.program_source setup wire route sign seed scalar candidate provider materials seeds work before)
  have original := congrArg (Functor.map (fun result => (result.1, recordView result.2.1.world)))
    (RegistrationNativeOpenRetainedSource.program_project setup wire route sign provider work before.1)
  simp only [Functor.map_map, Prod.map_def, id_eq, RegistrationNativeOpenRetainedSource.project, record_mask] at original
  let keysImpl := RegistrationNativeG3RetainedCallbacks.keys setup.source
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate materials seeds
  have nested := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT keysImpl
    (RegistrationNativeOpenRetainedSource.source setup wire route sign provider) work before.1 before.2
  have nestedObserved := congrArg (Functor.map (fun result => (result.1.1, recordView result.1.2.1.world))) nested
  have reference := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (RegistrationNativeOpenRetainedSource.close provider)
    (RegistrationNativeOpenRetained.compiler setup wire route sign)
    work (RegistrationNativeOpenRetained.mask before.1.1) (before.1.1.pool, before.1.2)
  have referenceObserved := congrArg (Functor.map (fun result => (result.1.1, recordView result.1.2.world))) reference
  have sourceEq : (fun result => (result.1, recordView result.2.1.1.world)) <$>
      (simulateQ (handler setup wire route sign seed scalar candidate provider materials seeds) work).run before =
      (simulateQ keysImpl ((fun result => (result.1, recordView result.2.1.world)) <$>
        (simulateQ (RegistrationNativeOpenRetainedSource.source setup wire route sign provider) work).run before.1)).run' before.2 := by
    simpa only [handler, keysImpl, StateT.run'_eq, simulateQ_map, StateT.run_map,
      Functor.map_map, Prod.map_def, id_eq] using nestedObserved.symm
  have referenceEq : (fun result => (result.1, recordView result.2.1.world)) <$>
      (simulateQ (RegistrationNativeOpenRetainedSource.reference setup wire route sign provider) work).run
        (RegistrationNativeOpenRetainedSource.project before.1) = client setup wire route sign provider work before.1 := by
    simpa only [RegistrationNativeOpenRetainedSource.reference, RegistrationNativeOpenRetainedSource.project,
      client, StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map, Prod.map_def, id_eq] using referenceObserved.symm
  have closed := congrArg (fun program => (simulateQ keysImpl program).run' before.2) (original.trans referenceEq)
  have first : (fun result => (result.1, recordView result.2.1.1.world)) <$>
      (simulateQ (handler setup wire route sign seed scalar candidate provider materials seeds) work).run before =
      (fun result => (result.1, recordView result.2.2)) <$>
        (simulateQ (RegistrationNativeG3MaterializedDirectFrontend.handler materials setup (RegistrationNativeWire.ledgerCodec wire)
          route wire sign seed scalar candidate provider seeds) work).run (project before) := by
    simpa only [Functor.map_map, Prod.map_def, id_eq, project, recordView, RegistrationNativeG3MetricWorld.mask,
      RegistrationNativeWorldView.project, RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin,
      RegistrationNativeKemWorldUniform.mask, PqxdhRecordLiftWorld.rawCounters] using same
  exact first.symm.trans (sourceEq.trans closed)

/-- The genuine indexed source provider closes this terminal observation to the original retained compiler, with no candidate-game identification. -/
theorem real_client (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) A)
    (before : RegistrationNativePublicInterpreter.State n KemSK) :
    client setup wire route sign (RegistrationNativeOpenRetainedReal.provider setup) work
      (RegistrationNativePublicRetained.clear before, ()) =
      (fun result => (result.1, recordView result.2.world)) <$>
        (simulateQ (RegistrationNativePublicRetained.compiler setup wire route sign) work).run
          (RegistrationNativePublicRetained.clear before) := by
  have source := RegistrationNativeOpenRetainedSource.program_project setup wire route sign
    (RegistrationNativeOpenRetainedReal.provider setup) work (RegistrationNativePublicRetained.clear before, ())
  rw [RegistrationNativeOpenRetainedReal.program_real] at source
  have observed := congrArg (Functor.map (fun result => (result.1, recordView result.2.1.world))) source
  have nested := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (RegistrationNativeOpenRetainedSource.close (RegistrationNativeOpenRetainedReal.provider setup))
    (RegistrationNativeOpenRetained.compiler setup wire route sign)
    work (RegistrationNativeOpenRetained.mask (RegistrationNativePublicRetained.clear before))
      ((RegistrationNativePublicRetained.clear before).pool, ())
  have nestedObserved := congrArg (Functor.map (fun result => (result.1.1, recordView result.1.2.world))) nested
  have referenceEq : (fun result => (result.1, recordView result.2.1.world)) <$>
      (simulateQ (RegistrationNativeOpenRetainedSource.reference setup wire route sign
        (RegistrationNativeOpenRetainedReal.provider setup)) work).run
          (RegistrationNativeOpenRetainedSource.project (RegistrationNativePublicRetained.clear before, ())) =
      client setup wire route sign (RegistrationNativeOpenRetainedReal.provider setup) work
        (RegistrationNativePublicRetained.clear before, ()) := by
    simpa only [RegistrationNativeOpenRetainedSource.reference, RegistrationNativeOpenRetainedSource.project,
      client, StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map, Prod.map_def, id_eq] using nestedObserved.symm
  have actual : (fun result => (result.1, recordView result.2.world)) <$>
      (simulateQ (RegistrationNativePublicRetained.compiler setup wire route sign) work).run
        (RegistrationNativePublicRetained.clear before) =
      (fun result => (result.1, recordView result.2.1.world)) <$>
        (simulateQ (RegistrationNativeOpenRetainedSource.reference setup wire route sign
          (RegistrationNativeOpenRetainedReal.provider setup)) work).run
            (RegistrationNativeOpenRetainedSource.project (RegistrationNativePublicRetained.clear before, ())) := by
    simpa only [Functor.map_map, Prod.map_def, id_eq, RegistrationNativeOpenRetainedSource.project, record_mask] using observed
  exact referenceEq.symm.trans actual.symm

/-- A source-derived demand budget closes finite material capacity while retaining all terminal record data. -/
theorem program_source (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) A)
    (bounded : work.IsQueryBoundP (RegistrationNativePublicCaps.IsDemand (KemSK := KemSK)) n)
    (frame : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (world : PqxdhRecordLiftWorld.State n) :
    (fun result => (result.1, recordView result.2.2)) <$>
      (simulateQ (RegistrationNativeG3MaterializedLocal.handler true materials seeds setup (RegistrationNativeWire.ledgerCodec wire)
        route wire sign seed scalar candidate provider) work).run (RegistrationNativeG3AuditTraceRun.cold frame ∅, world) =
    (simulateQ (RegistrationNativeG3RetainedCallbacks.keys setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate materials seeds)
      (client setup wire route sign provider work
        (RegistrationNativeG3MaterializedRetainedSource.ordinary frame world, frame.1.provider))).run'
        (RegistrationNativeHiddenService.initial, frame.2) := by
  have material := congrArg (Functor.map (fun result => (result.1, recordView result.2.2)))
    (RegistrationNativeG3MaterializedDirectRun.program_source materials setup (RegistrationNativeWire.ledgerCodec wire) route wire sign
      seed scalar candidate provider seeds work n bounded (RegistrationNativeG3AuditTraceRun.cold frame ∅, world)
      (by simp [RegistrationNativeG3AuditTraceRun.cold, RegistrationNativeHiddenService.initial]))
  have normalized := congrArg (Functor.map (fun result => (result.1, recordView result.2.2)))
    (RegistrationNativeG3MaterializedDirectWorld.program_source materials setup (RegistrationNativeWire.ledgerCodec wire) route wire sign
      seed scalar candidate provider seeds work (RegistrationNativeG3AuditTraceRun.cold frame ∅, world))
  have retained := retained_source setup wire route sign seed scalar candidate provider materials seeds work
    (RegistrationNativeG3MaterializedRetainedSource.sourceFrame frame world)
  have normalize : (fun result => (result.1, recordView result.2.2)) <$>
      (simulateQ (RegistrationNativeG3MaterializedDirectFrontend.handler materials setup (RegistrationNativeWire.ledgerCodec wire) route wire sign
        seed scalar candidate provider seeds) work).run (RegistrationNativeG3AuditTraceRun.cold frame ∅, world) =
      (fun result => (result.1, recordView result.2.2)) <$>
        (simulateQ (RegistrationNativeG3MaterializedDirectFrontend.handler materials setup (RegistrationNativeWire.ledgerCodec wire) route wire sign
          seed scalar candidate provider seeds) work).run
            (RegistrationNativeG3LocalKeys.project (RegistrationNativeG3AuditTraceRun.cold frame ∅, world)) := by
    simpa only [Functor.map_map, Prod.map_def, id_eq, RegistrationNativeG3LocalKeys.project,
      recordView, RegistrationNativeG3MetricWorld.mask, RegistrationNativeWorldView.project,
      RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin,
      RegistrationNativeKemWorldUniform.mask, PqxdhRecordLiftWorld.rawCounters] using normalized
  exact material.trans (normalize.trans (by
    simpa only [RegistrationNativeG3MaterializedRetainedSource.sourceFrame,
      RegistrationNativeG3MaterializedRetainedSource.ordinary, project, RegistrationNativeG3LocalKeys.project,
      RegistrationNativeG3AuditTraceRun.cold, RegistrationNativeHiddenService.initial] using retained))

private theorem embedded_bound (work : OracleComp (RegistrationNativePlatformPublicFrontend.Spec n KemSK) A)
    (count : Nat) (bounded : work.IsQueryBoundP (RegistrationNativePlatformPublicMaterialCaps.IsDemand (n := n) (KemSK := KemSK)) count) :
    (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed work).IsQueryBoundP
      (RegistrationNativePublicCaps.IsDemand (n := n) (KemSK := KemSK)) count := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work count bounded
  intro query
  cases query with
  | inl query =>
      by_cases counted : RegistrationNativePublicCaps.IsDemand (n := n) (KemSK := KemSK) query
      · simp only [RegistrationNativePlatformPublicCoinEmbedding.embed,
          RegistrationNativePlatformPublicMaterialLocal.IsDemand, ite_eq_left counted, isQueryBoundP_query_iff]
        intro _
        decide
      · simp only [RegistrationNativePlatformPublicCoinEmbedding.embed,
          RegistrationNativePlatformPublicMaterialLocal.IsDemand, ite_eq_right counted, isQueryBoundP_query_iff]
        intro impossible
        exact (counted impossible).elim
  | inr coin =>
      simp [RegistrationNativePlatformPublicCoinEmbedding.embed, RegistrationNativePublicFrontend.effect,
        RegistrationNativePublicFrontend.liftLocal, RegistrationNativePlatformPublicMaterialLocal.IsDemand,
        RegistrationNativePublicCaps.IsDemand, isQueryBoundP_query_iff]

/-- Literal corrected source syntax derives finite material room and the complete terminal-record retained-service law from the original raw budget. -/
theorem frontend_source {Platform E : Type} [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (budget : PqxdhDeploymentInterface.Budget)
    (materials : Slot (budget.cap 4 + budget.cap 5) → Material)
    (seeds : RegistrationNativeG3AuditedWorld.Seeds (budget.cap 4 + budget.cap 5))
    (checks : PqxdhServerAuthExperiment.Checks) (source : RegistrationNativeMldsa.Source)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (bounded : RegistrationNativeInterface.Respects budget work)
    (front : RegistrationNativePlatformPublicFrontend.State source Platform)
    (frame : RegistrationNativeSelectiveHiddenInterpreter.State (budget.cap 4 + budget.cap 5) KemSK ProviderState)
    (world : PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5)) :
    let canonical := RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
    let tree := RegistrationNativePlatformMaterializedWhole.tree setup wire sign scalar checks source selectedOwner selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front
    (fun result => (result.1, recordView result.2.2)) <$>
      (simulateQ (RegistrationNativeG3MaterializedLocal.handler true materials seeds setup (RegistrationNativeWire.ledgerCodec canonical)
        route canonical sign seed scalar candidate provider) tree).run (RegistrationNativeG3AuditTraceRun.cold frame ∅, world) =
      (simulateQ (RegistrationNativeG3RetainedCallbacks.keys setup.source
        (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate materials seeds)
        (client setup canonical route sign provider tree
          (RegistrationNativeG3MaterializedRetainedSource.ordinary frame world, frame.1.provider))).run'
          (RegistrationNativeHiddenService.initial, frame.2) := by
  apply program_source
  apply embedded_bound
  exact RegistrationNativePlatformPublicMaterialCaps.run_bound setup checks wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar)
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work budget bounded front

end BeaconcryptCore.Computational.RegistrationNativePlatformG3RetainedRecordSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RetainedRecordSource.retained_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RetainedRecordSource.retained_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RetainedRecordSource.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RetainedRecordSource.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RetainedRecordSource.frontend_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RetainedRecordSource.frontend_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RetainedRecordSource.real_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RetainedRecordSource.real_client
