-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedProtocol
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterializedTables
import BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedFrontend
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyExecution
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldObservation
/-! Whole-program assembly for the actual corrected material44 client. The literal callback source equations are joined with completed private material cells and fixed-seed World realization. The public endpoints derive their whole-callback translation internally and preserve the actual common platform state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedWhole
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

private theorem projected (full : Bool) (seeds : Seeds n)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) A) (before : State n KemSK ProviderState) :
    (simulateQ (handler full table seeds setup codec route wire sign seed scalar candidate provider) work).run' before =
      (simulateQ (handler full table seeds setup codec route wire sign seed scalar candidate provider) work).run' (project before) := by
  have same := congrArg (Functor.map Prod.fst)
    (RegistrationNativeG3MaterializedLocalKeys.fixed_program_project table setup codec route wire sign seed scalar candidate provider
      (simulateQ (translate full seeds) work) before)
  simpa only [handler, QueryImpl.simulateQ_compose, StateT.run'_eq, Functor.map_map, Prod.map_def, id_eq] using same

private theorem source_of_translation (seeds : Seeds n)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) A)
    (same : simulateQ (translate true seeds) work = simulateQ (translate false seeds) work)
    (before : State n KemSK ProviderState) :
    (simulateQ (handler true table seeds setup codec route wire sign seed scalar candidate provider) work).run' before =
      Prod.fst <$> RegistrationNativeG3GuardedCoupling.known setup codec route seeds
        ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
          work).run (put before (cache table)).1) before.2 := by
  have literal : (simulateQ (handler true table seeds setup codec route wire sign seed scalar candidate provider) work).run' (project before) =
      (simulateQ (handler false table seeds setup codec route wire sign seed scalar candidate provider) work).run' (project before) := by
    simp only [handler, QueryImpl.simulateQ_compose, same]
  have mixed := (projected table setup codec route wire sign seed scalar candidate provider true seeds work before).trans literal
  have actual := congrArg (Functor.map Prod.fst)
    (RegistrationNativeG3LocalMaterialCompletedSource.world_source table setup codec route wire sign seed scalar candidate provider
      (simulateQ (translate false seeds) work) before)
  have pulled := congrArg (fun program =>
    (fun result => result.1.1) <$> (simulateQ (CborRecordWorldSimulation.guarded setup codec route) program).run before.2)
    (RegistrationNativeG3MaterializedSelectivePullback.program_source setup wire sign seed scalar candidate provider seeds work
      (put before (cache table)).1)
  simp only [handler, QueryImpl.simulateQ_compose, StateT.run'_eq] at mixed
  simp only [Functor.map_map, Prod.map_def, id_eq] at actual
  have sameRealize : RegistrationNativeG3GuardedMaterializedWorld.realize seeds = RegistrationNativeG3MaterializedWorld.realize seeds := rfl
  have joined := mixed.trans (actual.symm.trans pulled.symm)
  simpa only [StateT.run'_eq, RegistrationNativeG3GuardedCoupling.known,
    RegistrationNativeG3GuardedMaterializedWorld.source, handler, sameRealize, QueryImpl.simulateQ_compose,
    Functor.map_map, Prod.map_def, id_eq, Function.comp_def] using joined
private theorem source_record_of_translation (seeds : Seeds n)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) A)
    (same : simulateQ (translate true seeds) work = simulateQ (translate false seeds) work)
    (before : State n KemSK ProviderState) :
    (fun result => (result.1, RegistrationNativePlatformPublicWorldObservation.recordView result.2.2)) <$>
      (simulateQ (handler true table seeds setup codec route wire sign seed scalar candidate provider) work).run before =
      (fun result => (result.1.1, RegistrationNativePlatformPublicWorldObservation.recordView result.2)) <$>
        (simulateQ (RegistrationNativeG3GuardedMaterializedWorld.source setup codec route seeds)
          ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
            work).run (put before (cache table)).1)).run before.2 := by
  have metric := congrArg (Functor.map (fun result =>
      (result.1, RegistrationNativePlatformPublicWorldObservation.recordView result.2.2)))
    (RegistrationNativeG3MaterializedLocalKeys.fixed_program_project table setup codec route wire sign seed scalar candidate provider
      (simulateQ (translate true seeds) work) before)
  have literal :
      (simulateQ (handler true table seeds setup codec route wire sign seed scalar candidate provider) work).run (project before) =
        (simulateQ (handler false table seeds setup codec route wire sign seed scalar candidate provider) work).run (project before) := by
    simp only [handler, QueryImpl.simulateQ_compose, same]
  have mixed := congrArg (Functor.map (fun result =>
      (result.1, RegistrationNativePlatformPublicWorldObservation.recordView result.2.2))) literal
  simp only [handler, QueryImpl.simulateQ_compose, Functor.map_map, Prod.map_def, id_eq,
    project, RegistrationNativePlatformPublicWorldObservation.recordView, RegistrationNativeG3MetricWorld.mask,
    RegistrationNativeWorldView.project, RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin,
    RegistrationNativeKemWorldUniform.mask] at metric mixed
  have actual := congrArg (Functor.map (fun result =>
      (result.1, RegistrationNativePlatformPublicWorldObservation.recordView result.2.2)))
    (RegistrationNativeG3LocalMaterialCompletedSource.world_source table setup codec route wire sign seed scalar candidate provider
      (simulateQ (translate false seeds) work) before)
  have pulled := congrArg (fun program =>
      (fun result => (result.1.1, RegistrationNativePlatformPublicWorldObservation.recordView result.2)) <$>
        (simulateQ (CborRecordWorldSimulation.guarded setup codec route) program).run before.2)
    (RegistrationNativeG3MaterializedSelectivePullback.program_source setup wire sign seed scalar candidate provider seeds work
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

private theorem world_embedding :
    RegistrationNativeSelectiveHiddenInterpreter.handler (n := n) setup wire sign seed scalar candidate provider ∘ₛ
      RegistrationNativePlatformPublicCoinEmbedding.embed =
      RegistrationNativePlatformSelectiveEntropyBackend.handler setup wire sign seed scalar candidate provider := by
  funext query
  cases query with
  | inl query =>
      simp only [QueryImpl.apply_compose, RegistrationNativePlatformPublicCoinEmbedding.embed,
        simulateQ_spec_query, RegistrationNativePlatformSelectiveEntropyBackend.handler]
  | inr coin =>
      funext before
      simp only [QueryImpl.apply_compose, RegistrationNativePlatformPublicCoinEmbedding.embed,
        RegistrationNativePublicFrontend.effect, RegistrationNativePublicFrontend.liftLocal, simulateQ_spec_query,
        RegistrationNativeSelectiveHiddenInterpreter.handler, RegistrationNativeSelectiveHiddenInterpreter.onBase,
        RegistrationNativeHiddenInterpreter.handler, RegistrationNativeHiddenInterpreter.effect,
        RegistrationNativePlatformSelectiveEntropyBackend.handler, StateT.run_lift, bind_pure_comp,
        PqxdhRecordLiftInterface.effectLift, Functor.map_map]
      rfl
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

noncomputable def tree (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (front : RegistrationNativePlatformPublicFrontend.State source Platform) :=
  simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
    (RegistrationNativePlatformPublicFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept
      (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      serverKeyId bounds mode work front)

noncomputable def world (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (front : RegistrationNativePlatformPublicFrontend.State source Platform)
    (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) :=
  (simulateQ (RegistrationNativePlatformSelectiveEntropyBackend.handler setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
    sign seed scalar candidate provider)
    (RegistrationNativePlatformPublicFrontend.run setup checks wire source sign selectedOwner selectedAccept
      (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      serverKeyId bounds mode work front)).run before

/-- The full actual corrected raw frontend is the literal opaque-slot World program after only private fixed-seed materialization. Its complete callback translation is discharged from actual bodies, with no whole-controller equation supplied by the caller. -/
theorem run_source (seeds : Seeds n) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (front : RegistrationNativePlatformPublicFrontend.State source Platform)
    (before : State n KemSK ProviderState) :
    (simulateQ (handler true table seeds setup codec route (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      sign seed scalar candidate provider)
      (tree setup wire sign scalar checks source selectedOwner selectedAccept view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front)).run' before =
      Prod.fst <$> RegistrationNativeG3GuardedCoupling.known setup codec route seeds
        (world setup wire sign seed scalar candidate provider checks source selectedOwner selectedAccept view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front (put before (cache table)).1) before.2 := by
  have compared := source_of_translation table setup codec route (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
    sign seed scalar candidate provider seeds
    (tree setup wire sign scalar checks source selectedOwner selectedAccept view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front)
    (RegistrationNativePlatformMaterializedFrontend.run_source setup checks wire source sign selectedOwner selectedAccept
      (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      seeds serverKeyId bounds mode work front) before
  simpa only [tree, world, ← QueryImpl.simulateQ_compose, world_embedding] using compared
/-- The same whole-source law retains terminal cache, crypto-produced frames and raw attempt counters, with the named accounting projection discharged internally. -/
theorem run_record_source (seeds : Seeds n) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (front : RegistrationNativePlatformPublicFrontend.State source Platform)
    (before : State n KemSK ProviderState) :
    (fun result => (result.1, RegistrationNativePlatformPublicWorldObservation.recordView result.2.2)) <$>
      (simulateQ (handler true table seeds setup codec route (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
        sign seed scalar candidate provider)
        (tree setup wire sign scalar checks source selectedOwner selectedAccept view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front)).run before =
      (fun result => (result.1.1, RegistrationNativePlatformPublicWorldObservation.recordView result.2)) <$>
        (simulateQ (RegistrationNativeG3GuardedMaterializedWorld.source setup codec route seeds)
          (world setup wire sign seed scalar candidate provider checks source selectedOwner selectedAccept view failure allocation
            reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front (put before (cache table)).1)).run before.2 := by
  have compared := source_record_of_translation table setup codec route (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
    sign seed scalar candidate provider seeds
    (tree setup wire sign scalar checks source selectedOwner selectedAccept view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front)
    (RegistrationNativePlatformMaterializedFrontend.run_source setup checks wire source sign selectedOwner selectedAccept
      (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      seeds serverKeyId bounds mode work front) before
  simpa only [tree, world, ← QueryImpl.simulateQ_compose, world_embedding] using compared
end BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedWhole

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedWhole.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedWhole.run_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedWhole.run_record_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedWhole.run_record_source
