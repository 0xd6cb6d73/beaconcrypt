-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RetainedRecordSource
import BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendCaps
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyClosure
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedRetainedLazy

/-! The actual materialized source closes through the open KEM/key compiler while retaining terminal CTX cache, produced-frame provenance and raw counters beside the original result, ledger and platform state. The finite material source law is derived for any bounded source tree; the concrete corrected frontend supplies that syntactic allowance separately. The named accounting projection preserves these record-data fields literally. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordOpenSource
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3MaterializedRetainedSource (ordinary)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)

noncomputable def retained (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : RegistrationNativePublicInterpreter.State n KemSK) :
    OracleComp (RegistrationNativeOpenRetained.Spec KemSK) (Value × RegistrationNativePlatformPublicWorldObservation.RecordView) :=
  (fun result => (result.1, RegistrationNativePlatformPublicWorldObservation.recordView result.2.world)) <$>
    (simulateQ (RegistrationNativeOpenRetained.compiler setup wire route sign) work).run (RegistrationNativeOpenRetained.mask before)

noncomputable def client (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (frame : RegistrationNativeHiddenInterpreter.State n KemSK ProviderState) (world : PqxdhRecordLiftWorld.State n) :=
  RegistrationNativeOpenKey.client setup.source
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
    (retained setup wire route sign work (ordinary (frame, ∅) world))

/-- Retaining terminal record data leaves the complete original client result and query tree unchanged under its literal projection. -/
theorem client_drop (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (frame : RegistrationNativeHiddenInterpreter.State n KemSK ProviderState) (world : PqxdhRecordLiftWorld.State n) :
    Prod.fst <$> client setup wire route sign seed scalar work frame world =
      RegistrationNativeG3MaterializedRetainedLazy.client setup wire route sign seed scalar work frame world := by
  simp only [client, retained, RegistrationNativeG3MaterializedRetainedLazy.client,
    RegistrationNativeOpenKey.client, RegistrationNativeOpenKey.phaseClient,
    RegistrationNativeOpenRetained.client, RegistrationNativeG3MaterializedRetainedSource.ordinary,
    RegistrationNativePublicRetained.clear, RegistrationNativePublicRootFrame.replace,
    StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map]

/-- The same terminal data and client result erase the chronological observer without changing any source request or effect. -/
theorem client_erase (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (frame : RegistrationNativeHiddenInterpreter.State n KemSK ProviderState) (world : PqxdhRecordLiftWorld.State n) :
    Prod.map Prod.fst id <$> client setup wire route sign seed scalar (RegistrationNativeG2Trace.program work) frame world =
      client setup wire route sign seed scalar work frame world := by
  have erased := congrArg (fun program => client setup wire route sign seed scalar program frame world)
    (RegistrationNativeG2Trace.program_erase work RegistrationNativeG2Trace.initial)
  simpa only [client, retained, RegistrationNativeOpenKey.client, RegistrationNativeOpenKey.phaseClient,
    RegistrationNativeG2Trace.program, StateT.run'_map', simulateQ_map, StateT.run_map, Functor.map_map,
    Prod.map_def, id_eq] using erased

private theorem retained_drop (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : RegistrationNativeOpenRetainedSource.SourceState n KemSK ProviderState) :
    Prod.fst <$> RegistrationNativePlatformG3RetainedRecordSource.client setup wire route sign provider work before =
      RegistrationNativeG3RetainedFrontendRun.retainedClient setup wire route sign provider work before := by
  simp only [RegistrationNativePlatformG3RetainedRecordSource.client, RegistrationNativeG3RetainedFrontendRun.retainedClient,
    StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map]

private theorem record_bound (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativePublicCaps.IsDemand (KemSK := KemSK)) count)
    (frame : RegistrationNativeHiddenInterpreter.State n KemSK ProviderState) (world : PqxdhRecordLiftWorld.State n) :
    (RegistrationNativeG3SelectiveDirectGame.compiled setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
      (RegistrationNativePlatformG3RetainedRecordSource.client setup wire route sign provider work
        (ordinary (frame, ∅) world, frame.provider))).IsQueryBoundP RegistrationNativeG3FirstTouchBound.IsValue count := by
  have cap := RegistrationNativeG3RetainedFrontendCaps.client_bound setup wire route sign seed scalar provider work count bounded (frame, ∅) world
  have drop := retained_drop setup wire route sign provider work (ordinary (frame, ∅) world, frame.provider)
  have mapped := congrArg (RegistrationNativeG3SelectiveDirectGame.compiled setup.source
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))) drop
  simp only [RegistrationNativeG3SelectiveDirectGame.compiled, RegistrationNativeRetainedService.client,
    RegistrationNativeKeyCompiler.client, simulateQ_map, StateT.run'_map'] at mapped
  simp only [RegistrationNativeG3SelectiveDirectGame.compiled, RegistrationNativeRetainedService.client,
    RegistrationNativeKeyCompiler.client] at cap ⊢
  rw [← mapped] at cap
  exact (isQueryBoundP_map_iff _ _ _).mp cap

/-- The actual sampled selected-table source equals the original candidate-independent open-key client closed by the same literal provider and ordinary lazy byte table. -/
theorem program_source (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (bounded : work.IsQueryBoundP (RegistrationNativePublicCaps.IsDemand (KemSK := KemSK)) n)
    (frame : RegistrationNativeHiddenInterpreter.State n KemSK ProviderState) (world : PqxdhRecordLiftWorld.State n) :
    LazyOracleDiscard.LawEq (do
      let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable n
      let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable n
      (fun result => (result.1, RegistrationNativePlatformPublicWorldObservation.recordView result.2.2)) <$>
      (simulateQ (RegistrationNativeG3MaterializedLocal.handler true materials seeds setup (RegistrationNativeWire.ledgerCodec wire) route wire sign seed scalar candidate provider) work).run
        (RegistrationNativeG3AuditTraceRun.cold (frame, ∅) ∅, world))
      ((simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl
        ((simulateQ (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider)
          (client setup wire route sign seed scalar work frame world)).run' (frame.pool, frame.provider))).run' ∅) := by
  let closed := RegistrationNativePlatformG3RetainedRecordSource.client setup wire route sign provider work
    (ordinary (frame, ∅) world, frame.provider)
  have cap := record_bound setup wire route sign seed scalar provider work n bounded frame world
  have source := RegistrationNativeG3SelectiveDirectGame.lazy_source setup.source
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate closed cap
  have sampled : (do
      let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable n
      let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable n
      (fun result => (result.1, RegistrationNativePlatformPublicWorldObservation.recordView result.2.2)) <$>
      (simulateQ (RegistrationNativeG3MaterializedLocal.handler true materials seeds setup (RegistrationNativeWire.ledgerCodec wire) route wire sign seed scalar candidate provider) work).run
        (RegistrationNativeG3AuditTraceRun.cold (frame, ∅) ∅, world)) = (do
      let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable n
      let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable n
      (simulateQ (RegistrationNativeG3RetainedCallbacks.keys setup.source
        (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate materials seeds) closed).run'
          (RegistrationNativeHiddenService.initial, ∅)) := by
    apply bind_congr
    intro materials
    apply bind_congr
    intro seeds
    exact RegistrationNativePlatformG3RetainedRecordSource.program_source setup wire route sign seed scalar candidate provider materials seeds work bounded (frame, ∅) world
  have closed : (simulateQ (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider)
      (client setup wire route sign seed scalar work frame world)).run' (frame.pool, frame.provider) =
      RegistrationNativeG3SelectiveDirectGame.compiled setup.source
        (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) closed := by
    rw [client, RegistrationNativeOpenKeyClosure.key_close]
    rfl
  rw [sampled, closed]
  exact source.symm

end BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordOpenSource


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordOpenSource.client_drop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordOpenSource.client_drop

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordOpenSource.client_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordOpenSource.client_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordOpenSource.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordOpenSource.program_source
