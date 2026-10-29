-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendOrdinary
import BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendKem

/-! The complete actual materialized native frontend is the original open retained compiler closed by its literal actual KEM provider and the actual selective direct108-byte service. Every source equality is derived from callbacks and keeps the original adaptive result, ledger and chronological observer together. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendRun
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3RetainedFrontendSource (Frame project handler)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)
  (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (materials : Slot n → Material) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)

/-- The complete original dispatch has the exact same reply and semantic state after the explicit full source reassembly. -/
theorem query_source (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (before : Frame n KemSK ProviderState) :
    Prod.map id project <$> (handler setup wire route sign seed scalar candidate provider materials seeds query).run before =
      (RegistrationNativeG3MaterializedDirectFrontend.handler materials setup (RegistrationNativeWire.ledgerCodec wire) route wire sign seed scalar candidate provider seeds query).run (project before) := by
  rcases query with (prepare | (demand | (publication | effect)) | kem) | record
  · exact RegistrationNativeG3RetainedFrontendSource.prepare_source setup wire route sign seed scalar candidate provider materials seeds prepare before
  · exact RegistrationNativeG3RetainedFrontendSource.demand_source setup wire route sign seed scalar candidate provider materials seeds demand before
  · exact RegistrationNativeG3RetainedFrontendOrdinary.publication_source setup wire route sign seed scalar candidate provider materials seeds publication before
  · exact RegistrationNativeG3RetainedFrontendOrdinary.effect_source setup wire route sign seed scalar candidate provider materials seeds effect before
  · exact RegistrationNativeG3RetainedFrontendKem.routed_source setup wire route sign seed scalar candidate provider materials seeds kem before
  · exact RegistrationNativeG3RetainedFrontendOrdinary.record_source setup wire route sign seed scalar candidate provider materials seeds record before

/-- Every adaptive native frontend continuation preserves its complete original result and semantic state under the same actual source map. -/
theorem program_source (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) (before : Frame n KemSK ProviderState) :
    Prod.map id project <$> (simulateQ (handler setup wire route sign seed scalar candidate provider materials seeds) work).run before =
      (simulateQ (RegistrationNativeG3MaterializedDirectFrontend.handler materials setup (RegistrationNativeWire.ledgerCodec wire) route wire sign seed scalar candidate provider seeds) work).run (project before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project
    (query_source setup wire route sign seed scalar candidate provider materials seeds) work before

noncomputable def retainedClient (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : RegistrationNativeOpenRetainedSource.SourceState n KemSK ProviderState) :
    OracleComp RegistrationNativeRetainedService.Spec Value :=
  (simulateQ (RegistrationNativeOpenRetainedSource.close provider)
    ((simulateQ (RegistrationNativeOpenRetained.compiler setup wire route sign) work).run'
      (RegistrationNativeOpenRetained.mask before.1))).run' (before.1.pool, before.2)

/-- The same full native result, including any chronological observer already in it, is produced by the original retained compiler and literal external provider. -/
theorem values_source (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) (before : Frame n KemSK ProviderState) :
    (simulateQ (RegistrationNativeG3MaterializedDirectFrontend.handler materials setup (RegistrationNativeWire.ledgerCodec wire) route wire sign seed scalar candidate provider seeds) work).run' (project before) =
      (simulateQ (RegistrationNativeG3RetainedCallbacks.keys setup.source
        (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate materials seeds)
        (retainedClient setup wire route sign provider work before.1)).run' before.2 := by
  have same := congrArg (Functor.map Prod.fst)
    (program_source setup wire route sign seed scalar candidate provider materials seeds work before)
  have original := congrArg (Functor.map Prod.fst)
    (RegistrationNativeOpenRetainedSource.program_project setup wire route sign provider work before.1)
  simp only [Functor.map_map, Prod.map_def, id_eq] at same original
  let keysImpl := RegistrationNativeG3RetainedCallbacks.keys setup.source
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate materials seeds
  have nested := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT keysImpl
    (RegistrationNativeOpenRetainedSource.source setup wire route sign provider) work before.1 before.2
  have nestedValues := congrArg (Functor.map (fun result => result.1.1)) nested
  have reference := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (RegistrationNativeOpenRetainedSource.close provider)
    (RegistrationNativeOpenRetained.compiler setup wire route sign)
    work (RegistrationNativeOpenRetained.mask before.1.1) (before.1.1.pool, before.1.2)
  have referenceValues := congrArg (Functor.map (fun result => result.1.1)) reference
  simp only [StateT.run'_eq, Functor.map_map,
    ] at nestedValues referenceValues ⊢
  have sourceEq : Prod.fst <$> (simulateQ (handler setup wire route sign seed scalar candidate provider materials seeds) work).run before =
      (simulateQ keysImpl ((simulateQ (RegistrationNativeOpenRetainedSource.source setup wire route sign provider) work).run' before.1)).run' before.2 := by
    simpa only [handler, keysImpl, StateT.run'_eq, simulateQ_map, StateT.run_map,
      Functor.map_map, Prod.map_def, id_eq] using nestedValues.symm
  have referenceEq : Prod.fst <$> (simulateQ (RegistrationNativeOpenRetainedSource.reference setup wire route sign provider) work).run
      (RegistrationNativeOpenRetainedSource.project before.1) = retainedClient setup wire route sign provider work before.1 := by
    simpa only [RegistrationNativeOpenRetainedSource.reference, RegistrationNativeOpenRetainedSource.project,
      retainedClient, StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map,
      Prod.map_def, id_eq] using referenceValues.symm
  have closed := congrArg (fun program => (simulateQ keysImpl program).run' before.2) (original.trans referenceEq)
  exact same.symm.trans (sourceEq.trans closed)

end BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendRun
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendRun.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendRun.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendRun.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendRun.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendRun.values_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendRun.values_source
