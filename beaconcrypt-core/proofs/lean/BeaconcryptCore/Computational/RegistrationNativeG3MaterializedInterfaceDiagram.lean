-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedPairedSource

/-! Every local native callback has the actual fixed-material source on the same complete private state. Concrete Common and demand laws, plus literal forwarding of preparation and routed KEM, derive the whole adaptive interface diagram under the bilateral accounting projection. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedInterfaceDiagram
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativeG3MaterializedState (Core View)
open RegistrationNativeG3MaterializedLocalCommon (project)
open RegistrationNativeG3MaterializedLocal (handler service fallback)
open RegistrationNativeG3MaterializedLocalSource (actual)
variable {n : Nat} {ι KemSK ProviderState Reader Response Value : Type} {base : OracleSpec ι}
variable (table : Slot n → Material) (setup : Setup base KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)
  (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)

noncomputable def implementation (full : Bool) (seeds : Seeds n) :=
  RegistrationNativeG3MaterializedBeaconComplete.localImpl full setup.source wire.frameWrite sign seeds
    (service (ProviderState := ProviderState) table setup seed scalar candidate)
    (fallback table setup codec route wire sign seed scalar candidate provider)

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (map : A → B) (work : StateT S m A) (before : S) :
    (map <$> work) before = Prod.map map id <$> work before := StateT.run_map map work before

private theorem unchanged (full : Bool) (seeds : Seeds n) (query : (RegistrationBeaconReferenceCompiler.Spec n KemSK).Domain)
    (same : simulateQ (RegistrationNativeG3MaterializedLocal.translate full seeds)
      (RegistrationNativePublicFrontend.liftLocal false query) = RegistrationNativePublicFrontend.liftLocal false query) :
    actual table setup codec route wire sign seed scalar candidate provider full seeds query =
      fallback table setup codec route wire sign seed scalar candidate provider query := by
  apply StateT.ext
  intro before
  simp only [actual, fallback, handler, StateT.run]
  rw [QueryImpl.simulateQ_compose, same]

private theorem demand_project (full : Bool) (seeds : Seeds n) (message : RegistrationNativeRelatedFamily.Message)
    (before : View n KemSK ProviderState) :
    Prod.map id project <$>
      (RegistrationNativeG3MaterializedBeaconComplete.paired full setup.source wire.frameWrite sign seeds
        (service table setup seed scalar candidate) (.inl message)).run before =
      (RegistrationNativeG3MaterializedBeaconComplete.paired full setup.source wire.frameWrite sign seeds
        (service table setup seed scalar candidate) (.inl message)).run (project before) := by
  cases full <;> simp only [RegistrationNativeG3MaterializedBeaconComplete.paired,
    RegistrationNativeG3MaterializedFrontend.known, RegistrationNativeG3MaterializedFrontend.thin,
    Bool.false_eq_true, ite_true, ite_false, RegistrationNativeG3MaterializedFrontend.keys,
    state_map_apply, StateT.run, project, Functor.map_map, Prod.map_def, id_eq]

/-- Every actual local callback has the concrete finite source diagram, retaining all private key/provider/receipt fields and the semantic World. -/
theorem query_source (full : Bool) (seeds : Seeds n) (query : (RegistrationBeaconReferenceCompiler.Spec n KemSK).Domain)
    (before : View n KemSK ProviderState) :
    Prod.map id project <$> (implementation table setup codec route wire sign seed scalar candidate provider full seeds query).run before =
      (actual table setup codec route wire sign seed scalar candidate provider full seeds query).run (project before) := by
  rcases query with message | (message | common) | kem
  · change Prod.map id project <$> (fallback table setup codec route wire sign seed scalar candidate provider (.inl message)).run before = _
    rw [unchanged table setup codec route wire sign seed scalar candidate provider full seeds (.inl message) (by
      simp only [RegistrationNativePublicFrontend.liftLocal, simulateQ_spec_query, RegistrationNativeG3MaterializedLocal.translate])]
    exact RegistrationNativeG3MaterializedLocalSource.fallback_project table setup codec route wire sign seed scalar candidate provider _ before
  · change Prod.map id project <$>
      (RegistrationNativeG3MaterializedBeaconComplete.paired full setup.source wire.frameWrite sign seeds
        (service table setup seed scalar candidate) (.inl message)).run before = _
    rw [demand_project]
    simpa only [actual, RegistrationNativePublicFrontend.liftLocal, simulateQ_spec_query, StateT.run] using
      (RegistrationNativeG3MaterializedLocalKeys.demand_view table setup codec route wire sign seed scalar candidate provider full seeds message (project before)).symm
  · exact RegistrationNativeG3MaterializedPairedSource.common_source table setup codec route wire sign seed scalar candidate provider full seeds common before
  · change Prod.map id project <$> (fallback table setup codec route wire sign seed scalar candidate provider (.inr (.inr kem))).run before = _
    rw [unchanged table setup codec route wire sign seed scalar candidate provider full seeds (.inr (.inr kem)) (by
      rcases kem with query | (query | key)
      all_goals simp only [RegistrationNativePublicFrontend.liftLocal, RegistrationNativePublicFrontend.liftRoutedKem,
        RegistrationNativeKemRouting.route, Bool.false_eq_true, ite_false, simulateQ_spec_query,
        RegistrationNativeG3MaterializedLocal.translate])]
    exact RegistrationNativeG3MaterializedLocalSource.fallback_project table setup codec route wire sign seed scalar candidate provider _ before

/-- The concrete source diagram composes through arbitrary complete native local programs, with no source or prefix-invariant premise. -/
theorem program_source (full : Bool) (seeds : Seeds n)
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value) (before : View n KemSK ProviderState) :
    Prod.map id project <$>
      (simulateQ (implementation table setup codec route wire sign seed scalar candidate provider full seeds) work).run before =
      (simulateQ (actual table setup codec route wire sign seed scalar candidate provider full seeds) work).run (project before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project
    (query_source table setup codec route wire sign seed scalar candidate provider full seeds) work before
end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedInterfaceDiagram
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedInterfaceDiagram.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedInterfaceDiagram.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedInterfaceDiagram.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedInterfaceDiagram.program_source
