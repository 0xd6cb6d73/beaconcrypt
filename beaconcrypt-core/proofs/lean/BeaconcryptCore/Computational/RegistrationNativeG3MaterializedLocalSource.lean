-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocalCommon

/-! The actual materialized local callback interpreter retains the exact routed fixed-material source under a bijection of private state. The finite key/Common interface is compared using a bilateral accounting projection, so no prefix-state invariant is a caller premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocalSource
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativeG3MaterializedState (Core View view restore)
open RegistrationNativeG3MaterializedLocalCommon (project)
open RegistrationNativeG3MaterializedLocal (handler service fallback)
open RegistrationNativeG3LocalMaterialCompletion (fixed)
variable {n : Nat} {ι KemSK ProviderState Reader Response Value : Type} {base : OracleSpec ι}
variable (table : Slot n → Material) (setup : Setup base KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)
  (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)

noncomputable def actual (full : Bool) (seeds : Seeds n) :
    QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (View n KemSK ProviderState) ProbComp) := fun query before =>
  Prod.map id view <$>
    (simulateQ (handler full table seeds setup codec route wire sign seed scalar candidate provider)
      (RegistrationNativePublicFrontend.liftLocal false query)).run (restore before)

/-- The executable fallback retains exactly the named accounting view on both sides of every local callback. -/
theorem fallback_project (query : (RegistrationBeaconReferenceCompiler.Spec n KemSK).Domain)
    (before : View n KemSK ProviderState) :
    Prod.map id project <$> (fallback table setup codec route wire sign seed scalar candidate provider query).run before =
      (fallback table setup codec route wire sign seed scalar candidate provider query).run (project before) := by
  have source := RegistrationNativeG3MaterializedLocalKeys.fixed_program_project table setup codec route wire sign seed scalar candidate provider
    (RegistrationNativePublicFrontend.liftLocal false query) (restore before)
  have mapped := congrArg (Functor.map (Prod.map id view)) source
  simpa only [fallback, StateT.run, Functor.map_map, Prod.map_def, id_eq, Function.comp_def,
    project, RegistrationNativeG3LocalKeys.project, view, restore] using mapped

/-- Arbitrary local continuations keep the complete actual fixed-material execution under the literal private-state bijection. -/
theorem actual_program (full : Bool) (seeds : Seeds n)
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value)
    (before : RegistrationNativeG3LocalKeys.State n KemSK ProviderState) :
    Prod.map id view <$>
      (simulateQ (handler full table seeds setup codec route wire sign seed scalar candidate provider)
        (simulateQ (RegistrationNativePublicFrontend.liftLocal false) work)).run before =
      (simulateQ (actual table setup codec route wire sign seed scalar candidate provider full seeds) work).run (view before) := by
  rw [← QueryImpl.simulateQ_compose]
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query current
  simp only [actual, QueryImpl.apply_compose, StateT.run,
    RegistrationNativeG3MaterializedState.restore_view]

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocalSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocalSource.fallback_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocalSource.fallback_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocalSource.actual_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocalSource.actual_program
