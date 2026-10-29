-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectFrontend

/-! The actual direct108-byte materialized frontend cannot read the three erased World accounting fields. Its original full result and trace therefore have identical laws from the original reached World and its explicitly named accounting projection, preserving every semantic World/cache coordinate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectWorld
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3LocalKeys (State project)
open RegistrationNativeG3MaterializedDirectFrontend (handler)
variable {n : Nat} {ι KemSK ProviderState Reader Response Value : Type} {base : OracleSpec ι}
variable (table : Slot n → Material) (setup : Setup base KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)
  (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (seeds : RegistrationNativeG3AuditedWorld.Seeds n)

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (map : A → B) (work : StateT S m A) (before : S) :
    (map <$> work) before = Prod.map map id <$> work before := StateT.run_map map work before

private theorem query_project (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (before : State n KemSK ProviderState) :
    Prod.map id project <$> (handler table setup codec route wire sign seed scalar candidate provider seeds query).run before =
      (handler table setup codec route wire sign seed scalar candidate provider seeds query).run (project before) := by
  rcases query with (prepare | (demand | common) | kem) | record
  · simp only [handler, RegistrationNativeG3MaterializedDirectFrontend.onKeys, StateT.run,
      project, Functor.map_map, Prod.map_def, id_eq]
  · simp only [handler, RegistrationNativeG3MaterializedDirectFrontend.onKeys, StateT.run,
      state_map_apply, project, Functor.map_map, Prod.map_def, id_eq]
  all_goals exact RegistrationNativeG3LocalKeys.execute_project setup codec route _ before

/-- Every adaptive continuation keeps its exact complete native result and semantic reached state under the existing World metric projection. -/
theorem program_source (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) (before : State n KemSK ProviderState) :
    Prod.map id project <$> (simulateQ (handler table setup codec route wire sign seed scalar candidate provider seeds) work).run before =
      (simulateQ (handler table setup codec route wire sign seed scalar candidate provider seeds) work).run (project before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project
    (query_project table setup codec route wire sign seed scalar candidate provider seeds) work before

/-- The original complete client observation, including its actual trace, is unchanged by erasing only the independently billed accounting fields at initialization. -/
theorem values_source (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) (before : State n KemSK ProviderState) :
    (simulateQ (handler table setup codec route wire sign seed scalar candidate provider seeds) work).run' before =
      (simulateQ (handler table setup codec route wire sign seed scalar candidate provider seeds) work).run' (project before) := by
  have source := congrArg (Functor.map Prod.fst)
    (program_source table setup codec route wire sign seed scalar candidate provider seeds work before)
  simpa only [StateT.run'_eq, Functor.map_map, Prod.map_def, id_eq] using source

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectWorld
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectWorld.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectWorld.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectWorld.values_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectWorld.values_source
