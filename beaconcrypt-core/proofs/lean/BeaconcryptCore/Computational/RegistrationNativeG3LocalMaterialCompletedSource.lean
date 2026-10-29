-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialCompletion

/-! The actual selective interpreter remains an open World program when its private material cache is completed. Its concrete closed execution agrees with the fixed material-table frontend after restoring exactly that cache. This supplies an open program for the guarded World coupling without assuming a closed-handler source equation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialCompletedSource
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3LocalKeys (State)
open RegistrationNativeG3LocalMaterialCompletion (put fixed lazy openHandler)
variable {n : Nat} {ι KemSK ProviderState Reader Response Value : Type} {base : OracleSpec ι}

def cache (table : Slot n → Material) : RegistrationNativeG3LocalMaterialCompletion.Cache n :=
  ⟨fun slot => some (table slot)⟩

private theorem full_query (table : Slot n → Material)
    (query : (RegistrationNativeG3CellEager.Spec (Slot n) Material).Domain) :
    (RegistrationNativeG3CellEager.lazy query).run (cache table) =
      (fun reply => (reply, cache table)) <$> RegistrationNativeG3CellEager.fixed table query := by
  cases query with
  | inl coin =>
      change (StateT.lift (unifSpec.query coin : ProbComp _)).run (cache table) =
        (fun reply => (reply, cache table)) <$> (unifSpec.query coin : ProbComp _)
      simp only [StateT.run_lift, bind_pure_comp]
  | inr slot =>
      simp only [RegistrationNativeG3CellEager.lazy, RegistrationNativeG3CellEager.fixed,
        QueryImpl.add_apply_inr]
      rw [QueryImpl.withCaching_run_some _ (show cache table slot = some (table slot) from rfl)]
      simp only [map_pure]

private theorem full_program {Result : Type} (table : Slot n → Material)
    (work : OracleComp (RegistrationNativeG3CellEager.Spec (Slot n) Material) Result) :
    (simulateQ RegistrationNativeG3CellEager.lazy work).run (cache table) =
      (fun reply => (reply, cache table)) <$> simulateQ (RegistrationNativeG3CellEager.fixed table) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, full_query,
        bind_map_left, map_bind]
      congr 1
      funext reply
      exact ih reply

/-- Fixing the material oracle is exactly the actual mixed interpreter with its material cache completed; every other reached coordinate is retained. -/
theorem program_source (table : Slot n → Material) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : State n KemSK ProviderState) :
    Prod.map id (fun after => put after (cache table)) <$>
      (simulateQ (fixed table setup codec route wire sign seed scalar candidate provider) work).run before =
      (simulateQ (RegistrationNativeG3LocalKeys.handler setup codec route wire sign seed scalar candidate provider) work).run
        (put before (cache table)) := by
  have source := RegistrationNativeG3LocalMaterialCompletion.program_source setup codec route wire sign seed scalar candidate provider
    work before (cache table)
  have associated := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT RegistrationNativeG3CellEager.lazy
    (openHandler setup codec route wire sign seed scalar candidate provider) work before (cache table)
  rw [full_program] at associated
  simp only [fixed]
  rw [← QueryImpl.simulateQ_mapStateTBase_run]
  rw [← source]
  have projected := congrArg (fun distribution =>
    (fun result => (result.1.1, put result.1.2 result.2)) <$> distribution) associated
  simpa only [Functor.map_map, Prod.map_def, id_eq, Function.comp_apply, lazy] using projected

/-- The literal selective open World program with completed private material cells is the fixed-table frontend under the proved accounting projection. The open program does not receive the hidden seed table. -/
theorem world_source (table : Slot n → Material) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : State n KemSK ProviderState) :
    (fun result => (result.1.1, (result.1.2, RegistrationNativeG3MetricWorld.mask result.2))) <$>
      (simulateQ (CborRecordWorldSimulation.guarded setup codec route)
        ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
          work).run (put before (cache table)).1)).run before.2 =
      Prod.map id (fun after => put after (cache table)) <$>
        (simulateQ (fixed table setup codec route wire sign seed scalar candidate provider) work).run
          (RegistrationNativeG3LocalKeys.project before) := by
  have source := RegistrationNativeG3LocalKeys.original_source setup codec route wire sign seed scalar candidate provider
    work (put before (cache table))
  exact source.trans (program_source table setup codec route wire sign seed scalar candidate provider work
    (RegistrationNativeG3LocalKeys.project before)).symm

end BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialCompletedSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialCompletedSource.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialCompletedSource.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialCompletedSource.world_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialCompletedSource.world_source
