-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocal
import BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialFixed
import BeaconcryptCore.Computational.RegistrationNativeG3LocalKeyFrame

/-! The concrete fixed-material callbacks retain the same bilateral World accounting view as the actual lazy source. Their exact demand source uses the current private allocator and known108 table and the literal receipt-separating state bijection. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocalKeys
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativeG3LocalKeys (State project)
open RegistrationNativeG3LocalMaterialCompletion (fixed)
open RegistrationNativeG3MaterializedState (View view restore)
variable {n : Nat} {ι KemSK ProviderState Reader Response Value : Type} {base : OracleSpec ι}
variable (table : Slot n → Material) (setup : Setup base KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)
  (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)

/-- Every actual fixed-material callback has the same bilateral accounting projection, including its unchanged provider and guarded record callbacks. -/
theorem fixed_query_project (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (before : State n KemSK ProviderState) :
    Prod.map id project <$> (fixed table setup codec route wire sign seed scalar candidate provider query).run before =
      (fixed table setup codec route wire sign seed scalar candidate provider query).run (project before) := by
  rcases query with (message | (message | common) | kem) | record
  · rw [RegistrationNativeG3LocalMaterialFixed.fixed_prepare, RegistrationNativeG3LocalMaterialFixed.fixed_prepare]
    simp only [project, Functor.map_map, Prod.map_def, id_eq]
  · rw [RegistrationNativeG3LocalMaterialFixed.fixed_demand, RegistrationNativeG3LocalMaterialFixed.fixed_demand]
    simp only [project, Functor.map_map, Prod.map_def, id_eq]
  all_goals rw [RegistrationNativeG3LocalMaterialFixed.fixed_ordinary table setup codec route wire sign seed scalar candidate provider _ (by trivial)]
  all_goals exact RegistrationNativeG3LocalKeys.execute_project setup codec route _ before

/-- The actual complete fixed-material client retains the derived accounting view through every adaptive continuation. -/
theorem fixed_program_project (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : State n KemSK ProviderState) :
    Prod.map id project <$> (simulateQ (fixed table setup codec route wire sign seed scalar candidate provider) work).run before =
      (simulateQ (fixed table setup codec route wire sign seed scalar candidate provider) work).run (project before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project
    (fixed_query_project table setup codec route wire sign seed scalar candidate provider) work before

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (map : A → B) (work : StateT S m A) (before : S) :
    (map <$> work) before = Prod.map map id <$> work before := StateT.run_map map work before

private theorem fixed_demand_apply (message : RegistrationNativeRelatedFamily.Message) (before : State n KemSK ProviderState) :
    fixed table setup codec route wire sign seed scalar candidate provider (.inl (.inr (.inl (.inl message)))) before =
      (fun result => (result.1, (RegistrationNativeG3LocalKeys.putKeys before.1 result.2, before.2))) <$>
        simulateQ (RegistrationNativeG3CellEager.fixed table)
          ((RegistrationNativeG3LocalMaterialService.demand setup.source
            (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
            (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate message).run
              (RegistrationNativeG3LocalKeys.getKeys before.1)) :=
  RegistrationNativeG3LocalMaterialFixed.fixed_demand table setup codec route wire sign seed scalar candidate provider message before

/-- The actual fixed-material demand is exactly the shared finite key service under the full private-state bijection, including optional failure and current allocation metadata. -/
theorem demand_view (full : Bool) (seeds : Seeds n) (message : RegistrationNativeRelatedFamily.Message)
    (before : View n KemSK ProviderState) :
    Prod.map id view <$>
      (RegistrationNativeG3MaterializedLocal.handler full table seeds setup codec route wire sign seed scalar candidate provider
        (.inl (.inr (.inl (.inl message))))).run (restore before) =
      (RegistrationNativeG3MaterializedBeaconComplete.paired full setup.source wire.frameWrite sign seeds
        (RegistrationNativeG3MaterializedLocal.service table setup seed scalar candidate) (.inl message)).run before := by
  cases full <;>
    simp only [RegistrationNativeG3MaterializedLocal.handler, QueryImpl.apply_compose,
      RegistrationNativeG3MaterializedLocal.translate, Bool.false_eq_true, ite_true, ite_false,
      simulateQ_map, simulateQ_spec_query, state_map_apply,
      fixed_demand_apply,
      RegistrationNativeG3MaterializedBeaconComplete.paired,
      RegistrationNativeG3MaterializedFrontend.known, RegistrationNativeG3MaterializedFrontend.thin,
      RegistrationNativeG3MaterializedFrontend.keys, RegistrationNativeG3MaterializedLocal.service,
      StateT.run, view, restore, RegistrationNativeG3MaterializedState.getKeys,
      RegistrationNativeG3MaterializedState.putKeys, RegistrationNativeG3LocalKeys.getKeys,
      RegistrationNativeG3LocalKeys.putKeys, Functor.map_map, Prod.map_def, id_eq]
end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocalKeys
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocalKeys.fixed_query_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocalKeys.fixed_query_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocalKeys.fixed_program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocalKeys.fixed_program_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocalKeys.demand_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocalKeys.demand_view
