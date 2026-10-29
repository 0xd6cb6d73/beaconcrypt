-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeInterpreter

/-! Pure native World-effect components are interpreted on the existing World. The proof retains every outer native field and recombines the unchanged local environment only after the actual effects; it does not flatten an arbitrary mutable environment into itself. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeEffects
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EnvEffects)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

def embed (before : RegistrationNativeExperiment.State n KemSK mlSource)
    (world : PqxdhRecordLiftWorld.State n) : RegistrationNativeExperiment.State n KemSK mlSource :=
  { before with server := { before.server with world := { before.server.world with
    world := (world, before.server.world.world.2) } } }

noncomputable def native (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) :
    QueryImpl (EnvEffects n) (RegistrationNativeExperiment.M n KemSK mlSource) :=
  fun query => RegistrationNativeExperiment.trusted setup checks representation created mlSource (.inl query)

/-- Every adaptive World-effect program retains the entire native envelope, including owner lists, pool, chronological receipts and callback logs. -/
theorem program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (work : OracleComp (EnvEffects n) Value)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    (simulateQ (native setup checks representation created) work).run before =
      Prod.map id (embed before) <$>
        (simulateQ PqxdhRecordLiftWorld.effects work).run before.server.world.world.1 := by
  have step (query : (EnvEffects n).Domain) (world : PqxdhRecordLiftWorld.State n) :
      Prod.map id (embed before) <$> (PqxdhRecordLiftWorld.effects query).run world =
      (native setup checks representation created query).run (embed before world) := by
    simp only [native, RegistrationNativeExperiment.trusted, RegistrationNativeExperiment.world,
      RegistrationNativeExperiment.server, StateT.run, embed, Functor.map_map, Prod.map_def, id_eq]
    rfl
  simpa only [embed] using
    (OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (embed before) step work before.server.world.world.1).symm

/-- The actual Beacon wrapper of a pure World-effect component uses exactly that same World program and cannot overwrite a signing receipt or local callback field. -/
theorem beacon_program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (work : OracleComp (EnvEffects n) Value) :
    RegistrationNativeExperiment.beacon setup checks representation created
      (StateT.lift (StateT.lift (simulateQ RegistrationBeaconReferenceNativeRecord.environment work))) =
      simulateQ (native (n := n) (mlSource := mlSource) setup checks representation created) work := by
  apply StateT.ext
  intro before
  have lifted (owners : RegistrationNativeBeaconFrontend.State mlSource)
      (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) :
      (((StateT.lift (StateT.lift (simulateQ RegistrationBeaconReferenceNativeRecord.environment work)) :
        RegistrationNativeBeaconFrontend.M n KemSK mlSource RegistrationServerRoleBackend.State Value).run owners).run env) =
        (fun reply => ((reply, owners), env)) <$> simulateQ RegistrationBeaconReferenceNativeRecord.environment work := by
    simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, Functor.map_map]
  have restriction : RegistrationNativeExperiment.trusted (n := n) setup checks representation created mlSource ∘ₛ
      RegistrationBeaconReferenceNativeRecord.environment (n := n) (KemSK := KemSK) =
      native (n := n) (mlSource := mlSource) setup checks representation created := by
    funext query
    simp only [QueryImpl.apply_compose, RegistrationBeaconReferenceNativeRecord.environment, simulateQ_spec_query, native]
  unfold RegistrationNativeExperiment.beacon
  simp only [lifted, simulateQ_map, ← QueryImpl.simulateQ_compose, restriction, StateT.run_map]
  rw [program]
  simp only [StateT.run, bind_pure_comp, Functor.map_map,
    RegistrationWorldAgreementCompiler.erase, RegistrationWorldAgreementCompiler.join]
  have evaluated : simulateQ (native setup checks representation created) work before =
      Prod.map id (embed before) <$>
        (simulateQ PqxdhRecordLiftWorld.effects work).run before.server.world.world.1 :=
    program setup checks representation created work before
  rw [evaluated]
  simp only [Functor.map_map, embed, Prod.map_def, id_eq]
  rfl

end BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeEffects

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeEffects.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeEffects.program

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeEffects.beacon_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeEffects.beacon_program
