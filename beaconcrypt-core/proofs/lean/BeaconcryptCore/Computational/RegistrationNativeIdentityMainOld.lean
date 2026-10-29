-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainOrdinary

/-! Restoring a fixed native owner roster around the public ambient context recovers the actual original Main trusted interpreter, including every private KEM, auxiliary and World coordinate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityMainOld
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityWorld (Context ambient)
open RegistrationNativeIdentityMainOrdinary (attach)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

/-- Actual ambient primitives do not read the fixed independent native owner roster. -/
theorem trusted_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (owners : RegistrationNativeBeaconFrontend.State mlSource)
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) (before : Context n KemSK) :
    Prod.map id (attach owners) <$> (ambient (mlSource := mlSource) setup checks representation created query).run before =
      (RegistrationNativeExperiment.trusted setup checks representation created mlSource query).run (attach owners before) := by
  cases query <;>
    simp only [ambient, RegistrationNativeExperiment.trusted, RegistrationNativeExperiment.world,
      RegistrationNativeExperiment.server, StateT.run, RegistrationNativeIdentityWorld.project,
      RegistrationNativeIdentityWorld.embed, attach, Functor.map_map, Prod.map, id_eq]
  all_goals simp only [map_bind, map_pure]

/-- Complete adaptive ambient source programs restore the original native trusted execution. -/
theorem trusted_program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (owners : RegistrationNativeBeaconFrontend.State mlSource)
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value) (before : Context n KemSK) :
    Prod.map id (attach owners) <$> (simulateQ (ambient (mlSource := mlSource) setup checks representation created) work).run before =
      (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource) work).run (attach owners before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (attach owners)
    (trusted_source setup checks representation created owners) work before

def assemble (result : ((Value × RegistrationNativeBeaconFrontend.State mlSource) ×
    RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × Context n KemSK) :
    Value × RegistrationNativeExperiment.State n KemSK mlSource :=
  (result.1.1.1, ⟨{ result.2.server with
      world := RegistrationWorldAgreementCompiler.join result.1.2 result.2.server.world.world.1 },
      result.1.1.2, result.2.kem, result.2.parsedAccepts⟩)

/-- Whole original native Beacon execution is recovered from its full owner/Env ambient source program. -/
theorem beacon_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeBeaconFrontend.M n KemSK mlSource RegistrationServerRoleBackend.State Value)
    (owners : RegistrationNativeBeaconFrontend.State mlSource) (before : Context n KemSK) :
    assemble <$> (simulateQ (ambient (mlSource := mlSource) setup checks representation created)
      ((work.run owners).run (RegistrationWorldAgreementCompiler.erase before.server.world))).run before =
      (RegistrationNativeExperiment.beacon setup checks representation created work).run (attach owners before) := by
  have law := congrArg (fun distribution => (fun result => (result.1.1.1,
    { result.2 with
      beacons := result.1.1.2
      server := { result.2.server with world :=
        RegistrationWorldAgreementCompiler.join result.1.2 result.2.server.world.world.1 } })) <$> distribution)
    (trusted_program setup checks representation created owners
      ((work.run owners).run (RegistrationWorldAgreementCompiler.erase before.server.world)) before)
  unfold assemble
  simp only [RegistrationNativeExperiment.beacon, StateT.run, bind_pure_comp,
    Functor.map_map, Prod.map, id_eq, attach] at law ⊢
  exact law

end BeaconcryptCore.Computational.RegistrationNativeIdentityMainOld

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainOld.trusted_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainOld.trusted_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainOld.trusted_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainOld.trusted_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainOld.beacon_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainOld.beacon_source
