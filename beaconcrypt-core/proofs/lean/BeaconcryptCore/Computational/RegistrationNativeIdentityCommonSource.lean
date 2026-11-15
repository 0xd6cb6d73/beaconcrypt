-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation

/-! Actual ordinary effects, randomness and mutable Env updates are shared by the indexed-identity frontend and the original native source. These component equalities preserve the private identity prefix and both original randomness counters through the concrete ambient interpreter. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCommonSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentitySourceSimulation
open RegistrationWorldAgreementCompiler (EnvState)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

private theorem lift_effect (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    (liftAmbient (StateT.lift ((RegistrationNativeIdentityFrontend.Ambient n KemSK).query (.inl query))) :
      RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source _) =
      RegistrationNativeIdentityFrontend.effect query := by
  apply StateT.ext
  intro current
  apply StateT.ext
  intro env
  simp only [liftAmbient, RegistrationNativeIdentityFrontend.effect, StateT.run_lift,
    bind_pure_comp, StateT.run_map, simulateQ_map, simulateQ_spec_query,
    RegistrationNativeIdentityFrontend.ambientLift]
  rfl

private theorem lift_modify (change : EnvState Auxiliary → EnvState Auxiliary) :
    (liftAmbient (modify change) : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Unit) =
      RegistrationNativeIdentityFrontend.updateEnv change := by
  apply StateT.ext
  intro current
  apply StateT.ext
  intro env
  simp only [liftAmbient, RegistrationNativeIdentityFrontend.updateEnv, StateT.run_lift,
    StateT.run_modify, simulateQ_pure, StateT.run_map, bind_pure_comp, map_pure]
  rfl

theorem effect_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (seeds : List PqxdhJointIdentity.IdentitySeed)
    (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Related (Auxiliary := Auxiliary) (source := source) setup checks representation created seeds
      (RegistrationNativeIdentityFrontend.effect query) (RegistrationNativeBeaconFrontend.effect query) := by
  rw [← lift_effect]
  exact related_lift setup checks representation created seeds _

theorem effect_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Keeps (Auxiliary := Auxiliary) (source := source) setup checks representation created
      (RegistrationNativeIdentityFrontend.effect query) := by
  rw [← lift_effect]
  exact keeps_lift setup checks representation created _

theorem sample_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (seeds : List PqxdhJointIdentity.IdentitySeed)
    (work : ProbComp Value) :
    Related (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created seeds
      (RegistrationNativeIdentityFrontend.sample work) (RegistrationNativeBeaconFrontend.sample work) :=
  related_program setup checks representation created seeds _ _
    (fun query => effect_source setup checks representation created seeds (.inl query))
    (fun query => effect_keeps setup checks representation created (.inl query)) work

theorem sample_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (work : ProbComp Value) :
    Keeps (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created
      (RegistrationNativeIdentityFrontend.sample work) :=
  keeps_program setup checks representation created _
    (fun query => effect_keeps setup checks representation created (.inl query)) work

theorem update_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (seeds : List PqxdhJointIdentity.IdentitySeed)
    (change : EnvState Auxiliary → EnvState Auxiliary) :
    Related (n := n) (source := source) setup checks representation created seeds
      (RegistrationNativeIdentityFrontend.updateEnv change) (RegistrationNativeBeaconFrontend.updateEnv change) := by
  rw [← lift_modify]
  exact related_lift setup checks representation created seeds _

theorem update_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (change : EnvState Auxiliary → EnvState Auxiliary) :
    Keeps (n := n) (source := source) setup checks representation created
      (RegistrationNativeIdentityFrontend.updateEnv change) := by
  rw [← lift_modify]
  exact keeps_lift setup checks representation created _

end BeaconcryptCore.Computational.RegistrationNativeIdentityCommonSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCommonSource.effect_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCommonSource.effect_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCommonSource.effect_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCommonSource.effect_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCommonSource.sample_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCommonSource.sample_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCommonSource.sample_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCommonSource.sample_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCommonSource.update_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCommonSource.update_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCommonSource.update_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCommonSource.update_keeps
