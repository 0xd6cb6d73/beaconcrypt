-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeScalarLeading

/-! A pure World-effect prefix can be closed before an arbitrary mutable Beacon continuation. This specialized law preserves its current environment and private state; it does not assert flattening for arbitrary mutable nested environments. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeScalarEffectBind
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationBeaconReferenceNativeEffects (embed native)
variable {n : Nat} {ι KemSK X Y : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

theorem effects_lift (work : OracleComp (EnvEffects n) X) :
    simulateQ (RegistrationNativeBeaconFrontend.effect (n := n) (KemSK := KemSK)
      (mldsaSource := source) (Auxiliary := RegistrationServerRoleBackend.State)) work =
      StateT.lift (StateT.lift (simulateQ RegistrationBeaconReferenceNativeRecord.environment work)) := by
  change simulateQ ((RegistrationBeaconReferenceNativeRecord.environment (n := n) (KemSK := KemSK)).liftTarget
    (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State)) work = _
  rw [simulateQ_liftTarget]
  rfl

/-- Closing the actual World-only prefix before the mutable native continuation retains the precise native poststate. -/
theorem beacon_bind (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (work : OracleComp (EnvEffects n) X)
    (next : X → RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Y)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    (RegistrationNativeExperiment.beacon setup checks representation created
      (simulateQ RegistrationNativeBeaconFrontend.effect work >>= next)).run before = (do
        let result ← (simulateQ PqxdhRecordLiftWorld.effects work).run before.server.world.world.1
        (RegistrationNativeExperiment.beacon setup checks representation created (next result.1)).run (embed before result.2)) := by
  rw [effects_lift]
  have restriction : RegistrationNativeExperiment.trusted (n := n) setup checks representation created source ∘ₛ
      RegistrationBeaconReferenceNativeRecord.environment (n := n) (KemSK := KemSK) = native setup checks representation created := by
    funext query
    simp only [QueryImpl.apply_compose, RegistrationBeaconReferenceNativeRecord.environment,
      simulateQ_spec_query, native]
  unfold RegistrationNativeExperiment.beacon
  simp only [StateT.run_bind, StateT.run_lift,
    bind_pure_comp, simulateQ_bind, bind_map_left,
    ← QueryImpl.simulateQ_compose, restriction, RegistrationBeaconReferenceNativeEffects.program,
    map_bind]
  apply bind_congr
  rintro ⟨reply, afterWorld⟩
  simp only [Prod.map_def, id_eq, embed,
    RegistrationWorldAgreementCompiler.erase, RegistrationWorldAgreementCompiler.join]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeScalarEffectBind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarEffectBind.effects_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarEffectBind.effects_lift
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarEffectBind.beacon_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarEffectBind.beacon_bind
