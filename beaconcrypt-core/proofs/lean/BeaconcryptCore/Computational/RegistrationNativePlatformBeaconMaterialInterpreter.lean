-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialKnown
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeInterpreter
/-! Private reference demand uses the root actually stored by preparation. The corrected public continuation then runs only its closed EnvEffects program. The full private memo, related-family bookkeeping and Native state remain in the joint execution; no earlier finishing profile is equated with this one. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialInterpreter
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationBeaconReferenceCompiler (SelectedOwner Spec effect trustedLift)
open RegistrationBeaconReferenceNativeRecord (environment)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceNativeInterpreter (State implementation)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

def demand (message : RegistrationNativeRelatedFamily.Message) : OracleComp (Spec n KemSK) (Option (RegistrationNativePairedChoice.Choice n)) :=
  (Spec n KemSK).query (.inr (.inl (.inl message)))

theorem effect_lift : trustedLift (n := n) (KemSK := KemSK) ∘ₛ environment = effect := by
  funext query
  simp only [QueryImpl.apply_compose, environment, simulateQ_spec_query, trustedLift, effect]

theorem chosen_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source) (owner current : SelectedOwner source)
    (ready : RegistrationBeaconReferenceRoot.Ready) (choice : RegistrationNativePairedChoice.Choice n)
    (env : EnvState RegistrationServerRoleBackend.State) (before : State n KemSK source) :
    (simulateQ (implementation setup checks wire representation created scalar credential)
      (((RegistrationNativePlatformBeaconMaterialFrontend.chosen setup.source wire.frameWrite effect owner ready choice).run current).run env)).run before =
      (fun result => (result.1, (before.1, (before.2.1, result.2)))) <$>
        (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
          (((RegistrationNativePlatformBeaconMaterialFrontend.chosen setup.source wire.frameWrite environment owner ready choice).run current).run env)).run before.2.2 := by
  have actual := RegistrationBeaconReferenceNativeInterpreter.trusted_program setup checks wire representation created scalar credential
    (simulateQ environment (((RegistrationNativePlatformBeaconMaterialFrontend.program setup.source wire.frameWrite owner ready choice).run current).run env)) before
  simpa only [RegistrationNativePlatformBeaconMaterialFrontend.chosen, StateT.run, ← QueryImpl.simulateQ_compose, effect_lift] using actual

theorem complete_known (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source) (owner current : SelectedOwner source)
    (ready : RegistrationBeaconReferenceRoot.Ready) (root : PqxdhSecretInputKdf.RootOutput)
    (env : EnvState RegistrationServerRoleBackend.State) (before : State n KemSK source)
    (prepared : before.1 ready.reference = some root) :
    (simulateQ (implementation setup checks wire representation created scalar credential)
      (((RegistrationNativePlatformBeaconMaterialFrontend.complete setup.source wire.frameWrite effect demand owner ready).run current).run env)).run before =
      (fun result => (result.1, (before.1, (before.2.1, result.2)))) <$>
        (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
          (((RegistrationNativePlatformBeaconMaterialFrontend.chosen setup.source wire.frameWrite environment owner ready
            (.known (PqxdhServerAuthKeySchedule.fromRoot setup.source root))).run current).run env)).run before.2.2 := by
  simp only [RegistrationNativePlatformBeaconMaterialFrontend.complete, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, simulateQ_bind, simulateQ_spec_query, demand, bind_map_left]
  rw [RegistrationBeaconReferenceNativeInterpreter.demand_known setup checks wire representation created scalar credential ready.reference before root prepared]
  simp only [pure_bind]
  exact chosen_source setup checks wire representation created scalar credential owner current ready _ env before

theorem abort_source {Value : Type} (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source) (owner current : SelectedOwner source)
    (env : EnvState RegistrationServerRoleBackend.State) (value : Value) (before : State n KemSK source) :
    (simulateQ (implementation setup checks wire representation created scalar credential)
      (((RegistrationNativePlatformBeaconMaterialFrontend.abort effect owner *> pure value :
        RegistrationNativePlatformBeaconMaterialFrontend.M source RegistrationServerRoleBackend.State (OracleComp (Spec n KemSK)) Value).run current).run env)).run before =
      (fun result => (result.1, (before.1, (before.2.1, result.2)))) <$>
        (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
          (((RegistrationNativePlatformBeaconMaterialFrontend.abort environment owner *> pure value :
            RegistrationNativePlatformBeaconMaterialFrontend.M source RegistrationServerRoleBackend.State
              (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)) Value).run current).run env)).run before.2.2 := by
  have lifted : simulateQ trustedLift
      (((RegistrationNativePlatformBeaconMaterialFrontend.abort environment owner *> pure value :
        RegistrationNativePlatformBeaconMaterialFrontend.M source RegistrationServerRoleBackend.State
          (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)) Value).run current).run env) =
      (((RegistrationNativePlatformBeaconMaterialFrontend.abort effect owner *> pure value :
        RegistrationNativePlatformBeaconMaterialFrontend.M source RegistrationServerRoleBackend.State (OracleComp (Spec n KemSK)) Value).run current).run env) := by
    simp only [RegistrationNativePlatformBeaconMaterialFrontend.abort, seqRight_eq_bind, StateT.run_lift,
      StateT.run_map, bind_pure_comp, simulateQ_map, environment, simulateQ_spec_query, trustedLift]
  rw [← lifted]
  exact RegistrationBeaconReferenceNativeInterpreter.trusted_program setup checks wire representation created scalar credential _ before

theorem complete_missing (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source) (owner current : SelectedOwner source)
    (ready : RegistrationBeaconReferenceRoot.Ready)
    (env : EnvState RegistrationServerRoleBackend.State) (before : State n KemSK source)
    (missing : before.1 ready.reference = none) :
    (simulateQ (implementation setup checks wire representation created scalar credential)
      (((RegistrationNativePlatformBeaconMaterialFrontend.complete setup.source wire.frameWrite effect demand owner ready).run current).run env)).run before =
      (fun result => (result.1, (before.1, (before.2.1, result.2)))) <$>
        (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
          (((RegistrationNativePlatformBeaconMaterialFrontend.abort environment owner *> pure (.ok none) :
            RegistrationNativePlatformBeaconMaterialFrontend.M source RegistrationServerRoleBackend.State
              (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)) (RustM (Option Pqxdh.Bytes))).run current).run env)).run before.2.2 := by
  simp only [RegistrationNativePlatformBeaconMaterialFrontend.complete, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, simulateQ_bind, simulateQ_spec_query, demand, bind_map_left]
  rw [RegistrationBeaconReferenceNativeInterpreter.demand_missing setup checks wire representation created scalar credential ready.reference before missing]
  simp only [pure_bind]
  exact abort_source setup checks wire representation created scalar credential owner current env _ before

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialInterpreter.effect_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialInterpreter.effect_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialInterpreter.chosen_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialInterpreter.chosen_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialInterpreter.complete_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialInterpreter.complete_known

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialInterpreter.abort_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialInterpreter.abort_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialInterpreter.complete_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialInterpreter.complete_missing

end BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialInterpreter
