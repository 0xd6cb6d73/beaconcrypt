-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeScalarBirth

/-! At the selected successful roster position the eager constructor keeps the original dummy draw and substitutes its private scalar only in the literal birth suffix. Every earlier optional source failure is retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeScalarEagerLocal
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (M Prepared sample appendBorn)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {ι KemSK X Y : Type} {base : OracleSpec ι}

def dummy {source : RegistrationNativeMldsa.Source} (scalar : PqxdhJointGapDh.ScalarBytes) :
    M n KemSK source RegistrationServerRoleBackend.State PqxdhJointGapDh.ScalarBytes := do
  let _ ← sample PqxdhJointGapDh.sampleScalar
  pure scalar

noncomputable def always (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (scalar : PqxdhJointGapDh.ScalarBytes) (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    M n KemSK source RegistrationServerRoleBackend.State (RustM (Option Nat)) := do
  match ← RegistrationNativeBeaconFrontend.prepare source edPin mlPin keyId with
  | .ok (some prepared) => appendBorn setup source edPin keyId prepared.pin prepared.identity scalar
  | .ok none => pure (.ok none)
  | .fail error => pure (.fail error)
  | .div => pure .div

/-- The actual selected-index choice is reached only after the unchanged owner roster prefix. -/
theorem target_program (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : EnvState RegistrationServerRoleBackend.State)
    (chosen : owners.length = selected) :
    ((RegistrationNativeScalarEager.create (n := n) setup source selected scalar edPin mlPin keyId).run owners).run env =
      ((always setup source scalar edPin mlPin keyId).run owners).run env := by
  rw [RegistrationNativeScalarEagerLaws.create_program]
  simp only [always, StateT.run_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro earlier supported
  have unchanged := RegistrationNativeKemBirthOwners.prepare_owners edPin mlPin keyId owners env earlier supported
  cases action : earlier.1.1 with
  | fail error => rfl
  | div => rfl
  | ok reply => cases reply with
    | none => rfl
    | some prepared => simp only [unchanged, chosen, ite_true]

/-- The selected constructor still performs its complete original prekey draw after all prefix gates. -/
theorem always_factor (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (scalar : PqxdhJointGapDh.ScalarBytes) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    always (n := n) setup source scalar edPin mlPin keyId =
      (RegistrationNativeScalarPreparation.leading source edPin mlPin keyId >>=
        RegistrationNativeScalarBirth.after setup source edPin keyId (dummy scalar)) := by
  rw [always, RegistrationNativeScalarPreparation.prepare, bind_assoc]
  apply congrArg (fun continuation =>
    (RegistrationNativeScalarPreparation.leading (n := n) (KemSK := KemSK)
      (Auxiliary := RegistrationServerRoleBackend.State) source edPin mlPin keyId >>= continuation))
  funext earlier
  cases earlier with
  | fail error => simp only [RegistrationNativeScalarPreparation.finish, pure_bind, RegistrationNativeScalarBirth.after]
  | div => simp only [RegistrationNativeScalarPreparation.finish, pure_bind, RegistrationNativeScalarBirth.after]
  | ok reply => cases reply with
    | none => simp only [RegistrationNativeScalarPreparation.finish, pure_bind, RegistrationNativeScalarBirth.after]
    | some prepared =>
        simp only [RegistrationNativeScalarPreparation.finish, RegistrationNativeScalarBirth.after, dummy,
          bind_assoc, pure_bind]

/-- The actual source wrapper inherits the selected constructor's optional-prefix factor, with its complete private state. -/
theorem target_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (source : RegistrationNativeMldsa.Source)
    (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativeExperiment.State n KemSK source) (chosen : before.beacons.length = selected) :
    (RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeScalarEager.create setup source selected scalar edPin mlPin keyId)).run before = (do
        let result ← (simulateQ PqxdhRecordLiftWorld.effects
          (RegistrationNativeScalarLeading.program source edPin mlPin keyId)).run before.server.world.world.1
        (RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativeScalarBirth.after setup source edPin keyId (dummy scalar) result.1)).run
            (RegistrationBeaconReferenceNativeEffects.embed before result.2)) := by
  have replaced : (RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeScalarEager.create setup source selected scalar edPin mlPin keyId)).run before =
      (RegistrationNativeExperiment.beacon setup checks representation created
        (always setup source scalar edPin mlPin keyId)).run before := by
    unfold RegistrationNativeExperiment.beacon
    have localEq := target_program (n := n) setup source selected scalar edPin mlPin keyId before.beacons
      (RegistrationWorldAgreementCompiler.erase before.server.world) chosen
    dsimp only [StateT.run]
    dsimp only [StateT.run] at localEq
    rw [localEq]
  rw [replaced, always_factor, RegistrationNativeScalarLeading.leading, RegistrationNativeScalarEffectBind.beacon_bind]

/-- An actual World-only scalar prefix closes before any later mutable Beacon continuation. -/
theorem sample_bind {source : RegistrationNativeMldsa.Source} (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (draw : ProbComp X)
    (next : X → M n KemSK source RegistrationServerRoleBackend.State Y)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    (RegistrationNativeExperiment.beacon setup checks representation created (sample draw >>= next)).run before = (do
      let result ← (RegistrationNativeExperiment.beacon setup checks representation created (sample draw)).run before
      (RegistrationNativeExperiment.beacon setup checks representation created (next result.1)).run result.2) := by
  have closed := RegistrationNativeScalarEffectBind.beacon_bind setup checks representation created
    (simulateQ RegistrationWorldCoinCompiler.envCoin draw) next before
  rw [RegistrationNativeScalarEffectBind.effects_lift, ← RegistrationNativeScalarSource.sample_effects,
    RegistrationWorldCoinCompiler.env_program] at closed
  rw [RegistrationNativeScalarSource.sample, bind_map_left]
  exact closed

end BeaconcryptCore.Computational.RegistrationNativeScalarEagerLocal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarEagerLocal.target_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarEagerLocal.target_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarEagerLocal.always_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarEagerLocal.always_factor
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarEagerLocal.target_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarEagerLocal.target_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarEagerLocal.sample_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarEagerLocal.sample_bind
