-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeScalarEffectBind

/-! The literal source constructor factors at its one final prekey draw; actual indexed KEM birth and public owner allocation stay in the same native suffix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeScalarBirth
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (M Prepared sample appendBorn)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}

noncomputable def after (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (edPin : Std.Array U8 32#usize) (keyId : U64)
    (draw : M n KemSK source RegistrationServerRoleBackend.State PqxdhJointGapDh.ScalarBytes)
    (prepared : RustM (Option (Prepared source))) :
    M n KemSK source RegistrationServerRoleBackend.State (RustM (Option Nat)) := do
  match prepared with
  | .ok (some prepared) =>
      let scalar ← draw
      appendBorn setup source edPin keyId prepared.pin prepared.identity scalar
  | .ok none => pure (.ok none)
  | .fail error => pure (.fail error)
  | .div => pure .div

/-- No optional preflight or post-draw KEM/owner callback is moved across the actual scalar boundary. -/
theorem create (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    RegistrationNativeBeaconFrontend.create (n := n) setup source edPin mlPin keyId =
      (RegistrationNativeScalarPreparation.leading source edPin mlPin keyId >>=
        after setup source edPin keyId (sample PqxdhJointGapDh.sampleScalar)) := by
  rw [RegistrationNativeBeaconFrontend.create, RegistrationNativeScalarPreparation.prepare, bind_assoc]
  apply congrArg (fun continuation =>
    (RegistrationNativeScalarPreparation.leading (n := n) (KemSK := KemSK)
      (Auxiliary := RegistrationServerRoleBackend.State) source edPin mlPin keyId >>= continuation))
  funext earlier
  cases earlier with
  | fail error => simp only [RegistrationNativeScalarPreparation.finish, pure_bind, after]
  | div => simp only [RegistrationNativeScalarPreparation.finish, pure_bind, after]
  | ok reply =>
      cases reply with
      | none => simp only [RegistrationNativeScalarPreparation.finish, pure_bind, after]
      | some prepared => simp only [RegistrationNativeScalarPreparation.finish, after, bind_assoc, pure_bind]

/-- The actual whole closed constructor keeps its optional prefix on the original World before its complete draw and birth suffix. -/
theorem source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (source : RegistrationNativeMldsa.Source)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    (RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId)).run before = (do
        let result ← (simulateQ PqxdhRecordLiftWorld.effects
          (RegistrationNativeScalarLeading.program source edPin mlPin keyId)).run before.server.world.world.1
        (RegistrationNativeExperiment.beacon setup checks representation created
          (after setup source edPin keyId (sample PqxdhJointGapDh.sampleScalar) result.1)).run
            (RegistrationBeaconReferenceNativeEffects.embed before result.2)) := by
  rw [create, RegistrationNativeScalarLeading.leading, RegistrationNativeScalarEffectBind.beacon_bind]

end BeaconcryptCore.Computational.RegistrationNativeScalarBirth

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarBirth.create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarBirth.create
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarBirth.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarBirth.source
