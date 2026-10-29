-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicOwnerRestore
import BeaconcryptCore.Computational.RegistrationNativeScalarEffectBind

/-! Native constructor preparation uses external source effects without consulting or modifying the current owner roster or local environment. Its complete ML, pin, identity and dummy-prekey draw prefix is retained literally. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicCreatePrefix
open RegistrationNativeBeaconFrontend (Trusted Prepared)
variable {n : Nat} {KemSK : Type}

noncomputable def core (source : RegistrationNativeMldsa.Source) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64) : OracleComp (Trusted n KemSK) (RustM (Option (Prepared source))) := do
  let earlier ← simulateQ RegistrationBeaconReferenceNativeRecord.environment
    (RegistrationNativeScalarLeading.program source edPin mlPin keyId)
  match earlier with
  | .ok (some prepared) =>
      let scalar ← simulateQ RegistrationBeaconReferenceNativeRecord.environment
        (simulateQ RegistrationWorldCoinCompiler.envCoin PqxdhJointGapDh.sampleScalar)
      pure (.ok (some { prepared with prekey := scalar }))
  | .ok none => pure (.ok none)
  | .fail error => pure (.fail error)
  | .div => pure .div

/-- Preparation has the same actual source-query AST on every roster and environment. -/
theorem prepare_program (source : RegistrationNativeMldsa.Source) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativeBeaconFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) :
    ((RegistrationNativeBeaconFrontend.prepare (n := n) (KemSK := KemSK) source edPin mlPin keyId).run owners).run env =
      (fun action => ((action, owners), env)) <$> core source edPin mlPin keyId := by
  rw [RegistrationNativeScalarPreparation.prepare, RegistrationNativeScalarLeading.leading,
    RegistrationNativeScalarEffectBind.effects_lift]
  simp only [StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left,
    core, map_bind]
  apply bind_congr
  intro earlier
  cases earlier with
  | fail error | div => simp only [RegistrationNativeScalarPreparation.finish, StateT.run_pure, map_pure]
  | ok reply => cases reply with
    | none => simp only [RegistrationNativeScalarPreparation.finish, StateT.run_pure, map_pure]
    | some prepared =>
        simp only [RegistrationNativeScalarPreparation.finish, RegistrationNativeScalarSource.sample_effects,
          StateT.run_lift, bind_pure_comp, StateT.run_map, Functor.map_map]

end BeaconcryptCore.Computational.RegistrationNativePublicCreatePrefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicCreatePrefix.prepare_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicCreatePrefix.prepare_program
