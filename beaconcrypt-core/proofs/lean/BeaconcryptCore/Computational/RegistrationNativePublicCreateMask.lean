-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicCreatePrefix

/-! The actual native constructor commutes with private selected-scalar reconstruction. All source-prefix draws stay in place; only the selected successful birth uses the independent private scalar. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicCreateMask
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePublicOwnerRestore (mask)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}

/-- Whole raw constructor execution restores the complete selected owner at its actual successful birth position. -/
theorem create_mask (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativeBeaconFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) :
    Prod.map (Prod.map id (mask selected scalar (setup.dh.publicKey scalar))) id <$>
      ((RegistrationNativeBeaconFrontend.create (n := n) setup source edPin mlPin keyId).run owners).run env =
      ((RegistrationNativeScalarEager.create setup source selected scalar edPin mlPin keyId).run
        (mask selected scalar (setup.dh.publicKey scalar) owners)).run env := by
  rw [RegistrationNativeBeaconBirth.create_program, RegistrationNativeScalarEagerLaws.create_program,
    RegistrationNativePublicCreatePrefix.prepare_program, RegistrationNativePublicCreatePrefix.prepare_program]
  simp only [bind_map_left, map_bind]
  apply bind_congr
  intro earlier
  cases earlier with
  | fail error | div => simp only [map_pure, Prod.map_def, id_eq]
  | ok reply => cases reply with
    | none => simp only [map_pure, Prod.map_def, id_eq]
    | some prepared =>
        simp only [RegistrationNativeBeaconBirth.append_program, map_bind, map_pure, Prod.map_def, id_eq,
          mask, List.length_mapIdx, List.mapIdx_concat]
        apply bind_congr
        intro born
        apply bind_congr
        intro worldOwner
        by_cases chosen : owners.length = selected
        · simp only [chosen, ite_true, RegistrationNativeBeaconBirth.owner]
        · simp only [chosen, ite_false]

end BeaconcryptCore.Computational.RegistrationNativePublicCreateMask
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicCreateMask.create_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicCreateMask.create_mask
