-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeScalarPreparation
import BeaconcryptCore.Computational.RegistrationNativeKemBirthOwners
import BeaconcryptCore.Computational.RegistrationNativeBeaconBirth

/-! The eager source constructor changes only a selected successful roster birth. These operational equations retain the actual optional prefix and prove that every ordinary creation remains literally the native source program. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeScalarEagerLaws
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeBeaconFrontend (Prepared Owner)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι}

theorem create_program (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : EnvState RegistrationServerRoleBackend.State) :
    ((RegistrationNativeScalarEager.create (n := n) setup source selected scalar edPin mlPin keyId).run owners).run env = (do
      let earlier ← ((RegistrationNativeBeaconFrontend.prepare (n := n) (KemSK := KemSK) source edPin mlPin keyId).run owners).run env
      match earlier.1.1 with
      | .ok (some prepared) =>
          ((RegistrationNativeBeaconFrontend.appendBorn setup source edPin keyId prepared.pin prepared.identity
            (if earlier.1.2.length = selected then scalar else prepared.prekey)).run earlier.1.2).run earlier.2
      | .ok none => pure ((.ok none, earlier.1.2), earlier.2)
      | .fail error => pure ((.fail error, earlier.1.2), earlier.2)
      | .div => pure ((.div, earlier.1.2), earlier.2)) := by
  simp only [RegistrationNativeScalarEager.create, StateT.run_bind]
  apply congrArg (fun continuation =>
    (((RegistrationNativeBeaconFrontend.prepare (n := n) (KemSK := KemSK) source edPin mlPin keyId).run owners).run env >>= continuation))
  funext earlier
  rcases earlier with ⟨⟨action, leadingOwners⟩, leadingEnv⟩
  cases action with
  | fail error => rfl
  | div => rfl
  | ok result =>
      cases result with
      | none => rfl
      | some prepared => simp only [StateT.run_bind, StateT.run_get, pure_bind]

/-- A constructor outside the selected roster index is the exact ordinary native constructor, including its actual prekey draw. -/
theorem ordinary_create (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : EnvState RegistrationServerRoleBackend.State)
    (ordinary : owners.length ≠ selected) :
    ((RegistrationNativeScalarEager.create (n := n) setup source selected scalar edPin mlPin keyId).run owners).run env =
      ((RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId).run owners).run env := by
  rw [create_program, RegistrationNativeBeaconBirth.create_program]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro earlier supported
  have unchanged := RegistrationNativeKemBirthOwners.prepare_owners edPin mlPin keyId owners env earlier supported
  cases action : earlier.1.1 with
  | fail error => rfl
  | div => rfl
  | ok result =>
      cases result with
      | none => rfl
      | some prepared => simp only [unchanged, ordinary, ite_false]

end BeaconcryptCore.Computational.RegistrationNativeScalarEagerLaws

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarEagerLaws.create_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarEagerLaws.create_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarEagerLaws.ordinary_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarEagerLaws.ordinary_create
