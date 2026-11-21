-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemBirthOwners
import BeaconcryptCore.Computational.RegistrationNativeBeaconBirth

/-! The actual constructor preserves every earlier local owner on all failure paths. A successful constructor appends precisely one owner and returns its local list index. The private KEM handle remains a separate field supplied by the actual indexed birth callback. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemBirthCreateShape
open RegistrationNativeBeaconFrontend
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhServerAuthExperiment (Setup)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}

def Shape {source : RegistrationNativeMldsa.Source} (before : State source)
    (reply : RustM (Option Nat)) (after : State source) : Prop :=
  match reply with
  | .ok (some index) => index = before.length ∧ ∃ owner, after = before ++ [owner]
  | _ => after = before

/-- The full constructor reaches indexed birth only after an owner-preserving prefix, then appends its exact actual callback replies. -/
theorem create_shape (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : State source) (env : EnvState Auxiliary)
    (reply : RustM (Option Nat)) (afterOwners : State source) (afterEnv : EnvState Auxiliary)
    (supported : ((reply, afterOwners), afterEnv) ∈ support
      (((create (n := n) setup source edPin mlPin keyId).run owners).run env)) : Shape owners reply afterOwners := by
  rw [RegistrationNativeBeaconBirth.create_program] at supported
  simp only [mem_support_bind_iff] at supported
  obtain ⟨earlier, reached, continued⟩ := supported
  have retained := RegistrationNativeKemBirthOwners.prepare_owners edPin mlPin keyId owners env earlier reached
  cases actual : earlier.1.1 with
  | fail error =>
      simp only [actual, support_pure, Set.mem_singleton_iff] at continued
      cases continued
      exact retained
  | div =>
      simp only [actual, support_pure, Set.mem_singleton_iff] at continued
      cases continued
      exact retained
  | ok result => cases result with
    | none =>
        simp only [actual, support_pure, Set.mem_singleton_iff] at continued
        cases continued
        exact retained
    | some prepared =>
        simp only [actual] at continued
        rw [RegistrationNativeBeaconBirth.append_program] at continued
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at continued
        obtain ⟨born, _, worldOwner, _, returned⟩ := continued
        cases returned
        refine ⟨congrArg List.length retained,
          RegistrationNativeBeaconBirth.owner setup source prepared.pin
            prepared.identity prepared.prekey born worldOwner, ?_⟩
        rw [retained]

end BeaconcryptCore.Computational.RegistrationNativeKemBirthCreateShape

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBirthCreateShape.create_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBirthCreateShape.create_shape
