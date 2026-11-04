-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFrontendHashBounds
/-! The actual native constructor has one shared pin hash. ML generation, indexed Ed/KEM birth, scalar sampling and owner bookkeeping retain their real samplers and outcomes without additional shared CTX calls. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBirthHashBounds
open BeaconcryptCore.Refinement
open RegistrationNativePlatformIdentityFrontendHashBounds
open RegistrationNativeIdentityFrontend (M Ambient)
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {I KemSK Auxiliary : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private theorem identity_create_bound :
    Bounded (StateT.lift (StateT.lift (RegistrationNativeIdentityInterface.create (Ambient n KemSK))) :
      M n KemSK Auxiliary source (Option RegistrationNativeIdentityInterface.Credential)) 0 := by
  apply lift_free_bound
  simp [RegistrationNativeIdentityInterface.create, IsHash]

/-- Literal native preparation hashes its supplied Server pin once through every optional failure and generated-key reply. -/
theorem prepare_bound (source : RegistrationNativeMldsa.Source) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Bounded (RegistrationNativeIdentityFrontend.prepare (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) source edPin mlPin keyId) 1 := by
  unfold RegistrationNativeIdentityFrontend.prepare
  apply bind_bound _ _ 0 1 (sample_bound _)
  intro optional
  cases optional with
  | none => exact pure_bound _ _
  | some credentials =>
    cases registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
    | fail error | div => exact pure_bound _ _
    | ok pending =>
      simp only
      cases pending.request with
      | fail error | div => exact pure_bound _ _
      | ok request =>
        simp only
        apply bind_bound _ _ 1 0 (hash_bound request)
        intro digest
        cases pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) with
        | fail error | div => exact pure_bound _ _
        | ok pin => cases pin with
          | none => exact pure_bound _ _
          | some pin =>
            simp only
            apply bind_bound _ _ 0 0 identity_create_bound
            intro generated
            cases generated with
            | none => exact pure_bound _ _
            | some identity =>
              exact bind_bound _ _ 0 0 (sample_bound _) (fun _ => pure_bound _ _)

/-- Actual source creation retains the complete pin/generation/owner-append path with at most one shared hash. -/
theorem create_bound (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Bounded (RegistrationNativeIdentityFrontend.create (n := n) (Auxiliary := Auxiliary) setup source edPin mlPin keyId) 1 := by
  unfold RegistrationNativeIdentityFrontend.create
  apply bind_bound _ _ 1 0 (prepare_bound source edPin mlPin keyId)
  intro prepared
  cases prepared with
  | fail error | div => exact pure_bound _ _
  | ok optional => cases optional with
    | none => exact pure_bound _ _
    | some prepared =>
      simp only
      apply bind_bound _ _ 0 0 (kem_bound _)
      intro born
      apply bind_bound _ _ 0 0 (effect_bound _)
      intro worldOwner
      apply bind_bound _ _ 0 0 get_bound
      intro owners
      apply bind_bound _ _ 0 0
      · exact fun _ _ => isQueryBoundP_pure _ _ _
      · intro _
        exact pure_bound _ _
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBirthHashBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBirthHashBounds.prepare_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBirthHashBounds.prepare_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBirthHashBounds.create_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBirthHashBounds.create_bound
