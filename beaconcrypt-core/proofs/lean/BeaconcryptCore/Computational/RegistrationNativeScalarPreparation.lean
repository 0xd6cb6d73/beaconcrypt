-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeScalarEager
import BeaconcryptCore.Computational.RegistrationNativeEnvSampling

/-! The actual constructor's optional prefix stops immediately before its final prekey draw. The factor retains every ML, pin and identity callback in source order and exposes that single scalar draw for the eager-sampling proof. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeScalarPreparation
open RegistrationNativeBeaconFrontend (M Prepared sample hash)
variable {n : Nat} {KemSK Auxiliary : Type}

noncomputable def leading (source : RegistrationNativeMldsa.Source) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64) : M n KemSK source Auxiliary (RustM (Option (Prepared source))) := do
  let generated ← sample (RegistrationNativeMldsa.generate source)
  match generated with
  | none => pure (.ok none)
  | some credentials =>
    match registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
    | .fail error => pure (.fail error)
    | .div => pure .div
    | .ok pending => match pending.request with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok request => do
        let digest ← hash request
        match pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) with
        | .fail error => pure (.fail error)
        | .div => pure .div
        | .ok .None => pure (.ok none)
        | .ok (.Some pin) => do
          let identity ← sample PqxdhJointIdentity.sampleSeed
          pure (.ok (some ⟨credentials, pin, identity, RegistrationNativePublicOwners.dummy⟩))

def finish {source : RegistrationNativeMldsa.Source}
    (draw : M n KemSK source Auxiliary PqxdhJointGapDh.ScalarBytes)
    (earlier : RustM (Option (Prepared source))) : M n KemSK source Auxiliary (RustM (Option (Prepared source))) := do
  match earlier with
  | .ok (some prepared) =>
      let scalar ← draw
      pure (.ok (some { prepared with prekey := scalar }))
  | .ok none => pure (.ok none)
  | .fail error => pure (.fail error)
  | .div => pure .div

/-- Source prekey generation is exactly one draw after all real optional prefix gates. -/
theorem prepare (source : RegistrationNativeMldsa.Source) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    RegistrationNativeBeaconFrontend.prepare (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) source edPin mlPin keyId =
      (leading source edPin mlPin keyId >>= finish (sample PqxdhJointGapDh.sampleScalar)) := by
  simp only [RegistrationNativeBeaconFrontend.prepare, leading, bind_assoc]
  apply congrArg (fun continuation => (sample (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary)
    (RegistrationNativeMldsa.generate source) >>= continuation))
  funext generated
  cases generated with
  | none => simp only [finish, pure_bind]
  | some credentials =>
      cases initial : registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
      | fail error => simp only [finish, pure_bind]
      | div => simp only [finish, pure_bind]
      | ok pending =>
          cases requested : pending.request with
          | fail error => simp only [requested, finish, pure_bind]
          | div => simp only [requested, finish, pure_bind]
          | ok request =>
              simp only [requested, bind_assoc]
              apply congrArg (fun continuation => (hash (n := n) (KemSK := KemSK) (mldsaSource := source)
                (Auxiliary := Auxiliary) request >>= continuation))
              funext digest
              cases resumed : pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) with
              | fail error => simp only [finish, pure_bind]
              | div => simp only [finish, pure_bind]
              | ok outcome =>
                  cases outcome with
                  | none => simp only [finish, pure_bind]
                  | some pin => simp only [bind_assoc, finish, pure_bind]

end BeaconcryptCore.Computational.RegistrationNativeScalarPreparation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarPreparation.prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarPreparation.prepare
