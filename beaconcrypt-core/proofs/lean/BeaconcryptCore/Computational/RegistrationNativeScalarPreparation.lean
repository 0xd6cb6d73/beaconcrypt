-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeScalarEager
import BeaconcryptCore.Computational.RegistrationNativeEnvSampling

/-! The actual constructor's optional prefix stops immediately before its final prekey draw. The factor retains pure pin selection and the generated Ed identity draw in source order and exposes that single scalar draw for the eager-sampling proof. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeScalarPreparation
open RegistrationNativeBeaconFrontend (M Prepared sample)
variable {n : Nat} {KemSK Auxiliary : Type}

noncomputable def leading (source : RegistrationNativeMldsa.Source) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64) : M n KemSK source Auxiliary (RustM (Option (Prepared source))) := do
  match registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok pin => do
    let identity ← sample PqxdhJointIdentity.sampleSeed
    pure (.ok (some ⟨pin, identity, RegistrationNativePublicOwners.dummy⟩))

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
  simp only [RegistrationNativeBeaconFrontend.prepare, leading]
  cases selected : registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
  | fail error | div => simp only [finish, pure_bind]
  | ok pin => simp only [bind_assoc, finish, pure_bind]

end BeaconcryptCore.Computational.RegistrationNativeScalarPreparation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarPreparation.prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarPreparation.prepare
