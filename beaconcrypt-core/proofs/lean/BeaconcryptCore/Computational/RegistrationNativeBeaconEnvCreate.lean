-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCallbacks

/-! Concrete Beacon creation retains the full generated owner and source queries without reading the unrelated record-kind analysis ledger. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCreate
open RegistrationNativeBeaconFrontend (M)
open RegistrationNativeBeaconEnvView (Stable)
open RegistrationNativeBeaconEnvCallbacks
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

/-- Pure pin selection and the actual identity/prekey draws preserve unrelated analysis input. -/
theorem prepare_stable (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : Std.U64) :
    Stable (RegistrationNativeBeaconFrontend.prepare mlSource edPin mlPin keyId : M n KemSK mlSource Auxiliary _) := by
  unfold RegistrationNativeBeaconFrontend.prepare
  cases registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
  | fail error | div => exact RegistrationNativeBeaconEnvView.pure_stable _
  | ok pin =>
      exact RegistrationNativeBeaconEnvView.bind_stable _ _ (sample_stable _) (fun _ =>
        RegistrationNativeBeaconEnvView.bind_stable _ _ (sample_stable _) (fun _ =>
          RegistrationNativeBeaconEnvView.pure_stable _))

/-- Successful source birth appends the same actual generated KEM handle and complete owner state. -/
theorem append_stable (setup : Setup base KemSK)
    (edPin : Std.Array U8 32#usize) (keyId : Std.U64) (pin : session.ServerAuthenticationPin)
    (identity : PqxdhJointIdentity.IdentitySeed)
    (prekey : PqxdhJointGapDh.ScalarBytes) :
    Stable (RegistrationNativeBeaconFrontend.appendBorn setup mlSource edPin keyId pin identity prekey :
      M n KemSK mlSource Auxiliary _) := by
  unfold RegistrationNativeBeaconFrontend.appendBorn
  apply RegistrationNativeBeaconEnvView.bind_stable
  · exact kem_stable _
  · intro born
    apply RegistrationNativeBeaconEnvView.bind_stable
    · exact effect_stable _
    · intro worldOwner
      apply RegistrationNativeBeaconEnvView.bind_stable
      · exact RegistrationNativeBeaconEnvView.get_stable
      · intro owners
        apply RegistrationNativeBeaconEnvView.bind_stable
        · exact RegistrationNativeBeaconEnvView.set_stable _
        · intro result; exact RegistrationNativeBeaconEnvView.pure_stable _

/-- Whole actual Beacon creation observes no omitted analysis input and keeps every source failure and returned owner handle. -/
theorem create_stable (setup : Setup base KemSK)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : Std.U64) :
    Stable (RegistrationNativeBeaconFrontend.create setup mlSource edPin mlPin keyId : M n KemSK mlSource Auxiliary _) := by
  unfold RegistrationNativeBeaconFrontend.create
  apply RegistrationNativeBeaconEnvView.bind_stable
  · exact prepare_stable edPin mlPin keyId
  · intro prepared
    cases prepared with
    | fail error | div => exact RegistrationNativeBeaconEnvView.pure_stable _
    | ok prepared => cases prepared with
      | none => exact RegistrationNativeBeaconEnvView.pure_stable _
      | some prepared => exact append_stable setup edPin keyId prepared.pin prepared.identity prepared.prekey

end BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCreate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCreate.prepare_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCreate.prepare_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCreate.append_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCreate.append_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCreate.create_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCreate.create_stable
