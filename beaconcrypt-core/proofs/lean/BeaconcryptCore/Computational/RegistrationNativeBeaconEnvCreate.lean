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

/-- The complete local prefix retains actual ML generation, pin hash, identity and prekey draws on all optional failure branches. -/
theorem prepare_stable (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : Std.U64) :
    Stable (RegistrationNativeBeaconFrontend.prepare mlSource edPin mlPin keyId : M n KemSK mlSource Auxiliary _) := by
  unfold RegistrationNativeBeaconFrontend.prepare
  apply RegistrationNativeBeaconEnvView.bind_stable
  · exact sample_stable _
  · intro generated
    cases generated with
    | none => exact RegistrationNativeBeaconEnvView.pure_stable _
    | some credentials =>
      cases registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
      | fail error | div => exact RegistrationNativeBeaconEnvView.pure_stable _
      | ok pending =>
        dsimp only
        cases requested : pending.request with
        | fail error | div =>
            exact RegistrationNativeBeaconEnvView.pure_stable _
        | ok request =>
          dsimp only
          apply RegistrationNativeBeaconEnvView.bind_stable
          · exact hash_stable request
          · intro digest
            cases pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) with
            | fail error | div => exact RegistrationNativeBeaconEnvView.pure_stable _
            | ok pin => cases pin with
              | none => exact RegistrationNativeBeaconEnvView.pure_stable _
              | some pin =>
                apply RegistrationNativeBeaconEnvView.bind_stable
                · exact sample_stable _
                · intro identity
                  apply RegistrationNativeBeaconEnvView.bind_stable
                  · exact sample_stable _
                  · intro prekey; exact RegistrationNativeBeaconEnvView.pure_stable _

/-- Successful source birth appends the same actual generated KEM handle and complete owner state. -/
theorem append_stable (setup : Setup base KemSK)
    (edPin : Std.Array U8 32#usize) (keyId : Std.U64) (pin : session.ServerAuthenticationPin)
    (credentials : RegistrationNativeMldsa.Credential mlSource) (identity : PqxdhJointIdentity.IdentitySeed)
    (prekey : PqxdhJointGapDh.ScalarBytes) :
    Stable (RegistrationNativeBeaconFrontend.appendBorn setup mlSource edPin keyId pin credentials identity prekey :
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
      | some prepared => exact append_stable setup edPin keyId prepared.pin prepared.credentials prepared.identity prepared.prekey

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
