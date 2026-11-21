-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconEnvCreate

/-! Actual outgoing Beacon publication keeps the three attached Ed signatures followed by its request hash, current owner history and all optional writer outcomes under unrelated record-kind input erasure. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconEnvBundle
open RegistrationNativeBeaconFrontend (M Owner)
open RegistrationNativeBeaconEnvView (Stable)
open RegistrationNativeBeaconEnvCallbacks
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

/-- All actual outgoing signature callbacks retain source replies, chronological receipts and owner history. -/
theorem outgoing_stable (setup : Setup base KemSK) (index : Nat) (owner : Owner mlSource)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Stable (RegistrationNativeBeaconFrontend.outgoing setup mlSource index owner query : M n KemSK mlSource Auxiliary _) := by
  classical
  cases query with
  | inl query => cases query with
    | hash request => exact hash_stable request
    | sign request payload digest => exact RegistrationNativeBeaconEnvView.pure_stable _
  | inr request =>
      unfold RegistrationNativeBeaconFrontend.outgoing
      dsimp only
      split
      · apply RegistrationNativeBeaconEnvView.bind_stable
        · exact log_stable index _ _
        · intro result; exact RegistrationNativeBeaconEnvView.pure_stable _
      · exact RegistrationNativeBeaconEnvView.pure_stable _

/-- The complete actual Beacon bundle operation preserves fresh or supplied one-time randomness, consumed owner phase, packing failure and returned bytes. -/
theorem bundle_stable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat) :
    Stable (RegistrationNativeBeaconFrontend.bundle setup mlSource wire index : M n KemSK mlSource Auxiliary _) := by
  unfold RegistrationNativeBeaconFrontend.bundle
  apply RegistrationNativeBeaconEnvView.bind_stable
  · exact RegistrationNativeBeaconEnvView.get_stable
  · intro owners
    cases found : owners[index]? with
    | none => exact RegistrationNativeBeaconEnvView.pure_stable _
    | some owner =>
      dsimp only
      cases owner.phase <;> dsimp only <;> first
        | exact RegistrationNativeBeaconEnvView.pure_stable _
        | apply RegistrationNativeBeaconEnvView.bind_stable
          · first
              | exact sample_stable _
              | exact RegistrationNativeBeaconEnvView.pure_stable _
          · intro oneTime
            apply RegistrationNativeBeaconEnvView.bind_stable
            · exact RegistrationNativeBeaconEnvView.program_stable _ (outgoing_stable setup index owner) _
            · intro published
              cases published with
              | fail error | div => exact RegistrationNativeBeaconEnvView.pure_stable _
              | ok outcome => cases outcome with
                | Err previous => exact RegistrationNativeBeaconEnvView.pure_stable _
                | Ok finished =>
                  apply RegistrationNativeBeaconEnvView.bind_stable
                  · exact phase_stable index _
                  · intro result
                    apply RegistrationNativeBeaconEnvView.bind_stable
                    · exact effect_stable _
                    · intro result; exact RegistrationNativeBeaconEnvView.pure_stable _

end BeaconcryptCore.Computational.RegistrationNativeBeaconEnvBundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvBundle.outgoing_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvBundle.outgoing_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvBundle.bundle_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvBundle.bundle_stable
