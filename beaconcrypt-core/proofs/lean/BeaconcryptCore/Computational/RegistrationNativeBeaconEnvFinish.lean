-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconEnvBundle

/-! The complete actual Beacon finish path preserves mandatory authentication, early InitSent consumption, optional agreement and record failure, terminal abort, real known-kernel insertion and every retained state coordinate under unrelated record-kind input erasure. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconEnvFinish
open RegistrationNativeBeaconFrontend (M Owner)
open RegistrationNativeBeaconEnvView (Stable)
open RegistrationNativeBeaconEnvCallbacks
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

/-- Actual terminal abort precedes the literal failed or empty reply. -/
theorem aborting_stable (owner : Owner mlSource) (value : Value) :
    Stable (RegistrationNativeBeaconFrontend.abort owner *> pure value : M n KemSK mlSource Auxiliary Value) := by
  simp only [seqRight_eq_bind]
  apply RegistrationNativeBeaconEnvView.bind_stable
  · exact abort_stable owner
  · intro result; exact RegistrationNativeBeaconEnvView.pure_stable value

/-- The full actual native Beacon finish controller reads no omitted record-kind ledger. -/
theorem finish_stable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket) :
    Stable (RegistrationNativeBeaconFrontend.finish setup mlSource wire index packet : M n KemSK mlSource Auxiliary _) := by
  unfold RegistrationNativeBeaconFrontend.finish
  apply RegistrationNativeBeaconEnvView.bind_stable
  · exact RegistrationNativeBeaconEnvView.get_stable
  · intro owners
    cases owners[index]? with
    | none => exact RegistrationNativeBeaconEnvView.pure_stable _
    | some owner =>
      dsimp only
      cases owner.phase with
      | fresh | freshWithCoins oneTime | established completed | aborted control =>
          exact RegistrationNativeBeaconEnvView.pure_stable _
      | initSent pending oneTime =>
        dsimp only
        cases requested : pending.aborted_state with
        | fail error | div =>
            exact RegistrationNativeBeaconEnvView.pure_stable _
        | ok aborted =>
          dsimp only
          apply RegistrationNativeBeaconEnvView.bind_stable
          · exact phase_stable index _
          · intro result
            apply RegistrationNativeBeaconEnvView.bind_stable
            · exact RegistrationNativeBeaconEnvView.program_stable _ (authentication_stable setup) _
            · intro authenticated
              cases authenticated with
              | fail error | div => exact aborting_stable owner _
              | ok outcome => cases outcome with
                | Err previous => exact aborting_stable owner _
                | Ok accepted =>
                  apply RegistrationNativeBeaconEnvView.bind_stable
                  · exact RegistrationNativeBeaconEnvView.program_stable _ (agreement_stable setup owner oneTime) _
                  · intro agreed
                    cases agreed with
                    | fail error | div => exact aborting_stable owner _
                    | ok effect => cases effect <;> first
                      | exact aborting_stable owner _
                      | apply RegistrationNativeBeaconEnvView.bind_stable
                        · exact RegistrationNativeBeaconEnvView.program_stable _ (record_stable setup wire) _
                        · intro opened
                          cases opened with
                          | fail error | div => exact aborting_stable owner _
                          | ok outcome => cases outcome with
                            | Err previous => exact aborting_stable owner _
                            | Ok established =>
                              apply RegistrationNativeBeaconEnvView.bind_stable
                              · exact effect_stable _
                              · intro installed
                                cases installed with
                                | false => exact aborting_stable owner _
                                | true =>
                                  apply RegistrationNativeBeaconEnvView.bind_stable
                                  · exact phase_stable index _
                                  · intro result; exact RegistrationNativeBeaconEnvView.pure_stable _

end BeaconcryptCore.Computational.RegistrationNativeBeaconEnvFinish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvFinish.aborting_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvFinish.aborting_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvFinish.finish_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvFinish.finish_stable
