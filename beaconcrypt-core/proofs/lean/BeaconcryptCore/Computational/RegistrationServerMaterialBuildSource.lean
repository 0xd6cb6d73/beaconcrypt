-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerMaterialCompleteSource

/-! The actual public build consumes its one-use reference capability before cancellation, complete-message preflight, occupancy, reservation and crypto work. Private token/root reconstruction preserves that exact SDK order and its complete semantic World. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerMaterialBuildSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationServerMaterialSourceState (State close project restore nativeView)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}

/-- The complete actual one-use material frontend is the concrete native SDK build controller through every cancellation, source failure and successful publication. -/
theorem native (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (roots : RegistrationServerReferenceRestore.Roots) (handle : Nat) (application : Option (Slice U8)) (before : State n) :
    Prod.map id (project roots) <$>
      (close setup.source wire.frameWrite sign roots
        (RegistrationServerMaterialFrontend.build wire checks.reservePeer handle application)).run before =
      Prod.map id nativeView <$>
        (RegistrationServerSdkSource.build setup (RegistrationNativeWire.ledgerCodec wire) checks sign wire.encodeResponse
          handle application).run (restore roots before) := by
  have taken := RegistrationServerReferenceRestore.take roots handle before.1 before.2
  change RegistrationServerSdkSource.take handle (restore roots before) =
    ((RegistrationServerMaterialFrontend.take handle before.1).1.map (RegistrationServerReferenceRestore.token roots),
      restore roots ((RegistrationServerMaterialFrontend.take handle before.1).2, before.2)) at taken
  simp only [close, StateT.run, RegistrationServerMaterialFrontend.build, RegistrationServerSdkSource.build]
  rw [taken]
  cases selected : RegistrationServerMaterialFrontend.take handle before.1 with
  | mk ready current =>
      cases ready with
      | none => rfl
      | some ready =>
          cases application with
          | none => rfl
          | some application =>
              change Prod.map id (project roots) <$>
                (close setup.source wire.frameWrite sign roots
                  (RegistrationServerMaterialFrontend.complete wire checks.reservePeer ready application)).run (current, before.2) =
                Prod.map id nativeView <$>
                  (RegistrationServerSdkSource.complete setup (RegistrationNativeWire.ledgerCodec wire) checks sign wire.encodeResponse
                    (RegistrationServerReferenceRestore.token roots ready) application).run (restore roots (current, before.2))
              exact RegistrationServerMaterialCompleteSource.native setup checks wire sign roots ready application (current, before.2)

end BeaconcryptCore.Computational.RegistrationServerMaterialBuildSource

/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialBuildSource.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialBuildSource.native
