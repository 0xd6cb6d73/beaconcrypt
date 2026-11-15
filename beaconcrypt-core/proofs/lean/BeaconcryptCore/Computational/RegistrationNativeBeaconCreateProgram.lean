-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGenericBundle
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Actual typed Native.prepare has a literal fixed-pin/Ed/X25519 program. Fixed-size Core pin construction is reduced from its source definitions; no primitive sampling or availability condition is assumed. These equations retain the full native effect and state sequence. -/
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconCreateProgram
open RegistrationNativeBeaconFrontend
variable {n : Nat} {KemSK Auxiliary : Type} {source : RegistrationNativeMldsa.Source}

def pin (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) : session.ServerAuthenticationPin :=
  ⟨⟨edPin, keyId⟩, mlPin⟩

noncomputable def program (source : RegistrationNativeMldsa.Source)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    M n KemSK source Auxiliary (RustM (Option (Prepared source))) := do
  let identity ← sample PqxdhJointIdentity.sampleSeed
  let prekey ← sample PqxdhJointGapDh.sampleScalar
  pure (.ok (some ⟨pin edPin mlPin keyId, identity, prekey⟩))

theorem prepare_program (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    (prepare source edPin mlPin keyId : M n KemSK source Auxiliary _) = program source edPin mlPin keyId := by
  simp only [prepare, program, registration.begin_server_pin, session.ServerAuthenticationPin.new, pin]

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem prepare_lift (implementation : QueryImpl (Trusted n KemSK) m)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    RegistrationNativePlatformGenericBundle.liftLegacy implementation (prepare source edPin mlPin keyId : M n KemSK source Auxiliary _) = (do
      let identity ← RegistrationNativePlatformGenericBundle.liftLegacy implementation (sample PqxdhJointIdentity.sampleSeed)
      let prekey ← RegistrationNativePlatformGenericBundle.liftLegacy implementation (sample PqxdhJointGapDh.sampleScalar)
      pure (.ok (some ⟨pin edPin mlPin keyId, identity, prekey⟩))) := by
  rw [prepare_program]
  simp only [program, RegistrationNativePlatformGenericBundle.liftLegacy_bind,
    RegistrationNativePlatformGenericBundle.liftLegacy_pure]

end BeaconcryptCore.Computational.RegistrationNativeBeaconCreateProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCreateProgram.prepare_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCreateProgram.prepare_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCreateProgram.prepare_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCreateProgram.prepare_lift
