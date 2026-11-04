-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconCreateEntry
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Whole native creation is the literal lifted ML/hash/Ed/X25519 prefix, one indexed KEM call, and owner registration. Prefix normality is reduced from the fixed Core pin controller, rather than assumed as a constructor law. -/
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconCreateLift
open RegistrationNativeBeaconFrontend
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

noncomputable def prepared (implementation : QueryImpl (Trusted n KemSK) m)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    RegistrationNativePlatformGenericBundle.M source Auxiliary m (Option (Prepared source)) := do
  let generated ← RegistrationNativePlatformGenericBundle.liftLegacy implementation (sample (RegistrationNativeMldsa.generate source))
  match generated with
  | none => pure none
  | some credentials =>
    let digest ← RegistrationNativePlatformGenericBundle.liftLegacy implementation (hash (.Single (Std.Array.to_slice mlPin)))
    let identity ← RegistrationNativePlatformGenericBundle.liftLegacy implementation (sample PqxdhJointIdentity.sampleSeed)
    let prekey ← RegistrationNativePlatformGenericBundle.liftLegacy implementation (sample PqxdhJointGapDh.sampleScalar)
    pure (some ⟨credentials, RegistrationNativeBeaconCreateProgram.pin edPin mlPin keyId digest, identity, prekey⟩)

theorem prepare (implementation : QueryImpl (Trusted n KemSK) m)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    RegistrationNativePlatformGenericBundle.liftLegacy implementation
        (RegistrationNativeBeaconFrontend.prepare source edPin mlPin keyId : M n KemSK source Auxiliary _) =
      RustM.ok <$> prepared implementation edPin mlPin keyId := by
  rw [RegistrationNativeBeaconCreateProgram.prepare_lift]
  simp only [prepared, map_bind]
  apply bind_congr
  intro generated
  cases generated with
  | none => simp only [map_pure]
  | some credential => simp only [map_bind, map_pure]

theorem create (implementation : QueryImpl (Trusted n KemSK) m)
    (setup : Setup base KemSK) (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    RegistrationNativePlatformGenericBundle.liftLegacy implementation
        (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId : M n KemSK source Auxiliary _) = (do
      let prepared ← prepared implementation edPin mlPin keyId
      match prepared with
      | none => pure (.ok none)
      | some ready =>
        let born ← RegistrationNativePlatformGenericBundle.liftLegacy implementation (kem (.inr (.inl .create)))
        RegistrationNativePlatformGenericBundle.liftLegacy implementation
          (RegistrationNativeBeaconCreateEntry.register setup edPin keyId ready born)) := by
  unfold RegistrationNativeBeaconFrontend.create
  rw [RegistrationNativePlatformGenericBundle.liftLegacy_bind, prepare]
  simp only [bind_map_left]
  apply bind_congr
  intro prepared
  cases prepared with
  | none => exact RegistrationNativePlatformGenericBundle.liftLegacy_pure implementation _
  | some ready =>
    dsimp only
    rw [RegistrationNativeBeaconCreateEntry.append_program setup edPin keyId ready, RegistrationNativePlatformGenericBundle.liftLegacy_bind]

end BeaconcryptCore.Computational.RegistrationNativeBeaconCreateLift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCreateLift.prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCreateLift.prepare

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCreateLift.create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCreateLift.create
