-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleMetadata
import BeaconcryptCore.Refinement.RegistrationSigningContinuations

/-! The suppressed role is the one-time-key signature. Equal tagged one-time messages retain the same public key, without equating private scalar realizations. The entire original publication tree depends on that public value and the complete immutable owner metadata, including pin, generated ML credential, identity seed, prekey and PQ key. This tree equality does not assert equality of different physical ROM states. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateAlias
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeOwnerFields (metadata)
variable {I KemSK Auxiliary Encoded : Type} {base : OracleSpec I} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

/-- The original full source publication tree takes the one-time PUBLIC key; it never receives its scalar. -/
noncomputable def program (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhEd25519EufCma.X25519PublicKey)
    (encode : registration.InitView → RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary
      (RustM (core.option.Option Encoded))) :=
  RegistrationNativePlatformBeaconPublication.begin
    (RegistrationNativeBeaconFrontend.outgoing setup source index owner) encode ⟨owner.pin.binding⟩
    (RegistrationNativeBeaconFrontend.inputs setup owner)
    ⟨PqxdhRootTableInitialization.rootArray oneTime⟩ owner.pin

/-- Resetting only phase and the private signing-history coordinate leaves the complete source request/continuation tree unchanged. -/
theorem metadata_program (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhEd25519EufCma.X25519PublicKey)
    (encode : registration.InitView → RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary
      (RustM (core.option.Option Encoded))) :
    program setup source index owner oneTime encode = program setup source index (metadata owner) oneTime encode := rfl

/-- The full actual source tree is stable under immutable metadata and repeated tagged one-time message, regardless of how its private scalar was obtained. -/
theorem one_time (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (left right : Owner source) (oneTimeLeft oneTimeRight : PqxdhEd25519EufCma.X25519PublicKey)
    (encode : registration.InitView → RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary
      (RustM (core.option.Option Encoded)))
    (retained : metadata left = metadata right)
    (message : PqxdhEd25519EufCma.oneTimeMessage oneTimeLeft = PqxdhEd25519EufCma.oneTimeMessage oneTimeRight) :
    program setup source index left oneTimeLeft encode = program setup source index right oneTimeRight encode := by
  have publicKey := PqxdhEd25519EufCma.oneTimeMessage_injective message
  calc
    _ = program setup source index (metadata left) oneTimeLeft encode := metadata_program _ _ _ _ _ _
    _ = program setup source index (metadata right) oneTimeRight encode := by rw [retained, publicKey]
    _ = _ := (metadata_program _ _ _ _ _ _).symm

/-- Metadata preservation is taken from the literal prior source bundle, including a failed writer. A repeated one-time message then selects the identical full publication tree at the next attempt. -/
theorem retry {E Platform : Type} (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (source : RegistrationNativeMldsa.Source)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (before after : RegistrationNativeExperiment.State n KemSK source) (previous next : Platform)
    (reply : RustM (Option Pqxdh.Bytes))
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer index).run before).run previous))
    (left right : Owner source) (foundLeft : before.beacons[index]? = some left) (foundRight : after.beacons[index]? = some right)
    (oneTimeLeft oneTimeRight : PqxdhEd25519EufCma.X25519PublicKey)
    (encode : registration.InitView → RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary
      (RustM (core.option.Option Encoded)))
    (message : PqxdhEd25519EufCma.oneTimeMessage oneTimeLeft = PqxdhEd25519EufCma.oneTimeMessage oneTimeRight) :
    program setup source index left oneTimeLeft encode = program setup source index right oneTimeRight encode := by
  have kept := RegistrationNativePlatformBundleMetadata.native_bundle coins setup checks representation created source writer index before after previous next reply supported
  have lookup := congrArg (fun owners => owners[index]?) kept
  simp only [List.getElem?_map, foundLeft, foundRight, Option.map_some, Option.some.injEq] at lookup
  exact one_time setup source index left right oneTimeLeft oneTimeRight encode lookup.symm message

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateAlias
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateAlias.metadata_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateAlias.metadata_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateAlias.one_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateAlias.one_time
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateAlias.retry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateAlias.retry
