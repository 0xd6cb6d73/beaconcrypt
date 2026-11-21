-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityPublication
import BeaconcryptCore.Computational.RegistrationNativeIdentityBundleSource

/-! The selected opaque-Ed source bundle continues actual stateful publication with its literal phase update and World owner advance. Failed signing/writing returns retain their reached source states. This is the selected-owner source body, before whole adaptive native profile restoration and publication-security reduction. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundle
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointIdentity (IdentitySeed)
open RegistrationNativePlatformIdentityProgram (M Original Related Keeps native original related_bind keeps_bind)
variable {n : Nat} {ι KemSK Auxiliary Platform E : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

abbrev Reply := RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))

def next (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    Reply → M n KemSK Auxiliary Platform source (RustM (Option (alloc.vec.Vec U8)))
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok published) => do
      native (RegistrationNativeIdentityFrontend.updatePhase index (.initSent published.pending oneTime))
      let _ ← native (RegistrationNativeIdentityFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent)))
      pure (.ok (some published.encoded))

def originalNext (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    Reply → Original n KemSK Auxiliary Platform source (RustM (Option (alloc.vec.Vec U8)))
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok published) => do
      original (RegistrationNativeBeaconFrontend.updatePhase index (.initSent published.pending oneTime))
      let _ ← original (RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent)))
      pure (.ok (some published.encoded))

/-- Actual source Ready/publication replies continue with the same native phase and owner-slot operation. -/
theorem next_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (seeds : List IdentitySeed) (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source) (seed : IdentitySeed)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (reply : Reply) :
    Related (n := n) (Auxiliary := Auxiliary) (Platform := Platform) setup checks representation created seeds
      (next index owner oneTime reply) (originalNext index (RegistrationNativeIdentityFrontend.restore seed owner) oneTime reply) := by
  cases reply with
  | fail error | div => exact RegistrationNativePlatformIdentityProgram.related_pure setup checks representation created seeds _
  | ok reply => cases reply with
    | Err error => exact RegistrationNativePlatformIdentityProgram.related_pure setup checks representation created seeds _
    | Ok published =>
      exact related_bind setup checks representation created seeds _ _ _ _
        (RegistrationNativePlatformIdentityProgram.native_related setup checks representation created seeds _ _
          (RegistrationNativeIdentityBundleSource.phase_source setup checks representation created seeds index (.initSent published.pending oneTime)))
        (RegistrationNativePlatformIdentityProgram.native_keeps setup checks representation created _
          (RegistrationNativeIdentityBundleSource.phase_keeps setup checks representation created index (.initSent published.pending oneTime)))
        (fun _ => related_bind setup checks representation created seeds _ _ _ _
          (RegistrationNativePlatformIdentityProgram.native_related setup checks representation created seeds _ _
            (RegistrationNativeIdentityCommonSource.effect_source setup checks representation created seeds _))
          (RegistrationNativePlatformIdentityProgram.native_keeps setup checks representation created _
            (RegistrationNativeIdentityCommonSource.effect_keeps setup checks representation created _))
          (fun _ => RegistrationNativePlatformIdentityProgram.related_pure setup checks representation created seeds _))

theorem next_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) (reply : Reply) :
    Keeps (n := n) (Auxiliary := Auxiliary) (Platform := Platform) setup checks representation created (next index owner oneTime reply) := by
  cases reply with
  | fail error | div => exact RegistrationNativePlatformIdentityProgram.keeps_pure setup checks representation created _
  | ok reply => cases reply with
    | Err error => exact RegistrationNativePlatformIdentityProgram.keeps_pure setup checks representation created _
    | Ok published =>
      exact keeps_bind setup checks representation created _ _
        (RegistrationNativePlatformIdentityProgram.native_keeps setup checks representation created _
          (RegistrationNativeIdentityBundleSource.phase_keeps setup checks representation created index (.initSent published.pending oneTime)))
        (fun _ => keeps_bind setup checks representation created _ _
          (RegistrationNativePlatformIdentityProgram.native_keeps setup checks representation created _
            (RegistrationNativeIdentityCommonSource.effect_keeps setup checks representation created _))
          (fun _ => RegistrationNativePlatformIdentityProgram.keeps_pure setup checks representation created _))

noncomputable def bundled (setup : Setup base KemSK) (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    M n KemSK Auxiliary Platform source (RustM (Option (alloc.vec.Vec U8))) := do
  let reply ← simulateQ (RegistrationNativePlatformIdentityPublication.callback setup index owner writer)
    (RegistrationNativePlatformWriter.begin E ⟨owner.pin.binding⟩ (RegistrationNativeIdentityFrontend.inputs owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin)
  next index owner oneTime reply

noncomputable def originalBundled (setup : Setup base KemSK) (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Original n KemSK Auxiliary Platform source (RustM (Option (alloc.vec.Vec U8))) := do
  let reply ← simulateQ (RegistrationNativePlatformIdentityPublication.originalCallback setup index owner writer)
    (RegistrationNativePlatformWriter.begin E ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin)
  originalNext index owner oneTime reply

/-- Full selected bundle execution preserves source hash/sign/serializer and lifecycle order, including every actual failed prefix. -/
theorem bundled_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (seeds : List IdentitySeed) (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source) (seed : IdentitySeed)
    (oneTime : PqxdhJointGapDh.ScalarBytes)
    (found : seeds[owner.identity.handle]? = some seed) (publicKey : owner.identity.publicIdentity = setup.joint.publicKeys seed)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds
      (bundled setup index owner oneTime writer) (originalBundled setup index (RegistrationNativeIdentityFrontend.restore seed owner) oneTime writer) :=
  related_bind setup checks representation created seeds _ _ _ _
    (RegistrationNativePlatformIdentityPublication.begin_source setup checks representation created seeds index owner seed oneTime found publicKey writer)
    (RegistrationNativePlatformIdentityPublication.begin_keeps setup checks representation created index owner oneTime writer)
    (next_source setup checks representation created seeds index owner seed oneTime)

theorem bundled_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created (bundled setup index owner oneTime writer) :=
  keeps_bind setup checks representation created _ _
    (RegistrationNativePlatformIdentityPublication.begin_keeps setup checks representation created index owner oneTime writer)
    (next_keeps setup checks representation created index owner oneTime)

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundle.next_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundle.next_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundle.next_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundle.next_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundle.bundled_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundle.bundled_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundle.bundled_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundle.bundled_keeps
