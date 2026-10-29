-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource

/-! Bundle publication uses the actual current-owner phase update after the complete outgoing source controller. Failed Ed/ML signing and encoding retain earlier history/World effects; successful publication advances the same native owner without replacing its reached signing history. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityBundleSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointIdentity (IdentitySeed)
open RegistrationNativeIdentitySourceSimulation
open RegistrationNativeIdentityFrontend (Owner)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

theorem phase_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (seeds : List IdentitySeed)
    (index : Nat) (phase : RegistrationNativeBeaconFrontend.Phase) :
    Related (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created seeds
      (RegistrationNativeIdentityFrontend.updatePhase index phase)
      (RegistrationNativeBeaconFrontend.updatePhase index phase) := by
  apply related_modify setup checks representation created seeds
  intro current
  exact RegistrationNativeIdentitySourceRoster.phase_source ⟨seeds, []⟩ current index phase

theorem phase_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (phase : RegistrationNativeBeaconFrontend.Phase) :
    Keeps (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created
      (RegistrationNativeIdentityFrontend.updatePhase index phase) :=
  keeps_modify setup checks representation created _

def next (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    RustM (RegistrationBeaconInitExecutor.Result Pqxdh.Bytes) →
      RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source (RustM (Option Pqxdh.Bytes))
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok published) => do
      RegistrationNativeIdentityFrontend.updatePhase index (.initSent published.pending oneTime)
      let _ ← RegistrationNativeIdentityFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent))
      pure (.ok (some published.encoded))

def original (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) :
    RustM (RegistrationBeaconInitExecutor.Result Pqxdh.Bytes) →
      RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes))
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok published) => do
      RegistrationNativeBeaconFrontend.updatePhase index (.initSent published.pending oneTime)
      let _ ← RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent))
      pure (.ok (some published.encoded))

theorem next_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (seeds : List IdentitySeed)
    (index : Nat) (owner : Owner source) (seed : IdentitySeed) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (reply : RustM (RegistrationBeaconInitExecutor.Result Pqxdh.Bytes)) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds
      (next index owner oneTime reply) (original index (RegistrationNativeIdentityFrontend.restore seed owner) oneTime reply) := by
  cases reply with
  | fail error | div => exact related_pure setup checks representation created seeds _
  | ok result => cases result with
    | Err error => exact related_pure setup checks representation created seeds _
    | Ok published =>
        exact related_bind setup checks representation created seeds _ _ _ _
          (phase_source setup checks representation created seeds index (.initSent published.pending oneTime))
          (phase_keeps setup checks representation created index (.initSent published.pending oneTime))
          (fun _ => related_bind setup checks representation created seeds _ _ _ _
            (RegistrationNativeIdentityCommonSource.effect_source setup checks representation created seeds _)
            (RegistrationNativeIdentityCommonSource.effect_keeps setup checks representation created _)
            (fun _ => related_pure setup checks representation created seeds _))

theorem next_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (reply : RustM (RegistrationBeaconInitExecutor.Result Pqxdh.Bytes)) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created (next index owner oneTime reply) := by
  cases reply with
  | fail error | div => exact keeps_pure setup checks representation created _
  | ok result => cases result with
    | Err error => exact keeps_pure setup checks representation created _
    | Ok published =>
        exact keeps_bind setup checks representation created _ _
          (phase_keeps setup checks representation created index (.initSent published.pending oneTime))
          (fun _ => keeps_bind setup checks representation created _ _
            (RegistrationNativeIdentityCommonSource.effect_keeps setup checks representation created _)
            (fun _ => keeps_pure setup checks representation created _))

noncomputable def bundled (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source (RustM (Option Pqxdh.Bytes)) := do
  let result ← simulateQ (RegistrationNativeIdentityFrontend.outgoing setup source index owner)
    (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩
      (RegistrationNativeIdentityFrontend.inputs owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey)
  next index owner oneTime result

noncomputable def oldBundled (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) := do
  let result ← simulateQ (RegistrationNativeBeaconFrontend.outgoing setup source index owner)
    (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩
      (RegistrationNativeBeaconFrontend.inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey)
  original index owner oneTime result

/-- The full successful or failed publication stage is the exact original native source stage under the privately generated credential. -/
theorem bundled_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (seeds : List IdentitySeed)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source) (seed : IdentitySeed)
    (oneTime : PqxdhJointGapDh.ScalarBytes)
    (found : seeds[owner.identity.handle]? = some seed)
    (publicKey : owner.identity.publicIdentity = setup.joint.publicKeys seed) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds
      (bundled setup wire index owner oneTime)
      (oldBundled setup wire index (RegistrationNativeIdentityFrontend.restore seed owner) oneTime) :=
  related_bind setup checks representation created seeds _ _ _ _
    (RegistrationNativeIdentityOutgoingSource.init_source setup checks representation created seeds wire index owner seed oneTime found publicKey)
    (RegistrationNativeIdentityOutgoingSource.init_keeps setup checks representation created wire index owner oneTime)
    (next_source setup checks representation created seeds index owner seed oneTime)

theorem bundled_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created (bundled setup wire index owner oneTime) :=
  keeps_bind setup checks representation created _ _
    (RegistrationNativeIdentityOutgoingSource.init_keeps setup checks representation created wire index owner oneTime)
    (next_keeps setup checks representation created index owner oneTime)

end BeaconcryptCore.Computational.RegistrationNativeIdentityBundleSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundleSource.phase_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundleSource.phase_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundleSource.phase_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundleSource.phase_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundleSource.next_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundleSource.next_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundleSource.next_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundleSource.next_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundleSource.bundled_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundleSource.bundled_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundleSource.bundled_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundleSource.bundled_keeps
