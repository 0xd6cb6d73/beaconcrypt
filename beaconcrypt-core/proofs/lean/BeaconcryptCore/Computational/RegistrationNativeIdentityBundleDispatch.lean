-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityBundleSource

/-! The actual public owner lookup and one-time-scalar choice dispatch into the source-related publication controller. All non-fresh phases reject without source effects; fresh owners use their actual optional supplied scalar or original counted sampler. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityBundleDispatch
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentitySourceSimulation
open RegistrationNativeIdentityBundleSource (bundled oldBundled)
open RegistrationNativeIdentityFrontend (Owner)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

noncomputable def start (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source) :
    RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source (RustM (Option Pqxdh.Bytes)) := do
  let selected : Option (Option PqxdhJointGapDh.ScalarBytes) := match owner.phase with
    | .fresh => some none
    | .freshWithCoins scalar => some (some scalar)
    | _ => none
  match selected with
  | none => pure (.ok none)
  | some supplied => do
      let oneTime ← match supplied with
        | some scalar => pure scalar
        | none => RegistrationNativeIdentityFrontend.sample PqxdhJointGapDh.sampleScalar
      bundled setup wire index owner oneTime

noncomputable def original (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) :
    RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) := do
  let selected : Option (Option PqxdhJointGapDh.ScalarBytes) := match owner.phase with
    | .fresh => some none
    | .freshWithCoins scalar => some (some scalar)
    | _ => none
  match selected with
  | none => pure (.ok none)
  | some supplied => do
      let oneTime ← match supplied with
        | some scalar => pure scalar
        | none => RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar
      oldBundled setup wire index owner oneTime

/-- Source owner dispatch preserves the original counted scalar choice and complete publication continuation. -/
theorem start_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (seeds : List PqxdhJointIdentity.IdentitySeed)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source) (seed : PqxdhJointIdentity.IdentitySeed)
    (found : seeds[owner.identity.handle]? = some seed)
    (publicKey : owner.identity.publicIdentity = setup.joint.publicKeys seed) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds
      (start setup wire index owner) (original setup wire index (RegistrationNativeIdentityFrontend.restore seed owner)) := by
  cases phase : owner.phase with
  | fresh =>
      simp only [start, original, RegistrationNativeIdentityFrontend.restore, phase]
      exact related_bind setup checks representation created seeds _ _ _ _
        (RegistrationNativeIdentityCommonSource.sample_source setup checks representation created seeds _)
        (RegistrationNativeIdentityCommonSource.sample_keeps setup checks representation created _)
        (fun scalar => RegistrationNativeIdentityBundleSource.bundled_source setup checks representation created seeds wire index owner seed scalar found publicKey)
  | freshWithCoins scalar =>
      simpa only [start, original, RegistrationNativeIdentityFrontend.restore, phase, pure_bind] using
        RegistrationNativeIdentityBundleSource.bundled_source setup checks representation created seeds wire index owner seed scalar found publicKey
  | initSent pending scalar | established completed | aborted aborted =>
      simpa only [start, original, RegistrationNativeIdentityFrontend.restore, phase] using
        (related_pure (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created seeds (.ok none : RustM (Option Pqxdh.Bytes)))

theorem start_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created (start setup wire index owner) := by
  cases phase : owner.phase with
  | fresh =>
      simp only [start, phase]
      exact keeps_bind setup checks representation created _ _
        (RegistrationNativeIdentityCommonSource.sample_keeps setup checks representation created _)
        (fun scalar => RegistrationNativeIdentityBundleSource.bundled_keeps setup checks representation created wire index owner scalar)
  | freshWithCoins scalar =>
      simpa only [start, phase, pure_bind] using
        RegistrationNativeIdentityBundleSource.bundled_keeps setup checks representation created wire index owner scalar
  | initSent pending scalar | established completed | aborted aborted =>
      simpa only [start, phase] using
        (keeps_pure (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created (.ok none : RustM (Option Pqxdh.Bytes)))

theorem new_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (owner : Owner source) (current : RegistrationNativeIdentityFrontend.State source)
    (found : current[index]? = some owner) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    ((RegistrationNativeIdentityFrontend.bundle (n := n) setup source wire index).run current).run env =
      ((start setup wire index owner).run current).run env := by
  cases phase : owner.phase <;>
    simp only [RegistrationNativeIdentityFrontend.bundle, start, bundled, RegistrationNativeIdentityBundleSource.next,
      StateT.run_bind, StateT.run_get, pure_bind, found, phase]
  all_goals rfl

theorem old_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (current : RegistrationNativeBeaconFrontend.State source)
    (found : current[index]? = some owner) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    ((RegistrationNativeBeaconFrontend.bundle (n := n) setup source wire index).run current).run env =
      ((original setup wire index owner).run current).run env := by
  cases phase : owner.phase <;>
    simp only [RegistrationNativeBeaconFrontend.bundle, original, oldBundled, RegistrationNativeIdentityBundleSource.original,
      StateT.run_bind, StateT.run_get, pure_bind, found, phase]
  all_goals rfl

end BeaconcryptCore.Computational.RegistrationNativeIdentityBundleDispatch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundleDispatch.start_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundleDispatch.start_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundleDispatch.start_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundleDispatch.start_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundleDispatch.new_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundleDispatch.new_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundleDispatch.old_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundleDispatch.old_run
