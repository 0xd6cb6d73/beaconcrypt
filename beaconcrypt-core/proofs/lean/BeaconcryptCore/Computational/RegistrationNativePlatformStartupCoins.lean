-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicStartupFrame
import BeaconcryptCore.Computational.RegistrationNativeSeedStart
import BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformStartupCoins
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {I KemSK : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
variable (ensureInit : StateT Unit ProbComp Bool) (qInit qGenerate : Nat)
variable (initialized : (ensureInit.run ()).IsTotalQueryBound qInit)
variable (generated : source.generate.IsTotalQueryBound qGenerate)
include initialized generated in
/-- The actual startup preceding the corrected source tree pays initialization, its retained dummy identity draw, generation and one64-byte ROM cache miss. -/
theorem public_start (identityIndex : Nat) (serverKeyId : U64) (identity : PqxdhJointIdentity.PublicIdentity)
    (before : PqxdhRecordLiftWorld.State n) :
    ((RegistrationNativePublicStartupFrame.startup setup source ensureInit identityIndex serverKeyId identity).run before).IsTotalQueryBound
      ((qInit + 32) + (qGenerate + 64)) := by
  simp only [RegistrationNativePublicStartupFrame.startup, StateT.run_bind]
  apply isTotalQueryBound_bind
    (RegistrationNativeMldsaCoinPrimitives.sampled _ _ (RegistrationNativePrimitiveCosts.constructor_bound setup.joint ensureInit qInit initialized identityIndex serverKeyId) before)
  rintro ⟨⟨constructed, initState⟩, world⟩
  cases built : constructed with
  | none => trivial
  | some created =>
      apply isTotalQueryBound_bind
        (RegistrationNativeMldsaCoinPrimitives.sampled _ _ (RegistrationNativePrimitiveCosts.generation_bound source qGenerate generated) world)
      rintro ⟨sampled, current⟩
      cases born : sampled with
      | none => trivial
      | some credential =>
          apply isTotalQueryBound_bind (n₁ := 0) (n₂ := 64)
          · cases present : current.server <;> simp only [PqxdhRecordLiftWorld.initializeServer, present, IsTotalQueryBound, isQueryBound_pure]
          · intro installed
            exact isTotalQueryBound_bind (n₂ := 0) (RegistrationNativeMldsaCoinPrimitives.hash _ installed.2) (fun _ => by trivial)
private theorem finish_bound (source : RegistrationNativeMldsa.Source) (qGenerate : Nat)
    (generated : source.generate.IsTotalQueryBound qGenerate)
    (constructed : (Option (PqxdhLiveServerConstruction.Created Unit) × Unit) × PqxdhRecordLiftWorld.State n) :
    (RegistrationNativeSeedStart.finish (KemSK := KemSK) source constructed).IsTotalQueryBound (qGenerate + 64) := by
  simp only [RegistrationNativeSeedStart.finish]
  cases built : constructed.1.1 with
  | none => trivial
  | some created =>
      apply isTotalQueryBound_bind
        (RegistrationNativeMldsaCoinPrimitives.sampled _ _ (RegistrationNativePrimitiveCosts.generation_bound source qGenerate generated) constructed.2)
      rintro ⟨sampled, current⟩
      cases born : sampled with
      | none => trivial
      | some credential =>
          apply isTotalQueryBound_bind (n₂ := 0) (RegistrationNativeMldsaCoinPrimitives.frontend_start _ _ _ current)
          intro result
          cases result.1 with
          | fail error | div => trivial
          | ok optional => cases optional <;> trivial
include initialized generated in
/-- The actual seeded source startup retains every dummy draw and failure while obeying the concrete startup sampler cap. -/
theorem seed_start (identityIndex : Nat) (serverKeyId : U64) (seed : PqxdhJointIdentity.IdentitySeed) :
    (RegistrationNativeSeedStart.start (n := n) setup source ensureInit identityIndex serverKeyId seed).IsTotalQueryBound
      ((qInit + 32) + (qGenerate + 64)) := by
  unfold RegistrationNativeSeedStart.start
  exact isTotalQueryBound_bind
    (RegistrationNativeMldsaCoinPrimitives.sampled _ _ (RegistrationNativePrimitiveCosts.constructor_bound setup.joint ensureInit qInit initialized identityIndex serverKeyId) _)
    (fun constructed => finish_bound (KemSK := KemSK) source qGenerate generated _)
include initialized generated in
/-- Original generated native startup has the same concrete cap with no whole-startup cost premise. -/
theorem native_start (identityIndex : Nat) (serverKeyId : U64) :
    (RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId).IsTotalQueryBound
      ((qInit + 32) + (qGenerate + 64)) := by
  change (do
    let constructed ← (PqxdhRecordLiftWorld.sampled
      ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ())).run
        (PqxdhRecordLiftWorld.initial : PqxdhRecordLiftWorld.State n)
    RegistrationNativeSeedStart.finish source constructed).IsTotalQueryBound _
  exact isTotalQueryBound_bind
    (RegistrationNativeMldsaCoinPrimitives.sampled _ _ (RegistrationNativePrimitiveCosts.constructor_bound setup.joint ensureInit qInit initialized identityIndex serverKeyId) _)
    (fun constructed => finish_bound (KemSK := KemSK) source qGenerate generated constructed)
end BeaconcryptCore.Computational.RegistrationNativePlatformStartupCoins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformStartupCoins.public_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformStartupCoins.public_start
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformStartupCoins.seed_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformStartupCoins.seed_start
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformStartupCoins.native_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformStartupCoins.native_start
