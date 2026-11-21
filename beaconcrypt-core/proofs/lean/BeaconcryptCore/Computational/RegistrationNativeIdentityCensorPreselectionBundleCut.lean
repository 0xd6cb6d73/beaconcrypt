-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPostselectionBundleCut
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleDispatch
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleBundlePair
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionOtherBundle
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedMain
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealBundleSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorGenuineBundleOriginal
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherMessageSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleDispatchSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSampleSource

/-! The actual target-none inactive bundle entry has matching real and censored public stopping cuts. Its fresh selected, stale selected, unarmed and other-owner branches are derived separately, preserving dynamic writer failures and the entire reached source/private/P state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionBundleCut
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open RegistrationNativeIdentityCensorBundleStopCut (cut)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (selected index : Nat) (placeholder : Ed25519Signature)
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "FullState" => Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "source(" censored "," work ")" => interpret setup.joint selected placeholder censored work
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reserve
local notation "body(" owner "," scalar ")" => Main (RegistrationNativePlatformIdentityBundle.bundled setup index owner scalar writer)

/-- Only an actual fresh selected operand uses the stopping comparison; stale and unarmed bodies retain exact full behavior. -/
theorem body (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (scalar : PqxdhJointGapDh.ScalarBytes)
    (before : FullState) (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (inactive : before.1.2.active = false)
    (row : owner.identity.handle = selected → ∃ seed, before.2.pool.seeds[selected]? = some seed) :
    cut placeholder <$> (source(false, body(owner, scalar))).run before =
      cut placeholder <$> (source(true, body(owner, scalar))).run before := by
  classical
  by_cases handle : owner.identity.handle = selected
  · by_cases armed : before.1.2.armed = true
    · obtain ⟨started,built⟩ := BeaconcryptCore.PanicFreedom.beacon_start_ok (pqxdh.BeaconFresh.mk owner.pin.binding)
        (RegistrationNativeIdentityFrontend.inputs owner)
        (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)))
      by_cases issued : PqxdhRefinement.absBytes started.message.one_time_key ∈ PqxdhJointIdentity.signedMessages
          (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript)
      · rw [RegistrationNativeIdentityCensorStaleBundlePair.bundled setup checks representation created index owner reserve selected placeholder
          scalar started built before handle held sourceTarget issued]
      · obtain ⟨seed,found⟩ := row handle
        exact RegistrationNativeIdentityCensorBundleStopCut.paired setup checks representation created selected index owner placeholder reserve
          scalar started built before seed handle armed held sourceTarget issued found
    · rw [RegistrationNativeIdentityCensorUnarmedMain.paired setup.joint selected placeholder (body(owner, scalar)) before
        ⟨Bool.eq_false_iff.mpr armed,held,inactive⟩]
  · rw [RegistrationNativeIdentityCensorPreselectionOtherBundle.bundled setup checks representation created selected index owner placeholder writer
      handle scalar before]

/-- The literal owner lookup, supplied/fresh scalar and every invalid phase retain the same public stopping cut. -/
theorem bundle (before : FullState)
    (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (inactive : before.1.2.active = false)
    (row : ∀ owner, before.1.1.1.beacons[index]? = some owner → owner.identity.handle = selected →
      ∃ seed, before.2.pool.seeds[selected]? = some seed) :
    cut placeholder <$> (source(false, Main (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer))).run before =
      cut placeholder <$> (source(true, Main (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer))).run before := by
  rw [RegistrationNativeIdentityCensorBundleDispatchSource.bundle,RegistrationNativeIdentityCensorBundleDispatchSource.bundle]
  cases ownerLookup : before.1.1.1.beacons[index]? with
  | none => rfl
  | some owner =>
    dsimp only
    rw [RegistrationNativeIdentityCensorBundleDispatchSource.start,RegistrationNativeIdentityCensorBundleDispatchSource.start]
    cases phase : owner.phase with
    | fresh =>
      simp only [map_bind]
      rw [RegistrationNativeIdentityCensorSampleSource.paired setup checks representation created selected placeholder PqxdhJointGapDh.sampleScalar before]
      apply bind_congr_of_forall_mem_support
      intro sampled reached
      have kept := RegistrationNativeIdentityCensorSampleSource.frame setup checks representation created selected placeholder true
        PqxdhJointGapDh.sampleScalar before sampled reached
      apply body setup checks representation created selected index placeholder reserve owner sampled.1 sampled.2
        ((congrArg (fun value => value.1.target) kept).trans held)
        ((congrArg (fun value => value.2.target) kept).trans sourceTarget)
        ((congrArg (fun value => value.1.active) kept).trans inactive)
      intro handle
      obtain ⟨seed,found⟩ := row owner ownerLookup handle
      exact ⟨seed,(congrArg (fun value => value.2.pool.seeds[selected]?) kept).trans found⟩
    | freshWithCoins scalar =>
      exact body setup checks representation created selected index placeholder reserve owner scalar before held sourceTarget inactive (row owner ownerLookup)
    | initSent pending scalar | established completed | aborted aborted => rfl

private theorem source_map {A B : Type} (censored : Bool) (change : A → B)
    (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A) :
    source(censored, change <$> work) = change <$> source(censored, work) := by
  rw [map_eq_bind_pure_comp,RegistrationNativeIdentityCensorSourceFold.bind_source]
  simp only [Function.comp_apply,RegistrationNativeIdentityCensorSourceFold.pure_source,bind_pure_comp]

/-- The literal typed Vec-to-byte reply conversion is included in the same public cut. -/
theorem callback (before : FullState)
    (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (inactive : before.1.2.active = false)
    (row : ∀ owner, before.1.1.1.beacons[index]? = some owner → owner.identity.handle = selected →
      ∃ seed, before.2.pool.seeds[selected]? = some seed) :
    RegistrationNativeIdentityCensorPostselectionBundleCut.replyCut placeholder <$>
      (source(false,RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index)).run before =
    RegistrationNativeIdentityCensorPostselectionBundleCut.replyCut placeholder <$>
      (source(true,RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index)).run before := by
  simp only [RegistrationNativePlatformIdentityCtxLifecycle.bundle,source_map,StateT.run_map,Functor.map_map]
  exact bundle setup checks representation created selected index placeholder reserve before held sourceTarget inactive row

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionBundleCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionBundleCut.body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionBundleCut.body

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionBundleCut.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionBundleCut.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionBundleCut.callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionBundleCut.callback
