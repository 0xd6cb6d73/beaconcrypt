-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleDispatch
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionBundleOriginal
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealBundleSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorGenuineBundleOriginal
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherMessageSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleDispatchSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSampleSource

/-! The original preselection marginal retains actual outer owner lookup, fresh or supplied scalar sampling, all invalid phases and the literal typed byte conversion. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionBundleSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (selected index : Nat) (placeholder : Ed25519Signature)
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "FullState" => Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "source(" censored "," work ")" => interpret setup.joint selected placeholder censored work
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reserve
local notation "body(" owner "," scalar ")" => Main (RegistrationNativePlatformIdentityBundle.bundled setup index owner scalar writer)

private theorem sample_original (before : FullState) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
      (source(false, Main (RegistrationNativePlatformIdentityProgram.native
        (RegistrationNativeIdentityFrontend.sample (n := n) (Auxiliary := RegistrationServerRoleBackend.State) (source := mlSource) PqxdhJointGapDh.sampleScalar)))).run before =
      (RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (Main (RegistrationNativePlatformIdentityProgram.native
        (RegistrationNativeIdentityFrontend.sample (n := n) (Auxiliary := RegistrationServerRoleBackend.State) (source := mlSource) PqxdhJointGapDh.sampleScalar)))).run
          (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  apply RegistrationNativeIdentityCensorRealSigning.main
  apply (RegistrationNativePlatformIdentityCtxSampleCoins.sample setup checks representation created PqxdhJointGapDh.sampleScalar before.1.1).mono
  intro query coin
  rcases query with ((uniform | request) | report) | bytes
  · trivial
  · exact False.elim coin
  · exact False.elim coin
  · exact False.elim coin

/-- The complete outer bundle has its original source marginal before selection, with the actual owner lookup and sampled prefix retained. -/
theorem bundle_original (before : FullState)
    (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (inactive : before.1.2.active = false)
    (row : ∀ owner, before.1.1.1.beacons[index]? = some owner → owner.identity.handle = selected →
      ∃ seed, before.2.pool.seeds[selected]? = some seed) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
      (source(false, Main (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer))).run before =
      (RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (Main (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer))).run
        (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  rw [RegistrationNativeIdentityCensorBundleDispatchSource.bundle, RegistrationNativePlatformIdentityCtxBundleDispatch.bundle]
  simp only [RegistrationNativeIdentityCensorActualHashSource.project]
  cases ownerLookup : before.1.1.1.beacons[index]? with
  | none => rfl
  | some owner =>
    dsimp only
    rw [RegistrationNativeIdentityCensorBundleDispatchSource.start, RegistrationNativePlatformIdentityCtxBundleDispatch.start]
    cases phase : owner.phase with
    | fresh =>
      simp only [map_bind]
      have drawSame := sample_original setup checks representation created selected placeholder before
      simp only [RegistrationNativeIdentityCensorActualHashSource.project] at drawSame
      rw [← drawSame, bind_map_left]
      apply bind_congr_of_forall_mem_support
      intro sampled reached
      have kept := RegistrationNativeIdentityCensorSampleSource.frame setup checks representation created selected placeholder false
        PqxdhJointGapDh.sampleScalar before sampled reached
      have keptTarget := congrArg (fun value => value.1.target) kept
      have keptActive := congrArg (fun value => value.1.active) kept
      have targetEq := congrArg (fun value => value.2.target) kept
      have seedsEq := congrArg (fun value => value.2.pool.seeds) kept
      apply RegistrationNativeIdentityCensorPreselectionBundleOriginal.before_selection setup checks representation created selected index owner placeholder reserve
        sampled.1 sampled.2 (keptActive.trans inactive) (keptTarget.trans held) (targetEq.trans sourceTarget)
      intro handle
      obtain ⟨seed, found⟩ := row owner ownerLookup handle
      exact ⟨seed, (congrArg (fun seeds => seeds[selected]?) seedsEq).trans found⟩
    | freshWithCoins scalar =>
      exact RegistrationNativeIdentityCensorPreselectionBundleOriginal.before_selection setup checks representation created selected index owner placeholder reserve
        scalar before inactive held sourceTarget (row owner ownerLookup)
    | initSent pending scalar | established completed | aborted aborted => rfl


private theorem source_map {A B : Type} (censored : Bool) (change : A → B)
    (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A) :
    source(censored, change <$> work) = change <$> source(censored, work) := by
  rw [map_eq_bind_pure_comp, RegistrationNativeIdentityCensorSourceFold.bind_source]
  simp only [Function.comp_apply, RegistrationNativeIdentityCensorSourceFold.pure_source, bind_pure_comp]

private theorem original_map {A B : Type} (change : A → B)
    (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A) :
    RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (change <$> work) =
      change <$> RegistrationNativePlatformIdentityCtxMain.interpret setup.joint work := by
  rw [map_eq_bind_pure_comp, RegistrationNativePlatformIdentityCtxOrdinary.interpret_bind]
  simp only [Function.comp_apply, RegistrationNativePlatformIdentityCtxOrdinary.interpret_pure, bind_pure_comp]


/-- Literal typed byte conversion retains the same original full source marginal before selection. -/
theorem callback_original (before : FullState)
    (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (inactive : before.1.2.active = false)
    (row : ∀ owner, before.1.1.1.beacons[index]? = some owner → owner.identity.handle = selected →
      ∃ seed, before.2.pool.seeds[selected]? = some seed) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
      (source(false, RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index)).run before =
      (RegistrationNativePlatformIdentityCtxMain.interpret setup.joint
        (RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index)).run
          (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  have base := bundle_original setup checks representation created selected index placeholder reserve before held sourceTarget inactive row
  have mapped := congrArg (fun distribution => Prod.map RegistrationNativePlatformIdentityNativeBundle.reply id <$> distribution) base
  simpa only [RegistrationNativePlatformIdentityCtxLifecycle.bundle, source_map, original_map, StateT.run_map,
    Functor.map_map, Prod.map_def, id_eq] using mapped



end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionBundleSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionBundleSource.bundle_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionBundleSource.bundle_original

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionBundleSource.callback_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionBundleSource.callback_original
