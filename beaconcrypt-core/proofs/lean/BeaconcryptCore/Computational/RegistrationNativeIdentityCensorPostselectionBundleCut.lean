-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleDispatch
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRepeatedStopCut
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealBundleSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorGenuineBundleOriginal
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherMessageSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleDispatchSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSampleSource

/-! After a target is selected, every actual captured bundle is either a matching repeated publication or a genuine other-handle/message request. The public publication cut has identical real/private-censored distributions, including sampled prefixes and failed writers. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPostselectionBundleCut
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

/-- Literal one-time operand lineage exhausts every current message and handle case after selection. No fresh-message, owner-admission or source-success premise is used. -/
theorem body (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (scalar : PqxdhJointGapDh.ScalarBytes)
    (target : Pqxdh.Bytes) (targetRole : RegistrationNativeIdentitySigningRole.oneTime target = true)
    (before : FullState) (seed : PqxdhJointIdentity.IdentitySeed)
    (held : before.1.2.target = some target) (sourceTarget : before.2.target = some target)
    (inactive : before.1.2.active = false) (found : before.2.pool.seeds[selected]? = some seed) :
    cut placeholder <$> (source(false, body(owner, scalar))).run before =
      cut placeholder <$> (source(true, body(owner, scalar))).run before := by
  by_cases handle : owner.identity.handle = selected
  · obtain ⟨started, built, tagged⟩ := RegistrationNativeIdentitySigningRole.initial
      (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)))
    by_cases message : target = PqxdhRefinement.absBytes started.message.one_time_key
    · exact RegistrationNativeIdentityCensorRepeatedStopCut.paired setup checks representation created selected index owner placeholder reserve
        scalar started built before seed handle (held.trans (congrArg some message)) (sourceTarget.trans (congrArg some message)) found
    · rw [RegistrationNativeIdentityCensorOtherMessageSource.bundled setup checks representation created selected index owner placeholder writer
        target targetRole scalar started built tagged message before ⟨held, inactive⟩]
  · rw [RegistrationNativeIdentityCensorOtherOwnerSource.bundled setup checks representation created selected index owner placeholder writer
      target handle scalar before ⟨held, inactive⟩]

/-- The same exhaustive captured-body cases retain the ordinary honest source marginal on the canonical side after selection. -/
theorem body_original (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (scalar : PqxdhJointGapDh.ScalarBytes)
    (target : Pqxdh.Bytes) (targetRole : RegistrationNativeIdentitySigningRole.oneTime target = true)
    (before : FullState) (seed : PqxdhJointIdentity.IdentitySeed)
    (held : before.1.2.target = some target) (sourceTarget : before.2.target = some target)
    (inactive : before.1.2.active = false) (found : before.2.pool.seeds[selected]? = some seed) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$> (source(false, body(owner, scalar))).run before =
      (RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (body(owner, scalar))).run
        (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  by_cases handle : owner.identity.handle = selected
  · obtain ⟨started, built, tagged⟩ := RegistrationNativeIdentitySigningRole.initial
      (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)))
    by_cases message : target = PqxdhRefinement.absBytes started.message.one_time_key
    · exact RegistrationNativeIdentityCensorRealBundleSource.repeated setup checks representation created selected index owner placeholder reserve
        scalar started built before seed handle (held.trans (congrArg some message)) (sourceTarget.trans (congrArg some message)) found
    · exact RegistrationNativeIdentityCensorGenuineBundleOriginal.message setup checks representation created selected index owner placeholder reserve
        false target targetRole scalar started built tagged message before ⟨held, inactive⟩
  · exact RegistrationNativeIdentityCensorGenuineBundleOriginal.other setup checks representation created selected index owner placeholder reserve
      false target handle scalar before ⟨held, inactive⟩


/-- The actual outer lookup and fresh/supplied sampler retain the same public cut after target selection, including absent owners and invalid phases. -/
theorem bundle (target : Pqxdh.Bytes) (targetRole : RegistrationNativeIdentitySigningRole.oneTime target = true)
    (before : FullState) (seed : PqxdhJointIdentity.IdentitySeed)
    (held : before.1.2.target = some target) (sourceTarget : before.2.target = some target)
    (inactive : before.1.2.active = false) (found : before.2.pool.seeds[selected]? = some seed) :
    cut placeholder <$> (source(false, Main (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer))).run before =
      cut placeholder <$> (source(true, Main (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer))).run before := by
  rw [RegistrationNativeIdentityCensorBundleDispatchSource.bundle, RegistrationNativeIdentityCensorBundleDispatchSource.bundle]
  cases ownerLookup : before.1.1.1.beacons[index]? with
  | none => rfl
  | some owner =>
    dsimp only
    rw [RegistrationNativeIdentityCensorBundleDispatchSource.start, RegistrationNativeIdentityCensorBundleDispatchSource.start]
    cases phase : owner.phase with
    | fresh =>
      simp only [map_bind]
      rw [RegistrationNativeIdentityCensorSampleSource.paired setup checks representation created selected placeholder PqxdhJointGapDh.sampleScalar before]
      apply bind_congr_of_forall_mem_support
      intro sampled reached
      have kept := RegistrationNativeIdentityCensorSampleSource.frame setup checks representation created selected placeholder true
        PqxdhJointGapDh.sampleScalar before sampled reached
      have keptTarget := congrArg (fun value => value.1.target) kept
      have keptActive := congrArg (fun value => value.1.active) kept
      have targetEq := congrArg (fun value => value.2.target) kept
      have seedsEq := congrArg (fun value => value.2.pool.seeds) kept
      exact body setup checks representation created selected index placeholder reserve owner sampled.1 target targetRole sampled.2 seed
        (keptTarget.trans held) (targetEq.trans sourceTarget) (keptActive.trans inactive) ((congrArg (fun seeds => seeds[selected]?) seedsEq).trans found)
    | freshWithCoins scalar =>
      exact body setup checks representation created selected index placeholder reserve owner scalar target targetRole before seed held sourceTarget inactive found
    | initSent pending scalar | established completed | aborted aborted => rfl

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

/-- After selection, the complete canonical outer bundle has the ordinary source marginal, with the actual owner lookup and sampled prefix retained. -/
theorem bundle_original (target : Pqxdh.Bytes) (targetRole : RegistrationNativeIdentitySigningRole.oneTime target = true)
    (before : FullState) (seed : PqxdhJointIdentity.IdentitySeed)
    (held : before.1.2.target = some target) (sourceTarget : before.2.target = some target)
    (inactive : before.1.2.active = false) (found : before.2.pool.seeds[selected]? = some seed) :
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
      exact body_original setup checks representation created selected index placeholder reserve owner sampled.1 target targetRole sampled.2 seed
        (keptTarget.trans held) (targetEq.trans sourceTarget) (keptActive.trans inactive) ((congrArg (fun seeds => seeds[selected]?) seedsEq).trans found)
    | freshWithCoins scalar =>
      exact body_original setup checks representation created selected index placeholder reserve owner scalar target targetRole before seed held sourceTarget inactive found
    | initSent pending scalar | established completed | aborted aborted => rfl


/-- This is exactly the public bundle observer on the literal typed byte reply. -/
def replyCut (placeholder : Ed25519Signature)
    (result : RustM (Option Pqxdh.Bytes) × FullState) : Option (RustM (Option Pqxdh.Bytes) × FullState) :=
  if result.2.1.2.active && (RegistrationNativeRawAdapter.resultOption result.1).isSome then none
  else some (result.1, RegistrationNativeIdentityCensorOutgoingView.view placeholder result.2)

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


/-- The actual typed bundle route includes the literal Vec-to-public-byte conversion before the existing public stop. -/
theorem callback (target : Pqxdh.Bytes) (targetRole : RegistrationNativeIdentitySigningRole.oneTime target = true)
    (before : FullState) (seed : PqxdhJointIdentity.IdentitySeed)
    (held : before.1.2.target = some target) (sourceTarget : before.2.target = some target)
    (inactive : before.1.2.active = false) (found : before.2.pool.seeds[selected]? = some seed) :
    replyCut placeholder <$> (source(false, RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index)).run before =
      replyCut placeholder <$> (source(true, RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index)).run before := by
  simp only [RegistrationNativePlatformIdentityCtxLifecycle.bundle, source_map, StateT.run_map, Functor.map_map]
  exact bundle setup checks representation created selected index placeholder reserve target targetRole before seed held sourceTarget inactive found

/-- The actual typed byte conversion also retains the honest canonical source marginal after selection. -/
theorem callback_original (target : Pqxdh.Bytes) (targetRole : RegistrationNativeIdentitySigningRole.oneTime target = true)
    (before : FullState) (seed : PqxdhJointIdentity.IdentitySeed)
    (held : before.1.2.target = some target) (sourceTarget : before.2.target = some target)
    (inactive : before.1.2.active = false) (found : before.2.pool.seeds[selected]? = some seed) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
      (source(false, RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index)).run before =
      (RegistrationNativePlatformIdentityCtxMain.interpret setup.joint
        (RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index)).run
          (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  have base := bundle_original setup checks representation created selected index placeholder reserve target targetRole before seed held sourceTarget inactive found
  have mapped := congrArg (fun distribution => Prod.map RegistrationNativePlatformIdentityNativeBundle.reply id <$> distribution) base
  simpa only [RegistrationNativePlatformIdentityCtxLifecycle.bundle, source_map, original_map, StateT.run_map,
    Functor.map_map, Prod.map_def, id_eq] using mapped


private theorem replyCut_view (result : RustM (Option Pqxdh.Bytes) × FullState) :
    replyCut placeholder (Prod.map id (RegistrationNativeIdentityCensorOutgoingView.view placeholder) result) =
      replyCut placeholder result := by
  change (if result.2.1.2.active && (RegistrationNativeRawAdapter.resultOption result.1).isSome then none
    else some (result.1, RegistrationNativeIdentityCensorOutgoingView.view placeholder
      (RegistrationNativeIdentityCensorOutgoingView.view placeholder result.2))) = _
  rw [RegistrationNativeIdentityCensorOutgoingView.view_idempotent]
  rfl

private theorem callback_view (censored : Bool) (before : FullState) :
    replyCut placeholder <$> (source(censored, RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index)).run before =
      replyCut placeholder <$> (source(censored, RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index)).run
        (RegistrationNativeIdentityCensorOutgoingView.view placeholder before) := by
  have law := RegistrationNativePlatformIdentityCtxTypedJointView.compose_stable (n := n) (source := mlSource) placeholder
    (RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index)
    (RegistrationNativePlatformIdentityCtxHistoryView.bundle_stable placeholder setup checks representation created writer index)
    (RegistrationNativePlatformIdentityCtxReceiptView.bundle_stable setup checks representation created writer index)
  have framed := RegistrationNativeIdentityCensorOutgoingView.interpreted setup.joint selected placeholder censored _ law before
  have compared := congrArg (fun distribution => replyCut placeholder <$> distribution) framed
  simpa only [Functor.map_map, Function.comp_def, replyCut_view] using compared

/-- Arbitrary previous canonical/placeholder history slots and compact ML receipts suffice for the literal selected-source bundle cut. Current replies, full private physical state and P are retained. -/
theorem paired (target : Pqxdh.Bytes) (targetRole : RegistrationNativeIdentitySigningRole.oneTime target = true)
    (left right : FullState) (seed : PqxdhJointIdentity.IdentitySeed)
    (same : RegistrationNativeIdentityCensorOutgoingView.view placeholder left = RegistrationNativeIdentityCensorOutgoingView.view placeholder right)
    (held : left.1.2.target = some target) (sourceTarget : left.2.target = some target)
    (inactive : left.1.2.active = false) (found : left.2.pool.seeds[selected]? = some seed) :
    replyCut placeholder <$> (source(false, RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index)).run left =
      replyCut placeholder <$> (source(true, RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index)).run right := by
  rw [callback_view setup checks representation created selected index placeholder reserve false left,
    callback_view setup checks representation created selected index placeholder reserve true right, ← same]
  exact callback setup checks representation created selected index placeholder reserve target targetRole
    (RegistrationNativeIdentityCensorOutgoingView.view placeholder left) seed held sourceTarget inactive found

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPostselectionBundleCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPostselectionBundleCut.body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPostselectionBundleCut.body

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPostselectionBundleCut.body_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPostselectionBundleCut.body_original

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPostselectionBundleCut.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPostselectionBundleCut.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPostselectionBundleCut.bundle_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPostselectionBundleCut.bundle_original

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPostselectionBundleCut.callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPostselectionBundleCut.callback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPostselectionBundleCut.callback_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPostselectionBundleCut.callback_original

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPostselectionBundleCut.paired' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPostselectionBundleCut.paired
