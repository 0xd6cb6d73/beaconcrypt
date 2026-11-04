-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleKeyScope

/-! The literal outer bundle lookup and fresh/supplied scalar dispatch close through the same private source interpretation. Every nontrivial supported outcome has an actual captured owner and an actual supplied or sampled scalar before the original bundled body. No generated-row, freshness or success condition is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleDispatch
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformIdentityCtxMain (Full interpret)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
local notation "FullState" => Full n KemSK Platform mlSource
local notation "Outcome" => RustM (Option (alloc.vec.Vec U8)) × FullState

variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (index : Nat)
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "source(" work ")" => interpret setup.joint work
local notation "body(" owner "," scalar ")" => Main (RegistrationNativePlatformIdentityBundle.bundled setup index owner scalar writer)
local notation "draw" => Main (RegistrationNativePlatformIdentityProgram.native
  (RegistrationNativeIdentityFrontend.sample (n := n) (KemSK := KemSK) (Auxiliary := RegistrationServerRoleBackend.State)
    (source := mlSource) PqxdhJointGapDh.sampleScalar))

/-- Fresh owners use the actual native scalar sampler; supplied material is reused literally, while all other phases reject without a source query. -/
theorem start (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (before : FullState) :
    (source(Main (RegistrationNativePlatformIdentityBundleRun.start setup index owner writer))).run before =
      match owner.phase with
      | .fresh => do
          let sampled ← (source(draw)).run before
          (source(body(owner, sampled.1))).run sampled.2
      | .freshWithCoins scalar => (source(body(owner, scalar))).run before
      | _ => pure (.ok none, before) := by
  cases phase : owner.phase with
  | fresh =>
    simp only [RegistrationNativePlatformIdentityBundleRun.start, phase]
    rw [RegistrationNativePlatformIdentityCtxOutgoingFold.bind_source setup checks representation created _ _
      (fun scalar => RegistrationNativePlatformIdentityCtxBundleScope.bundled setup index owner scalar writer),
      RegistrationNativePlatformIdentityCtxOrdinary.interpret_bind, StateT.run_bind]
  | freshWithCoins scalar =>
    simp only [RegistrationNativePlatformIdentityBundleRun.start, phase, pure_bind]
  | initSent pending scalar | established completed | aborted aborted =>
    simp only [RegistrationNativePlatformIdentityBundleRun.start, phase,
      RegistrationNativePlatformIdentityCtxOutgoingFold.pure_source,
      RegistrationNativePlatformIdentityCtxOrdinary.interpret_pure, StateT.run_pure]

private theorem get_run (before : FullState) :
    (source((fun state => pure (state.1.beacons, state) :
      RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource (RegistrationNativeIdentityFrontend.State mlSource)))).run before =
      pure (before.1.1.beacons, before) := by
  simp only [interpret, StateT.run, simulateQ_pure]
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (pure ((before.1.1.beacons, before.1), before.2) : ProbComp _) = _
  rw [map_pure]

/-- The owner supplied to the source controller is exactly the row returned by the literal current Main lookup. -/
theorem bundle (before : FullState) :
    (source(Main (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer))).run before =
      match before.1.1.beacons[index]? with
      | none => pure (.ok none, before)
      | some owner => (source(Main (RegistrationNativePlatformIdentityBundleRun.start setup index owner writer))).run before := by
  rw [RegistrationNativePlatformIdentityCtxBundleScope.bundle_fold,
    RegistrationNativePlatformIdentityCtxOrdinary.interpret_bind, StateT.run_bind, get_run, pure_bind]
  cases before.1.1.beacons[index]? with
  | none => rw [RegistrationNativePlatformIdentityCtxOrdinary.interpret_pure]; rfl
  | some owner => rfl

/-- Actual scalar provenance in the same source run, including the native sampler's complete reached state. -/
def Picked (owner : RegistrationNativeIdentityFrontend.Owner mlSource)
    (scalar : PqxdhJointGapDh.ScalarBytes) (before middle : FullState) : Prop :=
  (owner.phase = .fresh ∧ (scalar, middle) ∈ support ((source(draw)).run before)) ∨
    (owner.phase = .freshWithCoins scalar ∧ middle = before)

/-- Every supported outer outcome either is the literal no-op rejection or reaches an original bundled body using the actual current owner and actual supplied/sampled scalar. -/
theorem cut (before : FullState) (result : Outcome)
    (possible : result ∈ support ((source(Main (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer))).run before)) :
    result = (.ok none, before) ∨
      ∃ owner scalar middle, before.1.1.beacons[index]? = some owner ∧
        Picked setup checks representation created owner scalar before middle ∧
        result ∈ support ((source(body(owner, scalar))).run middle) := by
  rw [bundle] at possible
  cases found : before.1.1.beacons[index]? with
  | none =>
    simp only [found, mem_support_pure_iff] at possible
    exact Or.inl possible
  | some owner =>
    simp only [found] at possible
    rw [start] at possible
    cases phase : owner.phase with
    | fresh =>
      simp only [phase, mem_support_bind_iff] at possible
      obtain ⟨sampled, drawn, continued⟩ := possible
      exact Or.inr ⟨owner, sampled.1, sampled.2, rfl, Or.inl ⟨phase, drawn⟩, continued⟩
    | freshWithCoins scalar =>
      simp only [phase] at possible
      exact Or.inr ⟨owner, scalar, before, rfl, Or.inr ⟨phase, rfl⟩, possible⟩
    | initSent pending scalar | established completed | aborted aborted =>
      simp only [phase, mem_support_pure_iff] at possible
      exact Or.inl possible

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleDispatch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleDispatch.start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleDispatch.start
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleDispatch.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleDispatch.bundle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleDispatch.cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleDispatch.cut
