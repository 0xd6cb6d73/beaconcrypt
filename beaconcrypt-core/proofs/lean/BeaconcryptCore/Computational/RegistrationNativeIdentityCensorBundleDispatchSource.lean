-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleStopCut

/-! The literal outer bundle lookup and fresh/supplied scalar dispatch close through the same private source interpretation. Every nontrivial supported outcome has an actual captured owner and an actual supplied or sampled scalar before the original bundled body. No generated-row, freshness or success condition is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleDispatchSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
local notation "FullState" => Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)
local notation "Outcome" => RustM (Option (alloc.vec.Vec U8)) × FullState

variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (selected index : Nat) (placeholder : Ed25519Signature)
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "source(" censored "," work ")" => interpret setup.joint selected placeholder censored work
local notation "body(" owner "," scalar ")" => Main (RegistrationNativePlatformIdentityBundle.bundled setup index owner scalar writer)
local notation "draw" => Main (RegistrationNativePlatformIdentityProgram.native
  (RegistrationNativeIdentityFrontend.sample (n := n) (KemSK := KemSK) (Auxiliary := RegistrationServerRoleBackend.State)
    (source := mlSource) PqxdhJointGapDh.sampleScalar))

/-- Fresh owners use the actual native scalar sampler; supplied material is reused literally, while all other phases reject without a source query. -/
theorem start (censored : Bool) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (before : FullState) :
    (source(censored, Main (RegistrationNativePlatformIdentityBundleRun.start setup index owner writer))).run before =
      match owner.phase with
      | .fresh => do
          let sampled ← (source(censored, draw)).run before
          (source(censored, body(owner, sampled.1))).run sampled.2
      | .freshWithCoins scalar => (source(censored, body(owner, scalar))).run before
      | _ => pure (.ok none, before) := by
  cases phase : owner.phase with
  | fresh =>
    simp only [RegistrationNativePlatformIdentityBundleRun.start, phase]
    rw [RegistrationNativePlatformIdentityCtxOutgoingFold.bind_source setup checks representation created _ _
      (fun scalar => RegistrationNativePlatformIdentityCtxBundleScope.bundled setup index owner scalar writer),
      RegistrationNativeIdentityCensorSourceFold.bind_source, StateT.run_bind]
  | freshWithCoins scalar =>
    simp only [RegistrationNativePlatformIdentityBundleRun.start, phase, pure_bind]
  | initSent pending scalar | established completed | aborted aborted =>
    simp only [RegistrationNativePlatformIdentityBundleRun.start, phase,
      RegistrationNativePlatformIdentityCtxOutgoingFold.pure_source,
      RegistrationNativeIdentityCensorSourceFold.pure_source, StateT.run_pure]

private theorem get_run (censored : Bool) (before : FullState) :
    (source(censored, (fun state => pure (state.1.beacons, state) :
      RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource (RegistrationNativeIdentityFrontend.State mlSource)))).run before =
      pure (before.1.1.1.beacons, before) := by
  simp only [interpret, StateT.run, simulateQ_pure]
  change (do
    let result ← (simulateQ (if censored then RegistrationNativeIdentityCensorSource.censored setup.joint selected placeholder
      else RegistrationNativeIdentityCensorSource.implementation setup.joint selected)
      (pure ((before.1.1.1.beacons, before.1.1), before.1.2))).run before.2
    pure (result.1.1.1, ((result.1.1.2, result.1.2), result.2))) = _
  simp only [simulateQ_pure, StateT.run_pure, pure_bind]

/-- The owner supplied to the source controller is exactly the row returned by the literal current Main lookup. -/
theorem bundle (censored : Bool) (before : FullState) :
    (source(censored, Main (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer))).run before =
      match before.1.1.1.beacons[index]? with
      | none => pure (.ok none, before)
      | some owner => (source(censored, Main (RegistrationNativePlatformIdentityBundleRun.start setup index owner writer))).run before := by
  rw [RegistrationNativePlatformIdentityCtxBundleScope.bundle_fold,
    RegistrationNativeIdentityCensorSourceFold.bind_source, StateT.run_bind, get_run, pure_bind]
  cases before.1.1.1.beacons[index]? with
  | none => rw [RegistrationNativeIdentityCensorSourceFold.pure_source]; rfl
  | some owner => rfl

/-- Actual scalar provenance in the same source run, including the native sampler's complete reached state. -/
def Picked (censored : Bool) (owner : RegistrationNativeIdentityFrontend.Owner mlSource)
    (scalar : PqxdhJointGapDh.ScalarBytes) (before middle : FullState) : Prop :=
  (owner.phase = .fresh ∧ (scalar, middle) ∈ support ((source(censored, draw)).run before)) ∨
    (owner.phase = .freshWithCoins scalar ∧ middle = before)

/-- Every supported outer outcome either is the literal no-op rejection or reaches an original bundled body using the actual current owner and actual supplied/sampled scalar. -/
theorem cut (censored : Bool) (before : FullState) (result : Outcome)
    (possible : result ∈ support ((source(censored, Main (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer))).run before)) :
    result = (.ok none, before) ∨
      ∃ owner scalar middle, before.1.1.1.beacons[index]? = some owner ∧
        Picked setup checks representation created selected placeholder censored owner scalar before middle ∧
        result ∈ support ((source(censored, body(owner, scalar))).run middle) := by
  rw [bundle] at possible
  cases found : before.1.1.1.beacons[index]? with
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

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleDispatchSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleDispatchSource.start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleDispatchSource.start
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleDispatchSource.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleDispatchSource.bundle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleDispatchSource.cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleDispatchSource.cut
