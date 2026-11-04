-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOutgoingHashBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublicationHashBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleRun
/-! Actual dynamic-writer owner lookup, optional scalar sampling and publication have two shared hash calls. Every failed source prefix and P writer result remains in the literal controller; no published-bundle assumption or whole-handler bill is required. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleHashBounds
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformIdentitySourceHashBounds
variable {n : Nat} {I KemSK Auxiliary Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

/-- Each literal publication callback has exactly its explicit source hash charge. -/
theorem callback_bound (query : (RegistrationNativePlatformWriter.Spec E).Domain) :
    Bounded (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := Auxiliary) setup index owner writer query)
      (if RegistrationNativePlatformBeaconPublicationHashBounds.IsHash (E := E) query then 1 else 0) := by
  cases query with
  | inl query =>
    apply native_bound
    have actual := RegistrationNativePlatformIdentityOutgoingHashBounds.outgoing_bound (n := n) (Auxiliary := Auxiliary) setup index owner query
    cases query with
    | inl query => cases query <;> exact actual
    | inr query => exact actual
  | inr query => exact external_bound (writer query)

private theorem next_bound (oneTime : PqxdhJointGapDh.ScalarBytes) (reply : RegistrationNativePlatformIdentityBundle.Reply) :
    Bounded (RegistrationNativePlatformIdentityBundle.next (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) index owner oneTime reply) 0 := by
  cases reply with
  | fail error | div => exact pure_bound _ _
  | ok reply => cases reply with
    | Err error => exact pure_bound _ _
    | Ok published =>
      unfold RegistrationNativePlatformIdentityBundle.next
      apply bind_bound _ _ 0 0
      · apply native_bound
        exact RegistrationNativePlatformIdentityFrontendHashBounds.modify_bound _
      · intro _
        apply bind_bound _ _ 0 0
        · apply native_bound
          exact RegistrationNativePlatformIdentityFrontendHashBounds.effect_bound _
        · intro _
          exact pure_bound _ _

/-- The actual source publication and every reached lifecycle continuation use at most two shared hashes. -/
theorem bundled_bound (oneTime : PqxdhJointGapDh.ScalarBytes) :
    Bounded (RegistrationNativePlatformIdentityBundle.bundled (n := n) (Auxiliary := Auxiliary) setup index owner oneTime writer) 2 := by
  unfold RegistrationNativePlatformIdentityBundle.bundled
  apply bind_bound _ _ 2 0
  · exact program_bound (RegistrationNativePlatformBeaconPublicationHashBounds.IsHash (E := E)) _
      (callback_bound setup index owner writer) _ 2
      (RegistrationNativePlatformBeaconPublicationHashBounds.begin_bound _ _ _ _ _)
  · intro reply
    exact next_bound index owner oneTime reply

/-- Supplied or genuinely sampled one-time scalars retain the same two-hash publication cap. -/
theorem start_bound :
    Bounded (RegistrationNativePlatformIdentityBundleRun.start (n := n) (Auxiliary := Auxiliary) setup index owner writer) 2 := by
  cases phase : owner.phase with
  | fresh =>
      simp only [RegistrationNativePlatformIdentityBundleRun.start, phase]
      exact bind_bound _ _ 0 2 (native_bound _ _ (RegistrationNativePlatformIdentityFrontendHashBounds.sample_bound _))
        (fun scalar => bundled_bound setup index owner writer scalar)
  | freshWithCoins scalar =>
      simpa only [RegistrationNativePlatformIdentityBundleRun.start, phase, pure_bind] using
        bundled_bound (n := n) (Auxiliary := Auxiliary) setup index owner writer scalar
  | initSent pending scalar | established completed | aborted aborted =>
      simp only [RegistrationNativePlatformIdentityBundleRun.start, phase]
      exact pure_bound _ _

/-- Literal roster lookup and all dynamic writer failures preserve the actual two-hash bundle allowance. -/
theorem bundle_bound :
    Bounded (RegistrationNativePlatformIdentityBundleRun.bundle (n := n) (Auxiliary := Auxiliary) (source := source) setup index writer) 2 := by
  unfold RegistrationNativePlatformIdentityBundleRun.bundle
  apply bind_bound _ _ 0 2 get_bound
  intro owners
  cases owners[index]? with
  | none => exact pure_bound _ _
  | some owner => exact start_bound setup index owner writer
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleHashBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleHashBounds.callback_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleHashBounds.callback_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleHashBounds.bundled_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleHashBounds.bundled_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleHashBounds.start_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleHashBounds.start_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleHashBounds.bundle_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleHashBounds.bundle_bound
