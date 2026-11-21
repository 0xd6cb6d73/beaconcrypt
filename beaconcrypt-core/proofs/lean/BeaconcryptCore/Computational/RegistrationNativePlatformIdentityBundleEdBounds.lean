-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOutgoingEdBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublicationEdBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleRun
/-! The actual dynamic-writer bundle has at most three indexed Ed attempts. Owner lookup, optional scalar sampling, publication failures and the complete mutable writer state remain in the literal source controller. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleEdBounds
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformIdentitySourceEdBounds
variable {n : Nat} {I KemSK Auxiliary Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

theorem callback_bound (query : (RegistrationNativePlatformWriter.Spec E).Domain) :
    Bounded (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := Auxiliary) setup index owner writer query)
      (if RegistrationNativePlatformBeaconPublicationEdBounds.IsSign (E := E) query then 1 else 0) := by
  cases query with
  | inl query =>
    apply native_bound
    have actual := RegistrationNativePlatformIdentityOutgoingEdBounds.outgoing_bound (n := n) (Auxiliary := Auxiliary) setup index owner query
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
        exact RegistrationNativePlatformIdentityFrontendEdBounds.modify_bound _
      · intro _
        apply bind_bound _ _ 0 0
        · apply native_bound
          exact RegistrationNativePlatformIdentityFrontendEdBounds.effect_bound _
        · intro _
          exact pure_bound _ _

theorem bundled_bound (oneTime : PqxdhJointGapDh.ScalarBytes) :
    Bounded (RegistrationNativePlatformIdentityBundle.bundled (n := n) (Auxiliary := Auxiliary) setup index owner oneTime writer) 3 := by
  unfold RegistrationNativePlatformIdentityBundle.bundled
  apply bind_bound _ _ 3 0
  · exact program_bound (RegistrationNativePlatformBeaconPublicationEdBounds.IsSign (E := E)) _
      (callback_bound setup index owner writer) _ 3
      (RegistrationNativePlatformBeaconPublicationEdBounds.begin_bound _ _ _ _)
  · intro reply
    exact next_bound index owner oneTime reply

theorem start_bound :
    Bounded (RegistrationNativePlatformIdentityBundleRun.start (n := n) (Auxiliary := Auxiliary) setup index owner writer) 3 := by
  cases phase : owner.phase with
  | fresh =>
      simp only [RegistrationNativePlatformIdentityBundleRun.start, phase]
      exact bind_bound _ _ 0 3 (native_bound _ _ (RegistrationNativePlatformIdentityFrontendEdBounds.sample_bound _))
        (fun scalar => bundled_bound setup index owner writer scalar)
  | freshWithCoins scalar =>
      simpa only [RegistrationNativePlatformIdentityBundleRun.start, phase, pure_bind] using
        bundled_bound (n := n) (Auxiliary := Auxiliary) setup index owner writer scalar
  | initSent pending scalar | established completed | aborted aborted =>
      simp only [RegistrationNativePlatformIdentityBundleRun.start, phase]
      exact pure_bound _ _

theorem bundle_bound :
    Bounded (RegistrationNativePlatformIdentityBundleRun.bundle (n := n) (Auxiliary := Auxiliary) (source := source) setup index writer) 3 := by
  unfold RegistrationNativePlatformIdentityBundleRun.bundle
  apply bind_bound _ _ 0 3 get_bound
  intro owners
  cases owners[index]? with
  | none => exact pure_bound _ _
  | some owner => exact start_bound setup index owner writer
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleEdBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleEdBounds.callback_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleEdBounds.callback_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleEdBounds.bundled_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleEdBounds.bundled_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleEdBounds.start_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleEdBounds.start_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleEdBounds.bundle_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleEdBounds.bundle_bound
