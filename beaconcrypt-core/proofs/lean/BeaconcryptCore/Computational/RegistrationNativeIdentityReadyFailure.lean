-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSourceWriterFailureView
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication

/-! Failed concrete source Init publication retains the literal original Fresh control and full external poststate independently of all signature/field bytes. The actual source controller, fixed1490 reservation and generated Init serializer are used; no writer-purity or failure-independence premise is introduced. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityReadyFailure
open BeaconcryptCore.Refinement
open RegistrationNativeSourceWriterFailureView (writer)
variable {E Platform : Type}

def observe : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8)) → Option pqxdh.BeaconFresh
  | .ok (.Err previous) => some previous
  | _ => none

/-- The actual Ready/controller/serializer boundary reveals only reservation success; failure returns the same exact original Fresh state. -/
theorem source (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (other : RegistrationSerializerReachableSource.OtherBranches) (pending : registration.BeaconInitReady) (before : Platform) :
    Prod.map observe id <$>
      (RegistrationNativePlatformBeaconPublication.ready (writer reserve other) pending).run before =
      (fun result => ((match result.1 with | .Ok _ => none | .Err _ => some pending.state.original_control), result.2)) <$>
        (reserve 1490#usize).run before := by
  obtain ⟨view, message⟩ := BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconInitReady_message_total pending
  simp only [RegistrationNativePlatformBeaconPublication.ready, RegistrationNativePlatformBeaconPublication.continueWith,
    message, bind_pure_comp, writer,
    RegistrationNativeSourceWriterReadback.init_source, StateT.run_map, Functor.map_map]
  congr 1
  funext result
  cases result.1 <;> rfl

/-- Actual field/signature replacement cannot alter this failed-publication observation or the complete P transition. -/
theorem independent (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (other : RegistrationSerializerReachableSource.OtherBranches) (first second : registration.BeaconInitReady)
    (same : first.state.original_control = second.state.original_control) (before : Platform) :
    Prod.map observe id <$> (RegistrationNativePlatformBeaconPublication.ready (writer reserve other) first).run before =
      Prod.map observe id <$> (RegistrationNativePlatformBeaconPublication.ready (writer reserve other) second).run before := by
  rw [source, source, same]

end BeaconcryptCore.Computational.RegistrationNativeIdentityReadyFailure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReadyFailure.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReadyFailure.source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReadyFailure.independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReadyFailure.independent
