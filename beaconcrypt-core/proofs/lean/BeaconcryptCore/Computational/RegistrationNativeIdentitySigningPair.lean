-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityReadyFailure
import BeaconcryptCore.Refinement.RegistrationSigningContinuations

/-! The real/censored Init continuations differ in only the attached one-time field. Once the shared hash reply is fixed, the source ML request is identical. For every actual optional ML reply, the source continuation's failed-publication observation and complete external state agree, using the concrete6757 writer. No canonical signature or full raw-receipt equality is assumed. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySigningPair
open BeaconcryptCore.Refinement
open RegistrationNativeSourceWriterFailureView (writer)
variable {E Platform : Type}

def stripState (before : registration.BeaconInitState) : registration.BeaconInitState :=
  {before with one_time_key := Std.Array.repeat 98#usize 0#u8}
def strip (before : registration.BeaconMldsaSigning) : registration.BeaconMldsaSigning :=
  {before with state := stripState before.state}
def Same (left right : registration.BeaconMldsaSigning) : Prop := strip left = strip right

private theorem control (left right : registration.BeaconMldsaSigning) (same : Same left right) :
    left.state.original_control = right.state.original_control :=
  congrArg (fun pending => pending.state.original_control) same

/-- Source request construction never reads the attached one-time signature once the common transcript digest has produced its input. -/
theorem request (left right : registration.BeaconMldsaSigning) (same : Same left right) :
    left.request = right.request := by
  calc
    _ = (strip left).request := rfl
    _ = (strip right).request := congrArg registration.BeaconMldsaSigning.request same
    _ = _ := rfl

noncomputable def tail (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (other : RegistrationSerializerReachableSource.OtherBranches) (pending : registration.BeaconMldsaSigning)
    (signature : RegistrationSigningShared.SignReply) :
    StateT Platform ProbComp (RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) :=
  RegistrationNativePlatformBeaconPublication.continueWith (pending.resume signature) fun effect =>
    match effect with
    | .Rejected previous => pure (.ok (.Err previous))
    | .Ready selected => RegistrationNativePlatformBeaconPublication.ready (writer reserve other) selected
    | _ => pure .div

/-- This tail is the literal continuation of the original effectful source controller after its actual ML call. -/
theorem factor (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (other : RegistrationSerializerReachableSource.OtherBranches)
    (implementation : QueryImpl RegistrationBeaconInitExecutor.Spec (StateT Platform ProbComp))
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest) (pending : registration.BeaconMldsaSigning) :
    RegistrationNativePlatformBeaconPublication.fromSigning implementation (writer reserve other) payload digest pending =
      (RegistrationNativePlatformBeaconPublication.continueWith pending.request fun query => do
        let signature ← implementation (.inl (.sign query payload digest))
        tail reserve other pending signature) := rfl

private theorem classify (pending : registration.BeaconMldsaSigning) (signature : Slice U8) :
    (∃ previous, pending.resume (.Some signature) = .ok (.Rejected previous) ∧
      previous = pending.state.original_control ∧ signature.val.length ≠ 3309) ∨
    (∃ ready, pending.resume (.Some signature) = .ok (.Ready ready) ∧
      signature.val.length = 3309 ∧ ready.state = pending.state) := by
  obtain ⟨effect, resumed, facts⟩ := RegistrationSigningContinuations.beacon_mldsa_signature_exact pending signature
  cases effect <;> simp only [RegistrationSigningContinuations.signatureResult] at facts
  case Rejected previous => exact Or.inl ⟨previous, resumed, facts.1, facts.2⟩
  case Ready ready => exact Or.inr ⟨ready, resumed, facts.1, facts.2.1⟩

/-- Every real optional ML reply gives the same concrete failed-control/full-P result for the paired source continuations, including signature-width rejection. -/
theorem failure (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (other : RegistrationSerializerReachableSource.OtherBranches) (left right : registration.BeaconMldsaSigning)
    (same : Same left right) (signature : RegistrationSigningShared.SignReply) (before : Platform) :
    Prod.map RegistrationNativeIdentityReadyFailure.observe id <$> (tail reserve other left signature).run before =
      Prod.map RegistrationNativeIdentityReadyFailure.observe id <$> (tail reserve other right signature).run before := by
  have controls := control left right same
  cases signature with
  | none =>
    simp only [tail, registration.BeaconMldsaSigning.resume, RegistrationNativePlatformBeaconPublication.continueWith, controls]
  | some signature =>
    rcases classify left signature with ⟨previousLeft, resumedLeft, controlLeft, rejectedLeft⟩ | ⟨readyLeft, resumedLeft, acceptedLeft, stateLeft⟩
    · rcases classify right signature with ⟨previousRight, resumedRight, controlRight, _rejectedRight⟩ | ⟨readyRight, _resumedRight, acceptedRight, _stateRight⟩
      · simp only [tail, resumedLeft, resumedRight, RegistrationNativePlatformBeaconPublication.continueWith,
          controlLeft, controlRight, controls]
      · exact False.elim (rejectedLeft acceptedRight)
    · rcases classify right signature with ⟨previousRight, _resumedRight, _controlRight, rejectedRight⟩ | ⟨readyRight, resumedRight, _acceptedRight, stateRight⟩
      · exact False.elim (rejectedRight acceptedLeft)
      · simp only [tail, resumedLeft, resumedRight, RegistrationNativePlatformBeaconPublication.continueWith]
        apply RegistrationNativeIdentityReadyFailure.independent reserve other readyLeft readyRight
        exact (congrArg registration.BeaconInitState.original_control stateLeft).trans
          (controls.trans (congrArg registration.BeaconInitState.original_control stateRight).symm)

end BeaconcryptCore.Computational.RegistrationNativeIdentitySigningPair
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySigningPair.request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySigningPair.request
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySigningPair.factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySigningPair.factor
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySigningPair.failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySigningPair.failure
