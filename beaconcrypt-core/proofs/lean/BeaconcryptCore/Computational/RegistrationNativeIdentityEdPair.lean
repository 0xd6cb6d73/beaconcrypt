-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityEdProgress
import BeaconcryptCore.Computational.RegistrationNativeIdentityHashPair

/-! The literal source Ed continuations preserve a paired state differing only in its attached one-time field. The selected one-time reply may differ; subsequent equal PQ replies restore the pair needed by the common request-hash continuation. All copied bytes and source stages are derived from the actual resume bodies. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityEdPair
open BeaconcryptCore.Refinement
open RegistrationNativeIdentitySigningPair (stripState)
open RegistrationSigning (replyTailMatches)

def Same (left right : registration.BeaconEd25519Signing) : Prop :=
  stripState left.state = stripState right.state ∧ left.stage = right.stage

theorem request (left right : registration.BeaconEd25519Signing) (same : Same left right) :
    left.request = right.request := by
  have state := same.1
  have stage := same.2
  calc
    _ = ({left with state := stripState left.state} : registration.BeaconEd25519Signing).request := by
      cases selected : left.stage <;> simp only [registration.BeaconEd25519Signing.request, selected, stripState]
    _ = ({right with state := stripState right.state} : registration.BeaconEd25519Signing).request := by
      simp only [state, stage]
    _ = _ := by cases selected : right.stage <;> simp only [registration.BeaconEd25519Signing.request, selected, stripState]

theorem one_time (before : registration.BeaconEd25519Signing) (left right : Slice U8)
    (stage : before.stage = .OneTimeKey)
    (matchingLeft : replyTailMatches before (.Some left)) (matchingRight : replyTailMatches before (.Some right))
    (widthLeft : left.val.length = 98) (widthRight : right.val.length = 98) :
    ∃ nextLeft nextRight,
      before.resume (.Some left) = .ok (.Ed25519SigningRequested nextLeft) ∧
      before.resume (.Some right) = .ok (.Ed25519SigningRequested nextRight) ∧
      nextLeft.stage = .PqKey ∧ Same nextLeft nextRight := by
  obtain ⟨nextLeft, runLeft, stageLeft, _bytesLeft, restoreLeft⟩ :=
    RegistrationNativeIdentityEdProgress.one_time before left stage matchingLeft widthLeft
  obtain ⟨nextRight, runRight, stageRight, _bytesRight, restoreRight⟩ :=
    RegistrationNativeIdentityEdProgress.one_time before right stage matchingRight widthRight
  refine ⟨nextLeft, nextRight, runLeft, runRight, stageLeft, ?_, stageLeft.trans stageRight.symm⟩
  have pairedLeft := congrArg stripState restoreLeft
  have pairedRight := congrArg stripState restoreRight
  simpa only [stripState] using pairedLeft.trans pairedRight.symm

theorem pq_key (left right : registration.BeaconEd25519Signing) (same : Same left right) (signed : Slice U8)
    (stage : left.stage = .PqKey)
    (matchingLeft : replyTailMatches left (.Some signed)) (matchingRight : replyTailMatches right (.Some signed))
    (width : signed.val.length = 1249) :
    ∃ nextLeft nextRight,
      left.resume (.Some signed) = .ok (.HashRequested nextLeft) ∧
      right.resume (.Some signed) = .ok (.HashRequested nextRight) ∧
      stripState nextLeft.state = stripState nextRight.state := by
  obtain ⟨nextLeft, runLeft, bytesLeft, restoreLeft⟩ :=
    RegistrationNativeIdentityEdProgress.pq_key left signed stage matchingLeft width
  obtain ⟨nextRight, runRight, bytesRight, restoreRight⟩ :=
    RegistrationNativeIdentityEdProgress.pq_key right signed (same.2.symm.trans stage) matchingRight width
  have pqSame : nextLeft.state.pq_key = nextRight.state.pq_key := Subtype.ext (bytesLeft.trans bytesRight.symm)
  have keptLeft := congrArg (fun state => stripState {state with pq_key := nextLeft.state.pq_key}) restoreLeft
  have keptRight := congrArg (fun state => stripState {state with pq_key := nextRight.state.pq_key}) restoreRight
  refine ⟨nextLeft, nextRight, runLeft, runRight, ?_⟩
  have keptLeft' : stripState nextLeft.state = {stripState left.state with pq_key := nextLeft.state.pq_key} := by
    simpa only [stripState] using keptLeft
  have keptRight' : stripState nextRight.state = {stripState right.state with pq_key := nextRight.state.pq_key} := by
    simpa only [stripState] using keptRight
  calc
    _ = {stripState left.state with pq_key := nextLeft.state.pq_key} := keptLeft'
    _ = {stripState right.state with pq_key := nextRight.state.pq_key} := by rw [same.1, pqSame]
    _ = _ := keptRight'.symm

end BeaconcryptCore.Computational.RegistrationNativeIdentityEdPair

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityEdPair.request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityEdPair.request

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityEdPair.one_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityEdPair.one_time

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityEdPair.pq_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityEdPair.pq_key
