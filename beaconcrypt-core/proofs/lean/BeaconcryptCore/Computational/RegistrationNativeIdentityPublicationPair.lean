-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityHashRoute
import BeaconcryptCore.Computational.RegistrationNativeIdentityEdPair
import BeaconcryptCore.Computational.RegistrationNativeIdentityReadyFailure

/-! The actual Core three-Ed25519, hash and Ready suffix runs over one symbolic hash token. The sampler and concrete writer may share arbitrary mutable state; both sides retain that state through every optional signing, width and writer failure. The shared signature callback is unused by this Beacon suffix. This is the executable suffix coupling, not a whole native causal-event bound. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityPublicationPair
open BeaconcryptCore.Refinement
open RegistrationNativeIdentitySigningPair (stripState)
open RegistrationNativeSourceWriterFailureView (writer)
variable {E Platform : Type}

/-- Only this literal publication suffix routes its exact attached-signature Init hash to the internal token. The shared Server signing branch supplies no Beacon operation. -/
def callbacks (hash : Option Pqxdh.Bytes → StateT Platform ProbComp CtxRomAuth.CtxDigest)
    (_sign : registration.MldsaSigningRequest → StateT Platform ProbComp RegistrationSigningShared.SignReply)
    (ed : registration.Ed25519SigningRequest → StateT Platform ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl RegistrationBeaconInitExecutor.Spec (StateT Platform ProbComp)
  | .inl (.hash request) => hash (RegistrationNativeIdentityHashRoute.route (RegistrationInputs.hashBytes request))
  | .inl (.sign _ _ _) => pure .None
  | .inr request => ed request

/-- A single token answer drives both original hash continuations, including the same actual stateful signer and concrete source writer. -/
theorem hash (hash : Option Pqxdh.Bytes → StateT Platform ProbComp CtxRomAuth.CtxDigest)
    (sign : registration.MldsaSigningRequest → StateT Platform ProbComp RegistrationSigningShared.SignReply)
    (ed : registration.Ed25519SigningRequest → StateT Platform ProbComp RegistrationSigningShared.SignReply)
    (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (other : RegistrationSerializerReachableSource.OtherBranches) (left right : registration.BeaconInitHash)
    (same : RegistrationNativeIdentityHashPair.Same left right) (before : Platform) :
    Prod.map RegistrationNativeIdentityReadyFailure.observe id <$>
      (RegistrationNativePlatformBeaconPublication.fromHash (callbacks hash sign ed) (writer reserve other) left).run before =
    Prod.map RegistrationNativeIdentityReadyFailure.observe id <$>
      (RegistrationNativePlatformBeaconPublication.fromHash (callbacks hash sign ed) (writer reserve other) right).run before := by
  obtain ⟨requestLeft, requestedLeft, _bytesLeft, routeLeft⟩ := RegistrationNativeIdentityHashRoute.transcript left
  obtain ⟨requestRight, requestedRight, _bytesRight, routeRight⟩ := RegistrationNativeIdentityHashRoute.transcript right
  simp only [RegistrationNativePlatformBeaconPublication.fromHash, requestedLeft, requestedRight,
    RegistrationNativePlatformBeaconPublication.continueWith, callbacks, routeLeft, routeRight, StateT.run_bind, map_bind]
  apply bind_congr
  intro result
  obtain ⟨nextLeft, nextRight, resumedLeft, resumedRight, paired⟩ := RegistrationNativeIdentityHashPair.hash left right same
    (RegistrationAuthenticationShared.digestArray result.1)
  simp only [resumedLeft, resumedRight]
  exact RegistrationNativeIdentityReadyFailure.independent reserve other nextLeft nextRight paired result.2

private theorem pq_rejected (pending : registration.BeaconEd25519Signing) (reply : RegistrationSigningShared.SignReply)
    (stage : pending.stage = .PqKey)
    (invalid : ¬ ∃ signed, reply = .Some signed ∧ RegistrationSigning.replyTailMatches pending reply ∧ signed.val.length = 1249) :
    pending.resume reply = .ok (.Rejected pending.state.original_control) := by
  obtain ⟨effect, actual, facts⟩ := RegistrationSigning.ed_resume_refines pending reply
  cases effect <;> simp only [RegistrationSigning.EdReplyTransition, stage] at facts
  case Rejected previous => simpa only [facts] using actual
  case Ed25519SigningRequested next => exact False.elim facts.2
  case HashRequested next =>
    cases reply with
    | none => cases facts.1
    | some signed =>
      have bytes : next.state.pq_key.val = signed.val := facts.2.2.1
      have width : signed.val.length = 1249 := (congrArg List.length bytes).symm.trans next.state.pq_key.property
      exact False.elim (invalid ⟨signed, rfl, facts.1, width⟩)

/-- All possible actual PQ-signing replies, including missing, malformed-tail and wrong-width replies, preserve the paired failed-publication distribution. -/
theorem pq (hash : Option Pqxdh.Bytes → StateT Platform ProbComp CtxRomAuth.CtxDigest)
    (sign : registration.MldsaSigningRequest → StateT Platform ProbComp RegistrationSigningShared.SignReply)
    (ed : registration.Ed25519SigningRequest → StateT Platform ProbComp RegistrationSigningShared.SignReply)
    (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (other : RegistrationSerializerReachableSource.OtherBranches) (left right : registration.BeaconEd25519Signing)
    (same : RegistrationNativeIdentityEdPair.Same left right) (stage : left.stage = .PqKey) (before : Platform) :
    Prod.map RegistrationNativeIdentityReadyFailure.observe id <$>
      (RegistrationNativePlatformBeaconPublication.fromEd (callbacks hash sign ed) (writer reserve other) left).run before =
    Prod.map RegistrationNativeIdentityReadyFailure.observe id <$>
      (RegistrationNativePlatformBeaconPublication.fromEd (callbacks hash sign ed) (writer reserve other) right).run before := by
  obtain ⟨request, requestedLeft, _publicKey, _role, _message⟩ := RegistrationSigning.ed_request_exact left
  have requestedRight : right.request = .ok request := (RegistrationNativeIdentityEdPair.request left right same).symm.trans requestedLeft
  have stageRight : right.stage = .PqKey := same.2.symm.trans stage
  have started := congrArg registration.BeaconInitState.started same.1
  change left.state.started = right.state.started at started
  have controls := congrArg registration.BeaconInitState.original_control same.1
  change left.state.original_control = right.state.original_control at controls
  have matching (reply : RegistrationSigningShared.SignReply) :
      RegistrationSigning.replyTailMatches left reply ↔ RegistrationSigning.replyTailMatches right reply := by
    cases reply <;> simp only [RegistrationSigning.replyTailMatches, RegistrationSigning.signingMessageValues,
      stage, stageRight, started]
  conv_lhs => rw [RegistrationNativePlatformBeaconPublication.fromEd]
  conv_rhs => rw [RegistrationNativePlatformBeaconPublication.fromEd]
  simp only [requestedLeft, requestedRight, RegistrationNativePlatformBeaconPublication.continueWith,
    callbacks, StateT.run_bind, map_bind]
  apply bind_congr
  intro result
  by_cases valid : ∃ signed, result.1 = .Some signed ∧ RegistrationSigning.replyTailMatches left result.1 ∧ signed.val.length = 1249
  · obtain ⟨signed, returned, admitted, width⟩ := valid
    obtain ⟨nextLeft, nextRight, resumedLeft, resumedRight, paired⟩ := RegistrationNativeIdentityEdPair.pq_key left right same signed stage
      (returned ▸ admitted) (returned ▸ (matching result.1).mp admitted) width
    conv_lhs => rw [returned, resumedLeft]
    conv_rhs => rw [returned, resumedRight]
    exact RegistrationNativeIdentityPublicationPair.hash hash sign ed reserve other nextLeft nextRight paired result.2
  · have invalidRight : ¬ ∃ signed, result.1 = .Some signed ∧ RegistrationSigning.replyTailMatches right result.1 ∧ signed.val.length = 1249 := by
      rintro ⟨signed, returned, admitted, width⟩
      exact valid ⟨signed, returned, (matching result.1).mpr admitted, width⟩
    conv_lhs => rw [pq_rejected left result.1 stage valid]
    conv_rhs => rw [pq_rejected right result.1 stageRight invalidRight]
    simp only [controls]


/-- Two actual fixed-width one-time replies enter the identical failed-publication suffix distribution, including arbitrary later optional Ed/ML responses and shared allocator effects. -/
theorem one_time (hash : Option Pqxdh.Bytes → StateT Platform ProbComp CtxRomAuth.CtxDigest)
    (sign : registration.MldsaSigningRequest → StateT Platform ProbComp RegistrationSigningShared.SignReply)
    (ed : registration.Ed25519SigningRequest → StateT Platform ProbComp RegistrationSigningShared.SignReply)
    (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (other : RegistrationSerializerReachableSource.OtherBranches) (pending : registration.BeaconEd25519Signing)
    (left right : Slice U8) (stage : pending.stage = .OneTimeKey)
    (matchingLeft : RegistrationSigning.replyTailMatches pending (.Some left))
    (matchingRight : RegistrationSigning.replyTailMatches pending (.Some right))
    (widthLeft : left.val.length = 98) (widthRight : right.val.length = 98) (before : Platform) :
    ∃ nextLeft nextRight,
      pending.resume (.Some left) = .ok (.Ed25519SigningRequested nextLeft) ∧
      pending.resume (.Some right) = .ok (.Ed25519SigningRequested nextRight) ∧
      Prod.map RegistrationNativeIdentityReadyFailure.observe id <$>
        (RegistrationNativePlatformBeaconPublication.fromEd (callbacks hash sign ed) (writer reserve other) nextLeft).run before =
      Prod.map RegistrationNativeIdentityReadyFailure.observe id <$>
        (RegistrationNativePlatformBeaconPublication.fromEd (callbacks hash sign ed) (writer reserve other) nextRight).run before := by
  obtain ⟨nextLeft, nextRight, resumedLeft, resumedRight, stageLeft, paired⟩ :=
    RegistrationNativeIdentityEdPair.one_time pending left right stage matchingLeft matchingRight widthLeft widthRight
  exact ⟨nextLeft, nextRight, resumedLeft, resumedRight, pq hash sign ed reserve other nextLeft nextRight paired stageLeft before⟩

end BeaconcryptCore.Computational.RegistrationNativeIdentityPublicationPair


/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityPublicationPair.hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityPublicationPair.hash


/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityPublicationPair.pq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityPublicationPair.pq

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityPublicationPair.one_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityPublicationPair.one_time
