-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorReply

/-! The two actual one-time continuations receive their canonical and placeholder replies from the same reached private source call. Both retain the chronological canonical service receipt before running the original PQ-Ed/hash/Ready/Init1490 writer suffix. Only failed-publication observations are compared; a successful public publication removes this selected tuple failure and is not equated as a complete pending state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOneTimeSource
open BeaconcryptCore.Refinement
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorSource (State)
variable {Platform E : Type}

/-- This lift retains every private source field and the complete unrelated mutable platform state. -/
def liftPrivate (work : StateT State ProbComp (Option Ed25519Signature)) :
    StateT (State × Platform) ProbComp (Option Ed25519Signature) := fun before =>
  (fun result => (result.1, (result.2, before.2))) <$> work.run before.1

/-- The literal original resume distinguishes all RustM and Core outcomes before continuing the same suffix. -/
noncomputable def resumed (hash : Option Pqxdh.Bytes → StateT (State × Platform) ProbComp CtxRomAuth.CtxDigest)
    (sign : registration.MldsaSigningRequest → StateT (State × Platform) ProbComp RegistrationSigningShared.SignReply)
    (ed : registration.Ed25519SigningRequest → StateT (State × Platform) ProbComp RegistrationSigningShared.SignReply)
    (reserve : Usize → StateT (State × Platform) ProbComp (core.result.Result Unit E))
    (other : RegistrationSerializerReachableSource.OtherBranches) (pending : registration.BeaconEd25519Signing)
    (reply : Option Ed25519Signature) :
    StateT (State × Platform) ProbComp (RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) :=
  match pending.resume (RegistrationAuthenticationShared.openedBytes
      (reply.map (fun signature => signature.toList ++ absBytes pending.state.started.message.one_time_key))) with
  | .ok (.Rejected previous) => pure (.ok (.Err previous))
  | .ok (.Ed25519SigningRequested next) => RegistrationNativePlatformBeaconPublication.fromEd
      (RegistrationNativeIdentityPublicationPair.callbacks hash sign ed)
      (RegistrationNativeSourceWriterFailureView.writer reserve other) next
  | .ok (.HashRequested next) => RegistrationNativePlatformBeaconPublication.fromHash
      (RegistrationNativeIdentityPublicationPair.callbacks hash sign ed)
      (RegistrationNativeSourceWriterFailureView.writer reserve other) next
  | .ok _ => pure .div
  | .fail error => pure (.fail error)
  | .div => pure .div

/-- The private-censored interpretation performs the same actual source call and replaces only its delivered signature. It is separate from the executable zero-sign-call EUF interpretation. -/
noncomputable def run (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (censored : Bool) (placeholder : Ed25519Signature)
    (hash : Option Pqxdh.Bytes → StateT (State × Platform) ProbComp CtxRomAuth.CtxDigest)
    (sign : registration.MldsaSigningRequest → StateT (State × Platform) ProbComp RegistrationSigningShared.SignReply)
    (ed : registration.Ed25519SigningRequest → StateT (State × Platform) ProbComp RegistrationSigningShared.SignReply)
    (reserve : Usize → StateT (State × Platform) ProbComp (core.result.Result Unit E))
    (other : RegistrationSerializerReachableSource.OtherBranches) (pending : registration.BeaconEd25519Signing) :
    StateT (State × Platform) ProbComp (RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) := do
  let actual ← liftPrivate (RegistrationNativeIdentityCensorSource.omitted joint selected selected
    (absBytes pending.state.started.message.one_time_key))
  resumed hash sign ed reserve other pending (if censored then actual.map (fun _ => placeholder) else actual)

/-- A supported generated row supplies the canonical signature at its actual source position. The full postsource state is then shared by the two complete failed-writer suffixes. -/
theorem failed_source (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (hash : Option Pqxdh.Bytes → StateT (State × Platform) ProbComp CtxRomAuth.CtxDigest)
    (sign : registration.MldsaSigningRequest → StateT (State × Platform) ProbComp RegistrationSigningShared.SignReply)
    (ed : registration.Ed25519SigningRequest → StateT (State × Platform) ProbComp RegistrationSigningShared.SignReply)
    (reserve : Usize → StateT (State × Platform) ProbComp (core.result.Result Unit E))
    (other : RegistrationSerializerReachableSource.OtherBranches) (pending : registration.BeaconEd25519Signing)
    (stage : pending.stage = .OneTimeKey) (before : State × Platform) (seed : PqxdhJointIdentity.IdentitySeed)
    (found : before.1.pool.seeds[selected]? = some seed)
    (target : before.1.target = some (absBytes pending.state.started.message.one_time_key)) :
    Prod.map RegistrationNativeIdentityReadyFailure.observe id <$>
      (run joint selected false placeholder hash sign ed reserve other pending).run before =
    Prod.map RegistrationNativeIdentityReadyFailure.observe id <$>
      (run joint selected true placeholder hash sign ed reserve other pending).run before := by
  let message := absBytes pending.state.started.message.one_time_key
  let canonical := joint.sign seed message
  let after : State × Platform := ({before.1 with
    pool := PqxdhDynamicIdentityPool.record (.inr (.service selected (.sign message))) (some canonical) before.1.pool
    canonical := some canonical}, before.2)
  have call : (liftPrivate (Platform := Platform) (RegistrationNativeIdentityCensorSource.omitted joint selected selected message)).run before =
      pure (some canonical, after) := by
    change (fun result => (result.1, (result.2, before.2))) <$>
      (RegistrationNativeIdentityCensorSource.omitted joint selected selected message).run before.1 = _
    rw [RegistrationNativeIdentityCensorSource.omitted_source joint selected message before.1 seed found target, map_pure]
  change Prod.map RegistrationNativeIdentityReadyFailure.observe id <$> (do
      let result ← (liftPrivate (RegistrationNativeIdentityCensorSource.omitted joint selected selected message)).run before
      (resumed hash sign ed reserve other pending result.1).run result.2) =
    Prod.map RegistrationNativeIdentityReadyFailure.observe id <$> (do
      let result ← (liftPrivate (RegistrationNativeIdentityCensorSource.omitted joint selected selected message)).run before
      (resumed hash sign ed reserve other pending (result.1.map (fun _ => placeholder))).run result.2)
  rw [call]
  simp only [pure_bind, Option.map_some]
  obtain ⟨nextLeft, nextRight, resumedLeft, resumedRight, paired⟩ :=
    RegistrationNativeIdentityCensorReply.paired hash sign ed reserve other pending canonical placeholder stage after
  simpa only [resumed, Option.map_some, resumedLeft, resumedRight] using paired

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOneTimeSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOneTimeSource.failed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOneTimeSource.failed_source
