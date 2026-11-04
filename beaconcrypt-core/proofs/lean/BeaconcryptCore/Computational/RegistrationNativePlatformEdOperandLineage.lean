-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformWriter
import BeaconcryptCore.Computational.RegistrationNativeIdentityFrontend
import BeaconcryptCore.Refinement.RegistrationSigningContinuations
/-! Every Ed operand in the actual source writer tree is the public identity supplied at begin. Reply rejection, later writer failure and recursive Ed continuation preserve this data lineage; no signing-gate or successful-publication premise is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformEdOperandLineage
open BeaconcryptCore.Refinement.RegistrationSigning
open RegistrationNativePlatformWriter (Spec cryptoLift init)
open RegistrationNativePlatformBeaconPublication
variable {E : Type}
attribute [local irreducible] registration.BeaconInitHash.resume registration.BeaconFingerprint.resume
  registration.BeaconMldsaSigning.resume registration.BeaconEd25519Signing.resume registration.begin_beacon_init

def UsesKey (key : Std.Array U8 32#usize) : (Spec E).Domain → Prop
  | .inl (.inr request) => request.public_key = key
  | _ => True

/-- The actual source begin retains exactly its supplied public identity in the first Ed state. -/
theorem begin_identity (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs)
    (coins : pqxdh.BeaconCoins) (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize)
    (pending : registration.BeaconEd25519Signing)
    (begun : registration.begin_beacon_init control inputs coins pin mldsa = .ok (.Ed25519SigningRequested pending)) :
    pending.state.beacon_identity = inputs.identity_public_key := by
  obtain ⟨started, _built, exactBegin⟩ := BeaconcryptCore.Refinement.RegistrationSigningContinuations.begin_beacon_init_exact control inputs coins pin mldsa
  rw [exactBegin] at begun
  split at begun
  · cases begun
  · have same := registration.BeaconInitEffect.Ed25519SigningRequested.inj (RustM.ok.inj begun)
    subst pending
    rfl

/-- Every actual recursive Ed continuation retains its original public identity operand. -/
theorem resume_identity (pending next : registration.BeaconEd25519Signing)
    (reply : core.option.Option (Slice U8))
    (resumed : pending.resume reply = .ok (.Ed25519SigningRequested next)) :
    next.state.beacon_identity = pending.state.beacon_identity := by
  obtain ⟨effect, actual, progress⟩ := ed_resume_refines pending reply
  have same : effect = .Ed25519SigningRequested next := RustM.ok.inj (actual.symm.trans resumed)
  subst effect
  cases stage : pending.stage
  all_goals simp only [EdReplyTransition, stage] at progress
  · simpa only using congrArg (fun state : registration.BeaconInitState => state.beacon_identity) progress.2.2.2
  · simpa only using congrArg (fun state : registration.BeaconInitState => state.beacon_identity) progress.2.2.2
  · exact progress.2.elim

private theorem writer_allowed {A : Type} (key : Std.Array U8 32#usize)
    (work : OracleComp (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) A) :
    (simulateQ RegistrationNativePlatformWriter.writerLift work).AllQueriesSatisfy (UsesKey (E := E) key) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformWriter.writerLift,
      allQueriesSatisfy_query_bind_iff, UsesKey]
    exact ⟨trivial, ih⟩
private theorem continue_allowed {Input A : Type} (key : Std.Array U8 32#usize) (action : RustM Input)
    (next : Input → OracleComp (Spec E) (RustM (RegistrationBeaconInitExecutor.Result A)))
    (allowed : ∀ value, (next value).AllQueriesSatisfy (UsesKey (E := E) key)) :
    (continueWith action next).AllQueriesSatisfy (UsesKey (E := E) key) := by
  cases action with
  | ok value => exact allowed value
  | fail error | div => trivial
private theorem ready_allowed (key : Std.Array U8 32#usize) (pending : registration.BeaconInitReady) :
    (ready (init E) pending).AllQueriesSatisfy (UsesKey (E := E) key) := by
  unfold ready
  apply continue_allowed
  intro view
  exact allQueriesSatisfy_bind (writer_allowed key _) (fun _ => trivial)
private theorem signing_allowed (key : Std.Array U8 32#usize)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.BeaconMldsaSigning) :
    (fromSigning (cryptoLift (E := E)) (init E) payload digest pending).AllQueriesSatisfy (UsesKey (E := E) key) := by
  unfold fromSigning
  apply continue_allowed
  intro request
  simp only [cryptoLift, allQueriesSatisfy_query_bind_iff, UsesKey]
  refine ⟨trivial, fun signature => ?_⟩
  apply continue_allowed
  intro effect
  cases effect with
  | Ready selected => exact ready_allowed key selected
  | _ => trivial
private theorem hash_allowed (key : Std.Array U8 32#usize) (pending : registration.BeaconInitHash) :
    (fromHash (cryptoLift (E := E)) (init E) pending).AllQueriesSatisfy (UsesKey (E := E) key) := by
  unfold fromHash
  apply continue_allowed
  intro request
  simp only [cryptoLift, allQueriesSatisfy_query_bind_iff, UsesKey]
  refine ⟨trivial, fun digest => ?_⟩
  apply continue_allowed
  intro effect
  cases effect with
  | MldsaSigningRequested selected => exact signing_allowed key _ _ selected
  | _ => trivial
private theorem fingerprint_allowed (key : Std.Array U8 32#usize) (pending : registration.BeaconFingerprint) :
    (fromFingerprint (cryptoLift (E := E)) (init E) pending).AllQueriesSatisfy (UsesKey (E := E) key) := by
  unfold fromFingerprint
  apply continue_allowed
  intro request
  simp only [cryptoLift, allQueriesSatisfy_query_bind_iff, UsesKey]
  refine ⟨trivial, fun digest => ?_⟩
  apply continue_allowed
  intro effect
  cases effect with
  | HashRequested selected => exact hash_allowed key selected
  | _ => trivial

/-- All actual Ed retries use the original state's public identity, for arbitrary returned signatures and later failures. -/
theorem ed_allowed (key : Std.Array U8 32#usize) (pending : registration.BeaconEd25519Signing)
    (lineage : pending.state.beacon_identity = key) :
    (fromEd (cryptoLift (E := E)) (init E) pending).AllQueriesSatisfy (UsesKey (E := E) key) := by
  obtain ⟨request, requested, identity, _role, _message⟩ := ed_request_exact pending
  rw [fromEd.eq_def, requested]
  simp only [continueWith, cryptoLift, allQueriesSatisfy_query_bind_iff, UsesKey]
  refine ⟨identity.trans lineage, fun reply => ?_⟩
  cases actual : pending.resume reply with
  | fail error | div => trivial
  | ok effect => cases effect with
    | Ed25519SigningRequested next =>
      exact ed_allowed key next ((resume_identity pending next reply actual).trans lineage)
    | FingerprintRequested next => exact fingerprint_allowed key next
    | _ => trivial
termination_by RegistrationBeaconInitExecutor.edRank pending
decreasing_by exact RegistrationBeaconInitExecutor.ed_rank pending reply next actual

/-- The literal source writer begin uses only its supplied identity operand, including every failed signature and stateful serializer path. -/
theorem begin_allowed (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs)
    (coins : pqxdh.BeaconCoins) (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize) :
    (RegistrationNativePlatformWriter.begin E control inputs coins pin mldsa).AllQueriesSatisfy
      (UsesKey (E := E) inputs.identity_public_key) := by
  unfold RegistrationNativePlatformWriter.begin RegistrationNativePlatformBeaconPublication.begin
  cases begun : registration.begin_beacon_init control inputs coins pin mldsa with
  | fail error | div => trivial
  | ok effect => cases effect with
    | Ed25519SigningRequested pending =>
      exact ed_allowed inputs.identity_public_key pending (begin_identity control inputs coins pin mldsa pending begun)
    | _ => trivial

/-- The exact owner-captured Writer.begin used by the actual dynamic bundle passes that owner's Ed public key on every signing leaf. -/
theorem owner {I KemSK : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) :
    (RegistrationNativePlatformWriter.begin E ⟨owner.pin.binding⟩ (RegistrationNativeIdentityFrontend.inputs owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey).AllQueriesSatisfy
      (UsesKey (E := E) (PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519)) := by
  exact begin_allowed _ _ _ _ _
end BeaconcryptCore.Computational.RegistrationNativePlatformEdOperandLineage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformEdOperandLineage.begin_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformEdOperandLineage.begin_identity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformEdOperandLineage.resume_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformEdOperandLineage.resume_identity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformEdOperandLineage.ed_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformEdOperandLineage.ed_allowed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformEdOperandLineage.begin_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformEdOperandLineage.begin_allowed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformEdOperandLineage.owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformEdOperandLineage.owner
