-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformWriter
import BeaconcryptCore.Computational.RegistrationNativeIdentitySigningRole
import BeaconcryptCore.Refinement.RegistrationSigningContinuations
/-! Every role-one-time Ed request in the literal source publication uses the same original tagged one-time message. All source replies and later writer failures are retained; no signing success or whole-controller premise is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOneTimeOperandLineage
open BeaconcryptCore.Refinement.RegistrationSigning
open RegistrationNativePlatformWriter (Spec cryptoLift init)
open RegistrationNativePlatformBeaconPublication
variable {E : Type}
attribute [local irreducible] registration.BeaconInitHash.resume registration.BeaconFingerprint.resume
  registration.BeaconMldsaSigning.resume registration.BeaconEd25519Signing.resume registration.begin_beacon_init

def UsesMessage (message : Pqxdh.Bytes) : (Spec E).Domain → Prop
  | .inl (.inr request) => RegistrationNativeIdentitySigningRole.oneTime (TranscriptAuthParts.absSlice request.message) = true →
      TranscriptAuthParts.absSlice request.message = message
  | _ => True

private theorem begin_started (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs)
    (coins : pqxdh.BeaconCoins) (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize)
    (started : pqxdh.BeaconStart) (built : pqxdh.beacon_start control inputs coins = .ok started)
    (pending : registration.BeaconEd25519Signing)
    (begun : registration.begin_beacon_init control inputs coins pin mldsa = .ok (.Ed25519SigningRequested pending)) :
    pending.state.started = started := by
  obtain ⟨actual, actualRun, exactBegin⟩ := BeaconcryptCore.Refinement.RegistrationSigningContinuations.begin_beacon_init_exact control inputs coins pin mldsa
  have same : actual = started := RustM.ok.inj (actualRun.symm.trans built)
  subst actual
  rw [exactBegin] at begun
  split at begun
  · cases begun
  · have same := registration.BeaconInitEffect.Ed25519SigningRequested.inj (RustM.ok.inj begun)
    subst pending
    rfl

/-- The complete original tagged tuple survives every recursive Ed state transition. -/
theorem resume_started (pending next : registration.BeaconEd25519Signing)
    (reply : core.option.Option (Slice U8))
    (resumed : pending.resume reply = .ok (.Ed25519SigningRequested next)) :
    next.state.started = pending.state.started := by
  obtain ⟨effect, actual, progress⟩ := ed_resume_refines pending reply
  have same : effect = .Ed25519SigningRequested next := RustM.ok.inj (actual.symm.trans resumed)
  subst effect
  cases stage : pending.stage
  all_goals simp only [EdReplyTransition, stage] at progress
  · simpa only using congrArg (fun state : registration.BeaconInitState => state.started) progress.2.2.2
  · simpa only using congrArg (fun state : registration.BeaconInitState => state.started) progress.2.2.2
  · exact progress.2.elim

/-- The source role test identifies exactly the actual one-time message of the original tuple. -/
theorem request_message (pending : registration.BeaconEd25519Signing)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged pending.state.started)
    (request : registration.Ed25519SigningRequest) (requested : pending.request = .ok request)
    (role : RegistrationNativeIdentitySigningRole.oneTime (TranscriptAuthParts.absSlice request.message) = true) :
    TranscriptAuthParts.absSlice request.message = PqxdhRefinement.absBytes pending.state.started.message.one_time_key := by
  obtain ⟨actual, actualRun, currentRole⟩ := RegistrationNativeIdentitySigningRole.request pending tagged
  cases RustM.ok.inj (actualRun.symm.trans requested)
  have stage : pending.stage = .OneTimeKey := by
    cases selected : pending.stage with
    | PreKey | PqKey =>
      simp only [selected, RegistrationNativeIdentitySigningRole.slot, role] at currentRole
      cases currentRole
    | OneTimeKey => rfl
  obtain ⟨actual, actualRun, _publicKey, _role, message⟩ := ed_request_exact pending
  cases RustM.ok.inj (actualRun.symm.trans requested)
  exact congrArg (List.map PqxdhRefinement.absByte) (by simpa only [signingMessageValues, stage] using message)

private theorem writer_allowed {A : Type} (message : Pqxdh.Bytes)
    (work : OracleComp (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) A) :
    (simulateQ RegistrationNativePlatformWriter.writerLift work).AllQueriesSatisfy (UsesMessage (E := E) message) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformWriter.writerLift,
      allQueriesSatisfy_query_bind_iff, UsesMessage]
    exact ⟨trivial, ih⟩
private theorem continue_allowed {Input A : Type} (message : Pqxdh.Bytes) (action : RustM Input)
    (next : Input → OracleComp (Spec E) (RustM (RegistrationBeaconInitExecutor.Result A)))
    (allowed : ∀ value, (next value).AllQueriesSatisfy (UsesMessage (E := E) message)) :
    (continueWith action next).AllQueriesSatisfy (UsesMessage (E := E) message) := by
  cases action with
  | ok value => exact allowed value
  | fail error | div => trivial
private theorem ready_allowed (message : Pqxdh.Bytes) (pending : registration.BeaconInitReady) :
    (ready (init E) pending).AllQueriesSatisfy (UsesMessage (E := E) message) := by
  unfold ready
  apply continue_allowed
  intro view
  exact allQueriesSatisfy_bind (writer_allowed message _) (fun _ => trivial)
private theorem signing_allowed (message : Pqxdh.Bytes)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.BeaconMldsaSigning) :
    (fromSigning (cryptoLift (E := E)) (init E) payload digest pending).AllQueriesSatisfy (UsesMessage (E := E) message) := by
  unfold fromSigning
  apply continue_allowed
  intro request
  simp only [cryptoLift, allQueriesSatisfy_query_bind_iff, UsesMessage]
  refine ⟨trivial, fun signature => ?_⟩
  apply continue_allowed
  intro effect
  cases effect with
  | Ready selected => exact ready_allowed message selected
  | _ => trivial
private theorem hash_allowed (message : Pqxdh.Bytes) (pending : registration.BeaconInitHash) :
    (fromHash (cryptoLift (E := E)) (init E) pending).AllQueriesSatisfy (UsesMessage (E := E) message) := by
  unfold fromHash
  apply continue_allowed
  intro request
  simp only [cryptoLift, allQueriesSatisfy_query_bind_iff, UsesMessage]
  refine ⟨trivial, fun digest => ?_⟩
  apply continue_allowed
  intro effect
  cases effect with
  | MldsaSigningRequested selected => exact signing_allowed message _ _ selected
  | _ => trivial
private theorem fingerprint_allowed (message : Pqxdh.Bytes) (pending : registration.BeaconFingerprint) :
    (fromFingerprint (cryptoLift (E := E)) (init E) pending).AllQueriesSatisfy (UsesMessage (E := E) message) := by
  unfold fromFingerprint
  apply continue_allowed
  intro request
  simp only [cryptoLift, allQueriesSatisfy_query_bind_iff, UsesMessage]
  refine ⟨trivial, fun digest => ?_⟩
  apply continue_allowed
  intro effect
  cases effect with
  | HashRequested selected => exact hash_allowed message selected
  | _ => trivial

/-- Every actual Ed continuation uses the original one-time message on precisely its one-time signing role, under arbitrary returned attachments. -/
theorem ed_allowed (message : Pqxdh.Bytes) (pending : registration.BeaconEd25519Signing)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged pending.state.started)
    (lineage : PqxdhRefinement.absBytes pending.state.started.message.one_time_key = message) :
    (fromEd (cryptoLift (E := E)) (init E) pending).AllQueriesSatisfy (UsesMessage (E := E) message) := by
  obtain ⟨request, requested, _identity, _role, _message⟩ := ed_request_exact pending
  rw [fromEd.eq_def, requested]
  simp only [continueWith, cryptoLift, allQueriesSatisfy_query_bind_iff, UsesMessage]
  refine ⟨fun role => (request_message pending tagged request requested role).trans lineage, fun reply => ?_⟩
  cases actual : pending.resume reply with
  | fail error | div => trivial
  | ok effect => cases effect with
    | Ed25519SigningRequested next =>
      have nextTagged : RegistrationNativeIdentitySigningRole.Tagged next.state.started :=
        RegistrationNativeIdentitySigningRole.preserved pending tagged reply _ actual
      have nextLineage : PqxdhRefinement.absBytes next.state.started.message.one_time_key = message := by
        rw [resume_started pending next reply actual]
        exact lineage
      exact ed_allowed message next nextTagged nextLineage
    | FingerprintRequested next => exact fingerprint_allowed message next
    | _ => trivial
termination_by RegistrationBeaconInitExecutor.edRank pending
decreasing_by exact RegistrationBeaconInitExecutor.ed_rank pending reply next actual

/-- The literal source begin derives that same message lineage from the actual tuple construction, retaining rejected pins and every later failed writer. -/
theorem begin_allowed (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs)
    (coins : pqxdh.BeaconCoins) (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize)
    (started : pqxdh.BeaconStart) (built : pqxdh.beacon_start control inputs coins = .ok started)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged started) :
    (RegistrationNativePlatformWriter.begin E control inputs coins pin mldsa).AllQueriesSatisfy
      (UsesMessage (E := E) (PqxdhRefinement.absBytes started.message.one_time_key)) := by
  unfold RegistrationNativePlatformWriter.begin RegistrationNativePlatformBeaconPublication.begin
  cases begun : registration.begin_beacon_init control inputs coins pin mldsa with
  | fail error | div => trivial
  | ok effect => cases effect with
    | Ed25519SigningRequested pending =>
      have retained := begin_started control inputs coins pin mldsa started built pending begun
      exact ed_allowed _ pending (retained ▸ tagged) (by rw [retained])
    | _ => trivial
end BeaconcryptCore.Computational.RegistrationNativePlatformOneTimeOperandLineage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOneTimeOperandLineage.resume_started' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOneTimeOperandLineage.resume_started

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOneTimeOperandLineage.request_message' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOneTimeOperandLineage.request_message

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOneTimeOperandLineage.ed_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOneTimeOperandLineage.ed_allowed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOneTimeOperandLineage.begin_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOneTimeOperandLineage.begin_allowed
