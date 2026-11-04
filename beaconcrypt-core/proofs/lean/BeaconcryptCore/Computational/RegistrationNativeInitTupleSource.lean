-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInitStageContents
import BeaconcryptCore.Computational.RegistrationNativeBeaconPublication

/-! Successful outgoing Init source receipts retain the original tagged public tuple and every reached fingerprint/hash/sign/publication continuation. The encoder is used at its actual invocation; no decoder inversion, completed-peer premise or root equality is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInitTupleSource
open BeaconcryptCore.Refinement
open RegistrationBeaconInitExecutor
open RegistrationSigningContinuations (retainedFields)
attribute [local irreducible] registration.BeaconInitHash.resume registration.BeaconFingerprint.resume
variable {Encoded : Type}

def metadata (state : registration.BeaconInitState) :=
  (state.started, state.server_pin, state.beacon_identity, state.beacon_mldsa)

def Fixed (started : pqxdh.BeaconStart) (pin : session.ServerAuthenticationPin)
    (identity : Std.Array U8 32#usize) (mldsa : Std.Array U8 1952#usize) (state : registration.BeaconInitState) : Prop :=
  metadata state = (started, pin, identity, mldsa)

def Prekey (started : pqxdh.BeaconStart) (state : registration.BeaconInitState) : Prop :=
  state.pre_key.val.drop 64 = started.message.prekey.val

def OneTime (started : pqxdh.BeaconStart) (state : registration.BeaconInitState) : Prop :=
  state.one_time_key.val.drop 64 = started.message.one_time_key.val

def PqKey (started : pqxdh.BeaconStart) (state : registration.BeaconInitState) : Prop :=
  state.pq_key.val.drop 64 = started.message.pq_key.val

def Prefix (started : pqxdh.BeaconStart) (pending : registration.BeaconEd25519Signing) : Prop :=
  match pending.stage with
  | .PreKey => True
  | .OneTimeKey => Prekey started pending.state
  | .PqKey => Prekey started pending.state ∧ OneTime started pending.state

private theorem ed_fixed (before : registration.BeaconEd25519Signing) (reply : RegistrationSigningShared.SignReply)
    (next : registration.BeaconEd25519Signing)
    (actual : before.resume reply = .ok (.Ed25519SigningRequested next)) : metadata next.state = metadata before.state := by
  obtain ⟨effect, resumed, progress⟩ := RegistrationSigning.ed_resume_refines before reply
  have same := RustM.ok.inj (resumed.symm.trans actual)
  subst effect
  cases stage : before.stage
  all_goals simp only [RegistrationSigning.EdReplyTransition, stage] at progress
  · simpa only [metadata] using congrArg metadata progress.2.2.2
  · simpa only [metadata] using congrArg metadata progress.2.2.2
  · exact progress.2.elim

private theorem ed_prefix (started : pqxdh.BeaconStart) (before : registration.BeaconEd25519Signing)
    (reply : RegistrationSigningShared.SignReply) (next : registration.BeaconEd25519Signing)
    (raw : before.state.started = started) (prior : Prefix started before)
    (actual : before.resume reply = .ok (.Ed25519SigningRequested next)) : Prefix started next := by
  obtain ⟨effect, resumed, progress⟩ := RegistrationSigning.ed_resume_refines before reply
  have same := RustM.ok.inj (resumed.symm.trans actual)
  subst effect
  cases stage : before.stage
  all_goals simp only [RegistrationSigning.EdReplyTransition, stage] at progress
  · rcases progress with ⟨tail, nextStage, copied, _retained⟩
    simp only [Prefix, nextStage, Prekey, copied]
    cases reply with
    | none => exact tail.elim
    | some bytes => simpa only [RegistrationSigning.replyTailMatches, RegistrationSigning.signingMessageValues,
        stage, RegistrationSigning.replyValues, raw] using tail.2
  · rcases progress with ⟨tail, nextStage, copied, retained⟩
    have prekey : next.state.pre_key = before.state.pre_key := congrArg (fun state => state.pre_key) retained
    simp only [Prefix, nextStage, Prekey, prekey]
    refine ⟨?_, ?_⟩
    · simpa only [Prefix, stage, Prekey] using prior
    · change next.state.one_time_key.val.drop 64 = started.message.one_time_key.val
      rw [copied]
      cases reply with
      | none => exact tail.elim
      | some bytes => simpa only [RegistrationSigning.replyTailMatches, RegistrationSigning.signingMessageValues,
          stage, RegistrationSigning.replyValues, raw] using tail.2
  · exact progress.2.elim


def Attached (started : pqxdh.BeaconStart) (state : registration.BeaconInitState) : Prop :=
  Prekey started state ∧ OneTime started state ∧ PqKey started state

private theorem fingerprint_fixed (before : registration.BeaconEd25519Signing) (reply : RegistrationSigningShared.SignReply)
    (next : registration.BeaconFingerprint) (actual : before.resume reply = .ok (.FingerprintRequested next)) :
    metadata next.state = metadata before.state := by
  obtain ⟨effect, resumed, progress⟩ := RegistrationSigning.ed_resume_refines before reply
  have same := RustM.ok.inj (resumed.symm.trans actual)
  subst effect
  simp only [RegistrationSigning.EdReplyTransition] at progress
  simpa only [metadata] using congrArg metadata progress.2.2.2

private theorem fingerprint_attached (started : pqxdh.BeaconStart) (before : registration.BeaconEd25519Signing)
    (reply : RegistrationSigningShared.SignReply) (next : registration.BeaconFingerprint)
    (raw : before.state.started = started) (prior : Prefix started before)
    (actual : before.resume reply = .ok (.FingerprintRequested next)) : Attached started next.state := by
  obtain ⟨effect, resumed, progress⟩ := RegistrationSigning.ed_resume_refines before reply
  have same := RustM.ok.inj (resumed.symm.trans actual)
  subst effect
  simp only [RegistrationSigning.EdReplyTransition] at progress
  rcases progress with ⟨tail, stage, copied, retained⟩
  have prekey : next.state.pre_key = before.state.pre_key := congrArg (fun state => state.pre_key) retained
  have oneTime : next.state.one_time_key = before.state.one_time_key := congrArg (fun state => state.one_time_key) retained
  have earlier : Prekey started before.state ∧ OneTime started before.state := by simpa only [Prefix, stage] using prior
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Prekey, prekey] using earlier.1
  · simpa only [OneTime, oneTime] using earlier.2
  · change next.state.pq_key.val.drop 64 = started.message.pq_key.val
    rw [copied]
    cases reply with
    | none => exact tail.elim
    | some bytes => simpa only [RegistrationSigning.replyTailMatches, RegistrationSigning.signingMessageValues,
        stage, RegistrationSigning.replyValues, raw] using tail.2

variable {S : Type}

/-- Literal source signing and encoder cuts, retaining the actual state after the optional signature reply. -/
def SigningCut (implementation : QueryImpl Spec (StateT S ProbComp))
    (encode : registration.SignedInitView → core.option.Option Encoded)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.BeaconMldsaSigning) (before : S)
    (published : registration.PublishedBeaconInit Encoded) (after : S) : Prop :=
  ∃ request signature ready view,
    pending.request = .ok request ∧
    (signature, after) ∈ support ((implementation (.inl (.sign request payload digest))).run before) ∧
    pending.resume signature = .ok (.Ready ready) ∧ ready.message = .ok view ∧
    encode view = .Some published.encoded ∧ ready.publish (encode view) = .ok (.Ok published)

def HashCut (implementation : QueryImpl Spec (StateT S ProbComp))
    (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconInitHash) (before : S)
    (published : registration.PublishedBeaconInit Encoded) (after : S) : Prop :=
  ∃ request digest hashed signing,
    pending.request = .ok request ∧ (digest, hashed) ∈ support ((implementation (.inl (.hash request))).run before) ∧
    pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) = .ok (.MldsaSigningRequested signing) ∧
    SigningCut implementation encode ⟨.beacon, BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request⟩ digest signing hashed published after

def FingerprintCut (implementation : QueryImpl Spec (StateT S ProbComp))
    (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconFingerprint) (before : S)
    (published : registration.PublishedBeaconInit Encoded) (after : S) : Prop :=
  ∃ request digest hashed next,
    pending.request = .ok request ∧ (digest, hashed) ∈ support ((implementation (.inl (.hash request))).run before) ∧
    pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) = .ok (.HashRequested next) ∧
    HashCut implementation encode next hashed published after

private theorem continue_support {Input : Type} (implementation : QueryImpl Spec (StateT S ProbComp))
    (action : RustM Input) (next : Input → OracleComp Spec (RustM (Result Encoded)))
    (published : registration.PublishedBeaconInit Encoded) (before after : S)
    (supported : (.ok (.Ok published), after) ∈ support ((simulateQ implementation (continueWith action next)).run before)) :
    ∃ value, action = .ok value ∧ (.ok (.Ok published), after) ∈ support ((simulateQ implementation (next value)).run before) := by
  cases action <;> simp_all [continueWith, StateT.run_pure]

private theorem ready_cut (implementation : QueryImpl Spec (StateT S ProbComp))
    (encode : registration.SignedInitView → core.option.Option Encoded) (ready : registration.BeaconInitReady)
    (published : registration.PublishedBeaconInit Encoded) (before after : S)
    (supported : (.ok (.Ok published), after) ∈ support ((simulateQ implementation (RegistrationBeaconInitExecutor.ready encode ready)).run before)) :
    ∃ view, ready.message = .ok view ∧ encode view = .Some published.encoded ∧
      ready.publish (encode view) = .ok (.Ok published) ∧ after = before := by
  obtain ⟨view, requested, supported⟩ := continue_support implementation ready.message _ published before after supported
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
  cases encoded : encode view with
  | none => simp [registration.BeaconInitReady.publish, encoded] at supported
  | some bytes =>
    have publication := supported.1.symm
    have same := publication
    simp only [registration.BeaconInitReady.publish, encoded, RustM.ok.injEq,
      core.result.Result.Ok.injEq] at same
    have output : bytes = published.encoded := congrArg (fun value : registration.PublishedBeaconInit Encoded => value.encoded) same
    exact ⟨view, requested, output ▸ encoded, publication, supported.2⟩

private theorem signing_cut (implementation : QueryImpl Spec (StateT S ProbComp))
    (encode : registration.SignedInitView → core.option.Option Encoded)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.BeaconMldsaSigning) (before : S)
    (published : registration.PublishedBeaconInit Encoded) (after : S)
    (supported : (.ok (.Ok published), after) ∈ support
      ((simulateQ implementation (fromSigning encode payload digest pending)).run before)) :
    SigningCut implementation encode payload digest pending before published after := by
  obtain ⟨request, requested, called⟩ := continue_support implementation pending.request _ published before after supported
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at called
  obtain ⟨signed, signedSupport, continued⟩ := called
  obtain ⟨effect, resumed, continued⟩ := continue_support implementation (pending.resume signed.1) _ published signed.2 after continued
  cases effect with
  | Ready selected =>
    obtain ⟨view, message, encoded, publication, same⟩ := ready_cut implementation encode selected published signed.2 after continued
    subst after
    exact ⟨request, signed.1, selected, view, requested, signedSupport, resumed, message, encoded, publication⟩
  | _ => simp [StateT.run_pure] at continued

private theorem hash_cut (implementation : QueryImpl Spec (StateT S ProbComp))
    (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconInitHash) (before : S)
    (published : registration.PublishedBeaconInit Encoded) (after : S)
    (supported : (.ok (.Ok published), after) ∈ support ((simulateQ implementation (fromHash encode pending)).run before)) :
    HashCut implementation encode pending before published after := by
  obtain ⟨request, requested, called⟩ := continue_support implementation pending.request _ published before after supported
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at called
  obtain ⟨hashed, hashedSupport, continued⟩ := called
  obtain ⟨effect, resumed, continued⟩ := continue_support implementation
    (pending.resume (.Some (RegistrationAuthenticationShared.digestArray hashed.1))) _ published hashed.2 after continued
  cases effect with
  | MldsaSigningRequested selected =>
    exact ⟨request, hashed.1, hashed.2, selected, requested, hashedSupport, resumed,
      signing_cut implementation encode _ hashed.1 selected hashed.2 published after continued⟩
  | _ => simp [StateT.run_pure] at continued

private theorem fingerprint_cut (implementation : QueryImpl Spec (StateT S ProbComp))
    (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconFingerprint) (before : S)
    (published : registration.PublishedBeaconInit Encoded) (after : S)
    (supported : (.ok (.Ok published), after) ∈ support ((simulateQ implementation (fromFingerprint encode pending)).run before)) :
    FingerprintCut implementation encode pending before published after := by
  obtain ⟨request, requested, called⟩ := continue_support implementation pending.request _ published before after supported
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at called
  obtain ⟨hashed, hashedSupport, continued⟩ := called
  obtain ⟨effect, resumed, continued⟩ := continue_support implementation
    (pending.resume (.Some (RegistrationAuthenticationShared.digestArray hashed.1))) _ published hashed.2 after continued
  cases effect with
  | HashRequested selected =>
    exact ⟨request, hashed.1, hashed.2, selected, requested, hashedSupport, resumed,
      hash_cut implementation encode selected hashed.2 published after continued⟩
  | _ => simp [StateT.run_pure] at continued

inductive EdLead (implementation : QueryImpl Spec (StateT S ProbComp)) :
    registration.BeaconEd25519Signing → S → registration.BeaconFingerprint → S → Prop where
  | last (pending : registration.BeaconEd25519Signing) (before : S)
      (request : registration.Ed25519SigningRequest) (reply : RegistrationSigningShared.SignReply) (after : S)
      (fingerprint : registration.BeaconFingerprint)
      (requested : pending.request = .ok request)
      (called : (reply, after) ∈ support ((implementation (.inr request)).run before))
      (resumed : pending.resume reply = .ok (.FingerprintRequested fingerprint)) :
      EdLead implementation pending before fingerprint after
  | step (pending : registration.BeaconEd25519Signing) (before : S)
      (request : registration.Ed25519SigningRequest) (reply : RegistrationSigningShared.SignReply) (after : S)
      (next : registration.BeaconEd25519Signing) (fingerprint : registration.BeaconFingerprint) (lastState : S)
      (requested : pending.request = .ok request)
      (called : (reply, after) ∈ support ((implementation (.inr request)).run before))
      (resumed : pending.resume reply = .ok (.Ed25519SigningRequested next))
      (following : EdLead implementation next after fingerprint lastState) :
      EdLead implementation pending before fingerprint lastState

private theorem ed_reached (implementation : QueryImpl Spec (StateT S ProbComp))
    (encode : registration.SignedInitView → core.option.Option Encoded)
    (started : pqxdh.BeaconStart) (pin : session.ServerAuthenticationPin)
    (identity : Std.Array U8 32#usize) (mldsa : Std.Array U8 1952#usize)
    (pending : registration.BeaconEd25519Signing) (before : S)
    (published : registration.PublishedBeaconInit Encoded) (after : S)
    (fixed : Fixed started pin identity mldsa pending.state) (prior : Prefix started pending)
    (supported : (.ok (.Ok published), after) ∈ support ((simulateQ implementation (fromEd encode pending)).run before)) :
    ∃ fingerprint atFingerprint, EdLead implementation pending before fingerprint atFingerprint ∧
      Fixed started pin identity mldsa fingerprint.state ∧ Attached started fingerprint.state ∧
      FingerprintCut implementation encode fingerprint atFingerprint published after := by
  have raw : pending.state.started = started := congrArg Prod.fst fixed
  rw [fromEd.eq_def] at supported
  obtain ⟨request, requested, called⟩ := continue_support implementation pending.request _ published before after supported
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at called
  obtain ⟨signed, signedSupport, continued⟩ := called
  cases actual : pending.resume signed.1 with
  | fail error => rw [actual] at continued; simp [StateT.run_pure] at continued
  | div => rw [actual] at continued; simp [StateT.run_pure] at continued
  | ok effect => cases effect with
    | Ed25519SigningRequested next =>
      rw [actual] at continued
      obtain ⟨fingerprint, atFingerprint, leading, finalFixed, attached, cut⟩ := ed_reached implementation encode
        started pin identity mldsa next signed.2 published after ((ed_fixed pending signed.1 next actual).trans fixed)
        (ed_prefix started pending signed.1 next raw prior actual) continued
      exact ⟨fingerprint, atFingerprint, .step pending before request signed.1 signed.2 next fingerprint atFingerprint requested signedSupport actual leading,
        finalFixed, attached, cut⟩
    | FingerprintRequested fingerprint =>
      rw [actual] at continued
      exact ⟨fingerprint, signed.2, .last pending before request signed.1 signed.2 fingerprint requested signedSupport actual,
        (fingerprint_fixed pending signed.1 fingerprint actual).trans fixed,
        fingerprint_attached started pending signed.1 fingerprint raw prior actual,
        fingerprint_cut implementation encode fingerprint signed.2 published after continued⟩
    | _ => rw [actual] at continued; simp [StateT.run_pure] at continued
termination_by edRank pending
decreasing_by exact ed_rank pending signed.1 next actual

/-- A successful actual source execution has its original tagged public tuple, ordered attached-signature leading and exact same-state fingerprint/hash/sign/publication cuts. -/
theorem begin_receipt (implementation : QueryImpl Spec (StateT S ProbComp))
    (encode : registration.SignedInitView → core.option.Option Encoded)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize)
    (published : registration.PublishedBeaconInit Encoded) (before after : S)
    (supported : (.ok (.Ok published), after) ∈ support
      ((simulateQ implementation (begin encode control inputs coins pin mldsa)).run before)) :
    ∃ started pending fingerprint atFingerprint,
      pqxdh.beacon_start control inputs coins = .ok started ∧
      pqxdh.validate_init_kex started.message = .ok (.Ok {
        beacon_identity_public_key := inputs.identity_public_key,
        beacon_prekey_public_key := inputs.prekey_public_key,
        beacon_one_time_public_key := coins.one_time_public_key,
        beacon_pq_public_key := inputs.pq_public_key }) ∧
      registration.begin_beacon_init control inputs coins pin mldsa = .ok (.Ed25519SigningRequested pending) ∧
      EdLead implementation pending before fingerprint atFingerprint ∧
      Fixed started pin inputs.identity_public_key mldsa fingerprint.state ∧ Attached started fingerprint.state ∧
      FingerprintCut implementation encode fingerprint atFingerprint published after := by
  unfold RegistrationBeaconInitExecutor.begin at supported
  obtain ⟨effect, actual, continued⟩ := continue_support implementation
    (registration.begin_beacon_init control inputs coins pin mldsa) _ published before after supported
  obtain ⟨started, startedRun, validated, _binding, _identity⟩ := PqxdhSurface.beacon_start_validates control inputs coins
  obtain ⟨other, otherRun, beginRun⟩ := RegistrationSigningContinuations.begin_beacon_init_exact control inputs coins pin mldsa
  have same := RustM.ok.inj (startedRun.symm.trans otherRun)
  subst other
  have sourceRun := actual
  rw [beginRun] at actual
  split_ifs at actual
  · cases actual
    simp [StateT.run_pure] at continued
  · cases actual
    obtain ⟨fingerprint, atFingerprint, leading, fixed, attached, cut⟩ := ed_reached implementation encode
      started pin inputs.identity_public_key mldsa _ before published after (by rfl) (by trivial) continued
    exact ⟨started, _, fingerprint, atFingerprint, startedRun, validated, sourceRun, leading, fixed, attached, cut⟩

private theorem sign_payload_support (implementation : QueryImpl Spec (StateT S ProbComp))
    (request : registration.MldsaSigningRequest) (left right : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (reply : RegistrationSigningShared.SignReply) (before after : S) (same : left = right)
    (supported : (reply, after) ∈ support ((implementation (.inl (.sign request left digest))).run before)) :
    (reply, after) ∈ support ((implementation (.inl (.sign request right digest))).run before) := by
  cases same
  exact supported

/-- The actual source cuts identify the exact hash preimage, retained pending digest and public fields, and the same final-state ML attempt and encoder invocation. -/
theorem fingerprint_contents (implementation : QueryImpl Spec (StateT S ProbComp))
    (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconFingerprint) (before : S)
    (published : registration.PublishedBeaconInit Encoded) (after : S)
    (cut : FingerprintCut implementation encode pending before published after) :
    ∃ request digest beforeHash afterHash signRequest signature view,
      (digest, afterHash) ∈ support ((implementation (.inl (.hash request))).run beforeHash) ∧
      (signature, after) ∈ support ((implementation (.inl (.sign signRequest
        (RegistrationNativeInitStageContents.sourcePayload pending.state) digest))).run afterHash) ∧
      BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request =
        (RegistrationNativeInitStageContents.sourcePayload pending.state).transcript ∧
      signRequest.public_key = pending.state.beacon_mldsa ∧
      published.pending.control = pending.state.started.state ∧
      published.pending.binding.server_pin = pending.state.server_pin ∧
      published.pending.binding.beacon_identity_public_key = pending.state.beacon_identity ∧
      published.pending.binding.init_hash = RegistrationAuthenticationShared.digestArray digest ∧
      encode view = .Some published.encoded ∧ view.fields = retainedFields pending.state := by
  rcases cut with ⟨fpRequest, fpDigest, fpState, hashed, _fpRequest, _fpSupport, fpResume,
    request, digest, hashState, signing, hashRequest, hashSupport, hashResume, signCut⟩
  obtain ⟨actualHash, hashResumed, hashStateSame, _fingerprintSame, actualRequest, actualRequested, sourceBytes⟩ :=
    RegistrationSigningContinuations.beacon_fingerprint_some_exact pending (RegistrationAuthenticationShared.digestArray fpDigest)
  have hashSame := RustM.ok.inj (hashResumed.symm.trans fpResume)
  cases hashSame
  have requestSame := RustM.ok.inj (actualRequested.symm.trans hashRequest)
  subst actualRequest
  have bytes : BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request =
      (RegistrationNativeInitStageContents.sourcePayload pending.state).transcript := sourceBytes
  have payload : (⟨.beacon, BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request⟩ : MldsaTranscriptAuth.Payload) =
      RegistrationNativeInitStageContents.sourcePayload pending.state := by rw [bytes]; rfl
  obtain ⟨actualSign, signResumed, signStateSame, _signFingerprint, signDigest, _signRequest⟩ :=
    RegistrationSigningContinuations.beacon_init_hash_some_exact hashed (RegistrationAuthenticationShared.digestArray digest)
  have signSame := RustM.ok.inj (signResumed.symm.trans hashResume)
  cases signSame
  rcases signCut with ⟨signRequest, signature, ready, view, signRequested, signSupport, signResume, message, encoded, publication⟩
  cases signature with
  | none => cases signResume
  | some signature =>
    obtain ⟨effect, resumed, facts⟩ := RegistrationSigningContinuations.beacon_mldsa_signature_exact signing signature
    have same := RustM.ok.inj (resumed.symm.trans signResume)
    subst effect
    simp only [RegistrationSigningContinuations.signatureResult] at facts
    rcases facts with ⟨_width, readyState, _signature, pin, initHash, identity, _fingerprint, actualView, actualMessage, fields, _sig⟩
    have viewSame := RustM.ok.inj (actualMessage.symm.trans message)
    subst actualView
    have publishedSame := publication
    rw [encoded] at publishedSame
    simp only [registration.BeaconInitReady.publish, RustM.ok.injEq, core.result.Result.Ok.injEq] at publishedSame
    have readySame : ready.state = pending.state := readyState.trans (signStateSame.trans hashStateSame)
    have control := (congrArg (fun value : registration.PublishedBeaconInit Encoded => value.pending.control) publishedSame).symm
    have binding := (congrArg (fun value : registration.PublishedBeaconInit Encoded => value.pending.binding) publishedSame).symm
    refine ⟨request, digest, fpState, hashState, signRequest, .Some signature, view, hashSupport, ?_, bytes, ?_, ?_, ?_, ?_, ?_, encoded, ?_⟩
    · exact sign_payload_support implementation signRequest _ _ digest (.Some signature) hashState after payload signSupport
    · have key : signRequest.public_key = signing.state.beacon_mldsa := by
        have requested := signRequested
        simp only [registration.BeaconMldsaSigning.request, RustM.ok.injEq] at requested
        exact (congrArg (fun request : registration.MldsaSigningRequest => request.public_key) requested).symm
      exact key.trans (congrArg (fun state => state.beacon_mldsa) (signStateSame.trans hashStateSame))
    · exact control.trans (congrArg (fun state => state.started.state) readySame)
    · exact (congrArg (fun value : session.RegistrationBinding => value.server_pin) binding).trans
        (pin.trans (congrArg (fun state => state.server_pin) (signStateSame.trans hashStateSame)))
    · exact (congrArg (fun value : session.RegistrationBinding => value.beacon_identity_public_key) binding).trans
        (identity.trans (congrArg (fun state => state.beacon_identity) (signStateSame.trans hashStateSame)))
    · exact (congrArg (fun value : session.RegistrationBinding => value.init_hash) binding).trans (initHash.trans signDigest)
    · exact fields.trans (congrArg retainedFields (signStateSame.trans hashStateSame))

end BeaconcryptCore.Computational.RegistrationNativeInitTupleSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitTupleSource.begin_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitTupleSource.begin_receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitTupleSource.fingerprint_contents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitTupleSource.fingerprint_contents
