-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInitStageContents
import BeaconcryptCore.Computational.RegistrationBeaconInitExecutor
import BeaconcryptCore.Refinement.PqxdhSurface

/-! Successful outgoing Init source receipts retain the original tagged public tuple and the three Ed stages and exact request-hash/publication continuation. The encoder is used at its actual invocation; no decoder inversion, completed-peer premise or root equality is assumed. -/
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
attribute [local irreducible] registration.BeaconInitHash.resume
variable {Encoded : Type}

def metadata (state : registration.BeaconInitState) :=
  (state.started, state.server_pin, state.beacon_identity)

def Fixed (started : pqxdh.BeaconStart) (pin : session.ServerAuthenticationPin)
    (identity : Std.Array U8 32#usize) (state : registration.BeaconInitState) : Prop :=
  metadata state = (started, pin, identity)

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

private theorem hash_fixed (before : registration.BeaconEd25519Signing) (reply : RegistrationSigningShared.SignReply)
    (next : registration.BeaconInitHash) (actual : before.resume reply = .ok (.HashRequested next)) :
    metadata next.state = metadata before.state := by
  obtain ⟨effect, resumed, progress⟩ := RegistrationSigning.ed_resume_refines before reply
  have same := RustM.ok.inj (resumed.symm.trans actual)
  subst effect
  simp only [RegistrationSigning.EdReplyTransition] at progress
  simpa only [metadata] using congrArg metadata progress.2.2.2

private theorem hash_attached (started : pqxdh.BeaconStart) (before : registration.BeaconEd25519Signing)
    (reply : RegistrationSigningShared.SignReply) (next : registration.BeaconInitHash)
    (raw : before.state.started = started) (prior : Prefix started before)
    (actual : before.resume reply = .ok (.HashRequested next)) : Attached started next.state := by
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

/-- The actual final request hash and pure publication cut retain its reached state and exact four buffers. -/
def HashCut (implementation : QueryImpl Spec (StateT S ProbComp))
    (encode : registration.InitView → core.option.Option Encoded)
    (pending : registration.BeaconInitHash) (before : S)
    (published : registration.PublishedBeaconInit Encoded) (after : S) : Prop :=
  RegistrationNativeInitStageContents.Canonical pending ∧
    ∃ request digest ready view,
      pending.request = .ok request ∧
      (digest, after) ∈ support ((implementation (.inl (.hash request))).run before) ∧
      pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) = .ok (.Ready ready) ∧
      ready.message = .ok view ∧ encode view = .Some published.encoded ∧
      ready.publish (encode view) = .ok (.Ok published)

private theorem continue_support {Input : Type} (implementation : QueryImpl Spec (StateT S ProbComp))
    (action : RustM Input) (next : Input → OracleComp Spec (RustM (Result Encoded)))
    (published : registration.PublishedBeaconInit Encoded) (before after : S)
    (supported : (.ok (.Ok published), after) ∈ support ((simulateQ implementation (continueWith action next)).run before)) :
    ∃ value, action = .ok value ∧ (.ok (.Ok published), after) ∈ support ((simulateQ implementation (next value)).run before) := by
  cases action <;> simp_all [continueWith, StateT.run_pure]

private theorem ready_cut (implementation : QueryImpl Spec (StateT S ProbComp))
    (encode : registration.InitView → core.option.Option Encoded) (ready : registration.BeaconInitReady)
    (published : registration.PublishedBeaconInit Encoded) (before after : S)
    (supported : (.ok (.Ok published), after) ∈ support ((simulateQ implementation (RegistrationBeaconInitExecutor.ready encode ready)).run before)) :
    ∃ view, ready.message = .ok view ∧ encode view = .Some published.encoded ∧
      ready.publish (encode view) = .ok (.Ok published) ∧ after = before := by
  obtain ⟨view, requested, supported⟩ := continue_support implementation ready.message _ published before after supported
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
  cases encoded : encode view with
  | none =>
    rw [encoded, RegistrationSigningContinuations.failed_publication_preserves_fresh] at supported
    cases supported.1
  | some bytes =>
    have publication := supported.1.symm
    obtain ⟨result, ran, _control, _pin, _hash, _identity, _pre, _one, _pq, output⟩ :=
      RegistrationSigningContinuations.publication_retains_exact_request ready bytes
    have same : result = published := by
      have current := publication
      rw [encoded] at current
      simpa using ran.symm.trans current
    subst result
    exact ⟨view, requested, output ▸ encoded, publication, supported.2⟩

theorem canonical_of_resume (before : registration.BeaconEd25519Signing)
    (reply : RegistrationSigningShared.SignReply) (next : registration.BeaconInitHash)
    (resumed : before.resume reply = .ok (.HashRequested next)) :
    RegistrationNativeInitStageContents.Canonical next := by
  have built := RegistrationSigning.final_hash_input_exact before reply next resumed
  obtain ⟨input, ran, bytes⟩ := TranscriptAuthRefinement.build_init_transcript_abs
    (retainedFields next.state) next.state.server_pin.binding.identity_key_id
    next.state.server_pin.binding.identity_public_key next.state.server_pin.public_key
  have equal : input = next.input := RustM.ok.inj (ran.symm.trans built)
  subst input
  simpa only [RegistrationNativeInitStageContents.Canonical,
    RegistrationNativeInitStageContents.sourcePayload, MldsaTranscriptAuth.initPayload] using bytes

private theorem hash_cut (implementation : QueryImpl Spec (StateT S ProbComp))
    (encode : registration.InitView → core.option.Option Encoded)
    (pending : registration.BeaconInitHash) (before : S)
    (published : registration.PublishedBeaconInit Encoded) (after : S)
    (canonical : RegistrationNativeInitStageContents.Canonical pending)
    (supported : (.ok (.Ok published), after) ∈ support ((simulateQ implementation (fromHash encode pending)).run before)) :
    HashCut implementation encode pending before published after := by
  obtain ⟨request, requested, called⟩ := continue_support implementation pending.request _ published before after supported
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at called
  obtain ⟨hashed, hashedSupport, continued⟩ := called
  obtain ⟨effect, resumed, continued⟩ := continue_support implementation
    (pending.resume (.Some (RegistrationAuthenticationShared.digestArray hashed.1))) _ published hashed.2 after continued
  cases effect with
  | Ready selected =>
    obtain ⟨view, message, encoded, publication, same⟩ := ready_cut implementation encode selected published hashed.2 after continued
    subst after
    exact ⟨canonical, request, hashed.1, selected, view, requested, hashedSupport, resumed, message, encoded, publication⟩
  | _ => simp [StateT.run_pure] at continued

inductive EdLead (implementation : QueryImpl Spec (StateT S ProbComp)) :
    registration.BeaconEd25519Signing → S → registration.BeaconInitHash → S → Prop where
  | last (pending : registration.BeaconEd25519Signing) (before : S)
      (request : registration.Ed25519SigningRequest) (reply : RegistrationSigningShared.SignReply) (after : S)
      (hashing : registration.BeaconInitHash)
      (requested : pending.request = .ok request)
      (called : (reply, after) ∈ support ((implementation (.inr request)).run before))
      (resumed : pending.resume reply = .ok (.HashRequested hashing)) :
      EdLead implementation pending before hashing after
  | step (pending : registration.BeaconEd25519Signing) (before : S)
      (request : registration.Ed25519SigningRequest) (reply : RegistrationSigningShared.SignReply) (after : S)
      (next : registration.BeaconEd25519Signing) (hashing : registration.BeaconInitHash) (lastState : S)
      (requested : pending.request = .ok request)
      (called : (reply, after) ∈ support ((implementation (.inr request)).run before))
      (resumed : pending.resume reply = .ok (.Ed25519SigningRequested next))
      (following : EdLead implementation next after hashing lastState) :
      EdLead implementation pending before hashing lastState

private theorem ed_reached (implementation : QueryImpl Spec (StateT S ProbComp))
    (encode : registration.InitView → core.option.Option Encoded)
    (started : pqxdh.BeaconStart) (pin : session.ServerAuthenticationPin)
    (identity : Std.Array U8 32#usize)
    (pending : registration.BeaconEd25519Signing) (before : S)
    (published : registration.PublishedBeaconInit Encoded) (after : S)
    (fixed : Fixed started pin identity pending.state) (prior : Prefix started pending)
    (supported : (.ok (.Ok published), after) ∈ support ((simulateQ implementation (fromEd encode pending)).run before)) :
    ∃ hashing atHash, EdLead implementation pending before hashing atHash ∧
      Fixed started pin identity hashing.state ∧ Attached started hashing.state ∧
      HashCut implementation encode hashing atHash published after := by
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
      obtain ⟨hashing, atHash, leading, finalFixed, attached, cut⟩ := ed_reached implementation encode
        started pin identity next signed.2 published after ((ed_fixed pending signed.1 next actual).trans fixed)
        (ed_prefix started pending signed.1 next raw prior actual) continued
      exact ⟨hashing, atHash, .step pending before request signed.1 signed.2 next hashing atHash requested signedSupport actual leading,
        finalFixed, attached, cut⟩
    | HashRequested hashing =>
      rw [actual] at continued
      exact ⟨hashing, signed.2, .last pending before request signed.1 signed.2 hashing requested signedSupport actual,
        (hash_fixed pending signed.1 hashing actual).trans fixed,
        hash_attached started pending signed.1 hashing raw prior actual,
        hash_cut implementation encode hashing signed.2 published after
          (canonical_of_resume pending signed.1 hashing actual) continued⟩
    | _ => rw [actual] at continued; simp [StateT.run_pure] at continued
termination_by edRank pending
decreasing_by exact ed_rank pending signed.1 next actual

/-- A successful actual source execution has its original tagged public tuple, ordered attached-signature leading and exact same-state request-hash/publication cuts. -/
theorem begin_receipt (implementation : QueryImpl Spec (StateT S ProbComp))
    (encode : registration.InitView → core.option.Option Encoded)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin)
    (published : registration.PublishedBeaconInit Encoded) (before after : S)
    (supported : (.ok (.Ok published), after) ∈ support
      ((simulateQ implementation (begin encode control inputs coins pin)).run before)) :
    ∃ started pending hashing atHash,
      pqxdh.beacon_start control inputs coins = .ok started ∧
      pqxdh.validate_init_kex started.message = .ok (.Ok {
        beacon_identity_public_key := inputs.identity_public_key,
        beacon_prekey_public_key := inputs.prekey_public_key,
        beacon_one_time_public_key := coins.one_time_public_key,
        beacon_pq_public_key := inputs.pq_public_key }) ∧
      registration.begin_beacon_init control inputs coins pin = .ok (.Ed25519SigningRequested pending) ∧
      EdLead implementation pending before hashing atHash ∧
      Fixed started pin inputs.identity_public_key hashing.state ∧ Attached started hashing.state ∧
      HashCut implementation encode hashing atHash published after := by
  unfold RegistrationBeaconInitExecutor.begin at supported
  obtain ⟨effect, actual, continued⟩ := continue_support implementation
    (registration.begin_beacon_init control inputs coins pin) _ published before after supported
  obtain ⟨started, startedRun, validated, _binding, _identity⟩ := PqxdhSurface.beacon_start_validates control inputs coins
  obtain ⟨other, otherRun, beginRun⟩ := RegistrationSigningContinuations.begin_beacon_init_exact control inputs coins pin
  have same := RustM.ok.inj (startedRun.symm.trans otherRun)
  subst other
  have sourceRun := actual
  rw [beginRun] at actual
  split_ifs at actual
  · cases actual
    simp [StateT.run_pure] at continued
  · cases actual
    obtain ⟨hashing, atHash, leading, fixed, attached, cut⟩ := ed_reached implementation encode
      started pin inputs.identity_public_key _ before published after (by rfl) (by trivial) continued
    exact ⟨started, _, hashing, atHash, startedRun, validated, sourceRun, leading, fixed, attached, cut⟩

/-- The complete owned request retains the attached signature bytes in all four buffers. -/
def ownedFields (state : registration.BeaconInitState) : authentication.OwnedInitFields :=
  ⟨state.started.message.identity_key, state.pre_key, state.one_time_key, state.pq_key⟩

private theorem owned_fields_eq {left right : authentication.OwnedInitFields}
    (identity : left.identity_key = right.identity_key) (pre : left.pre_key = right.pre_key)
    (one : left.one_time_key = right.one_time_key) (pq : left.pq_key = right.pq_key) : left = right := by
  cases left
  cases right
  cases identity
  cases pre
  cases one
  cases pq
  rfl

/-- Successful publication owns every original attached Init buffer at the actual request-hash cut. -/
theorem hash_fields_contents (implementation : QueryImpl Spec (StateT S ProbComp))
    (encode : registration.InitView → core.option.Option Encoded)
    (pending : registration.BeaconInitHash) (before : S)
    (published : registration.PublishedBeaconInit Encoded) (after : S)
    (cut : HashCut implementation encode pending before published after) :
    published.pending.binding.init_fields = ownedFields pending.state := by
  rcases cut with ⟨_canonical, _request, digest, ready, _view, _requested, _called, resumed, _message, encoded, publication⟩
  obtain ⟨actual, actualResume, stateSame, _hashSame, _actualView, _actualMessage, _fields⟩ :=
    RegistrationSigningContinuations.beacon_init_hash_some_exact pending (RegistrationAuthenticationShared.digestArray digest)
  have readySame : actual = ready := by simpa using actualResume.symm.trans resumed
  subst actual
  obtain ⟨result, ran, _control, _pin, _initHash, identity, pre, one, pq, _output⟩ :=
    RegistrationSigningContinuations.publication_retains_exact_request ready published.encoded
  have resultSame : result = published := by
    have same := publication
    rw [encoded] at same
    simpa using ran.symm.trans same
  subst result
  apply owned_fields_eq
  · exact identity.trans (congrArg (fun state => state.started.message.identity_key) stateSame)
  · exact pre.trans (congrArg (fun state => state.pre_key) stateSame)
  · exact one.trans (congrArg (fun state => state.one_time_key) stateSame)
  · exact pq.trans (congrArg (fun state => state.pq_key) stateSame)

/-- The final source hash binds the exact selected request and retained fields before successful publication. -/
theorem hash_contents (implementation : QueryImpl Spec (StateT S ProbComp))
    (encode : registration.InitView → core.option.Option Encoded)
    (pending : registration.BeaconInitHash) (before : S)
    (published : registration.PublishedBeaconInit Encoded) (after : S)
    (cut : HashCut implementation encode pending before published after) :
    ∃ request digest view,
      (digest, after) ∈ support ((implementation (.inl (.hash request))).run before) ∧
      RegistrationInputs.hashBytes request = (RegistrationNativeInitStageContents.sourcePayload pending.state).transcript ∧
      published.pending.control = pending.state.started.state ∧
      published.pending.binding.server_pin = pending.state.server_pin ∧
      published.pending.binding.init_fields.identity_key = pending.state.started.message.identity_key ∧
      published.pending.binding.init_hash = RegistrationAuthenticationShared.digestArray digest ∧
      encode view = .Some published.encoded ∧ view.fields = retainedFields pending.state := by
  rcases cut with ⟨canonical, request, digest, ready, view, requested, called, resumed, message, encoded, publication⟩
  obtain ⟨actual, actualResume, stateSame, hashSame, actualView, actualMessage, fields⟩ :=
    RegistrationSigningContinuations.beacon_init_hash_some_exact pending (RegistrationAuthenticationShared.digestArray digest)
  have readySame : actual = ready := by simpa using actualResume.symm.trans resumed
  subst actual
  have viewSame : actualView = view := RustM.ok.inj (actualMessage.symm.trans message)
  subst actualView
  obtain ⟨result, ran, control, pin, initHash, identity, _pre, _one, _pq, output⟩ :=
    RegistrationSigningContinuations.publication_retains_exact_request ready published.encoded
  have resultSame : result = published := by
    have same := publication
    rw [encoded] at same
    simpa using ran.symm.trans same
  subst result
  refine ⟨request, digest, view, called, ?_, ?_, ?_, ?_, initHash.trans hashSame, encoded, ?_⟩
  · have literal : request = .Single pending.input.to_slice := RustM.ok.inj requested.symm
    subst request
    exact canonical
  · exact control.trans (congrArg (fun state => state.started.state) stateSame)
  · exact pin.trans (congrArg (fun state => state.server_pin) stateSame)
  · exact identity.trans (congrArg (fun state => state.started.message.identity_key) stateSame)
  · exact fields

end BeaconcryptCore.Computational.RegistrationNativeInitTupleSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitTupleSource.canonical_of_resume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitTupleSource.canonical_of_resume

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitTupleSource.hash_fields_contents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitTupleSource.hash_fields_contents

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitTupleSource.begin_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitTupleSource.begin_receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitTupleSource.hash_contents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitTupleSource.hash_contents
