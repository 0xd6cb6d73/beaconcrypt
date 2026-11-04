-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePrekeyPublication
import BeaconcryptCore.Computational.RegistrationNativeWire
import BeaconcryptCore.Computational.RegistrationBeaconInitExecutor

/-! The unsigned one-time operand is preserved by the actual three-stage Ed controller and all later fingerprint, hash, mandatory ML signature and encoding stages. The proof admits every reply and failure branch and asserts no signature uniqueness or cryptographic security property. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOneTimePublication
open PqxdhEd25519EufCma (X25519PublicKey)
open PqxdhEd25519EufCma (oneTimeMessage parseOneTimeMessage)
open BeaconcryptCore.Refinement
open RegistrationBeaconInitExecutor
variable {Encoded : Type}

def Started (key : X25519PublicKey) (pending : registration.BeaconEd25519Signing) : Prop :=
  absBytes pending.state.started.message.one_time_key = oneTimeMessage key ∧
    (pending.stage = .PqKey → (absBytes pending.state.one_time_key).drop 64 = oneTimeMessage key)

def Signed (key : X25519PublicKey) (state : registration.BeaconInitState) : Prop :=
  (absBytes state.one_time_key).drop 64 = oneTimeMessage key

/-- An actual successful writer invocation and the exact signed one-time payload it received. -/
def PublishedKey (encode : registration.SignedInitView → core.option.Option Encoded)
    (key : X25519PublicKey) (published : registration.PublishedBeaconInit Encoded) : Prop :=
  ∃ view, encode view = .Some published.encoded ∧
    (absBytes view.fields.one_time_key).drop 64 = oneTimeMessage key

attribute [local irreducible] RegistrationBeaconInitExecutor.begin
  registration.BeaconInitHash.resume registration.BeaconFingerprint.resume

private theorem continue_support {Input : Type} (action : RustM Input)
    (next : Input → OracleComp Spec (RustM (Result Encoded)))
    (published : registration.PublishedBeaconInit Encoded)
    (supported : .ok (.Ok published) ∈ support (continueWith action next)) :
    ∃ value, action = .ok value ∧ .ok (.Ok published) ∈ support (next value) := by
  cases action <;> simp_all [continueWith]

private theorem started_validation (input : pqxdh.InitKex) (verified : pqxdh.VerifiedInitKex)
    (validated : pqxdh.validate_init_kex input = .ok (.Ok verified)) :
    absBytes input.one_time_key = oneTimeMessage (PqxdhPhase2InputBytes.word verified.beacon_one_time_public_key) := by
  have parsed := ((PqxdhHeadlineBridges.validate_init_kex_bridge input).2.1 verified).mp validated
  simp only [PqxdhHeadlineBridges.parsedFields, PqxdhHeadlineBridges.parsedBytes,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at parsed
  obtain ⟨identity, _, prekey, _prekeyParsed, oneTime, oneParsed, pq, _, result⟩ := parsed
  have same := congrArg (fun value => value.2.oneTime) result
  have pqResult : parseOneTimeMessage (absBytes input.one_time_key) =
      some (PqxdhPhase2InputBytes.word verified.beacon_one_time_public_key) := by
    simpa only [PqxdhHeadlineBridges.typedVerified, PqxdhPhase2InputBytes.word] using
      oneParsed.trans (congrArg some same)
  exact (PqxdhEd25519EufCma.parseOneTimeMessage_eq_some_iff _ _).mp pqResult

/-- The raw one-time field is fixed by the actual source start, before any signature is requested. -/
theorem started_key (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (started : pqxdh.BeaconStart) (built : pqxdh.beacon_start control inputs coins = .ok started) :
    absBytes started.message.one_time_key = oneTimeMessage (PqxdhPhase2InputBytes.word coins.one_time_public_key) := by
  obtain ⟨actual,ran,validated,_binding,_identity⟩ := PqxdhSurface.beacon_start_validates control inputs coins
  have same := RustM.ok.inj (ran.symm.trans built)
  subst actual
  exact started_validation _ _ validated

private theorem ed_started (key : X25519PublicKey)
    (pending : registration.BeaconEd25519Signing) (reply : RegistrationSigningShared.SignReply)
    (next : registration.BeaconEd25519Signing) (prior : Started key pending)
    (actual : pending.resume reply = .ok (.Ed25519SigningRequested next)) : Started key next := by
  obtain ⟨effect, resumed, progress⟩ := RegistrationSigning.ed_resume_refines pending reply
  have same := RustM.ok.inj (resumed.symm.trans actual)
  subst effect
  cases stage : pending.stage
  all_goals simp only [RegistrationSigning.EdReplyTransition, stage] at progress
  · obtain ⟨_tail, nextStage, _copied, kept⟩ := progress
    refine ⟨?_, ?_⟩
    · exact (congrArg (fun state : registration.BeaconInitState => absBytes state.started.message.one_time_key) kept).trans prior.1
    · intro impossible
      rw [nextStage] at impossible
      cases impossible
  · obtain ⟨tail, _nextStage, copied, kept⟩ := progress
    refine ⟨(congrArg (fun state : registration.BeaconInitState => absBytes state.started.message.one_time_key) kept).trans prior.1, ?_⟩
    intro _
    cases reply with
    | none => exact tail.elim
    | some bytes =>
        simp only [RegistrationSigning.replyTailMatches, RegistrationSigning.signingMessageValues, stage] at tail
        simp only [absBytes, ← List.map_drop, copied, RegistrationSigning.replyValues, tail.2]
        exact prior.1
  · exact progress.2.elim

private theorem ed_signed (key : X25519PublicKey)
    (pending : registration.BeaconEd25519Signing) (reply : RegistrationSigningShared.SignReply)
    (next : registration.BeaconFingerprint) (prior : Started key pending)
    (actual : pending.resume reply = .ok (.FingerprintRequested next)) : Signed key next.state := by
  obtain ⟨effect, resumed, progress⟩ := RegistrationSigning.ed_resume_refines pending reply
  have same := RustM.ok.inj (resumed.symm.trans actual)
  subst effect
  simp only [RegistrationSigning.EdReplyTransition] at progress
  obtain ⟨_tail, stage, _copied, kept⟩ := progress
  have original := prior.2 stage
  have signed := congrArg (fun state : registration.BeaconInitState => (absBytes state.one_time_key).drop 64) kept
  exact signed.trans original

private theorem ready_key (encode : registration.SignedInitView → core.option.Option Encoded)
    (key : X25519PublicKey) (pending : registration.BeaconInitReady)
    (published : registration.PublishedBeaconInit Encoded) (prior : Signed key pending.state)
    (supported : .ok (.Ok published) ∈ support (ready encode pending)) : PublishedKey encode key published := by
  obtain ⟨view, requested, returned⟩ := continue_support pending.message _ published supported
  have fields : view.fields.one_time_key = pending.state.one_time_key := by
    simp only [registration.BeaconInitReady.message, RegistrationSigningContinuations.retained_fields_exact,
      bind_tc_ok, RustM.ok.injEq] at requested
    cases requested
    rfl
  simp only [support_pure, Set.mem_singleton_iff] at returned
  cases encoded : encode view with
  | none => simp [registration.BeaconInitReady.publish, encoded] at returned
  | some bytes =>
      simp only [registration.BeaconInitReady.publish, encoded, RustM.ok.injEq,
        core.result.Result.Ok.injEq] at returned
      cases returned
      exact ⟨view, encoded, by simpa only [fields, Signed] using prior⟩

private theorem signing_key (encode : registration.SignedInitView → core.option.Option Encoded)
    (key : X25519PublicKey) (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.BeaconMldsaSigning) (published : registration.PublishedBeaconInit Encoded)
    (prior : Signed key pending.state)
    (supported : .ok (.Ok published) ∈ support (fromSigning encode payload digest pending)) :
    PublishedKey encode key published := by
  obtain ⟨request, _, called⟩ := continue_support pending.request _ published supported
  simp only [mem_support_bind_iff] at called
  obtain ⟨signature, _, continued⟩ := called
  obtain ⟨effect, resumed, continued⟩ := continue_support (pending.resume signature) _ published continued
  cases signature with
  | none => cases resumed; simp at continued
  | some signature =>
      obtain ⟨actual, actualRun, facts⟩ := RegistrationSigningContinuations.beacon_mldsa_signature_exact pending signature
      have same := RustM.ok.inj (actualRun.symm.trans resumed)
      subst actual
      cases effect with
      | Ready selected =>
          exact ready_key encode key selected published (facts.2.1 ▸ prior) continued
      | _ => simp at continued

private theorem hash_key (encode : registration.SignedInitView → core.option.Option Encoded)
    (key : X25519PublicKey) (pending : registration.BeaconInitHash)
    (published : registration.PublishedBeaconInit Encoded) (prior : Signed key pending.state)
    (supported : .ok (.Ok published) ∈ support (fromHash encode pending)) : PublishedKey encode key published := by
  obtain ⟨request, _, called⟩ := continue_support pending.request _ published supported
  simp only [mem_support_bind_iff] at called
  obtain ⟨digest, _, continued⟩ := called
  obtain ⟨effect, resumed, continued⟩ := continue_support
    (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest))) _ published continued
  obtain ⟨next, actual, retained, _⟩ := RegistrationSigningContinuations.beacon_init_hash_some_exact
    pending (RegistrationAuthenticationShared.digestArray digest)
  rw [actual] at resumed
  cases resumed
  exact signing_key encode key _ digest next published (retained ▸ prior) continued

private theorem fingerprint_key (encode : registration.SignedInitView → core.option.Option Encoded)
    (key : X25519PublicKey) (pending : registration.BeaconFingerprint)
    (published : registration.PublishedBeaconInit Encoded) (prior : Signed key pending.state)
    (supported : .ok (.Ok published) ∈ support (fromFingerprint encode pending)) : PublishedKey encode key published := by
  obtain ⟨request, _, called⟩ := continue_support pending.request _ published supported
  simp only [mem_support_bind_iff] at called
  obtain ⟨digest, _, continued⟩ := called
  obtain ⟨effect, resumed, continued⟩ := continue_support
    (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest))) _ published continued
  obtain ⟨next, actual, retained, _⟩ := RegistrationSigningContinuations.beacon_fingerprint_some_exact
    pending (RegistrationAuthenticationShared.digestArray digest)
  rw [actual] at resumed
  cases resumed
  exact hash_key encode key next published (retained ▸ prior) continued

private theorem ed_key (encode : registration.SignedInitView → core.option.Option Encoded)
    (key : X25519PublicKey) (pending : registration.BeaconEd25519Signing)
    (published : registration.PublishedBeaconInit Encoded) (prior : Started key pending)
    (supported : .ok (.Ok published) ∈ support (fromEd encode pending)) : PublishedKey encode key published := by
  rw [fromEd.eq_def] at supported
  obtain ⟨request, _, called⟩ := continue_support pending.request _ published supported
  simp only [mem_support_bind_iff] at called
  obtain ⟨reply, _, continued⟩ := called
  cases actual : pending.resume reply with
  | fail error => rw [actual] at continued; simp at continued
  | div => rw [actual] at continued; simp at continued
  | ok effect => cases effect with
    | Ed25519SigningRequested next =>
        rw [actual] at continued
        exact ed_key encode key next published (ed_started key pending reply next prior actual) continued
    | FingerprintRequested next =>
        rw [actual] at continued
        exact fingerprint_key encode key next published (ed_signed key pending reply next prior actual) continued
    | _ => rw [actual] at continued; simp at continued
termination_by edRank pending
decreasing_by exact ed_rank pending reply next actual

/-- Every successful actual outgoing controller encoded its original one-time input after the real Ed3, fingerprint, Init hash and ML-signing stages. -/
theorem begin_key (encode : registration.SignedInitView → core.option.Option Encoded)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize)
    (published : registration.PublishedBeaconInit Encoded)
    (supported : .ok (.Ok published) ∈ support (begin encode control inputs coins pin mldsa)) :
    PublishedKey encode (PqxdhPhase2InputBytes.word coins.one_time_public_key) published := by
  unfold RegistrationBeaconInitExecutor.begin at supported
  obtain ⟨effect, actual, continued⟩ := continue_support
    (registration.begin_beacon_init control inputs coins pin mldsa) _ published supported
  obtain ⟨started, startedRun, validated, _, _⟩ := PqxdhSurface.beacon_start_validates control inputs coins
  obtain ⟨other, otherRun, beginRun⟩ := RegistrationSigningContinuations.begin_beacon_init_exact
    control inputs coins pin mldsa
  have same := RustM.ok.inj (startedRun.symm.trans otherRun)
  subst other
  rw [beginRun] at actual
  split_ifs at actual
  · cases actual; simp at continued
  · cases actual
    refine ed_key encode _ _ published ?_ continued
    exact ⟨started_validation _ _ validated, by intro impossible; cases impossible⟩

/-- Stateful interpretation retains the same successful writer receipt without any primitive-correctness or signing-origin assumption. -/
theorem simulated_key {State : Type} (implementation : QueryImpl Spec (StateT State ProbComp))
    (encode : registration.SignedInitView → core.option.Option Encoded)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize)
    (published : registration.PublishedBeaconInit Encoded) (before after : State)
    (supported : (.ok (.Ok published), after) ∈ support
      ((simulateQ implementation (begin encode control inputs coins pin mldsa)).run before)) :
    PublishedKey encode (PqxdhPhase2InputBytes.word coins.one_time_public_key) published := by
  apply begin_key encode control inputs coins pin mldsa published
  apply OracleComp.support_simulateQ_run'_subset implementation (begin encode control inputs coins pin mldsa) before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst supported

/-- Actual successful publication and the explicit native six-field readback contract recover the same generated PQ field from public bytes. -/
theorem decoded_key (wire : RegistrationNativeWire.Wire) (readback : RegistrationNativeWire.InitReadBack wire)
    (key : X25519PublicKey) (published : registration.PublishedBeaconInit Pqxdh.Bytes)
    (receipt : PublishedKey wire.encodeInit key published) :
    ∃ packet, RegistrationNativeWire.readInit wire published.encoded = some packet ∧
      (absBytes packet.one_time_key).drop 64 = oneTimeMessage key := by
  obtain ⟨view, written, payload⟩ := receipt
  exact ⟨RegistrationNativeWire.initPacket view, readback view published.encoded written, payload⟩


end BeaconcryptCore.Computational.RegistrationNativeOneTimePublication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOneTimePublication.begin_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOneTimePublication.begin_key

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOneTimePublication.simulated_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOneTimePublication.simulated_key

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOneTimePublication.decoded_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOneTimePublication.decoded_key

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOneTimePublication.started_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOneTimePublication.started_key
