-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemTarget
import BeaconcryptCore.Computational.RegistrationNativeWire
import BeaconcryptCore.Computational.RegistrationBeaconInitExecutor

/-! The actual three attached-signing continuations retain the original generated PQ payload. Fingerprinting, Init hashing, ML signing and dynamic publication preserve that same field. Every successful interpreted outgoing Init therefore has an actual encoded signed view with the generated public key, and the explicit native wire readback contract recovers that packet. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemPublication
open PqxdhKemIndCca (MlKem768PublicKey)
open PqxdhEd25519EufCma (pqMessage parsePqMessage)
open BeaconcryptCore.Refinement
open RegistrationBeaconInitExecutor
variable {Encoded : Type}

def Started (key : MlKem768PublicKey) (state : registration.BeaconInitState) : Prop :=
  absBytes state.started.message.pq_key = pqMessage key

def Signed (key : MlKem768PublicKey) (state : registration.BeaconInitState) : Prop :=
  (absBytes state.pq_key).drop 64 = pqMessage key

/-- An actual successful writer invocation and the exact signed PQ payload it received. -/
def PublishedKey (encode : registration.InitView → core.option.Option Encoded)
    (key : MlKem768PublicKey) (published : registration.PublishedBeaconInit Encoded) : Prop :=
  ∃ view, encode view = .Some published.encoded ∧
    (absBytes view.fields.pq_key).drop 64 = pqMessage key

attribute [local irreducible] RegistrationBeaconInitExecutor.begin
  registration.BeaconInitHash.resume

private theorem continue_support {Input : Type} (action : RustM Input)
    (next : Input → OracleComp Spec (RustM (Result Encoded)))
    (published : registration.PublishedBeaconInit Encoded)
    (supported : .ok (.Ok published) ∈ support (continueWith action next)) :
    ∃ value, action = .ok value ∧ .ok (.Ok published) ∈ support (next value) := by
  cases action <;> simp_all [continueWith]

private theorem started_validation (input : pqxdh.InitKex) (verified : pqxdh.VerifiedInitKex)
    (validated : pqxdh.validate_init_kex input = .ok (.Ok verified)) :
    absBytes input.pq_key = pqMessage (RegistrationRootInput.pqKey verified.beacon_pq_public_key) := by
  have parsed := ((PqxdhHeadlineBridges.validate_init_kex_bridge input).2.1 verified).mp validated
  simp only [PqxdhHeadlineBridges.parsedFields, PqxdhHeadlineBridges.parsedBytes,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at parsed
  obtain ⟨identity, _, prekey, _, oneTime, _, pq, pqParsed, result⟩ := parsed
  have same := congrArg (fun value => value.2.pqKey) result
  have pqResult : parsePqMessage (absBytes input.pq_key) =
      some (RegistrationRootInput.pqKey verified.beacon_pq_public_key) := by
    simpa only [PqxdhHeadlineBridges.typedVerified, RegistrationRootInput.pqKey] using
      pqParsed.trans (congrArg some same)
  exact (PqxdhEd25519EufCma.parsePqMessage_eq_some_iff _ _).mp pqResult

private theorem ed_started (key : MlKem768PublicKey)
    (pending : registration.BeaconEd25519Signing) (reply : RegistrationSigningShared.SignReply)
    (next : registration.BeaconEd25519Signing) (prior : Started key pending.state)
    (actual : pending.resume reply = .ok (.Ed25519SigningRequested next)) : Started key next.state := by
  obtain ⟨effect, resumed, progress⟩ := RegistrationSigning.ed_resume_refines pending reply
  have same := RustM.ok.inj (resumed.symm.trans actual)
  subst effect
  cases stage : pending.stage
  all_goals simp only [RegistrationSigning.EdReplyTransition, stage] at progress
  · exact (congrArg (Started key) progress.2.2.2).mpr prior
  · exact (congrArg (Started key) progress.2.2.2).mpr prior
  · exact progress.2.elim

private theorem ed_signed (key : MlKem768PublicKey)
    (pending : registration.BeaconEd25519Signing) (reply : RegistrationSigningShared.SignReply)
    (next : registration.BeaconInitHash) (prior : Started key pending.state)
    (actual : pending.resume reply = .ok (.HashRequested next)) : Signed key next.state := by
  obtain ⟨effect, resumed, progress⟩ := RegistrationSigning.ed_resume_refines pending reply
  have same := RustM.ok.inj (resumed.symm.trans actual)
  subst effect
  simp only [RegistrationSigning.EdReplyTransition] at progress
  obtain ⟨tail, stage, copied, _⟩ := progress
  cases reply with
  | none => exact tail.elim
  | some bytes =>
      simp only [RegistrationSigning.replyTailMatches, RegistrationSigning.signingMessageValues, stage] at tail
      simp only [Signed, absBytes, ← List.map_drop, copied, RegistrationSigning.replyValues, tail.2]
      exact prior

private theorem ready_key (encode : registration.InitView → core.option.Option Encoded)
    (key : MlKem768PublicKey) (pending : registration.BeaconInitReady)
    (published : registration.PublishedBeaconInit Encoded) (prior : Signed key pending.state)
    (supported : .ok (.Ok published) ∈ support (ready encode pending)) : PublishedKey encode key published := by
  obtain ⟨view, requested, returned⟩ := continue_support pending.message _ published supported
  have fields : view.fields.pq_key = pending.state.pq_key := by
    simp only [registration.BeaconInitReady.message, RegistrationSigningContinuations.retained_fields_exact,
      bind_tc_ok, RustM.ok.injEq] at requested
    cases requested
    rfl
  simp only [support_pure, Set.mem_singleton_iff] at returned
  cases encoded : encode view with
  | none =>
      rw [encoded,RegistrationSigningContinuations.failed_publication_preserves_fresh] at returned
      cases returned
  | some bytes =>
      obtain ⟨actual,ran,_control,_pin,_hash,_identity,_pre,_one,_pq,output⟩ :=
        RegistrationSigningContinuations.publication_retains_exact_request pending bytes
      have same : actual = published := by
        have current := returned
        rw [encoded] at current
        simpa using ran.symm.trans current.symm
      subst actual
      exact ⟨view,output ▸ encoded,by simpa only [fields,Signed] using prior⟩

private theorem hash_key (encode : registration.InitView → core.option.Option Encoded)
    (key : MlKem768PublicKey) (pending : registration.BeaconInitHash)
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
  exact ready_key encode key next published (retained ▸ prior) continued

private theorem ed_key (encode : registration.InitView → core.option.Option Encoded)
    (key : MlKem768PublicKey) (pending : registration.BeaconEd25519Signing)
    (published : registration.PublishedBeaconInit Encoded) (prior : Started key pending.state)
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
    | HashRequested next =>
        rw [actual] at continued
        exact hash_key encode key next published (ed_signed key pending reply next prior actual) continued
    | _ => rw [actual] at continued; simp at continued
termination_by edRank pending
decreasing_by exact ed_rank pending reply next actual

/-- Every successful actual outgoing controller encoded its original generated PQ input after the real Ed3, fingerprint, Init hash and ML-signing stages. -/
theorem begin_key (encode : registration.InitView → core.option.Option Encoded)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin)
    (published : registration.PublishedBeaconInit Encoded)
    (supported : .ok (.Ok published) ∈ support (begin encode control inputs coins pin)) :
    PublishedKey encode (RegistrationRootInput.pqKey inputs.pq_public_key) published := by
  unfold RegistrationBeaconInitExecutor.begin at supported
  obtain ⟨effect, actual, continued⟩ := continue_support
    (registration.begin_beacon_init control inputs coins pin) _ published supported
  obtain ⟨started, startedRun, validated, _, _⟩ := PqxdhSurface.beacon_start_validates control inputs coins
  obtain ⟨other, otherRun, beginRun⟩ := RegistrationSigningContinuations.begin_beacon_init_exact
    control inputs coins pin
  have same := RustM.ok.inj (startedRun.symm.trans otherRun)
  subst other
  rw [beginRun] at actual
  split_ifs at actual
  · cases actual; simp at continued
  · cases actual
    refine ed_key encode _ _ published ?_ continued
    exact started_validation _ _ validated

/-- Stateful interpretation retains the same successful writer receipt without any primitive-correctness or signing-origin assumption. -/
theorem simulated_key {State : Type} (implementation : QueryImpl Spec (StateT State ProbComp))
    (encode : registration.InitView → core.option.Option Encoded)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin)
    (published : registration.PublishedBeaconInit Encoded) (before after : State)
    (supported : (.ok (.Ok published), after) ∈ support
      ((simulateQ implementation (begin encode control inputs coins pin)).run before)) :
    PublishedKey encode (RegistrationRootInput.pqKey inputs.pq_public_key) published := by
  apply begin_key encode control inputs coins pin published
  apply OracleComp.support_simulateQ_run'_subset implementation (begin encode control inputs coins pin) before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst supported

/-- Actual successful publication and the explicit native four-field readback contract recover the same generated PQ field from public bytes. -/
theorem decoded_key (wire : RegistrationNativeWire.Wire) (readback : RegistrationNativeWire.InitReadBack wire)
    (key : MlKem768PublicKey) (published : registration.PublishedBeaconInit Pqxdh.Bytes)
    (receipt : PublishedKey wire.encodeInit key published) :
    ∃ packet, RegistrationNativeWire.readInit wire published.encoded = some packet ∧
      RegistrationNativeKemTarget.PacketKey packet key := by
  obtain ⟨view, written, payload⟩ := receipt
  exact ⟨RegistrationNativeWire.initPacket view, readback view published.encoded written, payload⟩

end BeaconcryptCore.Computational.RegistrationNativeKemPublication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemPublication.begin_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemPublication.begin_key

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemPublication.simulated_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemPublication.simulated_key

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemPublication.decoded_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemPublication.decoded_key
