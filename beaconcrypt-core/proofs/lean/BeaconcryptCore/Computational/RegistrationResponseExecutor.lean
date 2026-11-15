-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAuthenticationShared
import BeaconcryptCore.Refinement.RegistrationResponse

/-!
Executable response authentication uses the actual extracted begin/getter/resume operations. Its request hashes and ML verification use the same concrete callback interpreter as incoming Init authentication and all record hashes. Malformed input and optional hash failure preserve the actual terminal abort result and every reached primitive effect. No key-agreement or record-opening callback is invoked before the mandatory response signature gate.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.Computational.RegistrationResponseExecutor

open CtxRomAuth
open BeaconcryptCore.Refinement.RegistrationResponse

abbrev ResponseResult := core.result.Result registration.AuthenticatedResponse pqxdh.BeaconAborted

def continueResult {Input : Type} (result : RustM (core.result.Result Input pqxdh.BeaconAborted))
    (next : Input → OracleComp RegistrationAuthenticationExecutor.Spec (RustM ResponseResult)) :
    OracleComp RegistrationAuthenticationExecutor.Spec (RustM ResponseResult) :=
  match result with
  | .ok (.Ok value) => next value
  | .ok (.Err aborted) => pure (.ok (.Err aborted))
  | .fail error => pure (.fail error)
  | .div => pure .div

def begin (pending : registration.BeaconPending) (packet : core.option.Option registration.ResponsePacket) :
    OracleComp RegistrationAuthenticationExecutor.Spec (RustM ResponseResult) :=
  continueResult (registration.begin_response_authentication pending packet) fun hashState =>
    RegistrationAuthenticationExecutor.continueWith hashState.request fun hashRequest => do
      let digest ← RegistrationAuthenticationExecutor.Spec.query (.hash hashRequest)
      continueResult (hashState.resume digest) fun verificationState =>
        RegistrationAuthenticationExecutor.continueWith verificationState.request fun request => do
          let verified ← RegistrationAuthenticationExecutor.Spec.query (.mldsa request)
          continueResult (verificationState.resume verified) fun adState =>
            RegistrationAuthenticationExecutor.continueWith adState.request fun adRequest => do
              let adDigest ← RegistrationAuthenticationExecutor.Spec.query (.hash adRequest)
              pure (adState.resume adDigest)

noncomputable def execute {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (pending : registration.BeaconPending) (packet : core.option.Option registration.ResponsePacket) :=
  simulateQ (RegistrationAuthenticationShared.implementation crypto verify writer kdf) (begin pending packet)

def payload (pending : registration.BeaconPending) (packet : registration.ResponsePacket) : MldsaTranscriptAuth.Payload :=
  MldsaTranscriptAuth.responsePayload (absBytes pending.binding.init_hash)
    (TranscriptAuthRefinement.absResponse (responseFields packet))

def verification (verify : MldsaTranscriptAuth.Verify) (pending : registration.BeaconPending)
    (packet : registration.ResponsePacket) (digest : CtxDigest) : Bool :=
  verify (absBytes pending.binding.server_pin.public_key) Pqxdh.TranscriptAuth.signingContext
    (Pqxdh.TranscriptAuth.signatureInput .server digest.toList) (absBytes packet.signature)

/-- Public AD hash input selected after pinned verification. -/
def adPayload (pending : registration.BeaconPending) (packet : registration.ResponsePacket) : Pqxdh.Bytes :=
  BeaconcryptCore.Refinement.RegistrationAd.preimage pending.binding
    (BeaconcryptCore.Refinement.RegistrationAd.responseView packet.public)

noncomputable def completedBinding (pending : registration.BeaconPending) (digest : CtxDigest) :
    session.CompletedRegistrationBinding :=
  (BeaconcryptCore.Refinement.SessionBinding.complete_refines pending.binding
    (RegistrationAuthenticationShared.digestArray digest)).choose

theorem completedBinding_run (pending : registration.BeaconPending) (digest : CtxDigest) :
    pending.binding.complete (RegistrationAuthenticationShared.digestArray digest) =
      .ok (completedBinding pending digest) :=
  (BeaconcryptCore.Refinement.SessionBinding.complete_refines pending.binding
    (RegistrationAuthenticationShared.digestArray digest)).choose_spec.1

@[simp] theorem completedBinding_pin (pending : registration.BeaconPending) (digest : CtxDigest) :
    (completedBinding pending digest).server_pin = pending.binding.server_pin :=
  (BeaconcryptCore.Refinement.SessionBinding.complete_refines pending.binding
    (RegistrationAuthenticationShared.digestArray digest)).choose_spec.2.1

@[simp] theorem completedBinding_initHash (pending : registration.BeaconPending) (digest : CtxDigest) :
    (completedBinding pending digest).init_hash = pending.binding.init_hash :=
  (BeaconcryptCore.Refinement.SessionBinding.complete_refines pending.binding
    (RegistrationAuthenticationShared.digestArray digest)).choose_spec.2.2.1

@[simp] theorem completedBinding_digest (pending : registration.BeaconPending) (digest : CtxDigest) :
    (completedBinding pending digest).session_transcript_hash = RegistrationAuthenticationShared.digestArray digest :=
  (BeaconcryptCore.Refinement.SessionBinding.complete_refines pending.binding
    (RegistrationAuthenticationShared.digestArray digest)).choose_spec.2.2.2.2.1

@[simp] theorem completedBinding_consistent (pending : registration.BeaconPending) (digest : CtxDigest) :
    BeaconcryptCore.Refinement.SessionBinding.registrationConsistent (completedBinding pending digest) :=
  (BeaconcryptCore.Refinement.SessionBinding.complete_refines pending.binding
    (RegistrationAuthenticationShared.digestArray digest)).choose_spec.2.2.2.2.2

noncomputable def acceptedResponse (pending : registration.BeaconPending)
    (packet : registration.ResponsePacket) (digest : CtxDigest) : registration.AuthenticatedResponse :=
  ⟨pending.control, completedBinding pending digest, packet⟩

theorem ad_accept_exact (stage : registration.BeaconAdHash) (digest : CtxDigest) :
    stage.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) =
      .ok (.Ok (acceptedResponse stage.pending stage.packet digest)) := by
  simp only [registration.BeaconAdHash.resume, completedBinding_run, bind_tc_ok, acceptedResponse]

theorem begin_malformed (pending : registration.BeaconPending) :
    begin pending .None = pure (.ok (.Err (abortedState pending))) := by
  rfl

/-- Source order: response transcript hash, pinned signature verification, then the exact AD hash. False verification makes no AD request. -/
theorem execute_some {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (pending : registration.BeaconPending) (packet : registration.ResponsePacket)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (execute crypto verify writer kdf pending (.Some packet)).run state = (do
      let hashed ← (ctxRandomOracle ((), (payload pending packet).transcript)).run state.2
      if verification verify pending packet hashed.1 then
        let ad ← (ctxRandomOracle ((), adPayload pending packet)).run hashed.2
        pure (.ok (.Ok (acceptedResponse pending packet ad.1)), (state.1, ad.2))
      else pure (.ok (.Err (abortedState pending)), (state.1, hashed.2))) := by
  obtain ⟨hashState, started, samePending, samePacket, parts, requested, bytes⟩ :=
    begin_response_some_exact pending packet
  simp only [execute, begin, started, continueResult, RegistrationAuthenticationExecutor.continueWith,
    requested, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rw [RegistrationAuthenticationShared.hash_exact, bind_map_left, bytes]
  refine bind_congr (fun ⟨digest, cache⟩ => ?_)
  obtain ⟨verificationState, resumed, pendingSame, packetSame, request, requestRun,
    key, signature, context, contextBytes, inputBytes⟩ :=
    response_hash_some_exact hashState (RegistrationAuthenticationShared.digestArray digest)
  simp only [resumed, requestRun, simulateQ_bind, simulateQ_spec_query,
    simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rw [RegistrationAuthenticationShared.mldsa_exact, pure_bind]
  have verdictEq : verify (absBytes request.public_key) (absBytes request.context)
      (absBytes request.input) (absBytes request.signature) = verification verify pending packet digest := by
    simp only [key, signature, contextBytes, inputBytes, RegistrationAuthenticationShared.digest_array_bytes,
      samePending, samePacket, verification]
  rw [verdictEq]
  obtain ⟨adState, gate, adPending, adPacket, adInput⟩ :=
    response_mldsa_gate_exact verificationState (verification verify pending packet digest)
  have verificationPending := pendingSame.trans samePending
  have verificationPacket := packetSame.trans samePacket
  have retainedPending := adPending.trans verificationPending
  have retainedPacket := adPacket.trans verificationPacket
  have adAddress : absBytes adState.input = adPayload pending packet := by
    simpa only [adPayload, verificationPending, verificationPacket] using adInput
  by_cases verified : verification verify pending packet digest = true
  · simp only [verified, ite_true] at gate ⊢
    simp only [gate, continueResult, RegistrationAuthenticationExecutor.continueWith,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    obtain ⟨adRequest, adRequested, adBytes⟩ := response_ad_hash_request_exact adState
    simp only [adRequested, RegistrationAuthenticationExecutor.continueWith,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [RegistrationAuthenticationShared.hash_exact, bind_map_left, adBytes, adAddress]
    refine bind_congr (fun ⟨adDigest, adCache⟩ => ?_)
    simp only [simulateQ_pure, StateT.run_pure, ad_accept_exact,
      retainedPending, retainedPacket]
  · have declined : verification verify pending packet digest = false := Bool.eq_false_iff.mpr verified
    simp only [declined, Bool.false_eq_true, ite_false] at gate ⊢
    simp only [gate, continueResult, simulateQ_pure, StateT.run_pure,
      verificationPending]

/-- The accepted response is completed by an actual second hash, while the signature transcript receipt remains in the extended shared cache. -/
theorem accepted_ad_receipt {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (pending : registration.BeaconPending) (packet : registration.ResponsePacket)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary)
    (authenticated : registration.AuthenticatedResponse)
    (supported : (.ok (.Ok authenticated), after) ∈ support
      ((execute crypto verify writer kdf pending (.Some packet)).run before)) :
    ∃ digest adDigest, authenticated = acceptedResponse pending packet adDigest ∧
      verification verify pending packet digest = true ∧ after.1 = before.1 ∧
      before.2 ≤ after.2 ∧ after.2 ((), (payload pending packet).transcript) = some digest ∧
      after.2 ((), adPayload pending packet) = some adDigest := by
  rw [execute_some, mem_support_bind_iff] at supported
  obtain ⟨⟨digest, cache⟩, queried, returned⟩ := supported
  by_cases verified : verification verify pending packet digest = true
  · simp only [verified, ite_true, mem_support_bind_iff] at returned
    obtain ⟨⟨adDigest, adCache⟩, adQueried, returned⟩ := returned
    simp only [support_pure, Set.mem_singleton_iff] at returned
    have resultSame := congrArg Prod.fst returned
    have afterSame : after = (before.1, adCache) := congrArg Prod.snd returned
    simp only [RustM.ok.injEq, core.result.Result.Ok.injEq] at resultSame
    have first := MldsaSharedAuthentication.query_cached (payload pending packet).transcript
      before.2 (digest, cache) queried
    have second := MldsaSharedAuthentication.query_cached (adPayload pending packet)
      cache (adDigest, adCache) adQueried
    exact ⟨digest, adDigest, resultSame, verified, by rw [afterSame],
      by simpa only [afterSame] using first.1.trans second.1,
      by simpa only [afterSame] using second.1 first.2,
      by simpa only [afterSame] using second.2⟩
  · simp only [verified, ite_false, support_pure, Set.mem_singleton_iff] at returned
    have impossible := congrArg Prod.fst returned
    simp only [RustM.ok.injEq, reduceCtorEq] at impossible

/-- Signature-origin callers retain the original receipt interface; the AD digest is an actual reached continuation witness. -/
theorem accepted_receipt {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (pending : registration.BeaconPending) (packet : registration.ResponsePacket)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary)
    (authenticated : registration.AuthenticatedResponse)
    (supported : (.ok (.Ok authenticated), after) ∈ support
      ((execute crypto verify writer kdf pending (.Some packet)).run before)) :
    ∃ digest, (∃ adDigest, authenticated = acceptedResponse pending packet adDigest) ∧
      verification verify pending packet digest = true ∧ after.1 = before.1 ∧
      before.2 ≤ after.2 ∧ after.2 ((), (payload pending packet).transcript) = some digest := by
  obtain ⟨digest, adDigest, same, verified, state, extension, signatureCached, _adCached⟩ :=
    accepted_ad_receipt crypto verify writer kdf pending packet before after authenticated supported
  exact ⟨digest, ⟨adDigest, same⟩, verified, state, extension, signatureCached⟩

def trial (protectedKey : Bool) (pending : registration.BeaconPending)
    (packet : registration.ResponsePacket) (history : List MldsaTranscriptAuth.SigningCall) :
    MldsaTranscriptAuth.Trial :=
  ⟨absBytes pending.binding.server_pin.public_key, protectedKey, history,
    payload pending packet, absBytes packet.signature⟩

/-- Actual native acceptance supplies the ordinary ML unforgeability experiment with source-derived operands and the shared-cache digest. -/
theorem accepted_trial {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (pending : registration.BeaconPending) (packet : registration.ResponsePacket)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary)
    (authenticated : registration.AuthenticatedResponse)
    (supported : (.ok (.Ok authenticated), after) ∈ support
      ((execute crypto verify writer kdf pending (.Some packet)).run before))
    (protectedKey : Bool) (honest : protectedKey = true) (history : List MldsaTranscriptAuth.SigningCall) :
    MldsaTranscriptAuth.Accepted (MldsaSharedAuthentication.cacheHash after.2) verify
      (trial protectedKey pending packet history) := by
  obtain ⟨digest, _, verified, _, _, cached⟩ :=
    accepted_receipt crypto verify writer kdf pending packet before after authenticated supported
  refine ⟨honest, ?_, ?_, ?_⟩
  · simpa only [trial, absBytes, List.length_map, Std.UScalar.ofNatCore_val_eq]
      using pending.binding.server_pin.public_key.property
  · simpa only [trial, absBytes, List.length_map, Std.UScalar.ofNatCore_val_eq]
      using packet.signature.property
  · change verify (absBytes pending.binding.server_pin.public_key) Pqxdh.TranscriptAuth.signingContext
      (Pqxdh.TranscriptAuth.signatureInput .server
        (MldsaSharedAuthentication.cacheHash after.2 (payload pending packet).transcript))
      (absBytes packet.signature) = true
    rw [MldsaSharedAuthentication.cache_hash_reconstruct after.2 _ digest cached]
    exact verified

/-- A source-native accepted response absent from the retained signing prefix exposes a fresh ML message or a collision between actual shared-cache queries. -/
theorem origin_split {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (pending : registration.BeaconPending) (packet : registration.ResponsePacket)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary)
    (authenticated : registration.AuthenticatedResponse)
    (supported : (.ok (.Ok authenticated), after) ∈ support
      ((execute crypto verify writer kdf pending (.Some packet)).run before))
    (protectedKey : Bool) (honest : protectedKey = true) (history : List MldsaTranscriptAuth.SigningCall)
    (cachedHistory : MldsaSharedAuthentication.HistoryCached before.2 history)
    (absent : ¬ MldsaTranscriptAuth.Issued (trial protectedKey pending packet history)) :
    MldsaTranscriptAuth.WeakForgery (MldsaSharedAuthentication.cacheHash after.2) verify
      (trial protectedKey pending packet history) ∨ CacheHasCollision after.2 := by
  have accepted := accepted_trial crypto verify writer kdf pending packet before after authenticated
    supported protectedKey honest history
  obtain ⟨digest, _, _, _, extension, cached⟩ :=
    accepted_receipt crypto verify writer kdf pending packet before after authenticated supported
  rcases MldsaTranscriptAuth.origin_failure_split _ _ _ ⟨accepted, absent⟩ with forgery | collision
  · exact Or.inl forgery
  · apply Or.inr
    apply MldsaSharedAuthentication.transcript_collision_cached after.2
      (trial protectedKey pending packet history) ?_ ⟨digest, cached⟩ collision
    intro call member
    obtain ⟨value, receipt⟩ := cachedHistory call member
    exact ⟨value, extension receipt⟩

end BeaconcryptCore.Computational.RegistrationResponseExecutor

/-- info: 'BeaconcryptCore.Computational.RegistrationResponseExecutor.begin_malformed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationResponseExecutor.begin_malformed

/-- info: 'BeaconcryptCore.Computational.RegistrationResponseExecutor.execute_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationResponseExecutor.execute_some

/-- info: 'BeaconcryptCore.Computational.RegistrationResponseExecutor.accepted_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationResponseExecutor.accepted_receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationResponseExecutor.accepted_trial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationResponseExecutor.accepted_trial

/-- info: 'BeaconcryptCore.Computational.RegistrationResponseExecutor.origin_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationResponseExecutor.origin_split

/-- info: 'BeaconcryptCore.Computational.RegistrationResponseExecutor.completedBinding_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationResponseExecutor.completedBinding_run

/-- info: 'BeaconcryptCore.Computational.RegistrationResponseExecutor.completedBinding_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationResponseExecutor.completedBinding_pin

/-- info: 'BeaconcryptCore.Computational.RegistrationResponseExecutor.completedBinding_initHash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationResponseExecutor.completedBinding_initHash

/-- info: 'BeaconcryptCore.Computational.RegistrationResponseExecutor.completedBinding_digest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationResponseExecutor.completedBinding_digest

/-- info: 'BeaconcryptCore.Computational.RegistrationResponseExecutor.completedBinding_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationResponseExecutor.completedBinding_consistent

/-- info: 'BeaconcryptCore.Computational.RegistrationResponseExecutor.ad_accept_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationResponseExecutor.ad_accept_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationResponseExecutor.accepted_ad_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationResponseExecutor.accepted_ad_receipt
