-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAuthenticationInterpretation
import BeaconcryptCore.Computational.RegistrationInitGateExecutor
import BeaconcryptCore.Computational.RegistrationFingerprintExecutor
import BeaconcryptCore.Refinement.RegistrationAuthenticationMetadata

/-!
The complete actual Init executor is joined to its shared primitive interpretation. Every accepted run is cut at its reached source capabilities, so the first mandatory ML gate and the final populated AD retain the actual callback cache. Neither an independent authentication transcript nor an initialization simulation is an input to these statements.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 2048

namespace BeaconcryptCore.Computational.RegistrationAuthenticationNative

open CtxRomAuth RegistrationAuthenticationExecutor
open BeaconcryptCore.Refinement.RegistrationAuthentication
open BeaconcryptCore.Refinement.RegistrationAuthenticationFlow

attribute [local irreducible] execute registration.begin_init_authentication

private theorem metadata_suffix (pin : session.ServerAuthenticationPin) (leading : List Event)
    {start final : registration.InitAuthentication} {events : List Event}
    (run : Run start events final)
    (initial : BeaconcryptCore.Refinement.RegistrationAuthenticationMetadata.Metadata pin leading start) :
    BeaconcryptCore.Refinement.RegistrationAuthenticationMetadata.Metadata pin (leading ++ events) final := by
  induction run with
  | refl => simpa only [List.append_nil] using initial
  | step previous edge ih =>
      simpa only [List.append_assoc] using
        BeaconcryptCore.Refinement.RegistrationAuthenticationMetadata.step_metadata pin _ _ _ _ ih edge

theorem callback_cache_persists {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (query : RegistrationAuthenticationExecutor.Spec.Domain)
    (before : RawCtxSharedPrimitive.SharedState Auxiliary)
    (result : RegistrationAuthenticationExecutor.Spec.Range query × RawCtxSharedPrimitive.SharedState Auxiliary)
    (supported : result ∈ support
      ((RegistrationAuthenticationShared.implementation crypto verify writer kdf query).run before)) :
    before.2 ≤ result.2.2 := by
  cases query with
  | hash request =>
      exact (RegistrationAuthenticationShared.hash_reply_cached crypto verify writer kdf request before
        result.2 result.1 supported).choose_spec.2.2.1
  | mldsa request =>
      rw [RegistrationAuthenticationShared.mldsa_exact, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact le_refl _
  | ed25519 request =>
      rw [RegistrationAuthenticationShared.ed25519_exact, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact le_refl _

/-- All actual authentication callbacks preserve the reached shared cache, including continuations that reject or fail. -/
theorem program_cache_persists {Auxiliary Result : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (work : OracleComp RegistrationAuthenticationExecutor.Spec Result)
    (before : RawCtxSharedPrimitive.SharedState Auxiliary)
    (result : Result × RawCtxSharedPrimitive.SharedState Auxiliary)
    (supported : result ∈ support
      ((simulateQ (RegistrationAuthenticationShared.implementation crypto verify writer kdf) work).run before)) :
    before.2 ≤ result.2.2 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact le_refl _
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply, middle⟩, first, rest⟩ := supported
      exact (callback_cache_persists crypto verify writer kdf query before (reply, middle) first).trans
        (ih reply middle rest)

/-- The full shared execution starts at the actual native request builder, with its exact packet, pin and transcript bytes. -/
theorem begin_parts {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary) (events : List Event)
    (final : registration.InitAuthentication)
    (supported : (.ok (events, final), after) ∈ support
      ((RegistrationAuthenticationShared.begin crypto verify writer kdf pin packet).run before)) :
    ∃ initial : registration.InitHash,
      registration.begin_init_authentication pin packet = .ok (.HashRequested initial) ∧
      initial.packet = packet ∧ initial.server_pin = pin ∧ absBytes initial.input = initPreimage pin packet ∧
      (.ok (events, final), after) ∈ support
        ((simulateQ (RegistrationAuthenticationShared.implementation crypto verify writer kdf)
          (execute 8 (.HashRequested initial))).run before) := by
  unfold RegistrationAuthenticationShared.begin RegistrationAuthenticationExecutor.begin at supported
  obtain ⟨initial, started, executed⟩ := RegistrationAuthenticationInterpretation.continueWith_support
    (RegistrationAuthenticationShared.implementation crypto verify writer kdf)
    (registration.begin_init_authentication pin packet) (execute 8) (events, final) before after supported
  obtain ⟨source, sourceStarted, samePacket, samePin, preimage⟩ := begin_init_exact pin packet
  have same : initial = .HashRequested source := RustM.ok.inj (started.symm.trans sourceStarted)
  exact ⟨source, sourceStarted, samePacket, samePin, preimage, same ▸ executed⟩

/-- Every complete accepted Init supplies actual shared-cache fingerprint receipts for the ML keys carried by its source-owned binding and original packet. -/
theorem begin_binding_cached {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary) (events : List Event)
    (authenticated : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((RegistrationAuthenticationShared.begin crypto verify writer kdf pin packet).run before)) :
    RegistrationFingerprintExecutor.BindingCached authenticated.binding (absBytes packet.mldsa_public_key) after.2 := by
  obtain ⟨initial, started, samePacket, _, _, executed⟩ :=
    begin_parts crypto verify writer kdf pin packet before after events (.Accepted authenticated) supported
  have execution : Executes pin packet events (.Accepted authenticated) :=
    simulated_begin_sound (RegistrationAuthenticationShared.implementation crypto verify writer kdf)
      pin packet events (.Accepted authenticated) before after supported
  obtain ⟨digest, pq, pre, oneTime, serverFp, beaconFp, eventsSame, _⟩ :=
    accepted_requires_gates pin packet events authenticated execution
  rw [eventsSame] at executed
  let leading := [Event.hash (.Some digest), .mldsa true, .ed25519 .PqKey (.Some pq),
    .ed25519 .PreKey (.Some pre), .ed25519 .OneTimeKey (.Some oneTime)]
  let tail := [Event.serverFingerprint (.Some serverFp), .beaconFingerprint (.Some beaconFp)]
  obtain ⟨middle, primitive, leadingSupported, tailSupported⟩ :=
    RegistrationAuthenticationInterpretation.execute_tail_support
      (RegistrationAuthenticationShared.implementation crypto verify writer kdf) 8 (.HashRequested initial)
      leading tail (.Accepted authenticated) before after executed
  have leadingOpen : .ok (leading, middle) ∈ support (execute leading.length (.HashRequested initial)) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationAuthenticationShared.implementation crypto verify writer kdf) _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst leadingSupported
  have reached := run_preserves_prefix
    (execute_sound leading.length (.HashRequested initial) leading middle leadingOpen)
    (Prefix.hash initial samePacket)
  dsimp only [leading] at reached
  cases reached with
  | serverFingerprint source _ _ _ _ packetSame _ _ _ =>
      have receipts := RegistrationFingerprintExecutor.fingerprint_receipts crypto verify writer kdf 0 source
        primitive after tail authenticated tailSupported
      rw [packetSame] at receipts
      exact receipts.2.2.2.2.2.1
  | rejected =>
      simp [execute, step, continueWith, tail] at tailSupported
  | accepted _ _ gates =>
      obtain ⟨_, _, _, _, _, _, impossible, _⟩ := gates
      have lengths := congrArg List.length impossible
      simp at lengths

/-- Complete native Init acceptance reaches its actual mandatory ML verification under the same retained primitive interpretation. -/
theorem begin_gate_cut {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary) (events : List Event)
    (authenticated : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((RegistrationAuthenticationShared.begin crypto verify writer kdf pin packet).run before)) :
    ∃ (initial : registration.InitHash) (primitive : RawCtxSharedPrimitive.SharedState Auxiliary)
      (next : registration.InitEd25519Verification) (leading : List Event),
      initial.packet = packet ∧ initial.server_pin = pin ∧ absBytes initial.input = initPreimage pin packet ∧
      (.ok (leading, .Ed25519VerificationRequested next), primitive) ∈ support
        ((simulateQ (RegistrationAuthenticationShared.implementation crypto verify writer kdf)
          (execute 2 (.HashRequested initial))).run before) ∧ primitive.2 ≤ after.2 ∧
      next.state.init_hash = authenticated.binding.init_hash := by
  obtain ⟨initial, started, samePacket, samePin, preimage, executed⟩ :=
    begin_parts crypto verify writer kdf pin packet before after events (.Accepted authenticated) supported
  have execution : Executes pin packet events (.Accepted authenticated) :=
    simulated_begin_sound (RegistrationAuthenticationShared.implementation crypto verify writer kdf)
      pin packet events (.Accepted authenticated) before after supported
  obtain ⟨digest, pq, pre, oneTime, serverFp, beaconFp, eventsSame, _⟩ :=
    accepted_requires_gates pin packet events authenticated execution
  rw [eventsSame] at executed
  let leading := [Event.hash (.Some digest), .mldsa true]
  let tail := [Event.ed25519 .PqKey (.Some pq), .ed25519 .PreKey (.Some pre),
    .ed25519 .OneTimeKey (.Some oneTime), .serverFingerprint (.Some serverFp),
    .beaconFingerprint (.Some beaconFp)]
  obtain ⟨middle, primitive, leadingSupported, tailSupported⟩ :=
    RegistrationAuthenticationInterpretation.execute_tail_support
      (RegistrationAuthenticationShared.implementation crypto verify writer kdf) 8 (.HashRequested initial)
      leading tail (.Accepted authenticated) before after executed
  have leadingOpen : .ok (leading, middle) ∈ support (execute leading.length (.HashRequested initial)) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationAuthenticationShared.implementation crypto verify writer kdf) _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst leadingSupported
  have reached := run_preserves_prefix
    (execute_sound leading.length (.HashRequested initial) leading middle leadingOpen)
    (Prefix.hash initial samePacket)
  dsimp only [leading] at reached
  cases reached with
  | pq source _ _ _ =>
      have tailOpen : .ok (tail, .Accepted authenticated) ∈ support
          (execute tail.length (.Ed25519VerificationRequested source)) := by
        apply OracleComp.support_simulateQ_run'_subset
          (RegistrationAuthenticationShared.implementation crypto verify writer kdf) _ primitive
        rw [StateT.run'_eq, support_map]
        exact Set.mem_image_of_mem Prod.fst tailSupported
      have retained := metadata_suffix source.state.server_pin [Event.hash (.Some source.state.init_hash)]
        (execute_sound tail.length (.Ed25519VerificationRequested source) tail (.Accepted authenticated) tailOpen)
        (show BeaconcryptCore.Refinement.RegistrationAuthenticationMetadata.Metadata source.state.server_pin
          [Event.hash (.Some source.state.init_hash)] (.Ed25519VerificationRequested source) from
            ⟨⟨rfl, rfl⟩, rfl⟩)
      have sameDigest : source.state.init_hash = authenticated.binding.init_hash := by
        simpa only [BeaconcryptCore.Refinement.RegistrationAuthenticationMetadata.Metadata,
          List.cons_append, List.nil_append, List.head?_cons, Option.some.injEq, Event.hash.injEq,
          core.option.Option.Some] using retained.2
      exact ⟨initial, primitive, source, leading, samePacket, samePin, preimage, leadingSupported,
        program_cache_persists crypto verify writer kdf _ primitive _ tailSupported, sameDigest⟩
  | rejected =>
      simp [execute, step, continueWith, tail] at tailSupported
  | accepted _ _ gates =>
      obtain ⟨_, _, _, _, _, _, impossible, _⟩ := gates
      have lengths := congrArg List.length impossible
      simp at lengths

/-- Complete Init acceptance supplies the actual request verification verdict and its retained shared-cache transcript digest. -/
theorem begin_gate_receipt {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary) (events : List Event)
    (authenticated : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((RegistrationAuthenticationShared.begin crypto verify writer kdf pin packet).run before)) :
    ∃ digest, verify (absBytes packet.mldsa_public_key) Pqxdh.TranscriptAuth.signingContext
        (Pqxdh.TranscriptAuth.signatureInput .beacon digest.toList) (absBytes packet.signature) = true ∧
      after.2 ((), initPreimage pin packet) = some digest ∧ before.2 ≤ after.2 ∧
      authenticated.binding.init_hash = RegistrationAuthenticationShared.digestArray digest := by
  obtain ⟨initial, primitive, next, leading, samePacket, _, preimage, executed, extension, sameDigest⟩ :=
    begin_gate_cut crypto verify writer kdf pin packet before after events authenticated supported
  obtain ⟨digest, _, _, hashed, _, verified, _, previous, cached⟩ :=
    RegistrationInitGateExecutor.progress_receipt crypto verify writer kdf initial before primitive leading next executed
  refine ⟨digest, ?_, ?_, previous.trans extension, sameDigest.symm.trans hashed⟩
  · simpa only [RegistrationInitGateExecutor.verification, samePacket] using verified
  · rw [← preimage]
    exact extension cached

def trial (protectedKey : Bool) (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (history : List MldsaTranscriptAuth.SigningCall) : MldsaTranscriptAuth.Trial :=
  ⟨absBytes packet.mldsa_public_key, protectedKey, history,
    ⟨.beacon, initPreimage pin packet⟩, absBytes packet.signature⟩

/-- The complete accepted native Init, including every later Ed and fingerprint gate, yields an actual ordinary ML verification trial. -/
theorem begin_accepted_trial {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary) (events : List Event)
    (authenticated : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((RegistrationAuthenticationShared.begin crypto verify writer kdf pin packet).run before))
    (protectedKey : Bool) (honest : protectedKey = true) (history : List MldsaTranscriptAuth.SigningCall) :
    MldsaTranscriptAuth.Accepted (MldsaSharedAuthentication.cacheHash after.2) verify
      (trial protectedKey pin packet history) := by
  obtain ⟨digest, verified, cached, _, _⟩ :=
    begin_gate_receipt crypto verify writer kdf pin packet before after events authenticated supported
  refine ⟨honest, ?_, ?_, ?_⟩
  · simpa only [trial, absBytes, List.length_map, Std.UScalar.ofNatCore_val_eq]
      using packet.mldsa_public_key.property
  · simpa only [trial, absBytes, List.length_map, Std.UScalar.ofNatCore_val_eq]
      using packet.signature.property
  · change verify (absBytes packet.mldsa_public_key) Pqxdh.TranscriptAuth.signingContext
      (Pqxdh.TranscriptAuth.signatureInput .beacon
        (MldsaSharedAuthentication.cacheHash after.2 (initPreimage pin packet)))
      (absBytes packet.signature) = true
    rw [MldsaSharedAuthentication.cache_hash_reconstruct after.2 _ digest cached]
    exact verified

/-- Origin failure of a complete native Init exposes a fresh ML message or a collision between actual queries in the common record/authentication cache. -/
theorem begin_origin_split {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary) (events : List Event)
    (authenticated : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((RegistrationAuthenticationShared.begin crypto verify writer kdf pin packet).run before))
    (protectedKey : Bool) (honest : protectedKey = true) (history : List MldsaTranscriptAuth.SigningCall)
    (cachedHistory : MldsaSharedAuthentication.HistoryCached before.2 history)
    (absent : ¬ MldsaTranscriptAuth.Issued (trial protectedKey pin packet history)) :
    MldsaTranscriptAuth.WeakForgery (MldsaSharedAuthentication.cacheHash after.2) verify
      (trial protectedKey pin packet history) ∨ CacheHasCollision after.2 := by
  have accepted := begin_accepted_trial crypto verify writer kdf pin packet before after events authenticated
    supported protectedKey honest history
  obtain ⟨digest, _, cached, extension, _⟩ :=
    begin_gate_receipt crypto verify writer kdf pin packet before after events authenticated supported
  rcases MldsaTranscriptAuth.origin_failure_split _ _ _ ⟨accepted, absent⟩ with forgery | collision
  · exact Or.inl forgery
  · apply Or.inr
    apply MldsaSharedAuthentication.transcript_collision_cached after.2
      (trial protectedKey pin packet history) ?_ ⟨digest, cached⟩ collision
    intro call member
    obtain ⟨value, receipt⟩ := cachedHistory call member
    exact ⟨value, extension receipt⟩

/-- The record AD returned by the complete source executor is populated by the actual common-cache ML fingerprints. -/
theorem begin_associated_data {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary) (events : List Event)
    (authenticated : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((RegistrationAuthenticationShared.begin crypto verify writer kdf pin packet).run before)) :
    absBytes authenticated.binding.associated_data =
      BeaconcryptCore.Refinement.SessionBinding.boundAssociatedData
        (absBytes authenticated.binding.server_pin.binding.identity_public_key)
        (absBytes authenticated.binding.beacon_identity_public_key)
        (MldsaSharedAuthentication.cacheHash after.2 (absBytes authenticated.binding.server_pin.public_key))
        (MldsaSharedAuthentication.cacheHash after.2 (absBytes packet.mldsa_public_key)) :=
  RegistrationFingerprintExecutor.binding_associated_data _ _ _
    (begin_binding_cached crypto verify writer kdf pin packet before after events authenticated supported)

/-- Actual whole authentication retains the selected classical binding and ML public key; only its fingerprint slot is recomputed. -/
theorem begin_selected_pin {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary) (events : List Event)
    (authenticated : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((RegistrationAuthenticationShared.begin crypto verify writer kdf pin packet).run before)) :
    authenticated.binding.server_pin.binding = pin.binding ∧
      authenticated.binding.server_pin.public_key = pin.public_key := by
  have fields := BeaconcryptCore.Refinement.RegistrationAuthenticationMetadata.accepted_metadata
    pin packet events authenticated
      (simulated_begin_sound (RegistrationAuthenticationShared.implementation crypto verify writer kdf)
        pin packet events (.Accepted authenticated) before after supported)
  exact ⟨fields.1, fields.2.1⟩

/-- The request digest retained for response authentication and key agreement is the actual common-cache hash of the complete initial transcript. -/
theorem begin_init_hash {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary) (events : List Event)
    (authenticated : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((RegistrationAuthenticationShared.begin crypto verify writer kdf pin packet).run before)) :
    MldsaSharedAuthentication.cacheHash after.2 (initPreimage pin packet) =
      absBytes authenticated.binding.init_hash := by
  obtain ⟨digest, _, cached, _, sameDigest⟩ :=
    begin_gate_receipt crypto verify writer kdf pin packet before after events authenticated supported
  rw [MldsaSharedAuthentication.cache_hash_reconstruct after.2 _ digest cached, sameDigest,
    RegistrationAuthenticationShared.digest_array_bytes]

end BeaconcryptCore.Computational.RegistrationAuthenticationNative

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationNative.callback_cache_persists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationNative.callback_cache_persists

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationNative.program_cache_persists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationNative.program_cache_persists

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationNative.begin_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationNative.begin_parts

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationNative.begin_binding_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationNative.begin_binding_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationNative.begin_gate_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationNative.begin_gate_cut

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationNative.begin_gate_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationNative.begin_gate_receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationNative.begin_accepted_trial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationNative.begin_accepted_trial

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationNative.begin_origin_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationNative.begin_origin_split

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationNative.begin_associated_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationNative.begin_associated_data

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationNative.begin_selected_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationNative.begin_selected_pin

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationNative.begin_init_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationNative.begin_init_hash
