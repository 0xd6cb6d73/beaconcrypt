-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAuthenticationInterpretation
import BeaconcryptCore.Computational.RegistrationInitGateExecutor
import BeaconcryptCore.Refinement.RegistrationAuthenticationMetadata

/-!
The actual four-callback Init executor retains its selected Server pin and complete request-hash cache receipt. Acceptance owns the exact signed request buffers; final AD does not exist until the response-dependent hash continuation. Beacon ML credential origin and fingerprint receipts are retired.
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
      initial.fields = ownedFields packet ∧ initial.server_pin = pin ∧ absBytes initial.input = initPreimage pin packet ∧
      (.ok (events, final), after) ∈ support
        ((simulateQ (RegistrationAuthenticationShared.implementation crypto verify writer kdf)
          (execute 5 (.HashRequested initial))).run before) := by
  unfold RegistrationAuthenticationShared.begin RegistrationAuthenticationExecutor.begin at supported
  obtain ⟨initial, started, executed⟩ := RegistrationAuthenticationInterpretation.continueWith_support
    (RegistrationAuthenticationShared.implementation crypto verify writer kdf)
    (registration.begin_init_authentication pin packet) (execute 5) (events, final) before after supported
  obtain ⟨source, sourceStarted, samePacket, samePin, preimage⟩ := begin_init_exact pin packet
  have same : initial = .HashRequested source := RustM.ok.inj (started.symm.trans sourceStarted)
  exact ⟨source, sourceStarted, samePacket, samePin, preimage, same ▸ executed⟩

/-- Actual whole authentication retains the selected classical binding and ML public key; the exact pin is retained. -/
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
  obtain ⟨initial, _, _, _, preimage, executed⟩ :=
    begin_parts crypto verify writer kdf pin packet before after events (.Accepted authenticated) supported
  have execution := simulated_begin_sound (RegistrationAuthenticationShared.implementation crypto verify writer kdf)
    pin packet events (.Accepted authenticated) before after supported
  obtain ⟨_, _, tail, recorded⟩ := accepted_request_provenance pin packet events authenticated execution
  have trace := RegistrationAuthenticationInterpretation.execute_trace
    (RegistrationAuthenticationShared.implementation crypto verify writer kdf) 5 (.HashRequested initial)
    events (.Accepted authenticated) before after executed
  rw [recorded] at trace
  cases trace with
  | cons first rest =>
      obtain ⟨digest, sameEvent, _, cached⟩ := RegistrationInitGateExecutor.hash_edge_receipt
        crypto verify writer kdf initial _ _ _ _ first
      have digestSame : authenticated.binding.init_hash = RegistrationAuthenticationShared.digestArray digest := by
        simpa only [Event.hash.injEq, core.option.Option.Some, Option.some.injEq] using sameEvent
      have extension := program_cache_persists crypto verify writer kdf _ _ _
        (RegistrationAuthenticationInterpretation.trace_execute _ rest)
      have receipt : after.2 ((), initPreimage pin packet) = some digest := by
        rw [← preimage]
        exact extension cached
      rw [MldsaSharedAuthentication.cache_hash_reconstruct after.2 _ digest receipt, digestSame,
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
