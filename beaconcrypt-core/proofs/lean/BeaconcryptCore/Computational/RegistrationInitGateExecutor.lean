-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAuthenticationShared

/-!
The first two callbacks of the actual extracted Init executor use the shared transcript hash and the actual mandatory ML verification request. Successful progress to attached-key verification retains that exact digest, original packet and selected server pin. This is an execution theorem for the source controller, before the remaining Ed25519 and fingerprint gates.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationInitGateExecutor

open CtxRomAuth RegistrationAuthenticationExecutor
open BeaconcryptCore.Refinement.RegistrationAuthentication
open BeaconcryptCore.Refinement.RegistrationAuthenticationFlow (Event)

noncomputable def mldsaPhase (before : registration.InitHash) (digest : Std.Array Std.U8 64#usize) :
    registration.InitMldsaVerification :=
  Classical.choose (init_hash_success before digest)

theorem mldsa_phase_exact (before : registration.InitHash) (digest : Std.Array Std.U8 64#usize) :
    before.resume (.Some digest) = .ok (.MldsaVerificationRequested (mldsaPhase before digest)) ∧
      (mldsaPhase before digest).state.packet = before.packet ∧
      (mldsaPhase before digest).state.server_pin = before.server_pin ∧
      (mldsaPhase before digest).state.init_hash = digest ∧
      absBytes (mldsaPhase before digest).input = Pqxdh.TranscriptAuth.signatureInput .beacon (absBytes digest) :=
  Classical.choose_spec (init_hash_success before digest)

noncomputable def gatePhase (before : registration.InitHash) (digest : Std.Array Std.U8 64#usize)
    (verified : Bool) : registration.InitAuthentication :=
  Classical.choose (init_mldsa_exact (mldsaPhase before digest) verified)

theorem gate_phase_exact (before : registration.InitHash) (digest : Std.Array Std.U8 64#usize)
    (verified : Bool) :
    (mldsaPhase before digest).resume verified = .ok (gatePhase before digest verified) ∧
      initMldsaOutcome (mldsaPhase before digest) verified (gatePhase before digest verified) :=
  Classical.choose_spec (init_mldsa_exact (mldsaPhase before digest) verified)

def verification (verify : MldsaTranscriptAuth.Verify) (before : registration.InitHash) (digest : CtxDigest) : Bool :=
  verify (absBytes before.packet.mldsa_public_key) Pqxdh.TranscriptAuth.signingContext
    (Pqxdh.TranscriptAuth.signatureInput .beacon digest.toList) (absBytes before.packet.signature)

/-- The source's first two callbacks hash its actual request and verify that digest under its actual presented ML key. -/
theorem execute_gate {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (before : registration.InitHash) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (simulateQ (RegistrationAuthenticationShared.implementation crypto verify writer kdf)
      (execute 2 (.HashRequested before))).run state = (do
        let hashed ← (ctxRandomOracle ((), absBytes before.input)).run state.2
        let digest := RegistrationAuthenticationShared.digestArray hashed.1
        let verified := verification verify before hashed.1
        pure (.ok ([Event.hash (.Some digest), Event.mldsa verified], gatePhase before digest verified),
          (state.1, hashed.2))) := by
  obtain ⟨request, requested, bytes⟩ := init_hash_request before
  simp only [execute, step, continueWith, requested, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind, bind_assoc, pure_bind]
  rw [RegistrationAuthenticationShared.hash_exact, bind_map_left, bytes]
  refine bind_congr (fun ⟨digest, cache⟩ => ?_)
  have source := mldsa_phase_exact before (RegistrationAuthenticationShared.digestArray digest)
  simp only [source.1, edge, init_mldsa_request, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind, bind_assoc, pure_bind]
  rw [RegistrationAuthenticationShared.mldsa_exact, pure_bind]
  simp only [source.2.1, source.2.2.2.2, TranscriptAuthInputsRefinement.signing_context_abs,
    RegistrationAuthenticationShared.digest_array_bytes, verification,
    (gate_phase_exact before (RegistrationAuthenticationShared.digestArray digest) _).1]
  simp only [simulateQ_pure, StateT.run_pure, pure_bind]

/-- Reaching attached-key verification derives the mandatory ML success and retains the actual source hash receipt and owner. -/
theorem progress_receipt {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (before : registration.InitHash) (state after : RawCtxSharedPrimitive.SharedState Auxiliary)
    (events : List Event) (next : registration.InitEd25519Verification)
    (supported : (.ok (events, .Ed25519VerificationRequested next), after) ∈ support
      ((simulateQ (RegistrationAuthenticationShared.implementation crypto verify writer kdf)
        (execute 2 (.HashRequested before))).run state)) :
    ∃ digest, next.state.packet = before.packet ∧ next.state.server_pin = before.server_pin ∧
      next.state.init_hash = RegistrationAuthenticationShared.digestArray digest ∧ next.stage = .PqKey ∧
      verification verify before digest = true ∧ after.1 = state.1 ∧ state.2 ≤ after.2 ∧
      after.2 ((), absBytes before.input) = some digest := by
  rw [execute_gate, mem_support_bind_iff] at supported
  obtain ⟨⟨digest, cache⟩, queried, returned⟩ := supported
  simp only [support_pure, Set.mem_singleton_iff] at returned
  have resultSame := congrArg Prod.fst returned
  have afterSame : after = (state.1, cache) := congrArg Prod.snd returned
  simp only [RustM.ok.injEq, Prod.mk.injEq] at resultSame
  have source := mldsa_phase_exact before (RegistrationAuthenticationShared.digestArray digest)
  have gate := (gate_phase_exact before (RegistrationAuthenticationShared.digestArray digest)
    (verification verify before digest)).2
  rw [← resultSame.2] at gate
  simp only [initMldsaOutcome] at gate
  have cached := MldsaSharedAuthentication.query_cached (absBytes before.input) state.2 (digest, cache) queried
  exact ⟨digest,
    (congrArg (fun value => value.packet) gate.2.2.1).trans source.2.1,
    (congrArg (fun value => value.server_pin) gate.2.2.1).trans source.2.2.1,
    (congrArg (fun value => value.init_hash) gate.2.2.1).trans source.2.2.2.1,
    gate.2.2.2.1, gate.1, by rw [afterSame],
    by simpa only [afterSame] using cached.1, by simpa only [afterSame] using cached.2⟩

def trial (protectedKey : Bool) (before : registration.InitHash)
    (history : List MldsaTranscriptAuth.SigningCall) : MldsaTranscriptAuth.Trial :=
  ⟨absBytes before.packet.mldsa_public_key, protectedKey, history,
    ⟨.beacon, absBytes before.input⟩, absBytes before.packet.signature⟩

/-- Progress of the native Init executor yields the source-derived ordinary ML verification trial. -/
theorem accepted_trial {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (before : registration.InitHash) (state after : RawCtxSharedPrimitive.SharedState Auxiliary)
    (events : List Event) (next : registration.InitEd25519Verification)
    (supported : (.ok (events, .Ed25519VerificationRequested next), after) ∈ support
      ((simulateQ (RegistrationAuthenticationShared.implementation crypto verify writer kdf)
        (execute 2 (.HashRequested before))).run state))
    (protectedKey : Bool) (honest : protectedKey = true) (history : List MldsaTranscriptAuth.SigningCall) :
    MldsaTranscriptAuth.Accepted (MldsaSharedAuthentication.cacheHash after.2) verify
      (trial protectedKey before history) := by
  obtain ⟨digest, _, _, _, _, verified, _, _, cached⟩ :=
    progress_receipt crypto verify writer kdf before state after events next supported
  refine ⟨honest, ?_, ?_, ?_⟩
  · simpa only [trial, absBytes, List.length_map, Std.UScalar.ofNatCore_val_eq]
      using before.packet.mldsa_public_key.property
  · simpa only [trial, absBytes, List.length_map, Std.UScalar.ofNatCore_val_eq]
      using before.packet.signature.property
  · change verify (absBytes before.packet.mldsa_public_key) Pqxdh.TranscriptAuth.signingContext
      (Pqxdh.TranscriptAuth.signatureInput .beacon
        (MldsaSharedAuthentication.cacheHash after.2 (absBytes before.input)))
      (absBytes before.packet.signature) = true
    rw [MldsaSharedAuthentication.cache_hash_reconstruct after.2 _ digest cached]
    exact verified

/-- A native Init message absent from the frozen prior signing prefix exposes a fresh ML message or a collision between actual shared-cache queries. -/
theorem origin_split {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (before : registration.InitHash) (state after : RawCtxSharedPrimitive.SharedState Auxiliary)
    (events : List Event) (next : registration.InitEd25519Verification)
    (supported : (.ok (events, .Ed25519VerificationRequested next), after) ∈ support
      ((simulateQ (RegistrationAuthenticationShared.implementation crypto verify writer kdf)
        (execute 2 (.HashRequested before))).run state))
    (protectedKey : Bool) (honest : protectedKey = true) (history : List MldsaTranscriptAuth.SigningCall)
    (cachedHistory : MldsaSharedAuthentication.HistoryCached state.2 history)
    (absent : ¬ MldsaTranscriptAuth.Issued (trial protectedKey before history)) :
    MldsaTranscriptAuth.WeakForgery (MldsaSharedAuthentication.cacheHash after.2) verify
      (trial protectedKey before history) ∨ CacheHasCollision after.2 := by
  have accepted := accepted_trial crypto verify writer kdf before state after events next supported
    protectedKey honest history
  obtain ⟨digest, _, _, _, _, _, _, extension, cached⟩ :=
    progress_receipt crypto verify writer kdf before state after events next supported
  rcases MldsaTranscriptAuth.origin_failure_split _ _ _ ⟨accepted, absent⟩ with forgery | collision
  · exact Or.inl forgery
  · apply Or.inr
    apply MldsaSharedAuthentication.transcript_collision_cached after.2
      (trial protectedKey before history) ?_ ⟨digest, cached⟩ collision
    intro call member
    obtain ⟨value, receipt⟩ := cachedHistory call member
    exact ⟨value, extension receipt⟩

end BeaconcryptCore.Computational.RegistrationInitGateExecutor

/-- info: 'BeaconcryptCore.Computational.RegistrationInitGateExecutor.mldsa_phase_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationInitGateExecutor.mldsa_phase_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationInitGateExecutor.gate_phase_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationInitGateExecutor.gate_phase_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationInitGateExecutor.execute_gate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationInitGateExecutor.execute_gate

/-- info: 'BeaconcryptCore.Computational.RegistrationInitGateExecutor.progress_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationInitGateExecutor.progress_receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationInitGateExecutor.accepted_trial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationInitGateExecutor.accepted_trial

/-- info: 'BeaconcryptCore.Computational.RegistrationInitGateExecutor.origin_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationInitGateExecutor.origin_split
