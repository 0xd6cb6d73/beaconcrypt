-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhServerAuthRootProvenance
import BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl

/-!
# Transcript-hash cache receipts along source paths

The generic Server-authentication game hashes the registration transcript with the shared lazy BLAKE2b oracle `CtxRomAuth.ctxRandomOracle` on the cache `GameState.ctx` (design §4.3). The game-level identity argument (`PqxdhServerAuthTranscriptIdentity.path_identity`) compares the digests that the Server's build and the Beacon's finish read, at the final cache of one run. This module supplies the cache facts it needs:

- `query_cached`: one oracle read leaves its digest at the query and only extends the cache.
- `afterRoot_ctx_grows`: the Beacon's post-root native tail only extends the cache.
- `path_ctx_mono`: along every `PqxdhServerAuthRootOccurrences.Path`, cache entries persist (from `Grows.ctx`).
- `step_beaconInit`, `path_beaconInit`: no oracle changes the retained Phase 1 bundle `GameState.beaconInit`, so along every path it stays the bundle of the start state.
- `context_init`: in a sampled context whose Phase 1 was written, the retained bundle is the target Beacon's candidate (`PqxdhServerAuthNegativeControl.beaconCandidate`).

No assumption is used; every statement is a support fact of the existing programs.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCache
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthRootOccurrences
open PqxdhJointIdentity PqxdhJointGapDh PqxdhSecretInputKdf
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- One read of the shared BLAKE2b oracle only extends the cache and leaves the returned digest at the query. -/
theorem query_cached {query : CtxRomAuth.CtxRO.Domain} {cache hashed : CtxRomAuth.CtxRO.QueryCache}
    {digest : CtxRomAuth.CtxDigest}
    (run : (digest, hashed) ∈ support ((CtxRomAuth.ctxRandomOracle query).run cache)) :
    cache ≤ hashed ∧ hashed query = some digest :=
  ⟨QueryImpl.withCaching_cache_le uniformSampleImpl query cache (digest, hashed) run,
    QueryImpl.withCaching_run_caches uniformSampleImpl query cache (digest, hashed) run⟩

/-- Every run of the Beacon's native tail callbacks only extends the shared BLAKE2b cache. -/
theorem afterRoot_ctx_grows (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) {α : Type}
    (work : OracleComp (PqxdhBeaconPhase2Publication.NativeTailSpec Response) α)
    (before : RawCtxSharedPrimitive.SharedState Unit) (result : α × RawCtxSharedPrimitive.SharedState Unit)
    (supported : result ∈ support ((simulateQ (beaconNative setup codec) work).run before)) :
    before.2 ≤ result.2.2 :=
  run_rel _ (fun before after => before.2 ≤ after.2) (fun _ => le_rfl) (fun _ _ _ left right => le_trans left right)
    (fun query state result supported => beaconNative_grows setup codec query state result supported) work before
    result supported

/-- Along every actual callback path, every cached BLAKE2b digest stays cached. -/
theorem path_ctx_mono (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed seed : IdentitySeed) (scalar : ScalarBytes)
    (before after : GameState KemSK × PqxdhJointDhExtractFamily.State) (calls : List (Call KemSK))
    (path : Path setup codec checks publicValue beaconSeed seed scalar before calls after) :
    before.1.ctx ≤ after.1.ctx :=
  (PqxdhServerAuthRootProvenance.path_grows setup codec checks publicValue beaconSeed seed scalar before after calls
    path).ctx

/-- An accept keeps the retained Phase 1 bundle. -/
theorem accept_beaconInit (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (raw : Pqxdh.Bytes) (state : GameState KemSK)
    (result : Option Nat × GameState KemSK)
    (supported : result ∈ support ((acceptOracle setup codec checks publicValue raw).run state)) :
    result.2.beaconInit = state.beaconInit := by
  simp only [acceptOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  obtain ⟨collected, lifted, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
  obtain ⟨_, same⟩ := liftCoins_mem _ _ _ lifted
  simp only [StateT.run_set, pure_bind, same] at supported
  cases hc : collected.1.1 with
  | none =>
      simp only [hc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl
  | some input =>
      simp only [hc, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨returned, derived, supported⟩ := supported
      obtain ⟨consumed, extra, eq, _, _⟩ := client_run state.sessions (binding setup publicValue) input _ returned derived
      have initEq : returned.2.beaconInit = state.beaconInit := by rw [eq]
      rcases returned with ⟨outcome, after⟩
      dsimp only at initEq
      rcases outcome with (_ | token) | error | _
      all_goals simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at supported
      all_goals subst supported
      all_goals exact initEq

/-- A build keeps the retained Phase 1 bundle. -/
theorem build_beaconInit (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (session : Nat) (payload : Option Pqxdh.Bytes) (state : GameState KemSK)
    (result : Option PqxdhServerRegistrationPublication.Response × GameState KemSK)
    (supported : result ∈ support ((buildOracle setup codec checks session payload).run state)) :
    result.2.beaconInit = state.beaconInit := by
  simp only [buildOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases hp : state.pending session with
  | none =>
      simp only [hp, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl
  | some token =>
      simp only [hp] at supported
      cases hpre : PqxdhServerRegistrationPublication.prehash state.server token.pending payload with
      | none =>
          simp only [hpre, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at supported
          subst supported
          rfl
      | some candidate =>
          simp only [hpre, StateT.run_bind, mem_support_bind_iff] at supported
          obtain ⟨hashed, hashRun, supported⟩ := supported
          obtain ⟨hashEq, _, _⟩ := hashOracle_grows _ state hashed hashRun
          simp only [StateT.run_get] at supported
          obtain ⟨current, currentRun, supported⟩ := supported
          rw [support_pure, Set.mem_singleton_iff] at currentRun
          subst currentRun
          obtain ⟨tail, lifted, supported⟩ := supported
          obtain ⟨_, same⟩ := liftCoins_mem _ _ _ lifted
          simp only [same, StateT.run_set, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          obtain ⟨_, rfl, rfl⟩ := supported
          rw [hashEq]

/-- The Beacon's finish keeps the retained Phase 1 bundle, on success and on abort. -/
theorem finish_beaconInit (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (raw : Pqxdh.Bytes)
    (state : GameState KemSK) (result : Option Pqxdh.Bytes × GameState KemSK)
    (supported : result ∈ support ((finishOracle setup codec publicValue beaconSeed raw).run state)) :
    result.2.beaconInit = state.beaconInit := by
  simp only [finishOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases hphase : state.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [hphase] at supported
      rcases hinit : state.beaconInit with _ | init <;> rcases hresp : responseOf codec raw with _ | response
      all_goals simp only [hinit, hresp] at supported
      rotate_left 3
      · simp only [StateT.run_bind, mem_support_bind_iff] at supported
        obtain ⟨hashed, hashRun, supported⟩ := supported
        obtain ⟨hashEq, _, _⟩ := hashOracle_grows _ state hashed hashRun
        simp only [StateT.run_get] at supported
        obtain ⟨current, currentRun, supported⟩ := supported
        rw [support_pure, Set.mem_singleton_iff] at currentRun
        subst currentRun
        obtain ⟨staged, stageRun, supported⟩ := supported
        simp only [StateT.run_set, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at supported
        obtain ⟨_, rfl, _, rfl, rfl⟩ := supported
        rw [hashEq] at stageRun
        obtain ⟨cache, extra, stagedEq, _⟩ := stage_run _ setup codec beaconSeed publicValue control _ oneTime kem raw _
          staged stageRun
        rw [stagedEq]
        exact hinit
      all_goals
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
          Set.mem_singleton_iff] at supported
        subst supported
        rfl
  | _ =>
      simp only [hphase, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl

/-- No oracle of the game changes the retained Phase 1 bundle. -/
theorem step_beaconInit (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (query : ServerAuthSpec.Domain)
    (state : GameState KemSK) (result : ServerAuthSpec.Range query × GameState KemSK)
    (supported : result ∈ support ((authHandler setup codec checks publicValue beaconSeed query).run state)) :
    result.2.beaconInit = state.beaconInit := by
  rcases query with coin | query
  · rw [forward_support _ _ _ supported]
  cases query with
  | accept raw => exact accept_beaconInit setup codec checks publicValue raw state result supported
  | build index payload => exact build_beaconInit setup codec checks index payload state result supported
  | finish raw => exact finish_beaconInit setup codec publicValue beaconSeed raw state result supported
  | hmac key message =>
      change result ∈ support ((hmacOracle key message).run state) at supported
      simp only [hmacOracle] at supported
      split_ifs at supported
      · obtain ⟨middle, first, rest⟩ := run_bind_support _ _ _ _ supported
        rw [record_run, support_pure, Set.mem_singleton_iff] at first
        subst first
        rw [forward_support _ _ _ rest]
      · rw [forward_support _ _ _ supported]
  | hash bytes =>
      obtain ⟨eq, _, _⟩ := hashOracle_grows bytes state result supported
      rw [eq]
  | reveal keyId =>
      change result ∈ support (pure _ : OracleComp PqxdhJointDhExtractRoot.RootSpec _) at supported
      rw [support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl

/-- Along every actual callback path the retained Phase 1 bundle is the start state's. -/
theorem path_beaconInit (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed seed : IdentitySeed) (scalar : ScalarBytes)
    (before after : GameState KemSK × PqxdhJointDhExtractFamily.State) (calls : List (Call KemSK))
    (path : Path setup codec checks publicValue beaconSeed seed scalar before calls after) :
    after.1.beaconInit = before.1.beaconInit := by
  induction path with
  | nil state primitive => rfl
  | cons call primitive middle suffix final reached rest ih =>
      have source := callback_source setup codec checks publicValue beaconSeed seed scalar call primitive middle reached
      have bare := interpreted_source setup seed scalar
        (authHandler setup codec checks publicValue beaconSeed call.query)
        (call.before, primitive) (call.reply, call.after, middle) source
      exact ih.trans (step_beaconInit setup codec checks publicValue beaconSeed call.query call.before
        (call.reply, call.after) bare)

/-- In a sampled context whose Phase 1 was written, the retained bundle is the target Beacon's candidate. -/
theorem context_init (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (supported : context ∈ support (contextSample setup codec))
    (bytes : Pqxdh.Bytes) (published : context.published.1 = some bytes) :
    context.beaconInit = some (PqxdhServerAuthNegativeControl.beaconCandidate setup (context.publicValue setup)
      context.beaconSeed context.oneTime context.keys.1) := by
  simp only [contextSample, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨seed, _, scalar, _, beaconSeed, _, oneTime, _, keys, _, logged, loggedSupported, rfl⟩ := supported
  exact (PqxdhServerAuthNegativeControl.phase1Logged_bundle setup codec beaconSeed _ oneTime keys.1 keys.2 logged
    loggedSupported bytes published).1

end BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCache

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCache.query_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCache.query_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCache.afterRoot_ctx_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCache.afterRoot_ctx_grows

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCache.path_ctx_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCache.path_ctx_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCache.accept_beaconInit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCache.accept_beaconInit

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCache.build_beaconInit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCache.build_beaconInit

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCache.finish_beaconInit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCache.finish_beaconInit

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCache.step_beaconInit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCache.step_beaconInit

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCache.path_beaconInit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCache.path_beaconInit

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCache.context_init' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCache.context_init
