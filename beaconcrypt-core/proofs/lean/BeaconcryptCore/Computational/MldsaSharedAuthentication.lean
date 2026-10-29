-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.MldsaTranscriptAuth
import BeaconcryptCore.Computational.CtxRomAuth
import VCVio.OracleComp.QueryTracking.Collision

/-!
Authentication and records use the same actual CTX random-oracle interface. The total final-cache readback interprets only values accompanied by real query receipts. Collision extraction requires receipts for both the candidate and every prior signing payload, so an unqueried default value cannot create a spurious collision. Actual extracted-controller executions and populated native bindings are proved in the RegistrationAuthentication modules.
-/

open OracleComp OracleSpec

set_option autoImplicit false

namespace BeaconcryptCore.Computational.MldsaSharedAuthentication

open MldsaTranscriptAuth CtxRomAuth

/-- Both role-specific signing inputs are computed after querying the same shared hash capability. -/
def signingInput (payload : Payload) : OracleComp CtxRO Bytes := do
  let digest ← CtxRO.query ((), payload.transcript)
  pure (Pqxdh.TranscriptAuth.signatureInput payload.role digest.toList)

theorem signing_input_queries (payload : Payload) : (signingInput payload).IsTotalQueryBound 1 := by
  rw [signingInput, isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun _ => True.intro⟩

/-- Interpret arbitrary interleavings of these authentication and record hash programs with one real lazy cache. -/
def run {Result : Type} (work : OracleComp CtxRO Result) (cache : CtxRO.QueryCache) :
    ProbComp (Result × CtxRO.QueryCache) :=
  (simulateQ ctxRandomOracle work).run cache

/-- A total final-cache readback is defined only to interpret already reached hash inputs. -/
def cacheHash (cache : CtxRO.QueryCache) : Hash512 := fun input =>
  ((cache ((), input)).getD (List.Vector.replicate 64 0)).toList

theorem cache_hash_width (cache : CtxRO.QueryCache) : Pqxdh.TranscriptAuth.HashWidth (cacheHash cache) :=
  fun _ => List.Vector.toList_length _

theorem cache_hash_reconstruct (cache : CtxRO.QueryCache) (input : Bytes) (digest : CtxDigest)
    (cached : cache ((), input) = some digest) : cacheHash cache input = digest.toList := by
  simp only [cacheHash, cached, Option.getD_some]

/-- One actual shared query retains all previous entries and caches its actual returned digest. -/
theorem query_cached (input : Bytes) (cache : CtxRO.QueryCache) (result : CtxDigest × CtxRO.QueryCache)
    (supported : result ∈ support ((ctxRandomOracle ((), input)).run cache)) :
    cache ≤ result.2 ∧ result.2 ((), input) = some result.1 :=
  ⟨QueryImpl.withCaching_cache_le (uniformSampleImpl : QueryImpl CtxRO ProbComp) _ _ _ supported,
    QueryImpl.withCaching_run_caches (uniformSampleImpl : QueryImpl CtxRO ProbComp) _ _ _ supported⟩

/-- Rejection does not roll back hashes: every supported complete execution extends its actual entry cache. -/
theorem run_cache_persists {Result : Type} (work : OracleComp CtxRO Result) (cache : CtxRO.QueryCache)
    (result : Result × CtxRO.QueryCache) (supported : result ∈ support (run work cache)) :
    cache ≤ result.2 := by
  induction work using OracleComp.inductionOn generalizing cache result with
  | pure value =>
    simp only [run, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact le_rfl
  | query_bind query next ih =>
    rw [run, simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨step, first, rest⟩ := supported
    exact (QueryImpl.withCaching_cache_le (uniformSampleImpl : QueryImpl CtxRO ProbComp) _ _ _ first).trans
      (ih step.1 step.2 result rest)

/-- The complete actual signing input is exactly the payload interpreted by the reached cache. -/
theorem signing_input_cached (payload : Payload) (cache after : CtxRO.QueryCache) (input : Bytes)
    (supported : (input, after) ∈ support (run (signingInput payload) cache)) :
    input = payload.message (cacheHash after) := by
  simp only [run, signingInput, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    mem_support_bind_iff, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨⟨digest, next⟩, queried, same⟩ := supported
  have inputSame : input = Pqxdh.TranscriptAuth.signatureInput payload.role digest.toList :=
    congrArg Prod.fst same
  have cacheSame : after = next := congrArg Prod.snd same
  rw [inputSame, cacheSame]
  exact (congrArg (Pqxdh.TranscriptAuth.signatureInput payload.role)
    (cache_hash_reconstruct next payload.transcript digest (query_cached _ _ _ queried).2)).symm

/-- Each prior signing payload must retain the receipt of the hash operation that supplied its real signing input. -/
def HistoryCached (cache : CtxRO.QueryCache) (history : List SigningCall) : Prop :=
  ∀ call ∈ history, ∃ digest, cache ((), call.payload.transcript) = some digest

/-- The final-cache readback cannot invent the collision: both displayed inputs were actually queried. -/
theorem transcript_collision_cached (cache : CtxRO.QueryCache) (trial : Trial)
    (history : HistoryCached cache trial.history)
    (candidate : ∃ digest, cache ((), trial.candidate.transcript) = some digest)
    (collision : TranscriptCollision (cacheHash cache) trial) : CacheHasCollision cache := by
  obtain ⟨call, member, different, same⟩ := collision
  obtain ⟨left, leftCached⟩ := history call member
  obtain ⟨right, rightCached⟩ := candidate
  have sameDigest : left = right := List.Vector.toList_injective
    ((cache_hash_reconstruct cache _ _ leftCached).symm.trans
      (same.trans (cache_hash_reconstruct cache _ _ rightCached)))
  exact ⟨((), call.payload.transcript), ((), trial.candidate.transcript), left, right,
    (fun equal => different (congrArg Prod.snd equal)), leftCached, rightCached, heq_of_eq sameDigest⟩

end BeaconcryptCore.Computational.MldsaSharedAuthentication

/-- info: 'BeaconcryptCore.Computational.MldsaSharedAuthentication.cache_hash_width' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaSharedAuthentication.cache_hash_width

/-- info: 'BeaconcryptCore.Computational.MldsaSharedAuthentication.cache_hash_reconstruct' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaSharedAuthentication.cache_hash_reconstruct

/-- info: 'BeaconcryptCore.Computational.MldsaSharedAuthentication.query_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaSharedAuthentication.query_cached

/-- info: 'BeaconcryptCore.Computational.MldsaSharedAuthentication.run_cache_persists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaSharedAuthentication.run_cache_persists

/-- info: 'BeaconcryptCore.Computational.MldsaSharedAuthentication.signing_input_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaSharedAuthentication.signing_input_cached

/-- info: 'BeaconcryptCore.Computational.MldsaSharedAuthentication.transcript_collision_cached' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaSharedAuthentication.transcript_collision_cached

/-- info: 'BeaconcryptCore.Computational.MldsaSharedAuthentication.signing_input_queries' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaSharedAuthentication.signing_input_queries
