-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryCompiler
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCachedObservation

/-! Literal aliases in the actual combined symbolic-table and real suffix-key execution are bounded by one concrete ordinary suffix-key recovery adversary. Real off-protected side answers may depend arbitrarily on the candidate. The proof first uses identical-until-literal-hit at each fixed candidate and only then applies the ordinary recovery reduction; it never assumes that the real literal list is independent of the candidate. Both final observations retain the entire actual byte-cache lens. -/
open OracleComp OracleSpec CoreModels ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryBound
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWord (Cache actual)
open RegistrationNativeSecretWordRecoveryCompiler (IsKey IsSuffix literals closed guesses)
open RegistrationNativeSecretWordSource (ByteCache byteCache byteSource)
open RegistrationNativeSuffixKeyPrf (Secret)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
variable {Value Observation : Type}
attribute [local irreducible] uniformSample RegistrationNativeSuffixKeyPrf.value

noncomputable def normalized (source : FixedHkdfSha512NoSaltSource) (candidate : Secret) :
    QueryImpl Combined (StateT Cache ProbComp)
  | .inl query => actual candidate query
  | .inr head => fun before => pure (RegistrationNativeSuffixKeyPrf.value source candidate head, before)

noncomputable def bytes (source : FixedHkdfSha512NoSaltSource) (candidate : Secret) :
    QueryImpl Combined (StateT ByteCache ProbComp)
  | .inl query => byteSource candidate query
  | .inr head => fun before => pure (RegistrationNativeSuffixKeyPrf.value source candidate head, before)

noncomputable def logged (source : FixedHkdfSha512NoSaltSource) (candidate : Secret)
    (work : OracleComp Combined Value) :=
  (simulateQ (RawCtxSelectedQueryTrace.recorded (closed source candidate) literals) work).run (∅, [])

noncomputable def symbolicView (source : FixedHkdfSha512NoSaltSource)
    (observe : Secret → (Value × ByteCache) → Observation) (work : OracleComp Combined Value) : ProbComp Observation := do
  let candidate ← $ᵗ Secret
  (fun result => observe candidate (result.1, byteCache candidate result.2)) <$>
    (simulateQ (closed source candidate) work).run ∅

noncomputable def bytesView (source : FixedHkdfSha512NoSaltSource)
    (observe : Secret → (Value × ByteCache) → Observation) (work : OracleComp Combined Value) : ProbComp Observation := do
  let candidate ← $ᵗ Secret
  observe candidate <$> (simulateQ (bytes source candidate) work).run ∅

private theorem routed (source : FixedHkdfSha512NoSaltSource) (candidate : Secret) :
    RawCtxSelectedAliasCoupling.routed (closed source candidate) (normalized source candidate) literals candidate =
      normalized source candidate := by
  funext query
  cases query with
  | inl query =>
      simpa only [RawCtxSelectedAliasCoupling.routed, closed, normalized, literals] using
        congrFun (RegistrationNativeSecretWord.actual_routed candidate) query
  | inr head => simp only [RawCtxSelectedAliasCoupling.routed, literals, List.not_mem_nil, ite_false, closed, normalized]

/-- For each fixed candidate, the full table execution changes only after a literal equal to that candidate, even with real candidate-dependent side answers. -/
theorem fixed_distance (source : FixedHkdfSha512NoSaltSource) (candidate : Secret)
    (work : OracleComp Combined Value) :
    discreteDistance ((simulateQ (closed source candidate) work).run ∅)
      ((simulateQ (normalized source candidate) work).run ∅) ≤
      (Pr{let result ← logged source candidate work}[candidate ∈ result.2.2]).toReal := by
  have compared := RawCtxSelectedAliasCoupling.recorded_distance (closed source candidate) (normalized source candidate)
    literals candidate work (∅ : Cache)
  rw [routed] at compared
  have mapped := (discreteDistance_map_le (Prod.map id Prod.fst) _ _).trans compared
  simpa only [RawCtxSelectedQueryTrace.complete, logged] using mapped

/-- The actual normalized cache projects to the literal192-byte lazy oracle while retaining the real suffix-key side oracle. -/
theorem query_source (source : FixedHkdfSha512NoSaltSource) (candidate : Secret)
    (query : Combined.Domain) (before : Cache) :
    Prod.map id (byteCache candidate) <$> (normalized source candidate query).run before =
      (bytes source candidate query).run (byteCache candidate before) := by
  cases query with
  | inl query => exact RegistrationNativeSecretWordSource.query_source candidate query before
  | inr head => simp only [normalized, bytes, StateT.run, map_pure, Prod.map_def, id_eq]

/-- This source projection preserves the full reached byte cache through the complete combined adaptive client. -/
theorem program_source (source : FixedHkdfSha512NoSaltSource) (candidate : Secret)
    (work : OracleComp Combined Value) (before : Cache) :
    Prod.map id (byteCache candidate) <$> (simulateQ (normalized source candidate) work).run before =
      (simulateQ (bytes source candidate) work).run (byteCache candidate before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (byteCache candidate) (query_source source candidate) work before

private theorem guesses_source (source : FixedHkdfSha512NoSaltSource) (candidate : Secret)
    (work : OracleComp Combined Value) :
    simulateQ (RegistrationNativeSuffixKeyPrf.realImpl source candidate) (guesses work) =
      (fun result => result.2.2) <$> logged source candidate work := by
  simp only [guesses, RegistrationNativeSecretWordRecoveryCompiler.run, simulateQ_map,
    RegistrationNativeSecretWordRecoveryCompiler.program_source, logged]

private theorem hit_eq (source : FixedHkdfSha512NoSaltSource) (work : OracleComp Combined Value) :
    Pr{let pair ← (do let candidate ← $ᵗ Secret; let result ← logged source candidate work; pure (candidate, result))}[pair.1 ∈ pair.2.2.2] =
      Pr{let result ← RegistrationNativeSuffixKeyRecovery.guessed source (guesses work)}[result = true] := by
  simp only [RegistrationNativeSuffixKeyRecovery.guessed, guesses_source, map_bind,
    bind_pure_comp, Functor.map_map, decide_eq_true_eq]

private theorem cache_empty (candidate : Secret) : byteCache candidate ∅ = ∅ := by
  apply QueryCache.ext
  intro point
  change (RegistrationNativeSecretWord.decode candidate point).bind (fun _ => none) = none
  cases RegistrationNativeSecretWord.decode candidate point <;> rfl

private theorem fixed_observed (source : FixedHkdfSha512NoSaltSource) (candidate : Secret)
    (observe : Secret → (Value × ByteCache) → Observation) (work : OracleComp Combined Value) :
    discreteDistance
      ((fun result => observe candidate (result.1, byteCache candidate result.2)) <$>
        (simulateQ (closed source candidate) work).run ∅)
      (observe candidate <$> (simulateQ (bytes source candidate) work).run ∅) ≤
      (Pr{let result ← logged source candidate work}[candidate ∈ result.2.2]).toReal := by
  have projected := congrArg (Functor.map (observe candidate)) (program_source source candidate work ∅)
  rw [cache_empty] at projected
  have sourceEq : (fun result => observe candidate (result.1, byteCache candidate result.2)) <$>
      (simulateQ (normalized source candidate) work).run ∅ =
        observe candidate <$> (simulateQ (bytes source candidate) work).run ∅ := by
    simpa only [Functor.map_map, Function.comp_def, Prod.map_def, id_eq] using projected
  rw [← sourceEq]
  exact (discreteDistance_map_le _ _ _).trans (fixed_distance source candidate work)

attribute [local irreducible] closed normalized bytes logged byteCache guesses

private theorem average {Trace : Type} (left right : Secret → ProbComp Observation)
    (trace : Secret → ProbComp Trace) (event : Secret → Trace → Prop)
    (pointwise : ∀ candidate, discreteDistance (left candidate) (right candidate) ≤
      (Pr{let result ← trace candidate}[event candidate result]).toReal) :
    ENNReal.ofReal (discreteDistance ($ᵗ Secret >>= left) ($ᵗ Secret >>= right)) ≤
      Pr{let pair ← (do let candidate ← $ᵗ Secret; let result ← trace candidate; pure (candidate, result))}[event pair.1 pair.2] := by
  have compared := PqxdhExtractRomHiddenSuffix.tvDist_bind_le_probEvent ($ᵗ Secret) left right trace event
    (fun candidate _ => pointwise candidate)
  exact (ENNReal.ofReal_le_ofReal compared).trans (ENNReal.ofReal_toReal (prEvent_ne_top _)).le

private theorem averaged_distance (source : FixedHkdfSha512NoSaltSource)
    (observe : Secret → (Value × ByteCache) → Observation) (work : OracleComp Combined Value) :
    ENNReal.ofReal (discreteDistance (symbolicView source observe work) (bytesView source observe work)) ≤
      Pr{let pair ← (do let candidate ← $ᵗ Secret; let result ← logged source candidate work; pure (candidate, result))}[pair.1 ∈ pair.2.2.2] := by
  unfold symbolicView bytesView
  apply average (Trace := Value × (Cache × List Secret))
    (fun candidate => (fun result => observe candidate (result.1, byteCache candidate result.2)) <$>
      (simulateQ (closed source candidate) work).run ∅)
    (fun candidate => observe candidate <$> (simulateQ (bytes source candidate) work).run ∅)
    (fun candidate => logged source candidate work) (fun candidate result => candidate ∈ result.2.2)
  intro candidate
  exact fixed_observed (Value := Value) (Observation := Observation) source candidate observe work

attribute [local irreducible] RegistrationNativeSuffixKeyPrf.advantage RegistrationNativeSuffixKeyRecovery.adversary

/-- One explicit ordinary suffix-key adversary controls all literal aliases in the full real side-information execution, retaining any candidate-dependent final observation and the entire actual byte cache. -/
theorem observed_close (source : FixedHkdfSha512NoSaltSource)
    (observe : Secret → (Value × ByteCache) → Observation) (work : OracleComp Combined Value)
    (suffixCap keyCap : Nat) (suffixBound : work.IsQueryBoundP IsSuffix suffixCap)
    (keyBound : work.IsQueryBoundP IsKey keyCap) :
    ENNReal.ofReal (discreteDistance (symbolicView source observe work) (bytesView source observe work)) ≤
      ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage source
        (RegistrationNativeSuffixKeyRecovery.adversary source (guesses work))) +
          suffixCap * (256 ^ 160 : ℝ≥0∞)⁻¹ + keyCap * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  have compared := averaged_distance source observe work
  rw [hit_eq] at compared
  exact compared.trans (RegistrationNativeSuffixKeyRecovery.key_recovery_bound source (guesses work) suffixCap keyCap
    (RegistrationNativeSecretWordRecoveryCompiler.guesses_bound work suffixCap suffixBound)
    (RegistrationNativeSecretWordRecoveryCompiler.guesses_length work keyCap keyBound))

end BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryBound.fixed_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryBound.fixed_distance
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryBound.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryBound.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryBound.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryBound.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryBound.observed_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryBound.observed_close
