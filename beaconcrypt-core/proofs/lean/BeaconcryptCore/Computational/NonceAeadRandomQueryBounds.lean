import BeaconcryptCore.Computational.CtxComputationalSecurity
import BeaconcryptCore.Computational.CtxNonceAeadIndDollarValidation

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.NonceAeadRandomQueryBounds
open CtxRomAuth CtxNonceAeadIntCtxt CtxNonceAeadIndDollar CtxNonceAeadIndDollarValidation
open CtxComputationalSecurity

/-- Random sealing rejects used nonces before drawing; a fresh request samples the body width and detached sixteen-byte tag, with the checked cap below. -/
theorem randomSeal_uniform_bound (input : ModifiedNonceAeadSealInput)
    (state : ModifiedNonceAeadHandlerState) :
    ((modifiedNonceAeadINDDollarRandomSealOracle input).run state).IsTotalQueryBound
      (if input.nonce ∈ state.usedNonces then 0 else input.plaintext.length + 16) := by
  by_cases used : input.nonce ∈ state.usedNonces
  · simp only [modifiedNonceAeadINDDollarRandomSealOracle, StateT.run, used, ite_true]
    trivial
  · simp only [modifiedNonceAeadINDDollarRandomSealOracle, StateT.run, used, ite_false]
    apply OracleComp.isTotalQueryBound_bind (uniformFixedBytes_isTotalQueryBound input.plaintext.length)
    intro body
    simpa only [bind_pure_comp, OracleComp.IsTotalQueryBound, OracleComp.isQueryBound_map_iff] using
      uniformFixedBytes_isTotalQueryBound 16

/-- Submitted plaintext bytes are charged on every seal attempt, including a repeated nonce that may later be rejected. Source coins contribute no plaintext bytes. -/
def plaintextCost : ModifiedNonceAeadAdversarySpec.Domain → ℕ
  | .inl _ => 0
  | .inr input => input.plaintext.length

/-- A weighted source budget bounds the sum of all submitted plaintext lengths through every possible adaptive continuation. -/
def PlaintextBound {Result : Type} (client : OracleComp ModifiedNonceAeadAdversarySpec Result)
    (bytes : ℕ) : Prop :=
  client.IsQueryBound bytes (fun query available => plaintextCost query ≤ available)
    (fun query available => available - plaintextCost query)

/-- Every ordinary random-challenger request keeps both explicit source randomness and fresh ciphertext-body/tag generation in its budget. -/
theorem randomImpl_uniform_step (query : ModifiedNonceAeadAdversarySpec.Domain)
    (state : ModifiedNonceAeadHandlerState) :
    ((modifiedNonceAeadINDDollarRandomImpl query).run state).IsTotalQueryBound
      (match query with | .inl _ => 1 | .inr input => input.plaintext.length + 16) := by
  cases query with
  | inl coin =>
    change OracleComp.IsTotalQueryBound ((fun answer => (answer, state)) <$>
      (unifSpec.query coin : ProbComp (unifSpec.Range coin))) 1
    simp only [OracleComp.IsTotalQueryBound, OracleComp.isQueryBound_map_iff,
      OracleComp.isQueryBound_query_iff]
    decide
  | inr input =>
    change ((modifiedNonceAeadINDDollarRandomSealOracle input).run state).IsTotalQueryBound
      (input.plaintext.length + 16)
    apply (randomSeal_uniform_bound input state).mono
    split <;> omega

/-- The complete ordinary random-world challenger charges all explicit source coins, every submitted plaintext byte, and sixteen random tag bytes per sealing attempt. Used-nonce rejection may reduce the actual cost. -/
theorem randomRun_uniform_bound {Result : Type}
    (client : OracleComp ModifiedNonceAeadAdversarySpec Result) (qBytes qSeal qUniform : ℕ)
    (bytesBound : PlaintextBound client qBytes)
    (sealBound : client.IsQueryBoundP IsModifiedNonceAeadSealQuery qSeal)
    (coinBound : client.IsQueryBoundP IsModifiedNonceAeadUniformQuery qUniform)
    (state : ModifiedNonceAeadHandlerState) :
    ((simulateQ modifiedNonceAeadINDDollarRandomImpl client).run state).IsTotalQueryBound
      (qUniform + qBytes + 16 * qSeal) := by
  induction client using OracleComp.inductionOn generalizing qBytes qSeal qUniform state with
  | pure value => trivial
  | query_bind query next ih =>
    rw [PlaintextBound, OracleComp.isQueryBound_query_bind_iff] at bytesBound
    rw [OracleComp.isQueryBoundP_query_bind_iff] at sealBound coinBound
    change ((modifiedNonceAeadINDDollarRandomImpl query).run state >>= fun result =>
      (simulateQ modifiedNonceAeadINDDollarRandomImpl (next result.1)).run result.2).IsTotalQueryBound _
    have accounted := OracleComp.isTotalQueryBound_bind (randomImpl_uniform_step query state)
      (fun result => ih result.1 _ _ _ (bytesBound.2 result.1) (sealBound.2 result.1)
        (coinBound.2 result.1) result.2)
    apply accounted.mono
    have byteSize := bytesBound.1
    have sealPositive := sealBound.1
    have coinPositive := coinBound.1
    cases query with
    | inl coin =>
      simp only [plaintextCost, IsModifiedNonceAeadSealQuery, IsModifiedNonceAeadUniformQuery,
        Nat.sub_zero, not_false_eq_true, true_or, not_true_eq_false, false_or]
        at byteSize sealPositive coinPositive ⊢
      simp at byteSize sealPositive coinPositive ⊢
      omega
    | inr input =>
      simp only [plaintextCost, IsModifiedNonceAeadSealQuery, IsModifiedNonceAeadUniformQuery,
        not_false_eq_true, true_or, not_true_eq_false, false_or]
        at byteSize sealPositive coinPositive ⊢
      simp at byteSize sealPositive coinPositive ⊢
      omega

/-- Unlike the real experiment, the ordinary random experiment generates no encryption key. Its complete randomness is the forwarded coins plus fresh random bodies and tags. -/
theorem randomExperiment_uniform_bound (adversary : ModifiedNonceAeadINDDollarAdversary)
    (qBytes qSeal qUniform : ℕ) (bytesBound : PlaintextBound adversary.main qBytes)
    (sealBound : adversary.main.IsQueryBoundP IsModifiedNonceAeadSealQuery qSeal)
    (coinBound : adversary.main.IsQueryBoundP IsModifiedNonceAeadUniformQuery qUniform) :
    (modifiedNonceAeadINDDollarRandomExp adversary).IsTotalQueryBound (qUniform + qBytes + 16 * qSeal) := by
  simpa only [modifiedNonceAeadINDDollarRandomExp, bind_pure_comp,
    OracleComp.IsTotalQueryBound, OracleComp.isQueryBound_map_iff] using
      randomRun_uniform_bound adversary.main qBytes qSeal qUniform bytesBound sealBound coinBound
        emptyModifiedNonceAeadHandlerState

/-- Submitted plaintext budgets add through an arbitrary complete continuation; no branch may hide extra payload by returning a different oracle reply. -/
theorem plaintext_bind {First Result : Type}
    (first : OracleComp ModifiedNonceAeadAdversarySpec First)
    (next : First → OracleComp ModifiedNonceAeadAdversarySpec Result) (firstBytes nextBytes : ℕ)
    (firstBound : PlaintextBound first firstBytes) (nextBound : ∀ value, PlaintextBound (next value) nextBytes) :
    PlaintextBound (first >>= next) (firstBytes + nextBytes) := by
  exact OracleComp.isQueryBound_bind Nat.add
    (fun query left right available allowed => by
      change plaintextCost query ≤ left + available ∧ plaintextCost query ≤ available + right
      constructor <;> omega)
    (fun query left right available allowed => by
      change left + (available - plaintextCost query) = left + available - plaintextCost query ∧
        available + right - plaintextCost query = (available - plaintextCost query) + right
      constructor <;> omega)
    firstBound nextBound

/-- Transfer a weighted plaintext budget through an exact stateful source interpreter. Each source query supplies its declared payload budget; all other primitive, parser and cache operations must prove zero payload contribution explicitly. -/
theorem plaintext_simulate {SourceI State Result : Type} {sourceSpec : OracleSpec SourceI}
    (sourceCost : SourceI → ℕ)
    (impl : QueryImpl sourceSpec (StateT State (OracleComp ModifiedNonceAeadAdversarySpec)))
    (client : OracleComp sourceSpec Result) (qBytes : ℕ)
    (bounded : client.IsQueryBound qBytes (fun query available => sourceCost query ≤ available)
      (fun query available => available - sourceCost query))
    (step : ∀ query state, PlaintextBound ((impl query).run state) (sourceCost query)) (state : State) :
    PlaintextBound ((simulateQ impl client).run state) qBytes := by
  exact bounded.simulateQ_run_of_step (combine := Nat.add) (mapBudget := id)
    (stepBudget := fun query _ => sourceCost query)
    (fun firstBound nextBound => plaintext_bind _ _ _ _ firstBound nextBound)
    (fun query _available state _allowed => step query state)
    (fun _query _available allowed => by dsimp; omega) state

/-- A computation that cannot issue a sealing request contributes no submitted plaintext, regardless of its explicit uniform work. -/
theorem no_seal_plaintext_zero {Result : Type} (client : OracleComp ModifiedNonceAeadAdversarySpec Result)
    (bounded : client.IsQueryBoundP IsModifiedNonceAeadSealQuery 0) : PlaintextBound client 0 := by
  induction client using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
    rw [PlaintextBound, OracleComp.isQueryBound_query_bind_iff]
    cases query with
    | inl coin =>
      refine ⟨by simp [plaintextCost], ?_⟩
      intro answer
      exact ih answer (by simpa [IsModifiedNonceAeadSealQuery] using bounded.2 answer)
    | inr input =>
      have impossible : False := by simpa [IsModifiedNonceAeadSealQuery] using bounded.1
      exact impossible.elim

/-- Private/public cache sampling remains real uniform work but carries zero primitive plaintext bytes when lifted into the ordinary adversary interface. -/
theorem lifted_probability_plaintext_zero {Result : Type} (work : ProbComp Result) :
    PlaintextBound (OracleComp.liftComp work ModifiedNonceAeadAdversarySpec) 0 :=
  no_seal_plaintext_zero _ (liftProbComp_no_modifiedNonceAeadSealQueries work)

end BeaconcryptCore.Computational.NonceAeadRandomQueryBounds

/--
info: 'BeaconcryptCore.Computational.NonceAeadRandomQueryBounds.randomSeal_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.NonceAeadRandomQueryBounds.randomSeal_uniform_bound

/--
info: 'BeaconcryptCore.Computational.NonceAeadRandomQueryBounds.randomImpl_uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.NonceAeadRandomQueryBounds.randomImpl_uniform_step

/--
info: 'BeaconcryptCore.Computational.NonceAeadRandomQueryBounds.randomRun_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.NonceAeadRandomQueryBounds.randomRun_uniform_bound

/--
info: 'BeaconcryptCore.Computational.NonceAeadRandomQueryBounds.randomExperiment_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.NonceAeadRandomQueryBounds.randomExperiment_uniform_bound

/--
info: 'BeaconcryptCore.Computational.NonceAeadRandomQueryBounds.plaintext_bind' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.NonceAeadRandomQueryBounds.plaintext_bind

/--
info: 'BeaconcryptCore.Computational.NonceAeadRandomQueryBounds.plaintext_simulate' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.NonceAeadRandomQueryBounds.plaintext_simulate

/--
info: 'BeaconcryptCore.Computational.NonceAeadRandomQueryBounds.no_seal_plaintext_zero' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.NonceAeadRandomQueryBounds.no_seal_plaintext_zero

/--
info: 'BeaconcryptCore.Computational.NonceAeadRandomQueryBounds.lifted_probability_plaintext_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.NonceAeadRandomQueryBounds.lifted_probability_plaintext_zero
