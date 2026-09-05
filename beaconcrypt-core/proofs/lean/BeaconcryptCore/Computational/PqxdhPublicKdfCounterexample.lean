import BeaconcryptCore.Computational.PqxdhJointKdfGame

/-!
# Public evaluation refutes the fixed-HKDF/random-table security interpretation

The source is public and deterministic. One complete-stream query, compared with one local evaluation, accepts always in the real game and only on a uniform stream match in the random game. Query budgets do not charge local computation; this test is efficient whenever the implementation is efficient. No assumption about HKDF internals is used.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhPublicKdfCounterexample

open PqxdhJointKdf PqxdhJointKdfGame

/-- A single query followed by the public implementation's equality test. -/
def publicEvaluationMain (source : FixedHkdfSha512NoSaltSource)
    (address : JointKdfAddress) : OracleComp FixedHkdfSha512JointStreamSpec Bool := do
  let answer ← liftM (FixedHkdfSha512JointStreamSpec.query (.inr address))
  pure (decide (answer = productionStream source.crypto address))

/-- The real handler makes the equality test succeed identically. -/
theorem publicEvaluation_real (source : FixedHkdfSha512NoSaltSource)
    (address : JointKdfAddress) :
    simulateQ (fixedHkdfSha512JointStreamRealImpl source)
      (publicEvaluationMain source address) = pure true := by
  simp [publicEvaluationMain, fixedHkdfSha512JointStreamRealImpl]

/-- The negative control uses no adversary randomness and at most one stream query. -/
def publicEvaluationAdversary (source : FixedHkdfSha512NoSaltSource)
    (address : JointKdfAddress) : FixedHkdfSha512JointStreamAdversary 0 1 where
  main := publicEvaluationMain source address
  uniformQueryBound := by
    simp only [publicEvaluationMain, bind_pure_comp, isQueryBoundP_map_iff]
    exact (OracleComp.isQueryBoundP_query_iff
      (p := IsFixedHkdfSha512UniformQuery) (.inr address) 0).2 (by simp [IsFixedHkdfSha512UniformQuery])
  streamQueryBound := by
    simp only [publicEvaluationMain, bind_pure_comp, isQueryBoundP_map_iff]
    exact (OracleComp.isQueryBoundP_query_iff
      (p := IsFixedHkdfSha512StreamQuery) (.inr address) 1).2 (by simp [IsFixedHkdfSha512StreamQuery])

/-- On the empty lazy cache the test compares one fresh uniform stream with the public answer. -/
theorem publicEvaluation_random (source : FixedHkdfSha512NoSaltSource)
    (address : JointKdfAddress) :
    fixedHkdfSha512JointStreamRandomExp (publicEvaluationAdversary source address) =
      (fun answer => decide (answer = productionStream source.crypto address)) <$>
        ($ᵗ JointKdfStream) := by
  simp [fixedHkdfSha512JointStreamRandomExp, publicEvaluationAdversary,
    publicEvaluationMain, fixedHkdfSha512JointStreamRandomImpl,
    jointKdfLazyRandomStreamImpl, OracleSpec.randomOracle,
    uniformSampleImpl, StateT.run'_eq]

/-- Exact random-world false-positive probability; it is not close to the real world's one. -/
theorem publicEvaluation_random_probability (source : FixedHkdfSha512NoSaltSource)
    (address : JointKdfAddress) :
    Pr[= true | fixedHkdfSha512JointStreamRandomExp
      (publicEvaluationAdversary source address)] =
      (Fintype.card JointKdfStream : ℝ≥0∞)⁻¹ := by
  simp [publicEvaluation_random, probOutput_map,
    probOutput_uniformSample]

/-- The efficient control has advantage `1 - 1 / 2^608`, expressed without a giant numeral. -/
theorem publicEvaluation_advantage (source : FixedHkdfSha512NoSaltSource)
    (address : JointKdfAddress) :
    fixedHkdfSha512JointStreamAdvantage source
      (publicEvaluationAdversary source address) =
      |1 - ((Fintype.card JointKdfStream : ℝ≥0∞)⁻¹).toReal| := by
  unfold fixedHkdfSha512JointStreamAdvantage ProbComp.boolDistAdvantage
  rw [publicEvaluation_random_probability]
  simp [fixedHkdfSha512JointStreamRealExp, publicEvaluationAdversary, publicEvaluation_real]

/-- In particular no bound below one half holds for all one-query distinguishers in this game. -/
theorem publicEvaluation_advantage_ge_half (source : FixedHkdfSha512NoSaltSource)
    (address : JointKdfAddress) :
    (1 : ℝ) / 2 ≤ fixedHkdfSha512JointStreamAdvantage source
      (publicEvaluationAdversary source address) := by
  rw [publicEvaluation_advantage]
  norm_num [card_vector, show Fintype.card UInt8 = 256 from rfl]

end BeaconcryptCore.Computational.PqxdhPublicKdfCounterexample

/--
info: 'BeaconcryptCore.Computational.PqxdhPublicKdfCounterexample.publicEvaluation_advantage_ge_half' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPublicKdfCounterexample.publicEvaluation_advantage_ge_half
