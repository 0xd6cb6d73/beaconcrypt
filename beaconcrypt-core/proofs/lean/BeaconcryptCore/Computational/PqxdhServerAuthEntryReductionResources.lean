import BeaconcryptCore.Computational.PqxdhServerAuthEntryBound
import BeaconcryptCore.Computational.PqxdhServerAuthEntryResourceGame

open OracleComp OracleSpec
set_option autoImplicit false
set_option maxRecDepth 10000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open PqxdhServerAuthKeySchedule

/-- Both Extract endpoints use the literal 32-byte source sampler; its complete random-query bill is 32. -/
theorem entry_extract_sampler_uniform : uniform32.IsTotalQueryBound 32 := by
  simpa only [uniform32, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
    CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32

/-- The independent opposite-direction half is charged in every step observer execution. -/
theorem entry_step_observer_uniform (D : Distinguisher) (U : Nat)
    (bounded : ∀ value, (D value).IsTotalQueryBound U) :
    ∀ context output, (stepObserver D context output).IsTotalQueryBound (32 + U) := by
  intro context output
  exact OracleComp.isTotalQueryBound_bind
    (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32) fun other => bounded (output, other)


/-- The root-Expand reduction forwards all ordinary observer randomness and adds no local draw. -/
theorem entry_root_prf_uniform (source : FixedHkdfSha512NoSaltSource) (D : Distinguisher) (U : Nat)
    (bounded : ∀ value, (D value).IsTotalQueryBound U) :
    (rootExpandReduction source D).IsQueryBoundP IsHmacUniformQuery U := by
  simp only [rootExpandReduction, expandReduction, unitSample, liftM_pure, pure_bind]
  rw [OracleComp.isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl (by simp [IsHmacUniformQuery]), fun output => local_uniform_query_bound (bounded _)⟩


/-- The initializer-Expand reduction also adds no local draw to the complete observer bill. -/
theorem entry_init_prf_uniform (source : FixedHkdfSha512NoSaltSource) (D : Distinguisher) (U : Nat)
    (bounded : ∀ value, (D value).IsTotalQueryBound U) :
    (initExpandReduction source D).IsQueryBoundP IsHmacUniformQuery U := by
  unfold initExpandReduction
  rw [OracleComp.isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl (by simp [IsHmacUniformQuery]), fun output => local_uniform_query_bound (bounded _)⟩

/-- Two challenge calls add no local draw; the opposite-direction half costs 32. -/
theorem entry_step_prf_uniform (D : Distinguisher) (U : Nat)
    (bounded : ∀ value, (D value).IsTotalQueryBound U) :
    (stepExpandReduction D).IsQueryBoundP IsHmacUniformQuery (32 + U) := by
  simpa only [stepExpandReduction, Nat.zero_add] using
    fullExpandReduction_uniform_query_bound .ratchet unitSample (stepObserver D)
      (qSample := 0) (by simp [unitSample, IsTotalQueryBound, isQueryBound_pure]) (entry_step_observer_uniform D U bounded)

/-- The real root-PRF challenger charges its complete 64-byte secret key. -/
theorem entry_root_prf_real_uniform (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (D : Distinguisher) (U : Nat)
    (bounded : ∀ value, (D value).IsTotalQueryBound U) :
    (hmacPrfRealGame hmac (rootExpandReduction source D)).IsTotalQueryBound (64 + U) := by
  unfold hmacPrfRealGame
  refine OracleComp.isTotalQueryBound_bind
    (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64) fun key => ?_
  simpa only [rootExpandReduction, expandReduction_real, unitSample, pure_bind, rootObserver] using
    bounded (fromRoot source (expandRoot hmac key))

/-- The random root-PRF challenger draws the complete 64-byte reply, including its unused half. -/
theorem entry_root_prf_random_uniform (source : FixedHkdfSha512NoSaltSource)
    (D : Distinguisher) (U : Nat) (bounded : ∀ value, (D value).IsTotalQueryBound U) :
    (hmacPrfRandomGame (rootExpandReduction source D)).IsTotalQueryBound (64 + U) := by
  rw [rootExpandReduction, expandReduction_random]
  simpa only [unitSample, pure_bind, rootObserver] using
    OracleComp.isTotalQueryBound_bind
      (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64)
      (fun block => bounded (fromRoot source (first32 block)))

/-- Real initializer Extract retains its 32-byte input sample and all observer work. -/
theorem entry_init_extract_real_uniform (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (D : Distinguisher) (U : Nat)
    (bounded : ∀ value, (D value).IsTotalQueryBound U) :
    (extractRealGame hmac uniform32 (initExtractReduction source hmac D)).IsTotalQueryBound
      (32 + U) := by
  exact OracleComp.isTotalQueryBound_bind entry_extract_sampler_uniform (fun _ => bounded _)

/-- Random initializer Extract charges both the 32-byte input and 64-byte challenger PRK. -/
theorem entry_init_extract_random_uniform (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (D : Distinguisher) (U : Nat)
    (bounded : ∀ value, (D value).IsTotalQueryBound U) :
    (extractUniformGame uniform32 (initExtractReduction source hmac D)).IsTotalQueryBound
      (96 + U) := by
  simpa [extractUniformGame, initExtractReduction, ← Nat.add_assoc] using
    OracleComp.isTotalQueryBound_bind entry_extract_sampler_uniform (fun _ =>
      OracleComp.isTotalQueryBound_bind
        (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64) (fun key => bounded
          (fromInitializer source (hmac.eval key (firstExpandInput .ratchet)))))

/-- The initializer PRF real game samples the full 64-byte hidden key. -/
theorem entry_init_prf_real_uniform (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (D : Distinguisher) (U : Nat)
    (bounded : ∀ value, (D value).IsTotalQueryBound U) :
    (hmacPrfRealGame hmac (initExpandReduction source D)).IsTotalQueryBound (64 + U) := by
  rw [initExpand_real]
  exact OracleComp.isTotalQueryBound_bind
    (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64) (fun _ => bounded _)

/-- The initializer PRF random game charges its full 64-byte reply. -/
theorem entry_init_prf_random_uniform (source : FixedHkdfSha512NoSaltSource)
    (D : Distinguisher) (U : Nat) (bounded : ∀ value, (D value).IsTotalQueryBound U) :
    (hmacPrfRandomGame (initExpandReduction source D)).IsTotalQueryBound (64 + U) := by
  rw [initExpand_random]
  exact OracleComp.isTotalQueryBound_bind
    (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64) (fun _ => bounded _)

/-- The real step Extract game charges its input and the independently sampled opposite half. -/
theorem entry_step_extract_real_uniform (hmac : HmacSha512)
    (D : Distinguisher) (U : Nat) (bounded : ∀ value, (D value).IsTotalQueryBound U) :
    (extractRealGame hmac uniform32 (stepExtractReduction hmac D)).IsTotalQueryBound (64 + U) := by
  simpa [extractRealGame, stepExtractReduction, fullExtractReduction, ← Nat.add_assoc] using
    OracleComp.isTotalQueryBound_bind entry_extract_sampler_uniform
      (fun pair => entry_step_observer_uniform D U bounded pair.1
        (expandFull hmac .ratchet (extract hmac pair.2)))

/-- Random step Extract charges the 32-byte input, 64-byte challenger PRK and 32-byte opposite half, without dropping unused draws. -/
theorem entry_step_extract_random_uniform (hmac : HmacSha512)
    (D : Distinguisher) (U : Nat) (bounded : ∀ value, (D value).IsTotalQueryBound U) :
    (extractUniformGame uniform32 (stepExtractReduction hmac D)).IsTotalQueryBound (128 + U) := by
  simpa only [stepExtractReduction, ← Nat.add_assoc] using
    fullExtractUniform_uniform_query_bound hmac .ratchet uniform32 (stepObserver D)
      entry_extract_sampler_uniform (entry_step_observer_uniform D U bounded)

/-- The real step PRF game charges its 64-byte secret key and 32-byte opposite half. -/
theorem entry_step_prf_real_uniform (hmac : HmacSha512)
    (D : Distinguisher) (U : Nat) (bounded : ∀ value, (D value).IsTotalQueryBound U) :
    (hmacPrfRealGame hmac (stepExpandReduction D)).IsTotalQueryBound (96 + U) := by
  simpa only [stepExpandReduction, Nat.zero_add, ← Nat.add_assoc] using
    fullHmacReal_uniform_query_bound hmac .ratchet unitSample (stepObserver D)
      (qSample := 0) (by simp [unitSample, IsTotalQueryBound, isQueryBound_pure])
      (entry_step_observer_uniform D U bounded)

/-- The random step PRF challenger charges both full 64-byte blocks and the 32-byte opposite half. -/
theorem entry_step_prf_random_uniform (D : Distinguisher) (U : Nat)
    (bounded : ∀ value, (D value).IsTotalQueryBound U) :
    (hmacPrfRandomGame (stepExpandReduction D)).IsTotalQueryBound (160 + U) := by
  exact (fullHmacRandom_uniform_query_bound .ratchet unitSample (stepObserver D)
    (qSample := 0) (by simp [unitSample, IsTotalQueryBound, isQueryBound_pure])
    (entry_step_observer_uniform D U bounded)).mono (by omega)

/-- The actual pair sampler charges all 76 step bytes and all 32 opposite-direction bytes. -/
theorem entry_output_uniform : ($ᵗ Output : ProbComp Output).IsTotalQueryBound 108 := by
  simp only [← pairSample]
  exact OracleComp.isTotalQueryBound_bind
    (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76) (fun full =>
      OracleComp.isTotalQueryBound_bind
        (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
        (fun other => show (pure (full, other) : ProbComp Output).IsTotalQueryBound 0 from by trivial))

/-- The complete ordinary primitive-game ledger for one key-schedule distinguisher. Challenge calls, reduction coins and challenger coins are separate fields. This is a proved resource record, not a security contract. -/
structure EntryComponentBills (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (D : Distinguisher) (U : Nat) : Prop where
  rootQueries : (rootExpandReduction source D).IsQueryBoundP IsHmacChallengeQuery 1
  initQueries : (initExpandReduction source D).IsQueryBoundP IsHmacChallengeQuery 1
  stepQueries : (stepExpandReduction D).IsQueryBoundP IsHmacChallengeQuery 2
  rootCoins : (rootExpandReduction source D).IsQueryBoundP IsHmacUniformQuery U
  initCoins : (initExpandReduction source D).IsQueryBoundP IsHmacUniformQuery U
  stepCoins : (stepExpandReduction D).IsQueryBoundP IsHmacUniformQuery (32 + U)
  rootReal : (hmacPrfRealGame hmac (rootExpandReduction source D)).IsTotalQueryBound (64 + U)
  rootRandom : (hmacPrfRandomGame (rootExpandReduction source D)).IsTotalQueryBound (64 + U)
  initExtractReal :
    (extractRealGame hmac uniform32 (initExtractReduction source hmac D)).IsTotalQueryBound (32 + U)
  initExtractRandom :
    (extractUniformGame uniform32 (initExtractReduction source hmac D)).IsTotalQueryBound (96 + U)
  initReal : (hmacPrfRealGame hmac (initExpandReduction source D)).IsTotalQueryBound (64 + U)
  initRandom : (hmacPrfRandomGame (initExpandReduction source D)).IsTotalQueryBound (64 + U)
  stepExtractReal :
    (extractRealGame hmac uniform32 (stepExtractReduction hmac D)).IsTotalQueryBound (64 + U)
  stepExtractRandom :
    (extractUniformGame uniform32 (stepExtractReduction hmac D)).IsTotalQueryBound (128 + U)
  stepReal : (hmacPrfRealGame hmac (stepExpandReduction D)).IsTotalQueryBound (96 + U)
  stepRandom : (hmacPrfRandomGame (stepExpandReduction D)).IsTotalQueryBound (160 + U)

/-- Every field follows from the literal reduction definitions and the complete observer bill. The concrete source consumer below discharges that observer bill. -/
theorem entry_component_bills (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (D : Distinguisher) (U : Nat) (bounded : ∀ value, (D value).IsTotalQueryBound U) :
    EntryComponentBills source hmac D U := by
  exact ⟨rootExpandReduction_query_bound source D, initExpandReduction_query_bound source D,
    stepExpandReduction_query_bound D, entry_root_prf_uniform source D U bounded,
    entry_init_prf_uniform source D U bounded, entry_step_prf_uniform D U bounded,
    entry_root_prf_real_uniform source hmac D U bounded,
    entry_root_prf_random_uniform source D U bounded,
    entry_init_extract_real_uniform source hmac D U bounded,
    entry_init_extract_random_uniform source hmac D U bounded,
    entry_init_prf_real_uniform source hmac D U bounded,
    entry_init_prf_random_uniform source D U bounded,
    entry_step_extract_real_uniform hmac D U bounded,
    entry_step_extract_random_uniform hmac D U bounded,
    entry_step_prf_real_uniform hmac D U bounded,
    entry_step_prf_random_uniform D U bounded⟩

open PqxdhServerAuthExperiment PqxdhServerAuthSourceCosts PqxdhServerAuthGapDh PqxdhServerAuthBodyCosts
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- All five ordinary reduction games have the concrete source-derived ledger. Every ambient callback is covered by the actual entry reduction's checked budget, with no opaque observer-cost or security premise. -/
theorem actual_entry_component_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (revealSeed : Bool) (j : Fin (Q + 1)) :
    EntryComponentBills setup.source setup.hmac
      (entryReduction setup codec checks adversary revealSeed Q j)
      (entryReductionBudget caps qCoin Q qHash qH) := by
  exact entry_component_bills setup.source setup.hmac _ _
    (entry_reduction_uniform setup codec checks caps bounded adversary qCoin Q qHash qH
      coins accepts hashes rom revealSeed j)

/-- The actual factored source and uniform-output games retain their original context-first order and charge the additional 64/108-byte samples explicitly. -/
theorem actual_entry_games_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (revealSeed : Bool) (j : Fin (Q + 1)) :
    (realEntryGame setup codec checks adversary revealSeed Q j).IsTotalQueryBound
      (entryReductionBudget caps qCoin Q qHash qH + 64) ∧
    (uniformEntryGame setup codec checks adversary revealSeed Q j).IsTotalQueryBound
      (entryReductionBudget caps qCoin Q qHash qH + 108) := by
  constructor
  · unfold realEntryGame
    apply (OracleComp.isTotalQueryBound_bind (n₂ := 64 + entryRunBudget caps qCoin Q qHash qH)
      (context_uniform setup codec caps bounded) ?_).mono
      (by simp only [entryReductionBudget]; omega)
    intro context
    apply OracleComp.isTotalQueryBound_bind
      (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64)
    intro prk
    rw [source_hidden_factor]
    exact entry_distinguisher_uniform setup codec checks caps bounded adversary qCoin Q qHash qH
      coins accepts hashes rom revealSeed j context _
  · unfold uniformEntryGame
    apply (OracleComp.isTotalQueryBound_bind (n₂ := 108 + entryRunBudget caps qCoin Q qHash qH)
      (context_uniform setup codec caps bounded) ?_).mono
      (by simp only [entryReductionBudget]; omega)
    intro context
    exact OracleComp.isTotalQueryBound_bind entry_output_uniform
      (entry_distinguisher_uniform setup codec checks caps bounded adversary qCoin Q qHash qH
        coins accepts hashes rom revealSeed j context)

/-- The per-entry source authentication bound and every constructed primitive-game bill in one statement. All source-work obligations are discharged from actual KEM and adversary interface caps. -/
theorem entry_bound_with_resources (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (revealSeed : Bool) (j : Fin (Q + 1))
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (𝒟[actualEntryGame setup codec checks adversary revealSeed Q j] {true}).toReal ≤
      (𝒟[uniformEntryGame setup codec checks adversary revealSeed Q j] {true}).toReal +
        entryScheduleLoss setup codec checks adversary revealSeed Q j ∧
    EntryComponentBills setup.source setup.hmac
      (entryReduction setup codec checks adversary revealSeed Q j)
      (entryReductionBudget caps qCoin Q qHash qH) := by
  exact ⟨entry_le_uniform setup codec checks adversary revealSeed Q j correct,
    actual_entry_component_bills setup codec checks caps bounded adversary qCoin Q qHash qH
      coins accepts hashes rom revealSeed j⟩

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_extract_sampler_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_extract_sampler_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_step_observer_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_step_observer_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_root_prf_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_root_prf_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_init_prf_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_init_prf_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_step_prf_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_step_prf_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_root_prf_real_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_root_prf_real_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_root_prf_random_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_root_prf_random_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_init_extract_real_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_init_extract_real_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_init_extract_random_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_init_extract_random_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_init_prf_real_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_init_prf_real_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_init_prf_random_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_init_prf_random_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_step_extract_real_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_step_extract_real_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_step_extract_random_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_step_extract_random_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_step_prf_real_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_step_prf_real_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_step_prf_random_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_step_prf_random_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_output_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_output_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_component_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_component_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.actual_entry_component_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.actual_entry_component_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.actual_entry_games_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.actual_entry_games_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_bound_with_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_bound_with_resources
