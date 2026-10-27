-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftChainHop

/-! The complete ordered chain hybrid. Index zero of `PqxdhRecordLiftChainOrder` is `realChains` (`PqxdhRecordLiftIdeal.chains_selected_zero`). The last index `selected (positions budget) (hops n budget)` is ideal exactly on the coordinates of depth below `positions budget = sends + 51 * receives`; for every adversary within its budget it is `idealChains` (`chains_terminal`), because every coordinate that the run looks up is populated in the final table, whose depth is bounded by the executed native KDF count (`PqxdhRecordLiftMixedWorld.run_depth`). This support-level congruence uses the generic supported-prefix lemmas of `PqxdhRecordLiftSeedPolicy`. Telescoping the hops of `PqxdhRecordLiftChainHop` over all `hops n budget` indices gives the chain bound `chain_bound` and its `ENNReal` form `chain_loss`: real and chain-ideal worlds differ, for every decision on the permitted view and the final shared cache, by at most the sum over the indices of the Extract-on-`uniform32` and HMAC-PRF advantages of the explicit observers, each with coefficient one. No aliasing or refusal term arises: every hop changes the mode of one labelled coordinate only, and the world never refuses a chain callback. Contract: `SourceFullCorrect`. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftChainHybrid
open PqxdhRecordLiftInterface PqxdhRecordLiftProtocol PqxdhFullSecretInputKdf PqxdhSecretInputKdf
open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable PqxdhRecordLiftChainOrder
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds Budget)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

/-! ### The terminal hybrid -/

/-- Every lookup reached by the terminal hybrid's run is at a coordinate of bounded depth, where the terminal selector is ideal: the coordinate is populated in every supported final table, whose depth is bounded by the executed native KDF count. -/
theorem terminal_safe (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Aeneas.Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) :
    PqxdhRecordLiftAvailability.Safe
      (interpreter (PqxdhRecordLiftMixedWorld.policy setup.source
        (selected (PqxdhRecordLiftIdeal.positions budget) (PqxdhRecordLiftIdeal.hops n budget))) setup codec)
      (fun query _ => PqxdhRecordLiftPrefixPolicy.AgreesAt
        (selected (PqxdhRecordLiftIdeal.positions budget) (PqxdhRecordLiftIdeal.hops n budget)) (fun _ => true) query)
      (program env setup.source.crypto codec route serverKid bounds mode adversary) initialPrivate := by
  apply PqxdhRecordLiftSeedPolicy.safe_of_reaches
  intro query next after reached
  cases query with
  | lookup coordinate =>
      change selected (PqxdhRecordLiftIdeal.positions budget) (PqxdhRecordLiftIdeal.hops n budget) coordinate = true
      rw [PqxdhRecordLiftIdeal.hops, selected_last]
      obtain ⟨step, member⟩ := OracleComp.support_nonempty
        ((interpreter (PqxdhRecordLiftChainOracle.lookup setup.source ·
          (selected (PqxdhRecordLiftIdeal.positions budget) (PqxdhRecordLiftIdeal.hops n budget))) setup codec
          (.lookup coordinate)).run after)
      obtain ⟨final, finalMember⟩ := OracleComp.support_nonempty
        ((simulateQ (interpreter (PqxdhRecordLiftChainOracle.lookup setup.source ·
          (selected (PqxdhRecordLiftIdeal.positions budget) (PqxdhRecordLiftIdeal.hops n budget))) setup codec)
          (next step.1)).run step.2)
      have present := simulateQ_run_preservesInv _ _
        (PqxdhRecordLiftSeedPolicy.present_preserved setup.source _ setup codec coordinate) (next step.1) step.2
        (PqxdhRecordLiftSeedPolicy.lookup_present setup.source _ setup codec coordinate after step member)
        final finalMember
      have whole := PqxdhRecordLiftSeedPolicy.reaches_final
        (PqxdhRecordLiftSeedPolicy.reaches_step reached step member) final finalMember
      have depth := (PqxdhRecordLiftMixedWorld.protocol_run_bounds setup codec
        (selected (PqxdhRecordLiftIdeal.positions budget) (PqxdhRecordLiftIdeal.hops n budget)) route env serverKid
        bounds mode budget adversary respects final whole).2
      obtain ⟨value, found⟩ := Option.ne_none_iff_exists'.mp present
      exact depth coordinate value found
  | _ => trivial

/-- The terminal ordered hybrid is the chain-ideal world for every adversary within its budget. -/
theorem chains_terminal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Aeneas.Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) :
    PqxdhRecordLiftIdeal.chains
        (selected (PqxdhRecordLiftIdeal.positions budget) (PqxdhRecordLiftIdeal.hops n budget))
        setup codec route env serverKid bounds mode adversary =
      PqxdhRecordLiftIdeal.idealChains setup codec route env serverKid bounds mode adversary :=
  PqxdhRecordLiftSeedPolicy.run_agrees setup codec _ (fun _ => true) _ initialPrivate
    (terminal_safe setup codec route env serverKid bounds mode adversary budget respects)

/-! ### Telescope -/

/-- The first and last of a finite sequence of Boolean games differ by at most the sum of the adjacent advantages. -/
theorem telescope (games : Nat → ProbComp Bool) (count : Nat) :
    (games 0).boolDistance (games count) ≤
      ∑ index ∈ Finset.range count, (games index).boolDistance (games (index + 1)) := by
  induction count with
  | zero => simp only [ProbComp.boolDistance_self, Finset.range_zero, Finset.sum_empty, le_refl]
  | succ count ih =>
      rw [Finset.sum_range_succ]
      exact (ProbComp.boolDistance_triangle _ (games count) _).trans (add_le_add ih (le_refl _))

/-- The Extract-on-`uniform32` advantage of one full76 observer. -/
noncomputable def extractAdvantage (hmac : HmacSha512) (observer : FullObserver Unit) : ℝ :=
  (extractRealGame hmac PqxdhServerAuthKeySchedule.uniform32 (fullExtractReduction hmac .ratchet observer)).boolDistance
    (extractUniformGame PqxdhServerAuthKeySchedule.uniform32 (fullExtractReduction hmac .ratchet observer))

/-- The HMAC-PRF advantage of one full76 observer. -/
noncomputable def prfAdvantage (hmac : HmacSha512) (observer : FullObserver Unit) : ℝ :=
  (hmacPrfRealGame hmac (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32 observer)).boolDistance
    (hmacPrfRandomGame (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32 observer))

/-- The loss of `PqxdhRecordLiftIdeal.hopLoss` is the sum of the two real advantages, each with coefficient one. -/
theorem hopLoss_eq (hmac : HmacSha512) (observer : FullObserver Unit) :
    PqxdhRecordLiftIdeal.hopLoss hmac observer =
      ENNReal.ofReal (extractAdvantage hmac observer) + ENNReal.ofReal (prfAdvantage hmac observer) := rfl

/-- The explicit full76 observer of one ordered index of the hybrid over `hops n budget` indices. -/
noncomputable def observerAt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Aeneas.Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (decision : PqxdhRecordLiftIdeal.View n E X → CtxRomAuth.CtxRO.QueryCache → ProbComp Bool)
    (budget : Budget) (step : Fin (PqxdhRecordLiftIdeal.hops n budget)) : FullObserver Unit :=
  PqxdhRecordLiftChainHop.hopObserver setup codec route env serverKid bounds mode adversary decision
    (PqxdhRecordLiftIdeal.positions budget) step

/-- The chain bound: for every environment, every adversary within its budget and every decision on the permitted view and the final shared cache, the real and chain-ideal worlds differ by at most the sum over the `hops n budget` ordered indices of the Extract-on-`uniform32` and HMAC-PRF advantages of the explicit observers `hopObserver`, each with coefficient one. Contract: `SourceFullCorrect`. -/
theorem chain_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Aeneas.Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (hmac : HmacSha512) (correct : SourceFullCorrect setup.source hmac) (budget : Budget)
    (respects : budget.Respects adversary)
    (decision : PqxdhRecordLiftIdeal.View n E X → CtxRomAuth.CtxRO.QueryCache → ProbComp Bool) :
    (PqxdhRecordLiftIdeal.realChains setup codec route env serverKid bounds mode adversary >>= fun result =>
        decision (PqxdhRecordLiftIdeal.chainView result) (PqxdhRecordLiftIdeal.chainCache result)).boolDistance
      (PqxdhRecordLiftIdeal.idealChains setup codec route env serverKid bounds mode adversary >>= fun result =>
        decision (PqxdhRecordLiftIdeal.chainView result) (PqxdhRecordLiftIdeal.chainCache result)) ≤
    ∑ step : Fin (PqxdhRecordLiftIdeal.hops n budget),
      (extractAdvantage hmac (observerAt setup codec route env serverKid bounds mode adversary decision budget step) +
        prfAdvantage hmac (observerAt setup codec route env serverKid bounds mode adversary decision budget step)) := by
  let games : Nat → ProbComp Bool := fun index =>
    PqxdhRecordLiftIdeal.chains (selected (PqxdhRecordLiftIdeal.positions budget) index) setup codec route env
      serverKid bounds mode adversary >>= fun result =>
        decision (PqxdhRecordLiftIdeal.chainView result) (PqxdhRecordLiftIdeal.chainCache result)
  have first : (PqxdhRecordLiftIdeal.realChains setup codec route env serverKid bounds mode adversary >>= fun result =>
      decision (PqxdhRecordLiftIdeal.chainView result) (PqxdhRecordLiftIdeal.chainCache result)) = games 0 := by
    simp only [games, PqxdhRecordLiftIdeal.chains_selected_zero]
  have last : (PqxdhRecordLiftIdeal.idealChains setup codec route env serverKid bounds mode adversary >>= fun result =>
      decision (PqxdhRecordLiftIdeal.chainView result) (PqxdhRecordLiftIdeal.chainCache result)) =
      games (PqxdhRecordLiftIdeal.hops n budget) := by
    simp only [games, chains_terminal setup codec route env serverKid bounds mode adversary budget respects]
  rw [first, last]
  refine (telescope games _).trans ?_
  rw [← Fin.sum_univ_eq_sum_range (fun index => (games index).boolDistance (games (index + 1)))]
  apply Finset.sum_le_sum
  intro step _
  exact PqxdhRecordLiftChainHop.hop_bound setup codec route env serverKid bounds mode adversary hmac correct decision
    (PqxdhRecordLiftIdeal.positions budget) step

/-- The chain bound in the `ENNReal` form of `PqxdhRecordLiftIdeal.ChainLiftBool`, with the exact hop losses `PqxdhRecordLiftIdeal.hopLoss` of the explicit observers. Contract: `SourceFullCorrect`. -/
theorem chain_loss (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Aeneas.Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (hmac : HmacSha512) (correct : SourceFullCorrect setup.source hmac) (budget : Budget)
    (respects : budget.Respects adversary)
    (decision : PqxdhRecordLiftIdeal.View n E X → CtxRomAuth.CtxRO.QueryCache → ProbComp Bool) :
    ENNReal.ofReal
      ((PqxdhRecordLiftIdeal.realChains setup codec route env serverKid bounds mode adversary >>= fun result =>
          decision (PqxdhRecordLiftIdeal.chainView result) (PqxdhRecordLiftIdeal.chainCache result)).boolDistance
        (PqxdhRecordLiftIdeal.idealChains setup codec route env serverKid bounds mode adversary >>= fun result =>
          decision (PqxdhRecordLiftIdeal.chainView result) (PqxdhRecordLiftIdeal.chainCache result))) ≤
    ∑ step : Fin (PqxdhRecordLiftIdeal.hops n budget),
      PqxdhRecordLiftIdeal.hopLoss hmac
        (observerAt setup codec route env serverKid bounds mode adversary decision budget step) := by
  refine (ENNReal.ofReal_le_ofReal (chain_bound setup codec route env serverKid bounds mode adversary hmac correct
    budget respects decision)).trans (le_of_eq ?_)
  refine (ENNReal.ofReal_sum_of_nonneg (fun step _ => add_nonneg (abs_nonneg _) (abs_nonneg _))).trans ?_
  apply Finset.sum_congr rfl
  intro step _
  rw [hopLoss_eq]
  exact ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)

end BeaconcryptCore.Computational.PqxdhRecordLiftChainHybrid

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainHybrid.terminal_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainHybrid.terminal_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainHybrid.chains_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainHybrid.chains_terminal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainHybrid.telescope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainHybrid.telescope

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainHybrid.hopLoss_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainHybrid.hopLoss_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainHybrid.chain_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainHybrid.chain_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainHybrid.chain_loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainHybrid.chain_loss
