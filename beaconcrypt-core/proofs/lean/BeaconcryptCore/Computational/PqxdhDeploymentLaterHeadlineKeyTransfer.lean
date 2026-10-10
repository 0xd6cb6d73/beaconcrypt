-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain

/-!
# CE-KT-L: later-quantum key transfer of the common deployment experiment (CE-12 P3, design.md section 9.1)

The headline CE-KT-L (VC rows passive-quantum 168-173 with the KEM key transfer, design-v2 section 12): for every setup, codec, checks, router, runtime initializer, fresh bounds, run-phase adversary `first` within its budget, post adversary `second` within a post budget on every input, and runtime state, with identity index 0 and `supplied = none`, an arbitrary event and claim of the LQ-F observation (the post adversary's output after the reveal, the run-phase ledger and the produced frames) of the LQ-F game (`PqxdhDeploymentLaterServerGame.game`), and a designated target `g = (i, k)`, the probability that the LQ-F game ends with the event and the claim designating `g` differs from the probability that the later ideal game of `g` (`PqxdhDeploymentIdealLaterGame.idealLaterGame`: the challenger's draws, then the later game with the ideal registration of the target, in which item 2's two hidden entries are uniform values of a lazily sampled two-entry table keyed by their 128-byte DH coordinates, and the real post phase) ends with the same decision (`ceDecideL`) by at most `kemLossL g d_g + slotLossL g d_g`.

- `ce_kt_later` (one-sided), `ce_kt_later_close` (two-sided), `ce_kt_later_sum_le` and `ce_kt_later_sum` (summed over the tight target domain `Fin qAccept × Fin qCreate` by the exact split `PqxdhDeploymentLaterTargetRange.split_create_later`, coefficient one, no selection factor).
- World forms (`ce_kt_later_world`, `ce_kt_later_world_close`, `ce_kt_later_world_sum`): the same with the later record world with the ideal environment of the target of `g` and the environment's reveal (`PqxdhRecordLiftLater.run` with `PqxdhDeploymentIdealEnv.envGD` and `envReveal`) on the right, through `PqxdhDeploymentLaterHeadlineChain.ideal_world_later` (U-L2 and U-L3 are equalities).

The bill is `kemLossL` (one ML-KEM IND-CCA advantage of the logged per-target proof-carrying adversary plus the correctness error) plus `slotLossL` (item 2 over the logged source at two slots: `(qAccept + qFinish + qHmac + qHmac₂)/2^256`, two HMAC-PRF advantages and the key-schedule bounds of the two hidden entries, each of four Extract-on-uniform32 and HMAC-PRF advantages). Premises: `FunctionalDecapsulation setup.kem`, `Phase1ReadBack`, `Phase2ReadBack`, `SourceFullCorrect setup.source setup.hmac`, `budget.Respects first` and the post budget of `second` (`slotLossL` is evaluated at the transported caps of the compiled program, `PqxdhDeploymentLaterServerItemKeys.later_slots_two`). CE-KT-L is a confidentiality transfer, not `attacker(root)` secrecy: the ideal probability stays on the right. The post adversary sees the Server seed, every generated ephemeral and every Beacon secret of the profile, so the two hidden entries' DH coordinates are known to it; their unpredictability and independence rest on route R1 alone (the sharpened R1 caveat of `later_slots_two`). No origin, binding or authentication statement is made, and no theorem A2, T5 or T8 is cited on the later compiled program. No new assumption or contract.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineKeyTransfer
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLaterServerTransfer (happens designated)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealHandoff (decisionOn)
open PqxdhDeploymentEnvironmentJoin (envReveal)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Out : Type}

/-- **CE-KT-L, one-sided**: the probability that the LQ-F game ends with the event and the claim designating `g` is at most the probability that the later ideal game of `g` ends with the same decision, plus `kemLossL g d_g` and `slotLossL g d_g`. -/
theorem ce_kt_later (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} ≤
      𝒟[PqxdhDeploymentIdealLaterGame.ceDecideL setup codec budget event claim g <$>
        (PqxdhDeploymentIdealLaterGame.idealLaterGame setup codec route checks budget g ensureInit bounds mode first
          second).run runtime] {true} +
      ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds mode first second budget event claim g
        runtime) +
      ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds mode first second budget
        post event claim g runtime) :=
  PqxdhDeploymentLaterHeadlineChain.chain_ideal_later setup functional codec checks route ensureInit phase1 phase2
    correct bounds mode first second budget respects post postRespects event claim g runtime

/-- **CE-KT-L, two-sided** (design.md section 9.1, `|Pr_LQF[D_g] − Pr_{IL_g}[D_g]| ≤ kemLossL g d_g + slotLossL g d_g`): the probability that the LQ-F game ends with the event and the claim designating `g` and the probability that the later ideal game of `g` ends with the same decision differ by at most `kemLossL + slotLossL`. -/
theorem ce_kt_later_close (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    |(𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true}).toReal -
      (𝒟[PqxdhDeploymentIdealLaterGame.ceDecideL setup codec budget event claim g <$>
        (PqxdhDeploymentIdealLaterGame.idealLaterGame setup codec route checks budget g ensureInit bounds mode first
          second).run runtime] {true}).toReal| ≤
      kemLossL setup codec checks route ensureInit bounds mode first second budget event claim g runtime +
        slotLossL (Reader := Reader) setup codec checks route ensureInit bounds mode first second budget post event
          claim g runtime :=
  PqxdhDeploymentLaterHeadlineChain.chain_ideal_later_close setup functional codec checks route ensureInit phase1
    phase2 correct bounds mode first second budget respects post postRespects event claim g runtime

/-- **CE-KT-L, summed, one-sided**: the probability that the LQ-F game ends with the event and the claim designated at all (plain eligibility `PqxdhDeploymentLaterTargetRange.eligibleL`) is at most the sum over `g` in `Fin qAccept × Fin qCreate` (with `k` read in `Fin (qCreate + 1)`) of the probability that the later ideal game of `g` ends with `g`'s decision, plus `kemLossL` and `slotLossL` of `g`, each with coefficient one. -/
theorem ce_kt_later_sum_le (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        (PqxdhDeploymentLaterTargetRange.eligibleL setup.source.crypto codec setup.serverKeyId claim
          outcome).isSome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[PqxdhDeploymentIdealLaterGame.ceDecideL setup codec budget event claim (g.1, g.2.castSucc) <$>
            (PqxdhDeploymentIdealLaterGame.idealLaterGame setup codec route checks budget (g.1, g.2.castSucc)
              ensureInit bounds mode first second).run runtime] {true} +
          ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds mode first second budget event claim
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds mode first second
            budget post event claim (g.1, g.2.castSucc) runtime)) := by
  rw [PqxdhDeploymentLaterTargetRange.split_create_later setup codec checks route ensureInit phase1 phase2 bounds mode
    first second budget respects event claim runtime]
  exact Finset.sum_le_sum fun g _ => ce_kt_later setup functional codec checks route ensureInit phase1 phase2 correct
    bounds mode first second budget respects post postRespects event claim (g.1, g.2.castSucc) runtime

/-- **CE-KT-L, summed, two-sided**: the probability that the LQ-F game ends with the event and the claim designated at all, and the sum over `g` in `Fin qAccept × Fin qCreate` of the probability that the later ideal game of `g` ends with `g`'s decision, differ by at most the sum over the same targets of `kemLossL + slotLossL`. -/
theorem ce_kt_later_sum (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (runtime : A) :
    |(𝒟[(fun outcome => decide (happens event outcome = true ∧
        (PqxdhDeploymentLaterTargetRange.eligibleL setup.source.crypto codec setup.serverKeyId claim
          outcome).isSome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true}).toReal -
      ∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[PqxdhDeploymentIdealLaterGame.ceDecideL setup codec budget event claim (g.1, g.2.castSucc) <$>
            (PqxdhDeploymentIdealLaterGame.idealLaterGame setup codec route checks budget (g.1, g.2.castSucc)
              ensureInit bounds mode first second).run runtime] {true}).toReal| ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (kemLossL setup codec checks route ensureInit bounds mode first second budget event claim (g.1, g.2.castSucc)
            runtime +
          slotLossL (Reader := Reader) setup codec checks route ensureInit bounds mode first second budget post event
            claim (g.1, g.2.castSucc) runtime) := by
  rw [PqxdhDeploymentLaterTargetRange.split_create_later setup codec checks route ensureInit phase1 phase2 bounds mode
    first second budget respects event claim runtime]
  exact PqxdhDeploymentKemTwoSided.abs_sum_sub_le _ _ _ (fun _ => UniformTargetSelection.chance_ne_top _ _) fun g =>
    ce_kt_later_close setup functional codec checks route ensureInit phase1 phase2 correct bounds mode first second
      budget respects post postRespects event claim (g.1, g.2.castSucc) runtime

/-- **CE-KT-L, World form, one-sided**: the probability that the LQ-F game ends with the event and the claim designating `g` is at most the probability of the per-target decision on the later record world with the ideal environment of the target of `g` and the environment's reveal (`PqxdhDeploymentLaterHeadlineChain.ideal_world_later`), plus `kemLossL g d_g` and `slotLossL g d_g`. -/
theorem ce_kt_later_world (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} ≤
      𝒟[(fun result => (PqxdhRecordLiftWorld.observed result).any (decisionOn setup codec budget event claim g)) <$>
        PqxdhRecordLiftLater.run setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode envReveal first second] {true} +
      ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds mode first second budget event claim g
        runtime) +
      ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds mode first second budget
        post event claim g runtime) := by
  rw [← PqxdhDeploymentLaterHeadlineChain.ideal_world_later (Reader := Reader) setup codec checks route ensureInit
    phase1 phase2 bounds mode first second budget respects event claim g runtime]
  exact PqxdhDeploymentLaterHeadlineChain.chain_slot_later setup functional codec checks route ensureInit phase1 phase2
    correct bounds mode first second budget respects post postRespects event claim g runtime

/-- **CE-KT-L, World form, two-sided**: the probability that the LQ-F game ends with the event and the claim designating `g` and the probability of the per-target decision on the later record world with the ideal environment of the target of `g` and the environment's reveal differ by at most `kemLossL g d_g + slotLossL g d_g`. -/
theorem ce_kt_later_world_close (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    |(𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true}).toReal -
      (𝒟[(fun result => (PqxdhRecordLiftWorld.observed result).any (decisionOn setup codec budget event claim g)) <$>
        PqxdhRecordLiftLater.run setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode envReveal first second] {true}).toReal| ≤
      kemLossL setup codec checks route ensureInit bounds mode first second budget event claim g runtime +
        slotLossL (Reader := Reader) setup codec checks route ensureInit bounds mode first second budget post event
          claim g runtime := by
  rw [← PqxdhDeploymentLaterHeadlineChain.ideal_world_later (Reader := Reader) setup codec checks route ensureInit
    phase1 phase2 bounds mode first second budget respects event claim g runtime]
  exact PqxdhDeploymentLaterHeadlineChain.chain_slot_later_close setup functional codec checks route ensureInit phase1
    phase2 correct bounds mode first second budget respects post postRespects event claim g runtime

/-- **CE-KT-L, World form, summed, two-sided**: the probability that the LQ-F game ends with the event and the claim designated at all, and the sum over `g` in `Fin qAccept × Fin qCreate` of the probability of `g`'s decision on the later record world with the ideal environment of the target of `g` and the environment's reveal, differ by at most the sum over the same targets of `kemLossL + slotLossL`. -/
theorem ce_kt_later_world_sum (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (runtime : A) :
    |(𝒟[(fun outcome => decide (happens event outcome = true ∧
        (PqxdhDeploymentLaterTargetRange.eligibleL setup.source.crypto codec setup.serverKeyId claim
          outcome).isSome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true}).toReal -
      ∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[(fun result => (PqxdhRecordLiftWorld.observed result).any
            (decisionOn setup codec budget event claim (g.1, g.2.castSucc))) <$>
          PqxdhRecordLiftLater.run setup codec route
            (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget (g.1, g.2.castSucc)) ensureInit 0
              runtime) setup.serverKeyId bounds mode envReveal first second] {true}).toReal| ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (kemLossL setup codec checks route ensureInit bounds mode first second budget event claim (g.1, g.2.castSucc)
            runtime +
          slotLossL (Reader := Reader) setup codec checks route ensureInit bounds mode first second budget post event
            claim (g.1, g.2.castSucc) runtime) := by
  rw [PqxdhDeploymentLaterTargetRange.split_create_later setup codec checks route ensureInit phase1 phase2 bounds mode
    first second budget respects event claim runtime]
  exact PqxdhDeploymentKemTwoSided.abs_sum_sub_le _ _ _ (fun _ => UniformTargetSelection.chance_ne_top _ _) fun g =>
    ce_kt_later_world_close setup functional codec checks route ensureInit phase1 phase2 correct bounds mode first
      second budget respects post postRespects event claim (g.1, g.2.castSucc) runtime

end BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineKeyTransfer

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_close

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_sum_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_sum_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_sum

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_world

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_world_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_world_close

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_world_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_world_sum
