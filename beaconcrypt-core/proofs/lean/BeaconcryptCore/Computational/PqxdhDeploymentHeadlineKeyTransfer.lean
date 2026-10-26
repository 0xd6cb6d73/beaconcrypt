-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain

/-!
# CE-KT: key transfer of the common deployment experiment (CE-12 P1, design-v2 section 4.1)

The headline CE-KT (VC rows A1-root, S3-server and S3-beacon, design-v2 section 12): for every setup, codec, checks, router, runtime initializer, fresh bounds, budget-respecting adversary and runtime state, with identity index 0 and `supplied = none`, an arbitrary event and claim of the deployment experiment (`PqxdhDeploymentSecrecy.game`), and a designated target `g = (i, k)`, the probability that the experiment ends with the event and the claim designating `g` differs from the probability of the same decision on CE's un-compiled ideal game of `g` (`PqxdhDeploymentIdealSteps.idealGame`, in which item 2's two hidden entries, the target session's 108 bytes and owner `k`'s challenge finish, are uniform values of a lazily sampled two-entry table keyed by the 128-byte DH coordinates through item 2's first-touch allocator: one shared value when owner `k`'s finish reads at the target session's DH coordinates (the honest pairing), independent values otherwise) by at most `kemLoss g d_g + slotLoss g d_g`.

- `ce_kt` (one-sided, the probe `kt_le`), `ce_kt_close` (two-sided), `ce_kt_sum_le` and `ce_kt_sum` (summed over the tight target domain `Fin qAccept × Fin qCreate` by the exact split `PqxdhDeploymentKemTwoSided.split_create`, coefficient one, no selection factor).
- World forms (`ce_kt_world`, `ce_kt_world_close`, `ce_kt_world_sum`): the same with the record world with the ideal environment of the target of `g` (`PqxdhRecordLiftWorld.run` with `PqxdhDeploymentIdealEnv.envGD`) on the right, through CE-11b's `PqxdhDeploymentIdealHandoff.ideal_world` (C3-C4 are equalities). Design-v2 section 3 dropped these as having no consumer; they are included because the CE-12 P1 task names them.

The bill is `kemLoss` (one ML-KEM IND-CCA advantage of the per-target certified raw-ordinal adversary plus the correctness error) plus `slotLoss` (item 2's S7 with stage T at two slots: the R1 statistical term, two HMAC-PRF advantages and two key-schedule bounds, each of four Extract-on-uniform32 and HMAC-PRF advantages). Premises: `FunctionalDecapsulation setup.kem`, `Phase1ReadBack`, `Phase2ReadBack`, `SourceFullCorrect setup.source setup.hmac` and `budget.Respects adversary`. CE-KT is a transfer, not `attacker(root)` secrecy: the ideal probability stays on the right (plan section 9.7). No new assumption or contract.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineKeyTransfer
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealHandoff (decisionOn)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- **CE-KT, one-sided** (design-v2 section 4.1, the probe `kt_le`): the probability that the deployment experiment ends with the event and the claim designating `g` is at most the probability of the same decision on CE's un-compiled ideal game of `g`, plus `kemLoss g d_g` and `slotLoss g d_g`. -/
theorem ce_kt (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      𝒟[(fun outcome => decide (happens event (PqxdhDeploymentIdealBranch.classicalOf outcome) = true ∧
          designated setup.source.crypto codec setup.serverKeyId budget claim
            (PqxdhDeploymentIdealBranch.classicalOf outcome) = some g)) <$>
        (PqxdhDeploymentIdealSteps.idealGame setup codec route checks budget g ensureInit bounds mode adversary).run
          runtime] {true} +
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget event claim g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget event claim g runtime) :=
  PqxdhDeploymentHeadlineChain.chain_ideal setup functional codec checks route ensureInit phase1 phase2 correct bounds
    mode adversary budget respects event claim g runtime

/-- **CE-KT, two-sided** (design-v2 section 4.1): the probability that the deployment experiment ends with the event and the claim designating `g` and the probability of the same decision on CE's un-compiled ideal game of `g` differ by at most `kemLoss g d_g + slotLoss g d_g`. -/
theorem ce_kt_close (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    |(𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime]
        {true}).toReal -
      (𝒟[(fun outcome => decide (happens event (PqxdhDeploymentIdealBranch.classicalOf outcome) = true ∧
          designated setup.source.crypto codec setup.serverKeyId budget claim
            (PqxdhDeploymentIdealBranch.classicalOf outcome) = some g)) <$>
        (PqxdhDeploymentIdealSteps.idealGame setup codec route checks budget g ensureInit bounds mode adversary).run
          runtime] {true}).toReal| ≤
      kemLoss setup codec checks route ensureInit bounds mode adversary budget event claim g runtime +
        slotLoss setup codec checks route ensureInit bounds mode adversary budget event claim g runtime :=
  PqxdhDeploymentHeadlineChain.chain_ideal_close setup functional codec checks route ensureInit phase1 phase2 correct
    bounds mode adversary budget respects event claim g runtime

/-- **CE-KT, summed, one-sided** (design-v2 section 4.1): the probability that the deployment experiment ends with the event and the claim designated at all is at most the sum over `g` in `Fin qAccept × Fin qCreate` (with `k` read in `Fin (qCreate + 1)`) of the probability of `g`'s decision on CE's un-compiled ideal game of `g`, plus `kemLoss` and `slotLoss` of `g`, each with coefficient one. -/
theorem ce_kt_sum_le (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        (PqxdhDeploymentTargetRange.eligible setup.source.crypto codec setup.serverKeyId claim outcome).isSome)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[(fun outcome => decide (happens event (PqxdhDeploymentIdealBranch.classicalOf outcome) = true ∧
            designated setup.source.crypto codec setup.serverKeyId budget claim
              (PqxdhDeploymentIdealBranch.classicalOf outcome) =
                some ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity))) <$>
          (PqxdhDeploymentIdealSteps.idealGame setup codec route checks budget (g.1, g.2.castSucc) ensureInit bounds
            mode adversary).run runtime] {true} +
        ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget event claim
          (g.1, g.2.castSucc) runtime) +
        ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget event claim
          (g.1, g.2.castSucc) runtime)) := by
  rw [PqxdhDeploymentKemTwoSided.split_create setup codec checks route ensureInit phase1 phase2 bounds mode adversary
    budget respects event claim runtime]
  exact Finset.sum_le_sum fun g _ => ce_kt setup functional codec checks route ensureInit phase1 phase2 correct bounds
    mode adversary budget respects event claim (g.1, g.2.castSucc) runtime

/-- **CE-KT, summed, two-sided** (design-v2 section 4.1, `ce_kt_sum`): the probability that the deployment experiment ends with the event and the claim designated at all, and the sum over `g` in `Fin qAccept × Fin qCreate` of the probability of `g`'s decision on CE's un-compiled ideal game of `g`, differ by at most the sum over the same targets of `kemLoss + slotLoss`. -/
theorem ce_kt_sum (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (runtime : A) :
    |(𝒟[(fun outcome => decide (happens event outcome = true ∧
        (PqxdhDeploymentTargetRange.eligible setup.source.crypto codec setup.serverKeyId claim outcome).isSome)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime]
        {true}).toReal -
      ∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[(fun outcome => decide (happens event (PqxdhDeploymentIdealBranch.classicalOf outcome) = true ∧
            designated setup.source.crypto codec setup.serverKeyId budget claim
              (PqxdhDeploymentIdealBranch.classicalOf outcome) =
                some ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity))) <$>
          (PqxdhDeploymentIdealSteps.idealGame setup codec route checks budget (g.1, g.2.castSucc) ensureInit bounds
            mode adversary).run runtime] {true}).toReal| ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (kemLoss setup codec checks route ensureInit bounds mode adversary budget event claim (g.1, g.2.castSucc)
            runtime +
          slotLoss setup codec checks route ensureInit bounds mode adversary budget event claim (g.1, g.2.castSucc)
            runtime) := by
  rw [PqxdhDeploymentKemTwoSided.split_create setup codec checks route ensureInit phase1 phase2 bounds mode adversary
    budget respects event claim runtime]
  exact PqxdhDeploymentKemTwoSided.abs_sum_sub_le _ _ _ (fun _ => UniformTargetSelection.chance_ne_top _ _) fun g =>
    ce_kt_close setup functional codec checks route ensureInit phase1 phase2 correct bounds mode adversary budget
      respects event claim (g.1, g.2.castSucc) runtime

/-- **CE-KT, World form, one-sided**: the probability that the deployment experiment ends with the event and the claim designating `g` is at most the probability of the per-target decision on the record world with the ideal environment of the target of `g` (`PqxdhDeploymentIdealHandoff.ideal_world`), plus `kemLoss g d_g` and `slotLoss g d_g`. -/
theorem ce_kt_world (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      𝒟[(fun result => (PqxdhRecordLiftWorld.observed result).any (decisionOn setup codec budget event claim g)) <$>
        PqxdhRecordLiftWorld.run setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary] {true} +
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget event claim g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget event claim g runtime) := by
  rw [← PqxdhDeploymentIdealHandoff.ideal_world setup codec route checks phase1 phase2 ensureInit bounds mode adversary
    budget respects event claim g runtime]
  exact PqxdhDeploymentHeadlineChain.chain_slot setup functional codec checks route ensureInit phase1 phase2 correct
    bounds mode adversary budget respects event claim g runtime

/-- **CE-KT, World form, two-sided**: the probability that the deployment experiment ends with the event and the claim designating `g` and the probability of the per-target decision on the record world with the ideal environment of the target of `g` differ by at most `kemLoss g d_g + slotLoss g d_g`. -/
theorem ce_kt_world_close (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    |(𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime]
        {true}).toReal -
      (𝒟[(fun result => (PqxdhRecordLiftWorld.observed result).any (decisionOn setup codec budget event claim g)) <$>
        PqxdhRecordLiftWorld.run setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary] {true}).toReal| ≤
      kemLoss setup codec checks route ensureInit bounds mode adversary budget event claim g runtime +
        slotLoss setup codec checks route ensureInit bounds mode adversary budget event claim g runtime := by
  rw [← PqxdhDeploymentIdealHandoff.ideal_world setup codec route checks phase1 phase2 ensureInit bounds mode adversary
    budget respects event claim g runtime]
  exact PqxdhDeploymentHeadlineChain.chain_slot_close setup functional codec checks route ensureInit phase1 phase2
    correct bounds mode adversary budget respects event claim g runtime

/-- **CE-KT, World form, summed, two-sided**: the probability that the deployment experiment ends with the event and the claim designated at all, and the sum over `g` in `Fin qAccept × Fin qCreate` of the probability of `g`'s decision on the record world with the ideal environment of the target of `g`, differ by at most the sum over the same targets of `kemLoss + slotLoss`. -/
theorem ce_kt_world_sum (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (runtime : A) :
    |(𝒟[(fun outcome => decide (happens event outcome = true ∧
        (PqxdhDeploymentTargetRange.eligible setup.source.crypto codec setup.serverKeyId claim outcome).isSome)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime]
        {true}).toReal -
      ∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[(fun result => (PqxdhRecordLiftWorld.observed result).any
            (decisionOn setup codec budget event claim (g.1, g.2.castSucc))) <$>
          PqxdhRecordLiftWorld.run setup codec route
            (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget (g.1, g.2.castSucc)) ensureInit 0
              runtime) setup.serverKeyId bounds mode adversary] {true}).toReal| ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (kemLoss setup codec checks route ensureInit bounds mode adversary budget event claim (g.1, g.2.castSucc)
            runtime +
          slotLoss setup codec checks route ensureInit bounds mode adversary budget event claim (g.1, g.2.castSucc)
            runtime) := by
  rw [PqxdhDeploymentKemTwoSided.split_create setup codec checks route ensureInit phase1 phase2 bounds mode adversary
    budget respects event claim runtime]
  exact PqxdhDeploymentKemTwoSided.abs_sum_sub_le _ _ _ (fun _ => UniformTargetSelection.chance_ne_top _ _) fun g =>
    ce_kt_world_close setup functional codec checks route ensureInit phase1 phase2 correct bounds mode adversary budget
      respects event claim (g.1, g.2.castSucc) runtime

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineKeyTransfer

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineKeyTransfer.ce_kt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineKeyTransfer.ce_kt

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineKeyTransfer.ce_kt_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineKeyTransfer.ce_kt_close

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineKeyTransfer.ce_kt_sum_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineKeyTransfer.ce_kt_sum_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineKeyTransfer.ce_kt_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineKeyTransfer.ce_kt_sum

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineKeyTransfer.ce_kt_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineKeyTransfer.ce_kt_world

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineKeyTransfer.ce_kt_world_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineKeyTransfer.ce_kt_world_close

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineKeyTransfer.ce_kt_world_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineKeyTransfer.ce_kt_world_sum
