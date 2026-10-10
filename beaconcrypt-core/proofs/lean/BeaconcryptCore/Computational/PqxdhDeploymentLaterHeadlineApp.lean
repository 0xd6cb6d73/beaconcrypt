-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain
import BeaconcryptCore.Computational.PqxdhRecordFactsLaterFresh

/-!
# CE-APP-L: later-quantum fresh-message secrecy of the common deployment experiment (CE-12 P3, design.md section 9.1)

The headline CE-APP-L (VC rows passive-quantum 169-172, the fixed-name rows of the later mode, design-v2 section 12) in observation mode P: for the LQ-F game (`PqxdhDeploymentLaterServerGame.game`), the probability that the post adversary's output, produced after the post-run reveal of the Server seed, the ephemeral log and every Beacon secret of the profile, names an admitted fresh message of the run phase, sent on a designated handle, and guesses it exactly (`PqxdhDeploymentHeadlineEvents.AppWin` at the post output type) is at most the sum over the targets `g` in `Fin qAccept × Fin qCreate`, each with coefficient one, of

- `kemLossL` and `slotLossL` of `g`'s decision (the logged KEM transfer and item 2 over the logged source, `PqxdhDeploymentLaterHeadlineChain`),
- `β_g` of the run-phase adversary `first` (`PqxdhDeploymentHeadlineAnomaly.beta`: one IND-CCA advantage of the predict-then-compare adversary built from `first`'s anomaly guesser, the correctness error and `2^-256`; the anomaly is a run-phase event, `PqxdhDeploymentIdealLaterSlots.later_anomaly_eq`),
- `recLossL` of the view event `dec_g ∧ IS_g`, the later record-lift loss (`PqxdhRecordLiftLaterLift.later_record_lift`: later chain, integrity and privacy reductions, with the environment's reveal and the post budget),
- `2^-min`, the final-world guessing term (`PqxdhRecordFactsLaterFresh.later_idealRecords_fresh`).

`ce_app_later_target` is the per-target form and `ce_app_later` the summed form. `ce_app_server_later` and `ce_app_server_later_target` restrict the win to a fresh message on a Server peer (`AppWinPeer`) and drop `β_g`, using only the Server-side slot conjuncts (`PqxdhDeploymentLaterHeadlineChain.later_real_slots_server`). The chain is C1-C6 (`chain_beta_later`, `chain_server_later`), C7 (`records_le_later` at the frame of `frame_idealD`), the containment `PqxdhDeploymentHeadlineContain.app_hit` / `app_peer_hit` at the post output type and `LaterFreshGuessStatement`.

Premises: `FunctionalDecapsulation setup.kem`, `Phase1ReadBack`, `Phase2ReadBack`, `SourceFullCorrect setup.source setup.hmac`, `KemBound setup caps`, the total query bound `qInit` of the runtime initializer, `budget.Respects first` and the post budget of `second` on every input; the AEAD forgery fallback is a parameter of the integrity loss. The final term is per target, so the sum carries `qAccept · qCreate · 2^-min`. Later mode claims confidentiality only: no origin, binding or authentication statement, no theorem A2, T5 or T8 on the later compiled program. No new assumption or contract.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineApp
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLaterServerTransfer (happens designated)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentEnvironmentJoin (envReveal)
open PqxdhRecordLiftIdeal (ctxView)
open PqxdhRecordLiftLaterWorlds (laterIdealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Out : Type}

/-- The final-world guessing term on the record lift's view of `laterIdealRecords` (mode P) with the ideal environment of a target and the environment's reveal, for a claim read from the post adversary's output (`PqxdhRecordFactsLaterFresh.later_idealRecords_fresh`). -/
theorem fresh_final_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) (appClaim : Out → Option (Nat × Pqxdh.Bytes)) :
    𝒟[PqxdhRecordLiftIdeal.freshEvent appClaim <$> (ctxView <$> laterIdealRecords setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds .P envReveal first second)] {true} ≤ ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [Functor.map_map]
  exact PqxdhRecordFactsLaterFresh.later_idealRecords_fresh setup codec route setup.serverKeyId bounds 2 _ envReveal
    first second appClaim

/-- **CE-APP-L, per target**: in mode P, the probability that the LQ-F game ends with the CE-APP win of the post adversary's output and its claimed fresh message's handle designating `g` is at most `kemLossL + slotLossL + β_g(first) + recLossL(dec_g ∧ IS_g) + 2^-min`. -/
theorem ce_app_later_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes))
    (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[(fun outcome => decide (happens (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) outcome =
        true ∧ designated setup.source.crypto codec setup.serverKeyId budget (appHandle appClaim) outcome = some g)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime]
        {true} ≤
      ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
        (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime) +
      ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second budget post
        (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime) +
      beta setup codec route checks ensureInit bounds .P first budget g runtime +
      recLossL setup codec checks route ensureInit bounds .P first second budget post g runtime fallback caps qInit
        (slotted setup codec budget (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
          (appHandle appClaim) g) +
      ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ := by
  have chain := PqxdhDeploymentLaterHeadlineChain.chain_beta_later (Reader := Reader) setup functional codec checks
    route ensureInit phase1 phase2 correct bounds .P first second budget respects post postRespects
    (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime
  have lift := PqxdhDeploymentLaterHeadlineChain.records_le_later setup codec checks route correct caps bounded
    ensureInit qInit initBound bounds .P first second budget respects post postRespects g runtime fallback
    (slotted setup codec budget (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
      (appHandle appClaim) g)
  have hit := PqxdhDeploymentHeadlineContain.chance_mono
    (ctxView <$> laterIdealRecords setup codec route
      (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
      setup.serverKeyId bounds .P envReveal first second) _ _
    (PqxdhDeploymentHeadlineContain.app_hit setup codec budget appClaim g)
  have final := fresh_final_later setup codec checks route ensureInit bounds first second budget g runtime appClaim
  calc _ ≤ _ := chain
    _ ≤ ((((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ +
          recLossL setup codec checks route ensureInit bounds .P first second budget post g runtime fallback caps qInit
            (slotted setup codec budget (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
              (appHandle appClaim) g)) +
        beta setup codec route checks ensureInit bounds .P first budget g runtime +
        ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
          (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime)) +
        ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second budget
          post (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g
          runtime) :=
        add_le_add (add_le_add (add_le_add (lift.trans (add_le_add (hit.trans final) le_rfl)) le_rfl) le_rfl) le_rfl
    _ = _ := by ring

/-- **CE-APP-L** (design.md section 9.1): in mode P, the probability that the LQ-F game ends with the CE-APP win of the post adversary's output is at most the sum over `g` in `Fin qAccept × Fin qCreate` (with `k` read in `Fin (qCreate + 1)`) of `kemLossL + slotLossL + β_g(first) + recLossL(dec_g ∧ IS_g) + 2^-min`, each with coefficient one. -/
theorem ce_app_later (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes)) :
    𝒟[(fun outcome => happens (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) outcome) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime]
        {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
            (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second budget
            post (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          beta setup codec route checks ensureInit bounds .P first budget (g.1, g.2.castSucc) runtime +
          recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc) runtime
            fallback caps qInit (slotted setup codec budget
              (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
              (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹) := by
  rw [PqxdhDeploymentLaterHeadlineChain.split_named_later setup codec checks route ensureInit phase1 phase2 bounds .P
    first second budget respects _ _ runtime (PqxdhDeploymentHeadlineEvents.app_named setup.source.crypto codec
      setup.serverKeyId budget appClaim)]
  exact Finset.sum_le_sum fun g _ => ce_app_later_target setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound bounds first second budget respects post postRespects runtime fallback appClaim
    (g.1, g.2.castSucc)

/-- **CE-APP-L on a Server peer, per target**: in mode P, the probability that the LQ-F game ends with the Server-side CE-APP win of the post adversary's output and its claim designating `g` is at most `kemLossL + slotLossL + recLossL(dec_g ∧ ISs_g) + 2^-min`, with no anomaly term. -/
theorem ce_app_server_later_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes))
    (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[(fun outcome => decide (happens (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
        outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget (appHandle appClaim) outcome = some g)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime]
        {true} ≤
      ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
        (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime) +
      ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second budget post
        (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime) +
      recLossL setup codec checks route ensureInit bounds .P first second budget post g runtime fallback caps qInit
        (serverSlotted setup codec budget (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
          (appHandle appClaim) g) +
      ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ := by
  have chain := PqxdhDeploymentLaterHeadlineChain.chain_server_later (Reader := Reader) setup functional codec checks
    route ensureInit phase1 phase2 correct bounds .P first second budget respects post postRespects
    (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime
  have lift := PqxdhDeploymentLaterHeadlineChain.records_le_later setup codec checks route correct caps bounded
    ensureInit qInit initBound bounds .P first second budget respects post postRespects g runtime fallback
    (serverSlotted setup codec budget (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
      (appHandle appClaim) g)
  have hit := PqxdhDeploymentHeadlineContain.chance_mono
    (ctxView <$> laterIdealRecords setup codec route
      (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
      setup.serverKeyId bounds .P envReveal first second) _ _
    (PqxdhDeploymentHeadlineContain.app_peer_hit setup codec budget appClaim g)
  have final := fresh_final_later setup codec checks route ensureInit bounds first second budget g runtime appClaim
  calc _ ≤ _ := chain
    _ ≤ ((((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ +
          recLossL setup codec checks route ensureInit bounds .P first second budget post g runtime fallback caps qInit
            (serverSlotted setup codec budget
              (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g)) +
        ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
          (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime)) +
        ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second budget
          post (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g
          runtime) :=
        add_le_add (add_le_add (lift.trans (add_le_add (hit.trans final) le_rfl)) le_rfl) le_rfl
    _ = _ := by ring

/-- **CE-APP-L on a Server peer**: in mode P, the probability that the LQ-F game ends with the Server-side CE-APP win of the post adversary's output is at most the sum over `g` in `Fin qAccept × Fin qCreate` of `kemLossL + slotLossL + recLossL(dec_g ∧ ISs_g) + 2^-min`, each with coefficient one; no anomaly term. -/
theorem ce_app_server_later (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes)) :
    𝒟[(fun outcome => happens (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) outcome) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime]
        {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
            (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second budget
            post (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc) runtime
            fallback caps qInit (serverSlotted setup codec budget
              (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
              (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹) := by
  rw [PqxdhDeploymentLaterHeadlineChain.split_named_later setup codec checks route ensureInit phase1 phase2 bounds .P
    first second budget respects _ _ runtime (PqxdhDeploymentHeadlineEvents.appPeer_named setup.source.crypto codec
      setup.serverKeyId budget appClaim)]
  exact Finset.sum_le_sum fun g _ => ce_app_server_later_target setup functional codec checks route ensureInit phase1
    phase2 correct caps bounded qInit initBound bounds first second budget respects post postRespects runtime fallback
    appClaim (g.1, g.2.castSucc)

end BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineApp

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineApp.fresh_final_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineApp.fresh_final_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineApp.ce_app_later_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineApp.ce_app_later_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineApp.ce_app_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineApp.ce_app_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineApp.ce_app_server_later_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineApp.ce_app_server_later_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineApp.ce_app_server_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineApp.ce_app_server_later
