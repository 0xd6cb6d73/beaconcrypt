-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain
import BeaconcryptCore.Computational.PqxdhRecordLiftFresh

/-!
# CE-APP: fresh-message secrecy of the common deployment experiment (CE-12 P1, design-v2 section 4.4)

The headline CE-APP (VC rows App-b2s, App-s2b, b2s-S2, s2b-S1 and the fixed-name rows 163-166, design-v2 section 12), in observation mode P: the probability that the adversary's output names an admitted fresh message, sent on a designated handle, and guesses it exactly (`PqxdhDeploymentHeadlineEvents.AppWin`) is at most the sum over the targets `g` in `Fin qAccept × Fin qCreate`, each with coefficient one, of

- `kemLoss` and `slotLoss` of `g`'s decision (CE-9 and item 2, `PqxdhDeploymentHeadlineChain`),
- `β_g`, the anomaly term (`PqxdhDeploymentHeadlineAnomaly.beta`: one IND-CCA advantage of the predict-then-compare adversary, the correctness error and `2^-256`),
- `recLoss_g` of the view event `dec_g ∧ IS_g`, the record-lift loss (`PqxdhRecordLift.record_lift`: chain, integrity and privacy reductions),
- `2^-min`, the final-world guessing term (`PqxdhRecordLiftFresh.idealRecords_fresh`).

`ce_app_target` is the per-target form and `ce_app` the summed form. `ce_app_server` and `ce_app_server_target` restrict the win to a fresh message on a Server peer (`AppWinPeer`) and drop `β_g`, using only the Server-side slot conjuncts. The chain is C1-C6 (`chain_beta`, `chain_server`), C7 (`records_le` at the frame of `frame_idealD`), the containment `app_hit` / `app_peer_hit` and `FreshGuessStatement`.

Premises: `FunctionalDecapsulation setup.kem`, `Phase1ReadBack`, `Phase2ReadBack`, `SourceFullCorrect setup.source setup.hmac`, `KemBound setup caps`, the total query bound `qInit` of the runtime initializer, and `budget.Respects adversary`; the AEAD forgery fallback is a parameter of the integrity loss. The final term is per target, so the sum carries `N · 2^-min` (design.md section 4.4). No new assumption or contract.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineApp
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhRecordLiftIdeal (chainView ctxView realChains idealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss recLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The final-world guessing term on the record lift's view of `idealRecords` with the ideal environment of a target (`PqxdhRecordLiftFresh.idealRecords_fresh`). -/
theorem fresh_final (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X) (budget : Budget) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) (appClaim : X → Option (Nat × Pqxdh.Bytes)) :
    𝒟[PqxdhRecordLiftIdeal.freshEvent appClaim <$> (ctxView <$> idealRecords setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds .P adversary)] {true} ≤ ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [Functor.map_map]
  exact PqxdhRecordLiftFresh.idealRecords_fresh setup codec route setup.serverKeyId bounds 2 _ adversary appClaim

/-- **CE-APP, per target** (design-v2 section 4.4): in mode P, the probability that the deployment experiment ends with the CE-APP win and its claimed fresh message's handle designating `g` is at most `kemLoss + slotLoss + β_g + recLoss_g(dec_g ∧ IS_g) + 2^-min`. -/
theorem ce_app_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (appClaim : X → Option (Nat × Pqxdh.Bytes)) (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[(fun outcome => decide (happens (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) outcome =
        true ∧ designated setup.source.crypto codec setup.serverKeyId budget (appHandle appClaim) outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
        (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
        (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime) +
      beta setup codec route checks ensureInit bounds .P adversary budget g runtime +
      recLoss setup codec checks route ensureInit bounds .P adversary budget g runtime fallback caps qInit
        (slotted setup codec budget (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
          (appHandle appClaim) g) +
      ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ := by
  have chain := PqxdhDeploymentHeadlineAnomaly.chain_beta setup functional codec checks route ensureInit phase1 phase2
    correct bounds .P adversary budget respects (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
    (appHandle appClaim) g runtime
  have lift := PqxdhDeploymentHeadlineChain.records_le setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds .P adversary budget respects g runtime fallback
    (slotted setup codec budget (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
      (appHandle appClaim) g)
  have hit := PqxdhDeploymentHeadlineContain.chance_mono
    (ctxView <$> idealRecords setup codec route
      (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
      setup.serverKeyId bounds .P adversary) _ _
    (PqxdhDeploymentHeadlineContain.app_hit setup codec budget appClaim g)
  have final := fresh_final setup codec checks route ensureInit bounds adversary budget g runtime appClaim
  calc _ ≤ _ := chain
    _ ≤ ((((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ +
          recLoss setup codec checks route ensureInit bounds .P adversary budget g runtime fallback caps qInit
            (slotted setup codec budget (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
              (appHandle appClaim) g)) +
        beta setup codec route checks ensureInit bounds .P adversary budget g runtime +
        ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
          (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime)) +
        ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
          (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime) :=
        add_le_add (add_le_add (add_le_add (lift.trans (add_le_add (hit.trans final) le_rfl)) le_rfl) le_rfl) le_rfl
    _ = _ := by ring

/-- **CE-APP** (design-v2 section 4.4, `ce_app`): in mode P, the probability that the deployment experiment ends with the CE-APP win is at most the sum over `g` in `Fin qAccept × Fin qCreate` (with `k` read in `Fin (qCreate + 1)`) of `kemLoss + slotLoss + β_g + recLoss_g(dec_g ∧ IS_g) + 2^-min`, each with coefficient one. -/
theorem ce_app (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (appClaim : X → Option (Nat × Pqxdh.Bytes)) :
    𝒟[(fun outcome => happens (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) outcome) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
            (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
            (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          beta setup codec route checks ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime +
          recLoss setup codec checks route ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime fallback
            caps qInit (slotted setup codec budget (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
              (appHandle appClaim) (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹) := by
  rw [PqxdhDeploymentHeadlineChain.split_named setup codec checks route ensureInit phase1 phase2 bounds .P adversary
    budget respects _ _ runtime (PqxdhDeploymentHeadlineEvents.app_named setup.source.crypto codec setup.serverKeyId
      budget appClaim)]
  exact Finset.sum_le_sum fun g _ => ce_app_target setup functional codec checks route ensureInit phase1 phase2 correct
    caps bounded qInit initBound bounds adversary budget respects runtime fallback appClaim (g.1, g.2.castSucc)

/-- **CE-APP on a Server peer, per target** (design-v2 section 4.4, `ce_app_server`): in mode P, the probability that the deployment experiment ends with the Server-side CE-APP win and its claim designating `g` is at most `kemLoss + slotLoss + recLoss_g(dec_g ∧ ISs_g) + 2^-min`, with no anomaly term. -/
theorem ce_app_server_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (appClaim : X → Option (Nat × Pqxdh.Bytes)) (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[(fun outcome => decide (happens (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
        outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget (appHandle appClaim) outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
        (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
        (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime) +
      recLoss setup codec checks route ensureInit bounds .P adversary budget g runtime fallback caps qInit
        (serverSlotted setup codec budget (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
          (appHandle appClaim) g) +
      ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ := by
  have chain := PqxdhDeploymentHeadlineChain.chain_server setup functional codec checks route ensureInit phase1 phase2
    correct bounds .P adversary budget respects
    (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime
  have lift := PqxdhDeploymentHeadlineChain.records_le setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds .P adversary budget respects g runtime fallback
    (serverSlotted setup codec budget (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
      (appHandle appClaim) g)
  have hit := PqxdhDeploymentHeadlineContain.chance_mono
    (ctxView <$> idealRecords setup codec route
      (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
      setup.serverKeyId bounds .P adversary) _ _
    (PqxdhDeploymentHeadlineContain.app_peer_hit setup codec budget appClaim g)
  have final := fresh_final setup codec checks route ensureInit bounds adversary budget g runtime appClaim
  calc _ ≤ _ := chain
    _ ≤ ((((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ +
          recLoss setup codec checks route ensureInit bounds .P adversary budget g runtime fallback caps qInit
            (serverSlotted setup codec budget (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
              (appHandle appClaim) g)) +
        ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
          (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime)) +
        ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
          (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime) :=
        add_le_add (add_le_add (lift.trans (add_le_add (hit.trans final) le_rfl)) le_rfl) le_rfl
    _ = _ := by ring

/-- **CE-APP on a Server peer** (design-v2 section 4.4, `ce_app_server`): in mode P, the probability that the deployment experiment ends with the Server-side CE-APP win is at most the sum over `g` in `Fin qAccept × Fin qCreate` of `kemLoss + slotLoss + recLoss_g(dec_g ∧ ISs_g) + 2^-min`, each with coefficient one; no anomaly term. -/
theorem ce_app_server (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (appClaim : X → Option (Nat × Pqxdh.Bytes)) :
    𝒟[(fun outcome => happens (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) outcome) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
            (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
            (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          recLoss setup codec checks route ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime fallback
            caps qInit (serverSlotted setup codec budget
              (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
              (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹) := by
  rw [PqxdhDeploymentHeadlineChain.split_named setup codec checks route ensureInit phase1 phase2 bounds .P adversary
    budget respects _ _ runtime (PqxdhDeploymentHeadlineEvents.appPeer_named setup.source.crypto codec
      setup.serverKeyId budget appClaim)]
  exact Finset.sum_le_sum fun g _ => ce_app_server_target setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound bounds adversary budget respects runtime fallback appClaim (g.1, g.2.castSucc)

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineApp

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineApp.fresh_final' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineApp.fresh_final

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineApp.ce_app_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineApp.ce_app_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineApp.ce_app' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineApp.ce_app

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineApp.ce_app_server_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineApp.ce_app_server_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineApp.ce_app_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineApp.ce_app_server
