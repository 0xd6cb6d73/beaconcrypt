-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineApp

/-!
# Byte-accurate CE-APP-L bounds

These stronger siblings of `PqxdhDeploymentLaterHeadlineApp` preserve the complete later-disclosure experiment, adaptive post adversary, events, losses and resource premises. Each designated target pays `256^-min` for a fresh uniformly sampled message, with `min` measured in bytes. The original theorem statements remain available unchanged; no authentication or quantum-adversary claim is added.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineByteApp
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

/-- The final-world guessing term on the record lift's view of `laterIdealRecords` (mode P) with the ideal environment of a target and the environment's reveal, for a claim read from the post adversary's output (`PqxdhRecordFactsLaterFresh.later_idealRecords_fresh_bytes`). -/
theorem fresh_final_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) (appClaim : Out → Option (Nat × Pqxdh.Bytes)) :
    𝒟[PqxdhRecordLiftIdeal.freshEvent appClaim <$> (ctxView <$> laterIdealRecords setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds .P envReveal first second)] {true} ≤ ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ := by
  simpa only [Functor.map_map] using
    PqxdhRecordFactsLaterFresh.later_idealRecords_fresh_bytes setup codec route setup.serverKeyId bounds _ envReveal
      first second appClaim

/-- **CE-APP-L, per target**: in mode P, the probability that the LQ-F game ends with the CE-APP win of the post adversary's output and its claimed fresh message's handle designating `g` is at most `kemLossL + slotLossL + β_g(first) + recLossL(dec_g ∧ IS_g) + 256^-min`. -/
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
      ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ :=
  let chain := PqxdhDeploymentLaterHeadlineChain.chain_beta_later (Reader := Reader) setup functional codec checks
    route ensureInit phase1 phase2 correct bounds .P first second budget respects post postRespects
    (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime
  let lift := PqxdhDeploymentLaterHeadlineChain.records_le_later setup codec checks route correct caps bounded
    ensureInit qInit initBound bounds .P first second budget respects post postRespects g runtime fallback
    (slotted setup codec budget (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
      (appHandle appClaim) g)
  let hit := PqxdhDeploymentHeadlineContain.chance_mono
    (ctxView <$> laterIdealRecords setup codec route
      (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
      setup.serverKeyId bounds .P envReveal first second) _ _
    (PqxdhDeploymentHeadlineContain.app_hit setup codec budget appClaim g)
  let final := fresh_final_later setup codec checks route ensureInit bounds first second budget g runtime appClaim
  calc _ ≤ _ := chain
    _ ≤ ((((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ +
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

/-- **CE-APP-L** (design.md section 9.1): in mode P, the probability that the LQ-F game ends with the CE-APP win of the post adversary's output is at most the sum over `g` in `Fin qAccept × Fin qCreate` (with `k` read in `Fin (qCreate + 1)`) of `kemLossL + slotLossL + β_g(first) + recLossL(dec_g ∧ IS_g) + 256^-min`, each with coefficient one. -/
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
          ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹) :=
  (PqxdhDeploymentLaterHeadlineChain.split_named_later setup codec checks route ensureInit phase1 phase2 bounds .P
    first second budget respects _ _ runtime (PqxdhDeploymentHeadlineEvents.app_named setup.source.crypto codec
      setup.serverKeyId budget appClaim)).le.trans
    (Finset.sum_le_sum fun g _ => ce_app_later_target setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound bounds first second budget respects post postRespects runtime fallback appClaim
    (g.1, g.2.castSucc))

/-- **CE-APP-L on a Server peer, per target**: in mode P, the probability that the LQ-F game ends with the Server-side CE-APP win of the post adversary's output and its claim designating `g` is at most `kemLossL + slotLossL + recLossL(dec_g ∧ ISs_g) + 256^-min`, with no anomaly term. -/
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
      ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ :=
  let chain := PqxdhDeploymentLaterHeadlineChain.chain_server_later (Reader := Reader) setup functional codec checks
    route ensureInit phase1 phase2 correct bounds .P first second budget respects post postRespects
    (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime
  let lift := PqxdhDeploymentLaterHeadlineChain.records_le_later setup codec checks route correct caps bounded
    ensureInit qInit initBound bounds .P first second budget respects post postRespects g runtime fallback
    (serverSlotted setup codec budget (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
      (appHandle appClaim) g)
  let hit := PqxdhDeploymentHeadlineContain.chance_mono
    (ctxView <$> laterIdealRecords setup codec route
      (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
      setup.serverKeyId bounds .P envReveal first second) _ _
    (PqxdhDeploymentHeadlineContain.app_peer_hit setup codec budget appClaim g)
  let final := fresh_final_later setup codec checks route ensureInit bounds first second budget g runtime appClaim
  calc _ ≤ _ := chain
    _ ≤ ((((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ +
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

/-- **CE-APP-L on a Server peer**: in mode P, the probability that the LQ-F game ends with the Server-side CE-APP win of the post adversary's output is at most the sum over `g` in `Fin qAccept × Fin qCreate` of `kemLossL + slotLossL + recLossL(dec_g ∧ ISs_g) + 256^-min`, each with coefficient one; no anomaly term. -/
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
          ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹) :=
  (PqxdhDeploymentLaterHeadlineChain.split_named_later setup codec checks route ensureInit phase1 phase2 bounds .P
    first second budget respects _ _ runtime (PqxdhDeploymentHeadlineEvents.appPeer_named setup.source.crypto codec
      setup.serverKeyId budget appClaim)).le.trans
    (Finset.sum_le_sum fun g _ => ce_app_server_later_target setup functional codec checks route ensureInit phase1
    phase2 correct caps bounded qInit initBound bounds first second budget respects post postRespects runtime fallback
    appClaim (g.1, g.2.castSucc))

end BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineByteApp

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineByteApp.fresh_final_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineByteApp.fresh_final_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineByteApp.ce_app_later_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineByteApp.ce_app_later_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineByteApp.ce_app_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineByteApp.ce_app_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineByteApp.ce_app_server_later_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineByteApp.ce_app_server_later_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineByteApp.ce_app_server_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineByteApp.ce_app_server_later
