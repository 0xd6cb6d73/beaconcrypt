-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineApp

/-!
# Byte-accurate CE-APP bounds

These stronger siblings of `PqxdhDeploymentHeadlineApp` retain the same experiment, events, reductions, bills and premises, while preserving all eight bits per uniformly sampled byte in the final guessing term. The term is `256^-min` per designated target; the target sum and all cryptographic losses remain unchanged. The original public statements remain available without modification.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineByteApp
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

/-- The final-world guessing term on the record lift's view of `idealRecords` with the ideal environment of a target (`PqxdhRecordLiftFresh.idealRecords_fresh_bytes`). -/
theorem fresh_final (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X) (budget : Budget) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) (appClaim : X → Option (Nat × Pqxdh.Bytes)) :
    𝒟[PqxdhRecordLiftIdeal.freshEvent appClaim <$> (ctxView <$> idealRecords setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds .P adversary)] {true} ≤ ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ := by
  simpa only [Functor.map_map] using
    PqxdhRecordLiftFresh.idealRecords_fresh_bytes setup codec route setup.serverKeyId bounds _ adversary appClaim

/-- **CE-APP, per target** (design-v2 section 4.4): in mode P, the probability that the deployment experiment ends with the CE-APP win and its claimed fresh message's handle designating `g` is at most `kemLoss + slotLoss + β_g + recLoss_g(dec_g ∧ IS_g) + 256^-min`. -/
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
      ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ :=
  let chain := PqxdhDeploymentHeadlineAnomaly.chain_beta setup functional codec checks route ensureInit phase1 phase2
    correct bounds .P adversary budget respects (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
    (appHandle appClaim) g runtime
  let lift := PqxdhDeploymentHeadlineChain.records_le setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds .P adversary budget respects g runtime fallback
    (slotted setup codec budget (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
      (appHandle appClaim) g)
  let hit := PqxdhDeploymentHeadlineContain.chance_mono
    (ctxView <$> idealRecords setup codec route
      (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
      setup.serverKeyId bounds .P adversary) _ _
    (PqxdhDeploymentHeadlineContain.app_hit setup codec budget appClaim g)
  let final := fresh_final setup codec checks route ensureInit bounds adversary budget g runtime appClaim
  calc _ ≤ _ := chain
    _ ≤ ((((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ +
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

/-- **CE-APP** (design-v2 section 4.4, `ce_app`): in mode P, the probability that the deployment experiment ends with the CE-APP win is at most the sum over `g` in `Fin qAccept × Fin qCreate` (with `k` read in `Fin (qCreate + 1)`) of `kemLoss + slotLoss + β_g + recLoss_g(dec_g ∧ IS_g) + 256^-min`, each with coefficient one. -/
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
          ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹) :=
  (PqxdhDeploymentHeadlineChain.split_named setup codec checks route ensureInit phase1 phase2 bounds .P adversary
    budget respects _ _ runtime (PqxdhDeploymentHeadlineEvents.app_named setup.source.crypto codec setup.serverKeyId
      budget appClaim)).le.trans
    (Finset.sum_le_sum fun g _ => ce_app_target setup functional codec checks route ensureInit phase1 phase2 correct
    caps bounded qInit initBound bounds adversary budget respects runtime fallback appClaim (g.1, g.2.castSucc))

/-- **CE-APP on a Server peer, per target** (design-v2 section 4.4, `ce_app_server`): in mode P, the probability that the deployment experiment ends with the Server-side CE-APP win and its claim designating `g` is at most `kemLoss + slotLoss + recLoss_g(dec_g ∧ ISs_g) + 256^-min`, with no anomaly term. -/
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
      ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ :=
  let chain := PqxdhDeploymentHeadlineChain.chain_server setup functional codec checks route ensureInit phase1 phase2
    correct bounds .P adversary budget respects
    (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime
  let lift := PqxdhDeploymentHeadlineChain.records_le setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds .P adversary budget respects g runtime fallback
    (serverSlotted setup codec budget (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
      (appHandle appClaim) g)
  let hit := PqxdhDeploymentHeadlineContain.chance_mono
    (ctxView <$> idealRecords setup codec route
      (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
      setup.serverKeyId bounds .P adversary) _ _
    (PqxdhDeploymentHeadlineContain.app_peer_hit setup codec budget appClaim g)
  let final := fresh_final setup codec checks route ensureInit bounds adversary budget g runtime appClaim
  calc _ ≤ _ := chain
    _ ≤ ((((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ +
          recLoss setup codec checks route ensureInit bounds .P adversary budget g runtime fallback caps qInit
            (serverSlotted setup codec budget (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
              (appHandle appClaim) g)) +
        ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
          (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime)) +
        ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
          (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime) :=
        add_le_add (add_le_add (lift.trans (add_le_add (hit.trans final) le_rfl)) le_rfl) le_rfl
    _ = _ := by ring

/-- **CE-APP on a Server peer** (design-v2 section 4.4, `ce_app_server`): in mode P, the probability that the deployment experiment ends with the Server-side CE-APP win is at most the sum over `g` in `Fin qAccept × Fin qCreate` of `kemLoss + slotLoss + recLoss_g(dec_g ∧ ISs_g) + 256^-min`, each with coefficient one; no anomaly term. -/
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
          ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹) :=
  (PqxdhDeploymentHeadlineChain.split_named setup codec checks route ensureInit phase1 phase2 bounds .P adversary
    budget respects _ _ runtime (PqxdhDeploymentHeadlineEvents.appPeer_named setup.source.crypto codec
      setup.serverKeyId budget appClaim)).le.trans
    (Finset.sum_le_sum fun g _ => ce_app_server_target setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound bounds adversary budget respects runtime fallback appClaim (g.1, g.2.castSucc))

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineByteApp

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineByteApp.fresh_final' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineByteApp.fresh_final

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineByteApp.ce_app_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineByteApp.ce_app_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineByteApp.ce_app' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineByteApp.ce_app

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineByteApp.ce_app_server_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineByteApp.ce_app_server_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineByteApp.ce_app_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineByteApp.ce_app_server
