-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawHeadlineRecords
import BeaconcryptCore.Computational.CborRawHeadlineTargets
import BeaconcryptCore.Computational.CborRawHeadlineAnomaly
import BeaconcryptCore.Computational.CborRawRecordFresh
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain

/-! Raw-CBOR CE-APP uses the actual source experiment, native raw event ledger, cursor-compiled record world and byte-accurate fresh-message entropy. The remaining early-finish anomaly is an explicit event on that same raw transcript, ready for the concrete native predictor reduction. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawHeadlineApp
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget Handle)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhRecordLiftIdeal (View ctxView)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted startupG)
open PqxdhDeploymentEnvironment (allowanceG baseAllowance ceFirstTouch)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open CborRawHeadlineSlots (environment realView anomaly)
open CborTaggedSimulation (boundaryWire)
variable {ι KemSK Reader Response A E X : Type} {baseSpec : OracleSpec ι}

/-- The concrete raw ideal environment inherits every original source14 bill through the proved raw representation. -/
theorem frame (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (budget : Budget)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    PqxdhRecordLiftInterface.Frame (environment setup wire parse checks (Target.ofCE budget g) ensureInit runtime)
      (startupG caps qInit budget) (allowanceG (baseAllowance caps) ceFirstTouch) :=
  CborRawEnvironment.frame _ setup.serverKeyId _ _
    (PqxdhDeploymentIdealFrame.frame_idealD setup (CborRawCompile.sourceCodec wire parse) checks caps bounded
      (Target.ofCE budget g) ensureInit qInit initBound 0 runtime)

set_option maxHeartbeats 1000000 in
/-- The raw slotted CE-APP event has byte-accurate final random-record probability. -/
theorem final (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : PqxdhRecordLiftInterface.Environment 2 E)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (appClaim : X → Option (Nat × Pqxdh.Bytes)) (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[slotted setup codec budget
      (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g <$>
      (ctxView <$> PqxdhRecordLiftLaterWorlds.ctxRunOf (fun _ => .random) id setup codec
        route (CborRawRecordLiftBounds.client
          env setup.source.crypto
            codec setup.serverKeyId bounds .P adversary))] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ := by
  have hit := PqxdhDeploymentHeadlineContain.chance_mono
    (ctxView <$> PqxdhRecordLiftLaterWorlds.ctxRunOf (fun _ => .random) id setup codec
      route (CborRawRecordLiftBounds.client
        env setup.source.crypto
          codec setup.serverKeyId bounds .P adversary)) _ _
    (PqxdhDeploymentHeadlineContain.app_hit setup codec budget appClaim g)
  have entropy := CborRawRecordFresh.fresh_bytes setup codec route
    env setup.serverKeyId bounds adversary appClaim
  simp only [Functor.map_map] at hit
  simpa only [Functor.map_map] using hit.trans entropy

/-- Raw-CBOR CE-APP per target is bounded by explicit primitive reductions, the same-run native anomaly and byte entropy. -/
theorem ce_app_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse)) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (nativePhase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : Nat) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (appClaim : X → Option (Nat × Pqxdh.Bytes)) (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[(fun outcome => decide (happens
      (appEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget appClaim) outcome = true ∧
      designated setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (appHandle appClaim) outcome = some g)) <$>
      (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds .P adversary).run runtime] {true} ≤
    ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ +
    CborRawHeadlineRecords.randomLoss setup (boundaryWire wire parse) (CborRawCompile.route parse)
      (environment setup wire parse checks (Target.ofCE budget g) ensureInit runtime) setup.serverKeyId bounds .P budget
      adversary (slotted setup (boundaryWire wire parse) budget
        (appEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget appClaim) (appHandle appClaim) g)
      (startupG caps qInit budget) (allowanceG (baseAllowance caps) ceFirstTouch) fallback +
    𝒟[anomaly setup wire parse (Target.ofCE budget g) <$>
      realView setup wire parse checks (Target.ofCE budget g) ensureInit runtime bounds .P adversary] {true} +
    ENNReal.ofReal (CborRawHeadlineChain.kemLoss setup wire parse checks ensureInit bounds .P adversary budget
      (appEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime) +
    ENNReal.ofReal (CborRawHeadlineChain.slotLoss setup wire parse checks ensureInit bounds .P adversary budget
      (appEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime) := by
  have source := CborRawHeadlineSlots.chain_slots setup functional wire parse checks lengths parser ensureInit phase1
    phase2 nativePhase1 correct bounds .P adversary budget respects
    (appEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime
  have records := CborRawHeadlineRecords.random_le setup (boundaryWire wire parse) (CborRawCompile.route parse)
    (environment setup wire parse checks (Target.ofCE budget g) ensureInit runtime) (startupG caps qInit budget)
    (allowanceG (baseAllowance caps) ceFirstTouch)
    (frame setup wire parse checks caps bounded ensureInit qInit initBound budget g runtime) setup.serverKeyId bounds .P
    budget adversary respects (slotted setup (boundaryWire wire parse) budget
      (appEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget appClaim) (appHandle appClaim) g)
    correct fallback
  have entropy := final setup (boundaryWire wire parse) (CborRawCompile.route parse)
    (environment setup wire parse checks (Target.ofCE budget g) ensureInit runtime) bounds adversary budget appClaim g
  exact source.trans (add_le_add (add_le_add (add_le_add
    (records.trans (add_le_add entropy le_rfl)) le_rfl) le_rfl) le_rfl)

/-- The actual raw Server-side slotted event satisfies its concrete final-world bound. -/
theorem final_peer (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : PqxdhRecordLiftInterface.Environment 2 E)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (appClaim : X → Option (Nat × Pqxdh.Bytes)) (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[serverSlotted setup codec budget
      (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g <$>
      (ctxView <$> PqxdhRecordLiftLaterWorlds.ctxRunOf (fun _ => .random) id setup codec
        route (CborRawRecordLiftBounds.client
          env setup.source.crypto
            codec setup.serverKeyId bounds .P adversary))] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ := by
  have hit := PqxdhDeploymentHeadlineContain.chance_mono
    (ctxView <$> PqxdhRecordLiftLaterWorlds.ctxRunOf (fun _ => .random) id setup codec
      route (CborRawRecordLiftBounds.client
        env setup.source.crypto
          codec setup.serverKeyId bounds .P adversary)) _ _
    (PqxdhDeploymentHeadlineContain.app_peer_hit setup codec budget appClaim g)
  have entropy := CborRawRecordFresh.fresh_bytes setup codec route
    env setup.serverKeyId bounds adversary appClaim
  simp only [Functor.map_map] at hit
  simpa only [Functor.map_map] using hit.trans entropy

/-- The actual raw Server-side security bound has no early-finish anomaly term. -/
theorem ce_app_server_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse)) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (nativePhase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : Nat) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (appClaim : X → Option (Nat × Pqxdh.Bytes)) (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[(fun outcome => decide (happens
      (appPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget appClaim) outcome = true ∧
      designated setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (appHandle appClaim) outcome = some g)) <$>
      (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds .P adversary).run runtime] {true} ≤
    ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ +
    CborRawHeadlineRecords.randomLoss setup (boundaryWire wire parse) (CborRawCompile.route parse)
      (environment setup wire parse checks (Target.ofCE budget g) ensureInit runtime) setup.serverKeyId bounds .P budget
      adversary (serverSlotted setup (boundaryWire wire parse) budget
        (appPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget appClaim) (appHandle appClaim) g)
      (startupG caps qInit budget) (allowanceG (baseAllowance caps) ceFirstTouch) fallback +
    ENNReal.ofReal (CborRawHeadlineChain.kemLoss setup wire parse checks ensureInit bounds .P adversary budget
      (appPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime) +
    ENNReal.ofReal (CborRawHeadlineChain.slotLoss setup wire parse checks ensureInit bounds .P adversary budget
      (appPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime) := by
  have source := CborRawHeadlineSlots.chain_server setup functional wire parse checks lengths parser ensureInit phase1
    phase2 nativePhase1 correct bounds .P adversary budget respects
    (appPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime
  have records := CborRawHeadlineRecords.random_le setup (boundaryWire wire parse) (CborRawCompile.route parse)
    (environment setup wire parse checks (Target.ofCE budget g) ensureInit runtime) (startupG caps qInit budget)
    (allowanceG (baseAllowance caps) ceFirstTouch)
    (frame setup wire parse checks caps bounded ensureInit qInit initBound budget g runtime) setup.serverKeyId bounds .P
    budget adversary respects (serverSlotted setup (boundaryWire wire parse) budget
      (appPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget appClaim) (appHandle appClaim) g)
    correct fallback
  have entropy := final_peer setup (boundaryWire wire parse) (CborRawCompile.route parse)
    (environment setup wire parse checks (Target.ofCE budget g) ensureInit runtime) bounds adversary budget appClaim g
  exact source.trans (add_le_add (add_le_add
    (records.trans (add_le_add entropy le_rfl)) le_rfl) le_rfl)

/-- The actual raw security bound uses only explicit primitive reductions and its concrete final-world term. -/
theorem ce_app_target_beta (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse)) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (nativePhase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : Nat) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (appClaim : X → Option (Nat × Pqxdh.Bytes)) (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[(fun outcome => decide (happens
      (appEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget appClaim) outcome = true ∧
      designated setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (appHandle appClaim) outcome = some g)) <$>
      (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds .P adversary).run runtime] {true} ≤
    ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ +
    CborRawHeadlineRecords.randomLoss setup (boundaryWire wire parse) (CborRawCompile.route parse)
      (environment setup wire parse checks (Target.ofCE budget g) ensureInit runtime) setup.serverKeyId bounds .P budget
      adversary (slotted setup (boundaryWire wire parse) budget
        (appEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget appClaim) (appHandle appClaim) g)
      (startupG caps qInit budget) (allowanceG (baseAllowance caps) ceFirstTouch) fallback +
    CborRawAnomalyCca.beta setup wire parse checks (Target.ofCE budget g) ensureInit runtime bounds .P adversary +
    ENNReal.ofReal (CborRawHeadlineChain.kemLoss setup wire parse checks ensureInit bounds .P adversary budget
      (appEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime) +
    ENNReal.ofReal (CborRawHeadlineChain.slotLoss setup wire parse checks ensureInit bounds .P adversary budget
      (appEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime) := by
  have main := ce_app_target setup functional wire parse checks lengths parser ensureInit phase1 phase2 nativePhase1
    correct caps bounded qInit initBound bounds adversary budget respects runtime fallback appClaim g
  have anomaly := CborRawHeadlineAnomaly.anomaly_beta setup functional wire parse checks lengths parser phase1 phase2
    nativePhase1 (Target.ofCE budget g) ensureInit runtime bounds .P adversary
  exact main.trans (add_le_add (add_le_add (add_le_add le_rfl anomaly) le_rfl) le_rfl)

/-- The actual raw security event is bounded by the tight accept-times-create sum of its concrete per-target primitive and final-world terms. -/
theorem ce_app (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse)) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (nativePhase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : Nat) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (appClaim : X → Option (Nat × Pqxdh.Bytes)) :
    𝒟[(fun outcome => happens (appEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget appClaim) outcome) <$>
      (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds .P adversary).run runtime] {true} ≤
    ∑ g : Fin budget.accept × Fin budget.create,
      (((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ +
    CborRawHeadlineRecords.randomLoss setup (boundaryWire wire parse) (CborRawCompile.route parse)
      (environment setup wire parse checks (Target.ofCE budget (g.1, g.2.castSucc)) ensureInit runtime) setup.serverKeyId bounds .P budget
      adversary (slotted setup (boundaryWire wire parse) budget
        (appEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget appClaim) (appHandle appClaim) (g.1, g.2.castSucc))
      (startupG caps qInit budget) (allowanceG (baseAllowance caps) ceFirstTouch) fallback +
    CborRawAnomalyCca.beta setup wire parse checks (Target.ofCE budget (g.1, g.2.castSucc)) ensureInit runtime bounds .P adversary +
    ENNReal.ofReal (CborRawHeadlineChain.kemLoss setup wire parse checks ensureInit bounds .P adversary budget
      (appEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget appClaim) (appHandle appClaim) (g.1, g.2.castSucc) runtime) +
    ENNReal.ofReal (CborRawHeadlineChain.slotLoss setup wire parse checks ensureInit bounds .P adversary budget
      (appEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget appClaim) (appHandle appClaim) (g.1, g.2.castSucc) runtime)) := by
  rw [CborRawHeadlineTargets.split_named setup wire parse checks lengths parser ensureInit phase1 phase2 bounds .P
    adversary budget respects _ _ runtime (PqxdhDeploymentHeadlineEvents.app_named setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget appClaim)]
  exact Finset.sum_le_sum fun g _ => ce_app_target_beta setup functional wire parse checks lengths parser ensureInit phase1 phase2
    nativePhase1 correct caps bounded qInit initBound bounds adversary budget respects runtime fallback appClaim (g.1, g.2.castSucc)

/-- The actual raw security event is bounded by the tight accept-times-create sum of its concrete per-target primitive and final-world terms. -/
theorem ce_app_server (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse)) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (nativePhase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : Nat) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (appClaim : X → Option (Nat × Pqxdh.Bytes)) :
    𝒟[(fun outcome => happens (appPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget appClaim) outcome) <$>
      (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds .P adversary).run runtime] {true} ≤
    ∑ g : Fin budget.accept × Fin budget.create,
      (((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ +
    CborRawHeadlineRecords.randomLoss setup (boundaryWire wire parse) (CborRawCompile.route parse)
      (environment setup wire parse checks (Target.ofCE budget (g.1, g.2.castSucc)) ensureInit runtime) setup.serverKeyId bounds .P budget
      adversary (serverSlotted setup (boundaryWire wire parse) budget
        (appPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget appClaim) (appHandle appClaim) (g.1, g.2.castSucc))
      (startupG caps qInit budget) (allowanceG (baseAllowance caps) ceFirstTouch) fallback +
    ENNReal.ofReal (CborRawHeadlineChain.kemLoss setup wire parse checks ensureInit bounds .P adversary budget
      (appPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget appClaim) (appHandle appClaim) (g.1, g.2.castSucc) runtime) +
    ENNReal.ofReal (CborRawHeadlineChain.slotLoss setup wire parse checks ensureInit bounds .P adversary budget
      (appPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget appClaim) (appHandle appClaim) (g.1, g.2.castSucc) runtime)) := by
  rw [CborRawHeadlineTargets.split_named setup wire parse checks lengths parser ensureInit phase1 phase2 bounds .P
    adversary budget respects _ _ runtime (PqxdhDeploymentHeadlineEvents.appPeer_named setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget appClaim)]
  exact Finset.sum_le_sum fun g _ => ce_app_server_target setup functional wire parse checks lengths parser ensureInit phase1 phase2
    nativePhase1 correct caps bounded qInit initBound bounds adversary budget respects runtime fallback appClaim (g.1, g.2.castSucc)

end BeaconcryptCore.Computational.CborRawHeadlineApp

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineApp.frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineApp.frame
/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineApp.final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineApp.final

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineApp.ce_app_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineApp.ce_app_target

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineApp.final_peer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineApp.final_peer

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineApp.ce_app_server_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineApp.ce_app_server_target

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineApp.ce_app_target_beta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineApp.ce_app_target_beta

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineApp.ce_app' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineApp.ce_app

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineApp.ce_app_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineApp.ce_app_server
