-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawHeadlineApp
import BeaconcryptCore.Computational.CborRawHeadlineTargets
import BeaconcryptCore.Computational.CborRawRecordOriginClosure

/-! The raw Server-to-Beacon origin headline combines the actual raw event and compiler, explicit registration and record primitive losses, native slot anomaly and failed-writer publication term. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawHeadlineOrigin
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget Handle)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhRecordLiftIdeal (View ctxView publicationTerm)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted startupG)
open PqxdhDeploymentEnvironment (allowanceG baseAllowance ceFirstTouch)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open CborRawHeadlineSlots (environment realView anomaly)
open CborRawHeadlineApp (frame)
open CborTaggedSimulation (boundaryWire)
variable {ι KemSK Reader Response A E X : Type} {baseSpec : OracleSpec ι}

set_option maxHeartbeats 1000000 in
/-- Actual raw replay-ideal slotted origin failure is bounded by the concrete unpublished-origin term. -/
theorem final_s2b (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : PqxdhRecordLiftInterface.Environment 2 E)
    (startup : Nat) (allowance : Fin 14 → PqxdhRecordLiftInterface.EffectKind → Nat)
    (framed : PqxdhRecordLiftInterface.Frame env startup allowance) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[slotted setup codec budget
      (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
      (orClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g <$>
      (ctxView <$> PqxdhRecordLiftLaterWorlds.ctxRunOf (fun _ => .replay) id setup codec
        route (CborRawRecordLiftBounds.client
          env setup.source.crypto
            codec setup.serverKeyId bounds mode adversary))] {true} ≤ publicationTerm budget := by
  have hit := PqxdhDeploymentHeadlineContain.chance_mono
    (ctxView <$> PqxdhRecordLiftLaterWorlds.ctxRunOf (fun _ => .replay) id setup codec
      route (CborRawRecordLiftBounds.client
        env setup.source.crypto
          codec setup.serverKeyId bounds mode adversary)) _ _
    (PqxdhDeploymentHeadlineContain.origin_s2b setup codec budget route g)
  have publication := CborRawRecordOriginClosure.ctxRunOf_unpublished_bound (fun _ => .replay) (fun _ => by decide)
    id setup codec route readback
    env startup
    allowance
    framed setup.serverKeyId bounds
    mode budget adversary respects
  simp only [Functor.map_map] at hit
  simpa only [Functor.map_map] using hit.trans publication

/-- Raw-CBOR CE-OR Server-to-Beacon per target retains the concrete publication term and all explicit reduction losses. -/
theorem ce_or_s2b_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse)) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (nativePhase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : Nat) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack (boundaryWire wire parse))
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[(fun outcome => decide (happens
      (originEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) outcome = true ∧
      designated setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (orClaim setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) outcome = some g)) <$>
      (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds mode adversary).run runtime] {true} ≤
    publicationTerm budget +
    CborRawHeadlineRecords.integrityLoss setup (boundaryWire wire parse) (CborRawCompile.route parse)
      (environment setup wire parse checks (Target.ofCE budget g) ensureInit runtime) setup.serverKeyId bounds mode budget
      adversary (slotted setup (boundaryWire wire parse) budget
        (originEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) (orClaim setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) g)
      (startupG caps qInit budget) (allowanceG (baseAllowance caps) ceFirstTouch) fallback +
    𝒟[anomaly setup wire parse (Target.ofCE budget g) <$>
      realView setup wire parse checks (Target.ofCE budget g) ensureInit runtime bounds mode adversary] {true} +
    ENNReal.ofReal (CborRawHeadlineChain.kemLoss setup wire parse checks ensureInit bounds mode adversary budget
      (originEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) (orClaim setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) g runtime) +
    ENNReal.ofReal (CborRawHeadlineChain.slotLoss setup wire parse checks ensureInit bounds mode adversary budget
      (originEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) (orClaim setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) g runtime) := by
  have source := CborRawHeadlineSlots.chain_slots setup functional wire parse checks lengths parser ensureInit phase1
    phase2 nativePhase1 correct bounds mode adversary budget respects
    (originEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) (orClaim setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) g runtime
  have records := CborRawHeadlineRecords.integrity_le setup (boundaryWire wire parse) (CborRawCompile.route parse)
    (environment setup wire parse checks (Target.ofCE budget g) ensureInit runtime) (startupG caps qInit budget)
    (allowanceG (baseAllowance caps) ceFirstTouch)
    (frame setup wire parse checks caps bounded ensureInit qInit initBound budget g runtime) setup.serverKeyId bounds mode
    budget adversary respects (slotted setup (boundaryWire wire parse) budget
      (originEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) (orClaim setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) g)
    correct fallback
  have entropy := final_s2b setup (boundaryWire wire parse) (CborRawCompile.route parse)
    (environment setup wire parse checks (Target.ofCE budget g) ensureInit runtime) (startupG caps qInit budget)
    (allowanceG (baseAllowance caps) ceFirstTouch)
    (frame setup wire parse checks caps bounded ensureInit qInit initBound budget g runtime) bounds mode adversary budget
    respects readback g
  exact source.trans (add_le_add (add_le_add (add_le_add
    (records.trans (add_le_add entropy le_rfl)) le_rfl) le_rfl) le_rfl)

/-- The actual raw Server-side slotted event satisfies its concrete final-world bound. -/
theorem final_b2s (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : PqxdhRecordLiftInterface.Environment 2 E)
    (startup : Nat) (allowance : Fin 14 → PqxdhRecordLiftInterface.EffectKind → Nat)
    (framed : PqxdhRecordLiftInterface.Frame env startup allowance) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[serverSlotted setup codec budget
      (originEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
      (orClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g <$>
      (ctxView <$> PqxdhRecordLiftLaterWorlds.ctxRunOf (fun _ => .replay) id setup codec
        route (CborRawRecordLiftBounds.client
          env setup.source.crypto
            codec setup.serverKeyId bounds mode adversary))] {true} ≤ publicationTerm budget := by
  have hit := PqxdhDeploymentHeadlineContain.chance_mono
    (ctxView <$> PqxdhRecordLiftLaterWorlds.ctxRunOf (fun _ => .replay) id setup codec
      route (CborRawRecordLiftBounds.client
        env setup.source.crypto
          codec setup.serverKeyId bounds mode adversary)) _ _
    (PqxdhDeploymentHeadlineContain.origin_b2s setup codec budget route g)
  have publication := CborRawRecordOriginClosure.ctxRunOf_unpublished_bound (fun _ => .replay) (fun _ => by decide)
    id setup codec route readback
    env startup
    allowance
    framed setup.serverKeyId bounds
    mode budget adversary respects
  simp only [Functor.map_map] at hit
  simpa only [Functor.map_map] using hit.trans publication

/-- The actual raw Server-side security bound has no early-finish anomaly term. -/
theorem ce_or_b2s_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse)) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (nativePhase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : Nat) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack (boundaryWire wire parse))
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[(fun outcome => decide (happens
      (originEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .b2s) outcome = true ∧
      designated setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (orClaim setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .b2s) outcome = some g)) <$>
      (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds mode adversary).run runtime] {true} ≤
    publicationTerm budget +
    CborRawHeadlineRecords.integrityLoss setup (boundaryWire wire parse) (CborRawCompile.route parse)
      (environment setup wire parse checks (Target.ofCE budget g) ensureInit runtime) setup.serverKeyId bounds mode budget
      adversary (serverSlotted setup (boundaryWire wire parse) budget
        (originEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .b2s) (orClaim setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .b2s) g)
      (startupG caps qInit budget) (allowanceG (baseAllowance caps) ceFirstTouch) fallback +
    ENNReal.ofReal (CborRawHeadlineChain.kemLoss setup wire parse checks ensureInit bounds mode adversary budget
      (originEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .b2s) (orClaim setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .b2s) g runtime) +
    ENNReal.ofReal (CborRawHeadlineChain.slotLoss setup wire parse checks ensureInit bounds mode adversary budget
      (originEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .b2s) (orClaim setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .b2s) g runtime) := by
  have source := CborRawHeadlineSlots.chain_server setup functional wire parse checks lengths parser ensureInit phase1
    phase2 nativePhase1 correct bounds mode adversary budget respects
    (originEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .b2s) (orClaim setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .b2s) g runtime
  have records := CborRawHeadlineRecords.integrity_le setup (boundaryWire wire parse) (CborRawCompile.route parse)
    (environment setup wire parse checks (Target.ofCE budget g) ensureInit runtime) (startupG caps qInit budget)
    (allowanceG (baseAllowance caps) ceFirstTouch)
    (frame setup wire parse checks caps bounded ensureInit qInit initBound budget g runtime) setup.serverKeyId bounds mode
    budget adversary respects (serverSlotted setup (boundaryWire wire parse) budget
      (originEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .b2s) (orClaim setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .b2s) g)
    correct fallback
  have entropy := final_b2s setup (boundaryWire wire parse) (CborRawCompile.route parse)
    (environment setup wire parse checks (Target.ofCE budget g) ensureInit runtime) (startupG caps qInit budget)
    (allowanceG (baseAllowance caps) ceFirstTouch)
    (frame setup wire parse checks caps bounded ensureInit qInit initBound budget g runtime) bounds mode adversary budget
    respects readback g
  exact source.trans (add_le_add (add_le_add
    (records.trans (add_le_add entropy le_rfl)) le_rfl) le_rfl)

/-- The actual raw security bound uses only explicit primitive reductions and its concrete final-world term. -/
theorem ce_or_s2b_target_beta (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse)) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (nativePhase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : Nat) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack (boundaryWire wire parse))
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[(fun outcome => decide (happens
      (originEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) outcome = true ∧
      designated setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (orClaim setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) outcome = some g)) <$>
      (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds mode adversary).run runtime] {true} ≤
    publicationTerm budget +
    CborRawHeadlineRecords.integrityLoss setup (boundaryWire wire parse) (CborRawCompile.route parse)
      (environment setup wire parse checks (Target.ofCE budget g) ensureInit runtime) setup.serverKeyId bounds mode budget
      adversary (slotted setup (boundaryWire wire parse) budget
        (originEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) (orClaim setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) g)
      (startupG caps qInit budget) (allowanceG (baseAllowance caps) ceFirstTouch) fallback +
    CborRawAnomalyCca.beta setup wire parse checks (Target.ofCE budget g) ensureInit runtime bounds mode adversary +
    ENNReal.ofReal (CborRawHeadlineChain.kemLoss setup wire parse checks ensureInit bounds mode adversary budget
      (originEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) (orClaim setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) g runtime) +
    ENNReal.ofReal (CborRawHeadlineChain.slotLoss setup wire parse checks ensureInit bounds mode adversary budget
      (originEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) (orClaim setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) g runtime) := by
  have main := ce_or_s2b_target setup functional wire parse checks lengths parser ensureInit phase1 phase2 nativePhase1
    correct caps bounded qInit initBound readback bounds mode adversary budget respects runtime fallback g
  have anomaly := CborRawHeadlineAnomaly.anomaly_beta setup functional wire parse checks lengths parser phase1 phase2
    nativePhase1 (Target.ofCE budget g) ensureInit runtime bounds mode adversary
  exact main.trans (add_le_add (add_le_add (add_le_add le_rfl anomaly) le_rfl) le_rfl)

/-- The actual raw security event is bounded by the tight accept-times-create sum of its concrete per-target primitive and final-world terms. -/
theorem ce_or_s2b (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse)) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (nativePhase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : Nat) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack (boundaryWire wire parse))
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    :
    𝒟[(fun outcome => happens (originEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) outcome) <$>
      (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds mode adversary).run runtime] {true} ≤
    ∑ g : Fin budget.accept × Fin budget.create,
      (publicationTerm budget +
    CborRawHeadlineRecords.integrityLoss setup (boundaryWire wire parse) (CborRawCompile.route parse)
      (environment setup wire parse checks (Target.ofCE budget (g.1, g.2.castSucc)) ensureInit runtime) setup.serverKeyId bounds mode budget
      adversary (slotted setup (boundaryWire wire parse) budget
        (originEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) (orClaim setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) (g.1, g.2.castSucc))
      (startupG caps qInit budget) (allowanceG (baseAllowance caps) ceFirstTouch) fallback +
    CborRawAnomalyCca.beta setup wire parse checks (Target.ofCE budget (g.1, g.2.castSucc)) ensureInit runtime bounds mode adversary +
    ENNReal.ofReal (CborRawHeadlineChain.kemLoss setup wire parse checks ensureInit bounds mode adversary budget
      (originEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) (orClaim setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) (g.1, g.2.castSucc) runtime) +
    ENNReal.ofReal (CborRawHeadlineChain.slotLoss setup wire parse checks ensureInit bounds mode adversary budget
      (originEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) (orClaim setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b) (g.1, g.2.castSucc) runtime)) := by
  rw [CborRawHeadlineTargets.split_named setup wire parse checks lengths parser ensureInit phase1 phase2 bounds mode
    adversary budget respects _ _ runtime (PqxdhDeploymentHeadlineEvents.origin_named setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .s2b)]
  exact Finset.sum_le_sum fun g _ => ce_or_s2b_target_beta setup functional wire parse checks lengths parser ensureInit phase1 phase2
    nativePhase1 correct caps bounded qInit initBound readback bounds mode adversary budget respects runtime fallback (g.1, g.2.castSucc)

/-- The actual raw security event is bounded by the tight accept-times-create sum of its concrete per-target primitive and final-world terms. -/
theorem ce_or_b2s (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse)) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (nativePhase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : Nat) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack (boundaryWire wire parse))
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    :
    𝒟[(fun outcome => happens (originEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .b2s) outcome) <$>
      (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds mode adversary).run runtime] {true} ≤
    ∑ g : Fin budget.accept × Fin budget.create,
      (publicationTerm budget +
    CborRawHeadlineRecords.integrityLoss setup (boundaryWire wire parse) (CborRawCompile.route parse)
      (environment setup wire parse checks (Target.ofCE budget (g.1, g.2.castSucc)) ensureInit runtime) setup.serverKeyId bounds mode budget
      adversary (serverSlotted setup (boundaryWire wire parse) budget
        (originEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .b2s) (orClaim setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .b2s) (g.1, g.2.castSucc))
      (startupG caps qInit budget) (allowanceG (baseAllowance caps) ceFirstTouch) fallback +
    ENNReal.ofReal (CborRawHeadlineChain.kemLoss setup wire parse checks ensureInit bounds mode adversary budget
      (originEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .b2s) (orClaim setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .b2s) (g.1, g.2.castSucc) runtime) +
    ENNReal.ofReal (CborRawHeadlineChain.slotLoss setup wire parse checks ensureInit bounds mode adversary budget
      (originEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .b2s) (orClaim setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .b2s) (g.1, g.2.castSucc) runtime)) := by
  rw [CborRawHeadlineTargets.split_named setup wire parse checks lengths parser ensureInit phase1 phase2 bounds mode
    adversary budget respects _ _ runtime (PqxdhDeploymentHeadlineEvents.origin_named setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget (CborRawCompile.route parse) .b2s)]
  exact Finset.sum_le_sum fun g _ => ce_or_b2s_target setup functional wire parse checks lengths parser ensureInit phase1 phase2
    nativePhase1 correct caps bounded qInit initBound readback bounds mode adversary budget respects runtime fallback (g.1, g.2.castSucc)

end BeaconcryptCore.Computational.CborRawHeadlineOrigin

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineOrigin.final_s2b' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineOrigin.final_s2b
/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineOrigin.ce_or_s2b_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineOrigin.ce_or_s2b_target

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineOrigin.final_b2s' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineOrigin.final_b2s

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineOrigin.ce_or_b2s_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineOrigin.ce_or_b2s_target

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineOrigin.ce_or_s2b_target_beta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineOrigin.ce_or_s2b_target_beta

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineOrigin.ce_or_s2b' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineOrigin.ce_or_s2b

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineOrigin.ce_or_b2s' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineOrigin.ce_or_b2s
