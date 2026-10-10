-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineBills
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineApp
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineLor
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBillsFull

/-!
# The later-quantum CE-12 headlines with `β_g`, billed (CE-12 P4 step 1, P3b; design-v2 section 9)

The CE-12 P3 forms whose bound carries the anomaly term `β_g` of the run-phase adversary `first` (`PqxdhDeploymentHeadlineAnomaly.beta`, the classical `β_g` of `first`, carried to the later game by `PqxdhDeploymentIdealLaterSlots.later_anomaly_eq`) cite the IND-CCA advantage of the predict-then-compare adversary built from `first`'s anomaly guesser. Its phase-1 uniform bill (`guessBill`) was not on central when P3 was built, so P3 stated only its decapsulation count (`PqxdhDeploymentLaterHeadlineBills.beta_decapsulations_later`; guide "CE-12 P3: open points", item 2). CE-12 P2b proved that bill for every run-phase adversary (`PqxdhDeploymentHeadlineGuessBill.ptc_bills`). Here it is applied at `first`, and each theorem below restates one of those P3 forms unchanged and conjoins the bills of the reductions behind its terms:

- `LaterTargetBills`, the later per-target bills, for every event, claim, target and view event: `kem` (`kemLossL`, `PqxdhDeploymentLaterHeadlineBills.kem_bills_later`), `slot` (`slotLossL`, `slot_bills_later`), `beta` (`β_g` of `first`, `ptc_bills` at `first`: the conjunct `beta` of `PqxdhDeploymentHeadlineBillsFull.TargetBills` at `first`), `records` (`recLossL`, `records_bills_later` at the later bill input `inputL`) and `hashRoute` (the later C4 hash route, `hash_route_later`). The post budget `post` enters `kem`, `slot`, `records` and `hashRoute`; `beta` concerns the run phase only. `later_target_bills_full` proves it.
- `LaterHeadlineBills`: `LaterTargetBills` together with CE-12 P2b's bills of the symbolic terms at `first` (`A1Bills` for `ε_A1`, `A2Bills` for `ε_A2pub`), of the identity-collision reductions (`InjBills` for `ε_inj`) and of `pairAdversary` (`PairBills` for `ε_ctcoll`); `later_headline_bills` proves it. It covers the bills of every later form, including those without `β_g`.
- The billed forms: `ce_app_later_target_billed`, `ce_app_later_billed`, `ce_lor_later_target_billed` and `ce_lor_later_billed` with `LaterTargetBills`; `ce_app_later_sym_billed` with `LaterTargetBills`, `A2Bills` and `A1Bills`; `ce_app_beacon_later_sym_billed` with `LaterTargetBills` and `A1Bills`; `symbolic_lor_later_bound_billed` with `LaterTargetBills`, `A2Bills`, `A1Bills` and `InjBills`.

Not restated: the P3 forms without `β_g` (CE-KT-L with its World and symbolic forms, the Server-peer forms of CE-APP-L and CE-LOR-L and their symbolic forms, and `symbolic_lor_later`) were not gated on `guessBill`: their later bills are P3's (`later_target_bills`), the bills of their symbolic terms are P2b's at `first` (`a1_bills_all`, `a2_bills_all`, `inj_bills`), and `later_headline_bills` collects all of them. `ctGapTerm` and `ctCollTerm` are probabilities of the classical experiment of `first`, not advantages of reductions, so they have no bill; `ctCollTerm` is closed in `PqxdhDeploymentLaterHeadlineClosed`, `ctGapTerm` stays explicit (F-ct2). The bounds are the P3 theorems' own, with the same premises; the bill conjuncts add no premise beyond those the P3 form already takes (`KemBound`, `initBound`, `SourceFullCorrect`, the run budget and the post budget). No assumption or contract is added. Later mode claims confidentiality only: no origin, binding or authentication statement; the CE-A1, CE-A2pub and collider reductions are billed at the classical experiment of `first`, never on the later compiled program.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineGated

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Out : Type}

section Bills
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed selectedKem)
open PqxdhDeploymentLaterServerTransfer (decision)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhDeploymentLaterServerCompile (compileServer)
open PqxdhDeploymentLaterServerCompileBudget (laterTransported)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentEnvironmentJoin (envReveal)
open PqxdhRecordLiftIdeal (View)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (EnvG)
open PqxdhDeploymentLaterHeadlineChain (inputL)
open PqxdhDeploymentHeadlineGuessBill (guessBill)

/-- The bills of the per-target reductions of the later CE-12 headlines at the run budget and the post budget: the logged KEM adversary of `kemLossL`, the HMAC-PRF and key-schedule reductions of `slotLossL`, the predict-then-compare adversary of `β_g` of the run-phase adversary `first` (phase 1 within `guessBill` uniform queries, no base query and `qFinish + 1` decapsulations, nothing after the challenge), the later chain, integrity and privacy reductions of `recLossL` at the later bill input `inputL`, and the later C4 hash route of the record world with the ideal environment of each target. -/
structure LaterTargetBills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (caps : KemCaps) (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget) (post : PostBudget) (runtime : A) : Prop where
  kem : ∀ (event : Observed Out → Bool) (claim : Observed Out → Option Handle)
      (g : Fin budget.accept × Fin budget.capacity),
    (PqxdhDeploymentLaterServerKemHop.certified setup ensureInit none
        (PqxdhDeploymentLaterServerCut.scanned setup codec checks
          (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
          (compileServer setup codec route bounds mode first second) g.1.val)
        runtime budget.create (selectedKem budget g)).MakesAtMostQueries
      ((qInit + 32) + (caps.keygenCost * budget.create + PqxdhRegistrationJointKemPostBills.uniformCap caps budget.create
        budget.finish (PqxdhRegistrationJointOpenUniform.total caps (laterTransported bounds budget post))
        budget.accept))
      (caps.decapsBase * budget.finish) budget.finish
      (PqxdhRegistrationJointKemPostBills.uniformCap caps budget.create budget.finish
        (PqxdhRegistrationJointOpenUniform.total caps (laterTransported bounds budget post)) budget.accept)
      (caps.decapsBase * budget.finish) budget.finish
  slot : ∀ (event : Observed Out → Bool) (claim : Observed Out → Option Handle)
      (g : Fin budget.accept × Fin budget.capacity),
    (∀ slot ∈ Finset.range 2, PqxdhRegistrationJointKemKeyTransfer.PrfBills setup.hmac
      (PqxdhDeploymentLaterServerItemTargets.rootClientL (Reader := Reader) setup codec checks ensureInit none
        (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (compileServer setup codec route bounds mode first second) runtime budget.create (selectedKem budget g) g.1.val)
      slot (PqxdhDeploymentLaterServerItemTargets.rootBillL caps qInit none budget.create
        (laterTransported bounds budget post))) ∧
    ∀ k ∈ Finset.range 2, PqxdhServerAuthEntryFactor.EntryComponentBills setup.source setup.hmac
      (PqxdhDeploymentLaterServerItemTargets.entryDkL (Reader := Reader) setup codec checks ensureInit none
        (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (compileServer setup codec route bounds mode first second) runtime budget.create (selectedKem budget g) g.1.val
        k)
      (PqxdhDeploymentLaterServerItemTargets.rootBillL caps qInit none budget.create
        (laterTransported bounds budget post) + 216)
  beta : ∀ g : Fin budget.accept × Fin budget.capacity,
    (PqxdhDeploymentHeadlineAnomaly.ptc setup.kem (PqxdhDeploymentIdealAnomalyGuesser.anomalyGuesser setup codec route
      checks (Target.ofCE budget g) ensureInit 0 runtime bounds mode first)).MakesAtMostQueries
        (guessBill caps qInit budget bounds) 0 (budget.finish + 1) 0 0 0
  records : ∀ (g : Fin budget.accept × Fin budget.capacity) (event : View 2 (EnvG KemSK budget) Out → Bool),
    PqxdhRecordLiftLaterTargets.LaterRecordBounded 2
      (PqxdhRecordLiftLaterChain.laterChainReduction setup codec route setup.serverKeyId bounds 2)
      (PqxdhRecordLiftLaterCtx.laterCtxReduction setup codec route setup.serverKeyId bounds)
      (PqxdhRecordLiftLaterPriv.laterPrivReduction setup codec route setup.serverKeyId bounds)
      PqxdhRecordLiftLaterChain.laterChainBills PqxdhRecordLiftLaterCtx.laterCtxBills
      PqxdhRecordLiftLaterPriv.laterPrivBills
      (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime) mode envReveal
      first second (fun view => pure (event view)) budget post (inputL caps qInit budget bounds post)
  hashRoute : ∀ g : Fin budget.accept × Fin budget.capacity,
    ∀ result ∈ support (PqxdhRecordLiftLater.run setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode envReveal first second),
      result.2.primitive.1.effects .hash + result.2.primitive.1.native .hash ≤
          budget.hash + budget.sends + budget.receives + budget.build + budget.finish + post.hash ∧
        result.2.primitive.1.native .kdf ≤ budget.sends + 51 * budget.receives

/-- `LaterTargetBills` holds: `kem_bills_later`, `slot_bills_later`, `ptc_bills` at the run-phase adversary `first`, `records_bills_later` and `hash_route_later`. Premises: `SourceFullCorrect`, `KemBound`, `initBound`, `budget.Respects first` and the post budget of `second` on every input. -/
theorem later_target_bills_full (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    LaterTargetBills setup codec checks route caps ensureInit qInit bounds mode first second budget post runtime where
  kem event claim g := PqxdhDeploymentLaterHeadlineBills.kem_bills_later setup codec checks route caps bounded ensureInit
    qInit initBound bounds mode first second budget respects post postRespects event claim g runtime
  slot event claim g := PqxdhDeploymentLaterHeadlineBills.slot_bills_later setup codec checks route caps bounded
    ensureInit qInit initBound bounds mode first second budget respects post postRespects event claim g runtime
  beta g := PqxdhDeploymentHeadlineGuessBill.ptc_bills setup codec route checks caps bounded ensureInit qInit initBound
    bounds mode first budget respects g runtime
  records g event := PqxdhDeploymentLaterHeadlineBills.records_bills_later setup codec checks route correct caps bounded
    ensureInit qInit initBound bounds mode first second budget respects post postRespects g runtime fallback event
  hashRoute g := PqxdhDeploymentLaterHeadlineBills.hash_route_later setup codec checks route caps bounded ensureInit
    qInit initBound bounds mode first second budget respects post postRespects g runtime

/-- `LaterHeadlineBills`: the bills of every reduction behind the terms of the later CE-12 headlines and their symbolic corollaries: the later per-target bills (`LaterTargetBills`), and CE-12 P2b's bills of the terms of the classical experiment of the run-phase adversary `first` (`A1Bills` for `ε_A1`, `A2Bills` for `ε_A2pub`), of the identity-collision reductions (`InjBills` for `ε_inj`) and of `pairAdversary` (`PairBills` for `ε_ctcoll`). -/
structure LaterHeadlineBills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (caps : KemCaps) (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget) (post : PostBudget) (runtime : A)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    Prop where
  target : LaterTargetBills setup codec checks route caps ensureInit qInit bounds mode first second budget post runtime
  a1 : PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds mode first budget a1Fallback
    signatureFallback
  a2 : PqxdhDeploymentHeadlineBillsFull.A2Bills setup codec checks route caps ensureInit qInit bounds mode first budget
    runtime identityFallback ordinaryFallback
  inj : PqxdhDeploymentHeadlineBillsFull.InjBills setup budget
  pair : PqxdhDeploymentHeadlineBillsFull.PairBills setup caps

/-- `LaterHeadlineBills` holds. Premises: `SourceFullCorrect`, `KemBound`, `initBound`, `budget.Respects first` and the post budget of `second` on every input. -/
theorem later_headline_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    LaterHeadlineBills setup codec checks route caps ensureInit qInit bounds mode first second budget post runtime
      identityFallback ordinaryFallback a1Fallback signatureFallback where
  target := later_target_bills_full setup codec checks route correct caps bounded ensureInit qInit initBound bounds mode
    first second budget respects post postRespects runtime fallback
  a1 := PqxdhDeploymentHeadlineBillsFull.a1_bills_all setup codec checks caps bounded route bounds mode first budget
    respects a1Fallback signatureFallback
  a2 := PqxdhDeploymentHeadlineBillsFull.a2_bills_all setup codec checks route caps bounded ensureInit qInit initBound
    bounds mode first budget respects runtime identityFallback ordinaryFallback
  inj := PqxdhDeploymentHeadlineBillsFull.inj_bills setup budget
  pair := PqxdhDeploymentHeadlineBills.pair_bills setup caps bounded

end Bills

section App
open PqxdhDeploymentLaterHeadlineApp
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

/-- `ce_app_later_target` (`PqxdhDeploymentLaterHeadlineApp.ce_app_later_target`) with its bills: the same bound, together with the later per-target bills (`LaterTargetBills`: `kemLossL` and `slotLossL` at the post budget, `β_g` of the run-phase adversary `first` through `ptc_bills`, `recLossL` at the later bill input `inputL`, and the later C4 hash route), so that every advantage term of the bound, including `β_g`, cites a reduction whose query caps are proved at the run budget and the post budget. -/
theorem ce_app_later_target_billed (setup : Setup baseSpec KemSK)
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
    (𝒟[(fun outcome => decide (happens (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) outcome =
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
      ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹) ∧
      LaterTargetBills setup codec checks route caps ensureInit qInit bounds .P first second
        budget post runtime :=
  ⟨PqxdhDeploymentLaterHeadlineApp.ce_app_later_target setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound bounds first second budget respects post postRespects runtime fallback
    appClaim g,
   later_target_bills_full setup codec checks route correct caps bounded ensureInit qInit initBound bounds .P
    first second budget respects post postRespects runtime fallback⟩

/-- `ce_app_later` (`PqxdhDeploymentLaterHeadlineApp.ce_app_later`, CE-APP-L) with its bills: the same bound, together with the later per-target bills (`LaterTargetBills`: `kemLossL` and `slotLossL` at the post budget, `β_g` of the run-phase adversary `first` through `ptc_bills`, `recLossL` at the later bill input `inputL`, and the later C4 hash route), so that every advantage term of the bound, including `β_g`, cites a reduction whose query caps are proved at the run budget and the post budget. -/
theorem ce_app_later_billed (setup : Setup baseSpec KemSK)
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
    (𝒟[(fun outcome => happens (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) outcome) <$>
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
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) ∧
      LaterTargetBills setup codec checks route caps ensureInit qInit bounds .P first second
        budget post runtime :=
  ⟨PqxdhDeploymentLaterHeadlineApp.ce_app_later setup functional codec checks route ensureInit phase1 phase2 correct
    caps bounded qInit initBound bounds first second budget respects post postRespects runtime fallback appClaim,
   later_target_bills_full setup codec checks route correct caps bounded ensureInit qInit initBound bounds .P
    first second budget respects post postRespects runtime fallback⟩

end App

section Lor
open PqxdhDeploymentLaterHeadlineLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLaterServerTransfer (happens designated)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealTrace (IdealSlots)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentEnvironmentJoin (envReveal)
open PqxdhRecordLiftIdeal (View publicHiding chainView ctxView)
open PqxdhRecordLiftLaterWorlds (laterRealChains laterIdealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (EnvG ServerSlots slotted serverSlotted chance_ne_top)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (lorWinEvent lorEligEvent lorWinPeerEvent lorEligPeerEvent lorClaim)
open PqxdhDeploymentHeadlineLor (hidingOf decisionHiding)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

open Classical in
/-- `ce_lor_later_target` (`PqxdhDeploymentLaterHeadlineLor.ce_lor_later_target`) with its bills: the same bound, together with the later per-target bills (`LaterTargetBills`: `kemLossL` and `slotLossL` at the post budget, `β_g` of the run-phase adversary `first` through `ptc_bills`, `recLossL` at the later bill input `inputL`, and the later C4 hash route), so that every advantage term of the bound, including `β_g`, cites a reduction whose query caps are proved at the run budget and the post budget. -/
theorem ce_lor_later_target_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (guess : Out → Bool)
    (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool) (g : Fin budget.accept × Fin budget.capacity) :
    (ENNReal.ofReal |(𝒟[(fun outcome => decide (happens (lorWinEvent setup.source.crypto codec setup.serverKeyId budget
          guess filter) outcome = true ∧
          designated setup.source.crypto codec setup.serverKeyId budget lorClaim outcome = some g)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
          runtime] {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => decide (happens (lorEligEvent setup.source.crypto codec setup.serverKeyId budget
          filter) outcome = true ∧
          designated setup.source.crypto codec setup.serverKeyId budget lorClaim outcome = some g)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
          runtime] {true}).toReal| ≤
      ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
        (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim g runtime) +
      ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second budget post
        (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim g runtime) +
      recLossL setup codec checks route ensureInit bounds .P first second budget post g runtime fallback caps qInit
        (slotted setup codec budget (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter)
          lorClaim g) +
      2⁻¹ * (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
          (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g runtime) +
        ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second budget
          post (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g runtime) +
        recLossL setup codec checks route ensureInit bounds .P first second budget post g runtime fallback caps qInit
          (slotted setup codec budget (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter)
            lorClaim g)) +
      2⁻¹ * beta setup codec route checks ensureInit bounds .P first budget g runtime) ∧
      LaterTargetBills setup codec checks route caps ensureInit qInit bounds .P first second
        budget post runtime :=
  ⟨PqxdhDeploymentLaterHeadlineLor.ce_lor_later_target setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound bounds first second budget respects post postRespects runtime fallback guess
    filter g,
   later_target_bills_full setup codec checks route correct caps bounded ensureInit qInit initBound bounds .P
    first second budget respects post postRespects runtime fallback⟩

open Classical in
/-- `ce_lor_later` (`PqxdhDeploymentLaterHeadlineLor.ce_lor_later`, CE-LOR-L) with its bills: the same bound, together with the later per-target bills (`LaterTargetBills`: `kemLossL` and `slotLossL` at the post budget, `β_g` of the run-phase adversary `first` through `ptc_bills`, `recLossL` at the later bill input `inputL`, and the later C4 hash route), so that every advantage term of the bound, including `β_g`, cites a reduction whose query caps are proved at the run budget and the post budget. -/
theorem ce_lor_later_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (guess : Out → Bool)
    (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool) :
    (ENNReal.ofReal |(𝒟[(fun outcome => happens (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess
          filter) outcome) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
          runtime] {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => happens (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter)
          outcome) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
          runtime] {true}).toReal| ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
            (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim (g.1, g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second budget
            post (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc) runtime
            fallback caps qInit (slotted setup codec budget
              (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
              (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second
              budget post (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc) runtime
              fallback caps qInit (slotted setup codec budget
                (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup codec route checks ensureInit bounds .P first budget (g.1, g.2.castSucc) runtime)) ∧
      LaterTargetBills setup codec checks route caps ensureInit qInit bounds .P first second
        budget post runtime :=
  ⟨PqxdhDeploymentLaterHeadlineLor.ce_lor_later setup functional codec checks route ensureInit phase1 phase2 correct
    caps bounded qInit initBound bounds first second budget respects post postRespects runtime fallback guess filter,
   later_target_bills_full setup codec checks route correct caps bounded ensureInit qInit initBound bounds .P
    first second budget respects post postRespects runtime fallback⟩

end Lor

section Symbolic
open PqxdhDeploymentLaterHeadlineSymbolic
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal LaterState)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap ServerGap BeaconGap a2pubTerm a1Term ctGapTerm
  chance_le_add_support)
open PqxdhDeploymentHeadlineSymbolic (appSym appPeerSym appOwnerSym ktSym ktPeerSym ktOwnerSym)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

/-- `ce_app_later_sym` (`PqxdhDeploymentLaterHeadlineSymbolic.ce_app_later_sym`) with its bills: the same bound, together with the later per-target bills (`LaterTargetBills`: `kemLossL` and `slotLossL` at the post budget, `β_g` of the run-phase adversary `first` through `ptc_bills`, `recLossL` at the later bill input `inputL`, and the later C4 hash route), the bills of the CE-A2pub reductions behind `ε_A2pub` (`A2Bills`) and of the CE-A1 reductions behind `ε_A1` (`A1Bills`), both at the run-phase adversary `first`. `ctGapTerm` is a probability of the classical experiment of `first` and has no bill. -/
theorem ce_app_later_sym_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes))
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[(fun outcome => appSym setup codec appClaim (asClassical outcome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
        runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
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
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (a2pubTerm setup codec checks route ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds .P first budget a1Fallback signatureFallback) +
        ctGapTerm setup codec checks route ensureInit bounds .P first runtime)) ∧
      LaterTargetBills setup codec checks route caps ensureInit qInit bounds .P first second
        budget post runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup codec checks route caps ensureInit qInit bounds .P first budget
        runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds .P first budget a1Fallback
        signatureFallback :=
  ⟨PqxdhDeploymentLaterHeadlineSymbolic.ce_app_later_sym setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound shortRejects frameReadBack writable law spread adapter bounds first second
    budget respects post postRespects runtime fallback appClaim identityFallback ordinaryFallback a1Fallback
    signatureFallback,
   ⟨later_target_bills_full setup codec checks route correct caps bounded ensureInit qInit initBound bounds .P
    first second budget respects post postRespects runtime fallback,
    PqxdhDeploymentHeadlineBillsFull.a2_bills_all setup codec checks route caps bounded ensureInit qInit initBound
     bounds .P first budget respects runtime identityFallback ordinaryFallback,
    PqxdhDeploymentHeadlineBillsFull.a1_bills_all setup codec checks caps bounded route bounds .P first budget
     respects a1Fallback signatureFallback⟩⟩

/-- `ce_app_beacon_later_sym` (`PqxdhDeploymentLaterHeadlineSymbolic.ce_app_beacon_later_sym`) with its bills: the same bound, together with the later per-target bills (`LaterTargetBills`: `kemLossL` and `slotLossL` at the post budget, `β_g` of the run-phase adversary `first` through `ptc_bills`, `recLossL` at the later bill input `inputL`, and the later C4 hash route) and the bills of the CE-A1 reductions behind `ε_A1` at the run-phase adversary `first` (`A1Bills`). `ctGapTerm` is a probability of the classical experiment of `first` and has no bill. -/
theorem ce_app_beacon_later_sym_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes))
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[(fun outcome => appOwnerSym setup appClaim (asClassical outcome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
        runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
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
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (ENNReal.ofReal (a1Term setup codec checks caps route bounds .P first budget a1Fallback signatureFallback) +
        ctGapTerm setup codec checks route ensureInit bounds .P first runtime)) ∧
      LaterTargetBills setup codec checks route caps ensureInit qInit bounds .P first second
        budget post runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds .P first budget a1Fallback
        signatureFallback :=
  ⟨PqxdhDeploymentLaterHeadlineSymbolic.ce_app_beacon_later_sym setup functional codec checks route ensureInit phase1
    phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds first second budget
    respects post postRespects runtime fallback appClaim a1Fallback signatureFallback,
   ⟨later_target_bills_full setup codec checks route correct caps bounded ensureInit qInit initBound bounds .P
    first second budget respects post postRespects runtime fallback,
    PqxdhDeploymentHeadlineBillsFull.a1_bills_all setup codec checks caps bounded route bounds .P first budget
     respects a1Fallback signatureFallback⟩⟩

end Symbolic

section SymbolicLor
open PqxdhDeploymentLaterHeadlineSymbolicLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLater (PostSpec PostBudget Caches)
open PqxdhDeploymentLaterServerGame (Reveal LaterState)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap ServerGap BeaconGap a2pubTerm a1Term ctGapTerm
  chance_le_support chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (IdentityCollision ctCollEvent ctCollTerm injTerm)
open PqxdhDeploymentHeadlineEvents (LorElig PeerTests lorEligEvent lorWinEvent lorEligPeerEvent lorWinPeerEvent
  lorClaim)
open PqxdhDeploymentHeadlineSymbolicLor (LorEligSym LorWinSym lorEligSym lorWinSym LorEligPeerSym LorWinPeerSym
  lorEligPeerSym lorWinPeerSym nbfFilter)
open PqxdhDeploymentLaterHeadlineSymbolic (asClassical runOutcome classical_later)
open PqxdhDeploymentLaterHeadlineSymbolic (happens_asClassical gaps_later serverGap_later)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

/-- `symbolic_lor_later_bound` (`PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_later_bound`) with its bills: the same bound, together with the later per-target bills (`LaterTargetBills`: `kemLossL` and `slotLossL` at the post budget, `β_g` of the run-phase adversary `first` through `ptc_bills`, `recLossL` at the later bill input `inputL`, and the later C4 hash route), the bills of the CE-A2pub reductions (`A2Bills`) and of the CE-A1 reductions (`A1Bills`) at the run-phase adversary `first`, and the bills of the identity-collision reductions behind `ε_inj` (`InjBills`). `ctGapTerm` and `ctCollTerm` are probabilities of the classical experiment of `first` and have no bill; the closed form of `ctCollTerm` is `PqxdhDeploymentLaterHeadlineClosed.symbolic_lor_later_bound_closed_billed`. -/
theorem symbolic_lor_later_bound_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (runtime : A) (guess : Out → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    (ENNReal.ofReal |((𝒟[(fun outcome => lorWinSym setup codec guess (asClassical outcome)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => lorEligSym setup codec (asClassical outcome)) <$>
          (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
            (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim (g.1, g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second budget
            post (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc) runtime
            fallback caps qInit (slotted setup codec budget
              (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
              (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second
              budget post (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc) runtime
              fallback caps qInit (slotted setup codec budget
                (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup codec route checks ensureInit bounds .P first budget (g.1, g.2.castSucc) runtime)) +
      2⁻¹ * (a2pubTerm setup codec checks route ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds .P first budget a1Fallback signatureFallback) +
        ctGapTerm setup codec checks route ensureInit bounds .P first runtime +
        injTerm setup budget + ctCollTerm setup codec checks route ensureInit bounds .P first runtime)) ∧
      LaterTargetBills setup codec checks route caps ensureInit qInit bounds .P first second
        budget post runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup codec checks route caps ensureInit qInit bounds .P first budget
        runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds .P first budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget :=
  ⟨PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_later_bound setup functional codec checks caps bounded
    shortRejects route ensureInit phase1 phase2 frameBack writable law spread correct adapter bounds first second
    budget respects runtime guess identityFallback ordinaryFallback a1Fallback signatureFallback qInit initBound post
    postRespects fallback,
   ⟨later_target_bills_full setup codec checks route correct caps bounded ensureInit qInit initBound bounds .P
    first second budget respects post postRespects runtime fallback,
    PqxdhDeploymentHeadlineBillsFull.a2_bills_all setup codec checks route caps bounded ensureInit qInit initBound
     bounds .P first budget respects runtime identityFallback ordinaryFallback,
    PqxdhDeploymentHeadlineBillsFull.a1_bills_all setup codec checks caps bounded route bounds .P first budget
     respects a1Fallback signatureFallback,
    PqxdhDeploymentHeadlineBillsFull.inj_bills setup budget⟩⟩

end SymbolicLor

end BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineGated

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineGated.later_target_bills_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineGated.later_target_bills_full

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineGated.later_headline_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineGated.later_headline_bills

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineGated.ce_app_later_target_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineGated.ce_app_later_target_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineGated.ce_app_later_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineGated.ce_app_later_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineGated.ce_lor_later_target_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineGated.ce_lor_later_target_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineGated.ce_lor_later_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineGated.ce_lor_later_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineGated.ce_app_later_sym_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineGated.ce_app_later_sym_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineGated.ce_app_beacon_later_sym_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineGated.ce_app_beacon_later_sym_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineGated.symbolic_lor_later_bound_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineGated.symbolic_lor_later_bound_billed
