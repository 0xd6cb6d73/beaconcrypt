-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawHeadlineLor
import BeaconcryptCore.Computational.CborRawHeadlineTwoSided
import BeaconcryptCore.Computational.CborRawHeadlineApp
import BeaconcryptCore.Computational.CborRawHeadlineTargets

/-! The actual raw-CBOR CE-LOR advantage composes the exact source/record handoff, concrete primitive reductions, unchanged hidden-bit ledger and actual pre-challenge anomaly predictor. Server-peer endpoints retain no anomaly term, and total endpoints use the tight accept-times-create target sum. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawHeadlineLorSecurity
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FreshBounds ModeSpec Mode Budget Handle)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhRecordLiftIdeal (View chainView ctxView publicHiding)
open PqxdhRecordLiftInterface (Environment)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealTrace (IdealSlots)
open PqxdhDeploymentIdealHandoff (viewObserved decisionOn)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted ServerSlots startupG chance_ne_top)
open PqxdhDeploymentHeadlineEvents (lorWinEvent lorEligEvent lorWinPeerEvent lorEligPeerEvent lorClaim)
open PqxdhDeploymentHeadlineLor (decided_view lorEligPeerEvent_view lorClaim_view serverSlots_view decisionHiding
  hidingOf guess_hiding win_peer_slotted eligible_hiding lorWin_iff chance_split lor_bound lor_bound_server
  lorWin_named lorElig_named lorWinPeer_named lorEligPeer_named)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentEnvironment (allowanceG baseAllowance ceFirstTouch)
open CborRawHeadlineSlots (environment realView)
open CborRawHeadlineRecords (randomLoss)
open CborTaggedSimulation (boundaryWire)
variable {ι KemSK Reader Response A E X : Type} {baseSpec : OracleSpec ι}

abbrev EnvG (KemSK : Type) (budget : Budget) :=
  CborRawPublicState.Public × PqxdhDeploymentHeadlineChain.EnvG KemSK budget

noncomputable def recordLoss (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (caps : KemCaps) (qInit : Nat)
    (event : View 2 (EnvG KemSK budget) X → Bool) : ℝ≥0∞ :=
  randomLoss setup (boundaryWire wire parse) (CborRawCompile.route parse)
    (environment setup wire parse checks (Target.ofCE budget g) ensureInit runtime) setup.serverKeyId bounds mode budget
    adversary event (startupG caps qInit budget) (allowanceG (baseAllowance caps) ceFirstTouch) fallback

attribute [local irreducible] CborRawHeadlineRecords.randomLoss CborRawHeadlineChain.kemLoss CborRawHeadlineChain.slotLoss
  PqxdhRecordLiftLaterWorlds.chainsOf PqxdhRecordLiftLaterWorlds.ctxRunOf CborRawCompileSecrecy.game CborRawAnomalyCca.beta

/-- The actual raw random-record world has an unbiased hidden test bit on eligible Server peers. -/
theorem lor_server_final (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : PqxdhRecordLiftInterface.Environment 2 E)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (g : Fin budget.accept × Fin budget.capacity) (guess : X → Bool)
    (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool) :
    𝒟[serverSlotted setup codec budget (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess filter)
        lorClaim g <$> (ctxView <$> CborRawRecordHidingLaw.ctxRun (fun _ => .random) id setup codec route env setup.serverKeyId bounds .P adversary)] {true} =
      2⁻¹ * 𝒟[serverSlotted setup codec budget (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter)
        lorClaim g <$> (ctxView <$> CborRawRecordHidingLaw.ctxRun (fun _ => .random) id setup codec route env setup.serverKeyId bounds .P adversary)] {true} := by
  have invariant : ∀ view view' : View 2 (E) X, publicHiding view = publicHiding view' →
      serverSlotted setup codec budget (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g
        view =
      serverSlotted setup codec budget (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g
        view' := fun view view' same =>
    decided_view setup codec budget _ lorClaim g
      (fun transcript slots => ServerSlots setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) slots
        transcript)
      (lorEligPeerEvent_view setup.source.crypto codec setup.serverKeyId budget filter)
      (lorClaim_view setup.source.crypto codec setup.serverKeyId budget)
      (fun first second slots same => serverSlots_view setup.source.crypto codec setup.serverKeyId _ slots first second
        same) view view' same
  have hidden : ∀ view : View 2 (E) X,
      serverSlotted setup codec budget (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g
        view = true → PqxdhRecordLiftIdeal.TestsHidden setup.source.crypto codec setup.serverKeyId view :=
    fun view held => PqxdhDeploymentHeadlineContain.lor_peer_hidden setup codec budget filter g view held
  have win : serverSlotted (E := E) setup codec budget
      (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim g =
      fun view => PqxdhRecordLiftIdeal.lorGuess setup.source.crypto codec setup.serverKeyId (decisionHiding guess)
        (hidingOf (serverSlotted setup codec budget (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter)
          lorClaim g)) view := funext fun view => by
    rw [guess_hiding setup codec guess _ invariant hidden view, win_peer_slotted]
  have eligible : serverSlotted (E := E) setup codec budget
      (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g =
      fun view => PqxdhRecordLiftIdeal.lorEligible setup.source.crypto codec setup.serverKeyId
        (hidingOf (serverSlotted setup codec budget (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter)
          lorClaim g)) view := funext fun view => (eligible_hiding setup codec _ invariant hidden view).symm
  conv_lhs => rw [win, Functor.map_map]
  conv_rhs => rw [eligible, Functor.map_map]
  exact CborRawRecordLor.lor setup codec route env setup.serverKeyId bounds adversary (decisionHiding guess) _



/-- Unslotted eligibility in the complete raw World is covered by the actual native early-finish event. -/
theorem unslotted (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (nativePhase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (ensureInit : StateT A ProbComp Bool) (runtime : A) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (event : Observed X → Bool)
    (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity) :
    letI := Classical.propDecidable
    𝒟[(fun view => decide ((viewObserved view).any (decisionOn setup (boundaryWire wire parse) budget event claim g) = true ∧
      ¬(∀ value, view.result = some value → IdealSlots setup.source.crypto (boundaryWire wire parse)
        setup.serverKeyId (Target.ofCE budget g) view.slots value.2.1.transcript))) <$>
      realView setup wire parse checks (Target.ofCE budget g) ensureInit runtime bounds mode adversary] {true} ≤
    𝒟[CborRawHeadlineSlots.anomaly setup wire parse (Target.ofCE budget g) <$>
      realView setup wire parse checks (Target.ofCE budget g) ensureInit runtime bounds mode adversary] {true} := by
  classical
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map]
  apply prEvent_mono_of_support
  intro view member held
  simp only [CborRawHeadlineSlots.anomaly, decide_eq_true_eq] at held ⊢
  rw [realView, support_map] at member
  obtain ⟨result, resultMember, rfl⟩ := member
  obtain ⟨value, unslotted⟩ := Classical.not_forall.mp held.2
  obtain ⟨found, failed⟩ := Classical.not_imp.mp unslotted
  exact ⟨value, found, (CborRawRecordProvenance.real_slots_or_anomaly setup wire parse checks nativePhase1 phase2
    (Target.ofCE budget g) ensureInit 0 runtime bounds mode adversary result resultMember value found).resolve_left failed⟩

/-- All actual raw World outcomes satisfy the Server slot conditions used by Server-peer decisions. -/
theorem server_view (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (nativePhase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (ensureInit : StateT A ProbComp Bool) (runtime : A) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (event : Observed X → Bool)
    (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[(fun view => (viewObserved view).any (decisionOn setup (boundaryWire wire parse) budget event claim g)) <$>
      realView setup wire parse checks (Target.ofCE budget g) ensureInit runtime bounds mode adversary] {true} =
    𝒟[serverSlotted setup (boundaryWire wire parse) budget event claim g <$>
      realView setup wire parse checks (Target.ofCE budget g) ensureInit runtime bounds mode adversary] {true} := by
  classical
  unfold realView
  congr 2
  rw [Functor.map_map, Functor.map_map]
  refine PqxdhDeploymentKemTransfer.map_support_congr _ _ _ fun result member => ?_
  simp only [serverSlotted]
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact ⟨fun held => ⟨held, CborRawRecordProvenance.real_server_slots setup wire parse checks nativePhase1 phase2
    (Target.ofCE budget g) ensureInit 0 runtime bounds mode adversary result member⟩, And.left⟩

open Classical in
/-- The actual raw per-target CE-LOR advantage has concrete source, record and half-anomaly losses. -/
theorem ce_lor_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse))
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (nativePhase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (guess : X → Bool) (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool)
    (g : Fin budget.accept × Fin budget.capacity) :
    ENNReal.ofReal |(𝒟[(fun outcome => decide (happens (lorWinEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget
          guess filter) outcome = true ∧
          designated setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget lorClaim outcome = some g)) <$>
        (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => decide (happens (lorEligEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget
          filter) outcome = true ∧
          designated setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget lorClaim outcome = some g)) <$>
        (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal| ≤
      ENNReal.ofReal (CborRawHeadlineChain.kemLoss setup wire parse checks ensureInit bounds .P adversary budget
        (lorWinEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget guess filter) lorClaim g runtime) +
      ENNReal.ofReal (CborRawHeadlineChain.slotLoss setup wire parse checks ensureInit bounds .P adversary budget
        (lorWinEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget guess filter) lorClaim g runtime) +
      recordLoss setup wire parse checks ensureInit bounds .P adversary budget g runtime fallback caps qInit
        (slotted setup (boundaryWire wire parse) budget (lorWinEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget guess filter)
          lorClaim g) +
      2⁻¹ * (ENNReal.ofReal (CborRawHeadlineChain.kemLoss setup wire parse checks ensureInit bounds .P adversary budget
          (lorEligEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget filter) lorClaim g runtime) +
        ENNReal.ofReal (CborRawHeadlineChain.slotLoss setup wire parse checks ensureInit bounds .P adversary budget
          (lorEligEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget filter) lorClaim g runtime) +
        recordLoss setup wire parse checks ensureInit bounds .P adversary budget g runtime fallback caps qInit
          (slotted setup (boundaryWire wire parse) budget (lorEligEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget filter)
            lorClaim g)) +
      2⁻¹ * CborRawAnomalyCca.beta setup wire parse checks (Target.ofCE budget g) ensureInit runtime bounds .P adversary := by
  set realView := CborRawHeadlineSlots.realView setup wire parse checks (Target.ofCE budget g) ensureInit runtime bounds
    .P adversary with hrealView
  set idealView := ctxView <$> PqxdhRecordLiftLaterWorlds.ctxRunOf (fun _ => .random) id setup (boundaryWire wire parse)
    (CborRawCompile.route parse) (CborRawRecordLiftBounds.client
      (environment setup wire parse checks (Target.ofCE budget g) ensureInit runtime) setup.source.crypto
      (boundaryWire wire parse) setup.serverKeyId bounds .P adversary) with hidealView
  set win := lorWinEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget guess filter with hwin
  set elig := lorEligEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget filter with helig
  set ideal : View 2 (EnvG KemSK budget) X → Prop := fun view => ∀ value, view.result = some value →
    IdealSlots setup.source.crypto (boundaryWire wire parse) setup.serverKeyId (Target.ofCE budget g) view.slots value.2.1.transcript
    with hideal
  have winElig : ∀ view : View 2 (EnvG KemSK budget) X,
      (viewObserved view).any (decisionOn setup (boundaryWire wire parse) budget win lorClaim g) = true →
        (viewObserved view).any (decisionOn setup (boundaryWire wire parse) budget elig lorClaim g) = true := by
    intro view held
    rcases view with ⟨_ | value, produced, raw, slots⟩
    · simp [viewObserved] at held
    · simp only [viewObserved, Option.map_some, Option.any_some, decisionOn, Bool.and_eq_true] at held ⊢
      exact ⟨((lorWin_iff setup (boundaryWire wire parse) budget guess filter _).mp held.1).1, held.2⟩
  have splitW := chance_split realView (fun view => (viewObserved view).any (decisionOn setup (boundaryWire wire parse) budget win lorClaim g))
    ideal
  have splitE := chance_split realView (fun view => (viewObserved view).any
    (decisionOn setup (boundaryWire wire parse) budget elig lorClaim g)) ideal
  have below := PqxdhDeploymentHeadlineContain.chance_mono realView
    (fun view => decide ((viewObserved view).any (decisionOn setup (boundaryWire wire parse) budget win lorClaim g) = true ∧ ¬ideal view))
    (fun view => decide ((viewObserved view).any (decisionOn setup (boundaryWire wire parse) budget elig lorClaim g) = true ∧ ¬ideal view))
    (fun view held => by
      rw [decide_eq_true_iff] at held ⊢
      exact ⟨winElig view held.1, held.2⟩)
  have anomaly := (unslotted setup wire parse checks nativePhase1 phase2 ensureInit runtime bounds .P adversary budget
    elig lorClaim g).trans (CborRawHeadlineAnomaly.anomaly_beta setup functional wire parse checks lengths parser phase1
      phase2 nativePhase1 (Target.ofCE budget g) ensureInit runtime bounds .P adversary)
  have anomaly' :
      𝒟[(fun view : View 2 (EnvG KemSK budget) X => decide
        ((viewObserved view).any (decisionOn setup (boundaryWire wire parse) budget elig lorClaim g) = true ∧
          ¬ideal view)) <$> realView] {true} ≤
        CborRawAnomalyCca.beta setup wire parse checks (Target.ofCE budget g) ensureInit runtime bounds .P adversary := by
    rw [← prEvent_eq_evalDist_singleton _ true, prEvent_map] at anomaly ⊢
    simpa only [decide_eq_true_eq] using anomaly
  have final := CborRawHeadlineLor.lor_final setup (boundaryWire wire parse) (CborRawCompile.route parse)
    (environment setup wire parse checks (Target.ofCE budget g) ensureInit runtime) bounds adversary budget g guess filter
  have chainW := CborRawHeadlineTwoSided.chain_real_close setup functional wire parse checks lengths parser nativePhase1
    ensureInit phase1 phase2 correct bounds .P adversary budget respects win lorClaim g runtime
  have chainE := CborRawHeadlineTwoSided.chain_real_close setup functional wire parse checks lengths parser nativePhase1
    ensureInit phase1 phase2 correct bounds .P adversary budget respects elig lorClaim g runtime
  have framed := CborRawHeadlineApp.frame setup wire parse checks caps bounded ensureInit qInit initBound budget g runtime
  have liftW := CborRawHeadlineRecords.random_close setup (boundaryWire wire parse) (CborRawCompile.route parse)
    (environment setup wire parse checks (Target.ofCE budget g) ensureInit runtime) (startupG caps qInit budget)
    (allowanceG (baseAllowance caps) ceFirstTouch) framed setup.serverKeyId bounds .P budget adversary respects
    (slotted setup (boundaryWire wire parse) budget win lorClaim g) correct fallback
  have liftE := CborRawHeadlineRecords.random_close setup (boundaryWire wire parse) (CborRawCompile.route parse)
    (environment setup wire parse checks (Target.ofCE budget g) ensureInit runtime) (startupG caps qInit budget)
    (allowanceG (baseAllowance caps) ceFirstTouch) framed setup.serverKeyId bounds .P budget adversary respects
    (slotted setup (boundaryWire wire parse) budget elig lorClaim g) correct fallback
  have bound := lor_bound _ _ _ _ _ _ _ _ _ _ (chance_ne_top _ _) (chance_ne_top _ _) (chance_ne_top _ _)
    (chance_ne_top _ _) splitW splitE final below _ _ chainW chainE _ _ liftW liftE _ anomaly'
  refine bound.trans ?_
  gcongr ?_ + _ + 2⁻¹ * (?_ + _) + _ <;> exact ENNReal.ofReal_add_le

open Classical in
/-- The actual raw Server-peer CE-LOR advantage has concrete source and record losses with no anomaly term. -/
theorem ce_lor_server_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse))
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (nativePhase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (guess : X → Bool) (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool)
    (g : Fin budget.accept × Fin budget.capacity) :
    ENNReal.ofReal |(𝒟[(fun outcome => decide (happens (lorWinPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId
          budget guess filter) outcome = true ∧
          designated setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget lorClaim outcome = some g)) <$>
        (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => decide (happens (lorEligPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId
          budget filter) outcome = true ∧
          designated setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget lorClaim outcome = some g)) <$>
        (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal| ≤
      ENNReal.ofReal (CborRawHeadlineChain.kemLoss setup wire parse checks ensureInit bounds .P adversary budget
        (lorWinPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget guess filter) lorClaim g runtime) +
      ENNReal.ofReal (CborRawHeadlineChain.slotLoss setup wire parse checks ensureInit bounds .P adversary budget
        (lorWinPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget guess filter) lorClaim g runtime) +
      recordLoss setup wire parse checks ensureInit bounds .P adversary budget g runtime fallback caps qInit
        (serverSlotted setup (boundaryWire wire parse) budget
          (lorWinPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget guess filter) lorClaim g) +
      2⁻¹ * (ENNReal.ofReal (CborRawHeadlineChain.kemLoss setup wire parse checks ensureInit bounds .P adversary budget
          (lorEligPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget filter) lorClaim g runtime) +
        ENNReal.ofReal (CborRawHeadlineChain.slotLoss setup wire parse checks ensureInit bounds .P adversary budget
          (lorEligPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget filter) lorClaim g runtime) +
        recordLoss setup wire parse checks ensureInit bounds .P adversary budget g runtime fallback caps qInit
          (serverSlotted setup (boundaryWire wire parse) budget
            (lorEligPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget filter) lorClaim g)) := by
  set win := lorWinPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget guess filter
  set elig := lorEligPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget filter
  have viewW := server_view setup wire parse checks nativePhase1 phase2 ensureInit runtime bounds .P adversary budget
    win lorClaim g
  have viewE := server_view setup wire parse checks nativePhase1 phase2 ensureInit runtime bounds .P adversary budget
    elig lorClaim g
  have final := lor_server_final setup (boundaryWire wire parse) (CborRawCompile.route parse)
    (environment setup wire parse checks (Target.ofCE budget g) ensureInit runtime) bounds adversary budget g guess filter
  have chainW := CborRawHeadlineTwoSided.chain_real_close setup functional wire parse checks lengths parser nativePhase1
    ensureInit phase1 phase2 correct bounds .P adversary budget respects win lorClaim g runtime
  have chainE := CborRawHeadlineTwoSided.chain_real_close setup functional wire parse checks lengths parser nativePhase1
    ensureInit phase1 phase2 correct bounds .P adversary budget respects elig lorClaim g runtime
  have framed := CborRawHeadlineApp.frame setup wire parse checks caps bounded ensureInit qInit initBound budget g runtime
  have liftW := CborRawHeadlineRecords.random_close setup (boundaryWire wire parse) (CborRawCompile.route parse)
    (environment setup wire parse checks (Target.ofCE budget g) ensureInit runtime) (startupG caps qInit budget)
    (allowanceG (baseAllowance caps) ceFirstTouch) framed setup.serverKeyId bounds .P budget adversary respects
    (serverSlotted setup (boundaryWire wire parse) budget win lorClaim g) correct fallback
  have liftE := CborRawHeadlineRecords.random_close setup (boundaryWire wire parse) (CborRawCompile.route parse)
    (environment setup wire parse checks (Target.ofCE budget g) ensureInit runtime) (startupG caps qInit budget)
    (allowanceG (baseAllowance caps) ceFirstTouch) framed setup.serverKeyId bounds .P budget adversary respects
    (serverSlotted setup (boundaryWire wire parse) budget elig lorClaim g) correct fallback
  have bound := lor_bound_server _ _ _ _ _ _ _ _ (chance_ne_top _ _) (chance_ne_top _ _) viewW viewE final _ _ chainW
    chainE _ _ liftW liftE
  refine bound.trans ?_
  gcongr ?_ + _ + 2⁻¹ * (?_ + _) <;> exact ENNReal.ofReal_add_le

open Classical in
/-- The actual raw CE-LOR advantage is bounded by the tight accept-times-create sum of concrete per-target losses. -/
theorem ce_lor (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse))
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (nativePhase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (guess : X → Bool) (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool) :
    ENNReal.ofReal |(𝒟[(fun outcome => happens (lorWinEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget guess
          filter) outcome) <$>
        (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => happens (lorEligEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget filter)
          outcome) <$>
        (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal| ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (CborRawHeadlineChain.kemLoss setup wire parse checks ensureInit bounds .P adversary budget
            (lorWinEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget guess filter) lorClaim (g.1, g.2.castSucc)
            runtime) +
          ENNReal.ofReal (CborRawHeadlineChain.slotLoss setup wire parse checks ensureInit bounds .P adversary budget
            (lorWinEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget guess filter) lorClaim (g.1, g.2.castSucc)
            runtime) +
          recordLoss setup wire parse checks ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime fallback
            caps qInit (slotted setup (boundaryWire wire parse) budget
              (lorWinEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget guess filter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (CborRawHeadlineChain.kemLoss setup wire parse checks ensureInit bounds .P adversary budget
              (lorEligEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget filter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (CborRawHeadlineChain.slotLoss setup wire parse checks ensureInit bounds .P adversary budget
              (lorEligEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget filter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            recordLoss setup wire parse checks ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime fallback
              caps qInit (slotted setup (boundaryWire wire parse) budget
                (lorEligEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget filter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * CborRawAnomalyCca.beta setup wire parse checks (Target.ofCE budget (g.1, g.2.castSucc)) ensureInit runtime bounds .P adversary) := by
  rw [CborRawHeadlineTargets.split_named setup wire parse checks lengths parser ensureInit phase1 phase2 bounds .P adversary
      budget respects _ lorClaim runtime (lorWin_named setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget guess filter),
    CborRawHeadlineTargets.split_named setup wire parse checks lengths parser ensureInit phase1 phase2 bounds .P adversary
      budget respects _ lorClaim runtime (lorElig_named setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget filter),
    ENNReal.toReal_sum (fun _ _ => chance_ne_top _ _), ENNReal.toReal_sum (fun _ _ => chance_ne_top _ _),
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
  exact Finset.sum_le_sum fun g _ => ce_lor_target setup functional wire parse checks lengths parser ensureInit phase1 phase2 nativePhase1 correct
    caps bounded qInit initBound bounds adversary budget respects runtime fallback guess filter (g.1, g.2.castSucc)

open Classical in
/-- The actual raw CE-LOR advantage is bounded by the tight accept-times-create sum of concrete per-target losses. -/
theorem ce_lor_server (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse))
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (nativePhase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (guess : X → Bool) (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool) :
    ENNReal.ofReal |(𝒟[(fun outcome => happens (lorWinPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget guess
          filter) outcome) <$>
        (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => happens (lorEligPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget
          filter) outcome) <$>
        (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal| ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (CborRawHeadlineChain.kemLoss setup wire parse checks ensureInit bounds .P adversary budget
            (lorWinPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget guess filter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (CborRawHeadlineChain.slotLoss setup wire parse checks ensureInit bounds .P adversary budget
            (lorWinPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget guess filter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recordLoss setup wire parse checks ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime fallback
            caps qInit (serverSlotted setup (boundaryWire wire parse) budget
              (lorWinPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget guess filter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (CborRawHeadlineChain.kemLoss setup wire parse checks ensureInit bounds .P adversary budget
              (lorEligPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget filter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            ENNReal.ofReal (CborRawHeadlineChain.slotLoss setup wire parse checks ensureInit bounds .P adversary budget
              (lorEligPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget filter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recordLoss setup wire parse checks ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime fallback
              caps qInit (serverSlotted setup (boundaryWire wire parse) budget
                (lorEligPeerEvent setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget filter) lorClaim
                (g.1, g.2.castSucc)))) := by
  rw [CborRawHeadlineTargets.split_named setup wire parse checks lengths parser ensureInit phase1 phase2 bounds .P adversary
      budget respects _ lorClaim runtime
      (lorWinPeer_named setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget guess filter),
    CborRawHeadlineTargets.split_named setup wire parse checks lengths parser ensureInit phase1 phase2 bounds .P adversary
      budget respects _ lorClaim runtime (lorEligPeer_named setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget filter),
    ENNReal.toReal_sum (fun _ _ => chance_ne_top _ _), ENNReal.toReal_sum (fun _ _ => chance_ne_top _ _),
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
  exact Finset.sum_le_sum fun g _ => ce_lor_server_target setup functional wire parse checks lengths parser ensureInit phase1 phase2
    nativePhase1 correct caps bounded qInit initBound bounds adversary budget respects runtime fallback guess filter
    (g.1, g.2.castSucc)

end BeaconcryptCore.Computational.CborRawHeadlineLorSecurity

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineLorSecurity.lor_server_final' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineLorSecurity.lor_server_final

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineLorSecurity.unslotted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineLorSecurity.unslotted

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineLorSecurity.server_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineLorSecurity.server_view

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineLorSecurity.ce_lor_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineLorSecurity.ce_lor_target

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineLorSecurity.ce_lor_server_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineLorSecurity.ce_lor_server_target

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineLorSecurity.ce_lor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineLorSecurity.ce_lor

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineLorSecurity.ce_lor_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineLorSecurity.ce_lor_server
