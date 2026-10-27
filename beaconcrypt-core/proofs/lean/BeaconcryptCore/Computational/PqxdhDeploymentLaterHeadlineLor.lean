-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor
import BeaconcryptCore.Computational.PqxdhRecordFactsLaterLor

/-!
# CE-LOR-L: later-quantum left-or-right secrecy of the single test session (CE-12 P3, design.md section 9.1)

The headline CE-LOR-L in observation mode P (VC rows passive-quantum 173 and the later forms of SSX-b2s, SSX-s2b, SS-b2s, SS-s2b, design-v2 section 12), for the LQ-F game (`PqxdhDeploymentLaterServerGame.game`), for every public filter `F` on the mode-P transcript view of the run phase:

- Eligibility (`PqxdhDeploymentHeadlineEvents.LorElig` at the post output type): a test session exists, `F` holds, and every admitted test entry's handle designates the target of the first admitted test entry (`PqxdhRecordLiftIdeal.firstTest`, the claim). The win (`LorWin`) adds that the guess read from the post adversary's output, produced after the post-run reveal of the Server seed, the ephemeral log and every Beacon secret of the profile, equals the test bit.
- `ce_lor_later`: the advantage `|Pr_LQF[win] - ½ Pr_LQF[eligible]|` is at most the sum over the targets `g` in `Fin qAccept × Fin qCreate`, each with coefficient one, of `kemLossL + slotLossL + recLossL(dec_g(W) ∧ IS_g)` of the win, half of the same terms of the eligibility, and `½ β_g` of the run-phase adversary `first`; two transfers per target, one per event. `ce_lor_later_target` is the per-target form.
- `ce_lor_server_later` and `ce_lor_server_later_target`: the same for Server-side tests (`PeerTests`), with `ServerSlots` and no `β_g`.

Proof per target, as for CE-LOR (`PqxdhDeploymentHeadlineLor`): both events go two-sidedly along C1-C5 (`PqxdhDeploymentLaterHeadlineChain.chain_close_later`); on the view of the all-real later chain world the slot differences are combined before splitting (`PqxdhDeploymentHeadlineLor.chance_split`, `PqxdhDeploymentLaterHeadlineChain.later_view_unslotted`, `PqxdhDeploymentHeadlineAnomaly.anomaly_beta` on `first`'s run, `lor_bound`); both slotted events go two-sidedly through the later record lift (`records_close_later`); and in `laterIdealRecords` the slotted win has exactly half the probability of the slotted eligibility (`lor_final_later`): `dec_g(E) ∧ IS_g` depends on a view only through the public hiding projection (`decided_view`), implies `TestsHidden` (`PqxdhDeploymentHeadlineContain.lor_hidden`), and the win is the eligibility with the test bit equal to the projected guess (`win_slotted`), so `PqxdhRecordFactsLaterLor.later_idealRecords_lor` applies with the public eligibility `hidingOf` and the projected guess `decisionHiding`. The public hiding projection contains the post adversary's output and the environment state after the post phase, and excludes the test bit.

Premises: `FunctionalDecapsulation setup.kem`, `Phase1ReadBack`, `Phase2ReadBack`, `SourceFullCorrect setup.source setup.hmac`, `KemBound setup caps`, the total query bound `qInit` of the runtime initializer, `budget.Respects first` and the post budget of `second` on every input; the AEAD forgery fallback is a parameter of the integrity loss. Later mode claims confidentiality only: no origin, binding or authentication statement, no theorem A2, T5 or T8 on the later compiled program. No new assumption or contract.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineLor
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

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Out : Type}

/-! ### The final world -/

/-- C8 for CE-LOR-L: on the record lift's view of `laterIdealRecords` (mode P) with the ideal environment of the target of `g`, the environment's reveal and the post adversary, the win with `IdealSlots` has exactly half the probability of the eligibility with `IdealSlots` (`PqxdhRecordFactsLaterLor.later_idealRecords_lor` with the projected guess and the public eligibility of `dec_g(E) ∧ IS_g`, which factors through the public hiding projection and implies `TestsHidden`). -/
theorem lor_final_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) (guess : Out → Bool)
    (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool) :
    𝒟[slotted setup codec budget (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter)
        lorClaim g <$> (ctxView <$> laterIdealRecords setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds .P envReveal first second)] {true} =
      2⁻¹ * 𝒟[slotted setup codec budget (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter)
        lorClaim g <$> (ctxView <$> laterIdealRecords setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds .P envReveal first second)] {true} := by
  have invariant : ∀ view view' : View 2 (EnvG KemSK budget) Out, publicHiding view = publicHiding view' →
      slotted setup codec budget (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g
        view =
      slotted setup codec budget (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g
        view' := fun view view' same =>
    PqxdhDeploymentHeadlineLor.decided_view setup codec budget _ lorClaim g
      (fun transcript slots => IdealSlots setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) slots
        transcript)
      (PqxdhDeploymentHeadlineLor.lorEligEvent_view setup.source.crypto codec setup.serverKeyId budget filter)
      (PqxdhDeploymentHeadlineLor.lorClaim_view setup.source.crypto codec setup.serverKeyId budget)
      (fun first second slots same => PqxdhDeploymentHeadlineLor.idealSlots_view setup.source.crypto codec
        setup.serverKeyId _ slots first second same) view view' same
  have hidden : ∀ view : View 2 (EnvG KemSK budget) Out,
      slotted setup codec budget (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g
        view = true → PqxdhRecordLiftIdeal.TestsHidden setup.source.crypto codec setup.serverKeyId view :=
    fun view held => PqxdhDeploymentHeadlineContain.lor_hidden setup codec budget filter g view held
  have win : slotted (E := EnvG KemSK budget) setup codec budget
      (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim g =
      fun view => PqxdhRecordLiftIdeal.lorGuess setup.source.crypto codec setup.serverKeyId (decisionHiding guess)
        (hidingOf (slotted setup codec budget (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter)
          lorClaim g)) view := funext fun view => by
    rw [PqxdhDeploymentHeadlineLor.guess_hiding setup codec guess _ invariant hidden view,
      PqxdhDeploymentHeadlineLor.win_slotted]
  have eligible : slotted (E := EnvG KemSK budget) setup codec budget
      (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g =
      fun view => PqxdhRecordLiftIdeal.lorEligible setup.source.crypto codec setup.serverKeyId
        (hidingOf (slotted setup codec budget (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter)
          lorClaim g)) view :=
    funext fun view => (PqxdhDeploymentHeadlineLor.eligible_hiding setup codec _ invariant hidden view).symm
  conv_lhs => rw [win, Functor.map_map]
  conv_rhs => rw [eligible, Functor.map_map]
  exact PqxdhRecordFactsLaterLor.later_idealRecords_lor setup codec route setup.serverKeyId bounds 2 _ envReveal first
    second (decisionHiding guess) _

/-- C8 for the Server-side CE-LOR-L: on the record lift's view of `laterIdealRecords` (mode P) with the ideal environment of the target of `g`, the Server-side win with `ServerSlots` has exactly half the probability of the Server-side eligibility with `ServerSlots`. -/
theorem lor_peer_final_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) (guess : Out → Bool)
    (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool) :
    𝒟[serverSlotted setup codec budget (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess filter)
        lorClaim g <$> (ctxView <$> laterIdealRecords setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds .P envReveal first second)] {true} =
      2⁻¹ * 𝒟[serverSlotted setup codec budget
        (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g <$>
          (ctxView <$> laterIdealRecords setup codec route
            (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
            setup.serverKeyId bounds .P envReveal first second)] {true} := by
  have invariant : ∀ view view' : View 2 (EnvG KemSK budget) Out, publicHiding view = publicHiding view' →
      serverSlotted setup codec budget (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter)
        lorClaim g view =
      serverSlotted setup codec budget (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter)
        lorClaim g view' := fun view view' same =>
    PqxdhDeploymentHeadlineLor.decided_view setup codec budget _ lorClaim g
      (fun transcript slots => ServerSlots setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) slots
        transcript)
      (PqxdhDeploymentHeadlineLor.lorEligPeerEvent_view setup.source.crypto codec setup.serverKeyId budget filter)
      (PqxdhDeploymentHeadlineLor.lorClaim_view setup.source.crypto codec setup.serverKeyId budget)
      (fun first second slots same => PqxdhDeploymentHeadlineLor.serverSlots_view setup.source.crypto codec
        setup.serverKeyId _ slots first second same) view view' same
  have hidden : ∀ view : View 2 (EnvG KemSK budget) Out,
      serverSlotted setup codec budget (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter)
        lorClaim g view = true → PqxdhRecordLiftIdeal.TestsHidden setup.source.crypto codec setup.serverKeyId view :=
    fun view held => PqxdhDeploymentHeadlineContain.lor_peer_hidden setup codec budget filter g view held
  have win : serverSlotted (E := EnvG KemSK budget) setup codec budget
      (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim g =
      fun view => PqxdhRecordLiftIdeal.lorGuess setup.source.crypto codec setup.serverKeyId (decisionHiding guess)
        (hidingOf (serverSlotted setup codec budget
          (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g)) view :=
    funext fun view => by
      rw [PqxdhDeploymentHeadlineLor.guess_hiding setup codec guess _ invariant hidden view,
        PqxdhDeploymentHeadlineLor.win_peer_slotted]
  have eligible : serverSlotted (E := EnvG KemSK budget) setup codec budget
      (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g =
      fun view => PqxdhRecordLiftIdeal.lorEligible setup.source.crypto codec setup.serverKeyId
        (hidingOf (serverSlotted setup codec budget
          (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g)) view :=
    funext fun view => (PqxdhDeploymentHeadlineLor.eligible_hiding setup codec _ invariant hidden view).symm
  conv_lhs => rw [win, Functor.map_map]
  conv_rhs => rw [eligible, Functor.map_map]
  exact PqxdhRecordFactsLaterLor.later_idealRecords_lor setup codec route setup.serverKeyId bounds 2 _ envReveal first
    second (decisionHiding guess) _

/-! ### CE-LOR-L -/

open Classical in
/-- On the view of the all-real later chain world with the ideal environment of a target, under `Phase1ReadBack`, a per-target decision has the probability of the decision with `ServerSlots` (`PqxdhDeploymentLaterHeadlineChain.later_real_slots_server`). -/
theorem server_view_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[(fun view => (viewObserved view).any (decisionOn setup codec budget event claim g)) <$>
        (chainView <$> laterRealChains setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode envReveal first second)] {true} =
      𝒟[serverSlotted setup codec budget event claim g <$>
        (chainView <$> laterRealChains setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode envReveal first second)] {true} := by
  congr 2
  rw [Functor.map_map, Functor.map_map]
  refine PqxdhDeploymentKemTransfer.map_support_congr _ _ _ fun result member => ?_
  simp only [serverSlotted]
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact ⟨fun held => ⟨held, PqxdhDeploymentLaterHeadlineChain.later_real_slots_server setup codec checks route phase1
    (Target.ofCE budget g) ensureInit 0 runtime bounds mode envReveal first second result member⟩, And.left⟩

open Classical in
/-- **CE-LOR-L, per target**: in mode P, for the target `g`, the left-or-right advantage of the LQ-F game at `g` (the probability of the win, with the guess read from the post adversary's output, and the first admitted test designating `g`, minus half the probability of the eligibility with the same designation) is at most `kemLossL + slotLossL + recLossL(dec_g(W) ∧ IS_g)` of the win, plus half of `kemLossL + slotLossL + recLossL(dec_g(E) ∧ IS_g)` of the eligibility, plus `½ β_g` of the run-phase adversary `first`. -/
theorem ce_lor_later_target (setup : Setup baseSpec KemSK)
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
    ENNReal.ofReal |(𝒟[(fun outcome => decide (happens (lorWinEvent setup.source.crypto codec setup.serverKeyId budget
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
      2⁻¹ * beta setup codec route checks ensureInit bounds .P first budget g runtime := by
  set realView := chainView <$> laterRealChains setup codec route
    (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
    setup.serverKeyId bounds .P envReveal first second with hrealView
  set win := lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter with hwin
  set elig := lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter with helig
  set ideal : View 2 (EnvG KemSK budget) Out → Prop := fun view => ∀ value, view.result = some value →
    IdealSlots setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) view.slots value.2.1.transcript
    with hideal
  have winElig : ∀ view : View 2 (EnvG KemSK budget) Out,
      (viewObserved view).any (decisionOn setup codec budget win lorClaim g) = true →
        (viewObserved view).any (decisionOn setup codec budget elig lorClaim g) = true := by
    intro view held
    rcases view with ⟨_ | value, produced, raw, slots⟩
    · simp [viewObserved] at held
    · simp only [viewObserved, Option.map_some, Option.any_some, decisionOn, Bool.and_eq_true] at held ⊢
      exact ⟨((PqxdhDeploymentHeadlineLor.lorWin_iff setup codec budget guess filter _).mp held.1).1, held.2⟩
  have splitW := PqxdhDeploymentHeadlineLor.chance_split realView
    (fun view => (viewObserved view).any (decisionOn setup codec budget win lorClaim g)) ideal
  have splitE := PqxdhDeploymentHeadlineLor.chance_split realView (fun view => (viewObserved view).any
    (decisionOn setup codec budget elig lorClaim g)) ideal
  have below := PqxdhDeploymentHeadlineContain.chance_mono realView
    (fun view => decide ((viewObserved view).any (decisionOn setup codec budget win lorClaim g) = true ∧ ¬ideal view))
    (fun view => decide ((viewObserved view).any (decisionOn setup codec budget elig lorClaim g) = true ∧ ¬ideal view))
    (fun view held => by
      rw [decide_eq_true_iff] at held ⊢
      exact ⟨winElig view held.1, held.2⟩)
  have anomaly := (PqxdhDeploymentLaterHeadlineChain.later_view_unslotted setup codec checks route phase1 phase2
    (Target.ofCE budget g) ensureInit 0 runtime bounds .P envReveal first second
    (fun view => (viewObserved view).any (decisionOn setup codec budget elig lorClaim g))).trans
      (PqxdhDeploymentHeadlineAnomaly.anomaly_beta setup functional codec checks route ensureInit phase1 phase2 bounds .P
        first budget g runtime)
  have final := lor_final_later setup codec checks route ensureInit bounds first second budget g runtime guess filter
  have chainW := PqxdhDeploymentLaterHeadlineChain.chain_close_later (Reader := Reader) setup functional codec checks
    route ensureInit phase1 phase2 correct bounds .P first second budget respects post postRespects win lorClaim g
    runtime
  have chainE := PqxdhDeploymentLaterHeadlineChain.chain_close_later (Reader := Reader) setup functional codec checks
    route ensureInit phase1 phase2 correct bounds .P first second budget respects post postRespects elig lorClaim g
    runtime
  have liftW := PqxdhDeploymentLaterHeadlineChain.records_close_later setup codec checks route correct caps bounded
    ensureInit qInit initBound bounds .P first second budget respects post postRespects g runtime fallback
    (slotted setup codec budget win lorClaim g)
  have liftE := PqxdhDeploymentLaterHeadlineChain.records_close_later setup codec checks route correct caps bounded
    ensureInit qInit initBound bounds .P first second budget respects post postRespects g runtime fallback
    (slotted setup codec budget elig lorClaim g)
  have bound := PqxdhDeploymentHeadlineLor.lor_bound _ _ _ _ _ _ _ _ _ _ (chance_ne_top _ _) (chance_ne_top _ _)
    (chance_ne_top _ _) (chance_ne_top _ _) splitW splitE final below _ _ chainW chainE _ _ liftW liftE _ anomaly
  refine bound.trans ?_
  gcongr ?_ + _ + 2⁻¹ * (?_ + _) + _ <;> exact ENNReal.ofReal_add_le

open Classical in
/-- **CE-LOR-L** (design.md section 9.1): in mode P, for every public filter `F` on the mode-P transcript view, the left-or-right advantage of the LQ-F game, the probability that the guess read from the post adversary's output equals the test bit with eligibility minus half the probability of eligibility, is at most the sum over `g` in `Fin qAccept × Fin qCreate` of the per-target bound of `ce_lor_later_target`, each with coefficient one. -/
theorem ce_lor_later (setup : Setup baseSpec KemSK)
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
    ENNReal.ofReal |(𝒟[(fun outcome => happens (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess
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
          2⁻¹ * beta setup codec route checks ensureInit bounds .P first budget (g.1, g.2.castSucc) runtime) := by
  rw [PqxdhDeploymentLaterHeadlineChain.split_named_later setup codec checks route ensureInit phase1 phase2 bounds .P
      first second budget respects _ lorClaim runtime
      (PqxdhDeploymentHeadlineLor.lorWin_named setup.source.crypto codec setup.serverKeyId budget guess filter),
    PqxdhDeploymentLaterHeadlineChain.split_named_later setup codec checks route ensureInit phase1 phase2 bounds .P
      first second budget respects _ lorClaim runtime
      (PqxdhDeploymentHeadlineLor.lorElig_named setup.source.crypto codec setup.serverKeyId budget filter),
    ENNReal.toReal_sum (fun _ _ => chance_ne_top _ _), ENNReal.toReal_sum (fun _ _ => chance_ne_top _ _),
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
  exact Finset.sum_le_sum fun g _ => ce_lor_later_target setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound bounds first second budget respects post postRespects runtime fallback guess
    filter (g.1, g.2.castSucc)

open Classical in
/-- **CE-LOR-L on Server peers, per target**: the per-target bound of `ce_lor_later_target` for the Server-side events (every admitted test handle a Server peer), with `ServerSlots` and no anomaly term. -/
theorem ce_lor_server_later_target (setup : Setup baseSpec KemSK)
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
    ENNReal.ofReal |(𝒟[(fun outcome => decide (happens (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId
          budget guess filter) outcome = true ∧
          designated setup.source.crypto codec setup.serverKeyId budget lorClaim outcome = some g)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
          runtime] {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => decide (happens (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId
          budget filter) outcome = true ∧
          designated setup.source.crypto codec setup.serverKeyId budget lorClaim outcome = some g)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
          runtime] {true}).toReal| ≤
      ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
        (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim g runtime) +
      ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second budget post
        (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim g runtime) +
      recLossL setup codec checks route ensureInit bounds .P first second budget post g runtime fallback caps qInit
        (serverSlotted setup codec budget
          (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim g) +
      2⁻¹ * (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
          (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g runtime) +
        ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second budget
          post (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g runtime) +
        recLossL setup codec checks route ensureInit bounds .P first second budget post g runtime fallback caps qInit
          (serverSlotted setup codec budget
            (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g)) := by
  have viewW := server_view_later setup codec checks route phase1 ensureInit bounds .P first second budget
    (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim g runtime
  have viewE := server_view_later setup codec checks route phase1 ensureInit bounds .P first second budget
    (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g runtime
  have final := lor_peer_final_later setup codec checks route ensureInit bounds first second budget g runtime guess
    filter
  have chainW := PqxdhDeploymentLaterHeadlineChain.chain_close_later (Reader := Reader) setup functional codec checks
    route ensureInit phase1 phase2 correct bounds .P first second budget respects post postRespects
    (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim g runtime
  have chainE := PqxdhDeploymentLaterHeadlineChain.chain_close_later (Reader := Reader) setup functional codec checks
    route ensureInit phase1 phase2 correct bounds .P first second budget respects post postRespects
    (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g runtime
  have liftW := PqxdhDeploymentLaterHeadlineChain.records_close_later setup codec checks route correct caps bounded
    ensureInit qInit initBound bounds .P first second budget respects post postRespects g runtime fallback
    (serverSlotted setup codec budget
      (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim g)
  have liftE := PqxdhDeploymentLaterHeadlineChain.records_close_later setup codec checks route correct caps bounded
    ensureInit qInit initBound bounds .P first second budget respects post postRespects g runtime fallback
    (serverSlotted setup codec budget
      (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g)
  have bound := PqxdhDeploymentHeadlineLor.lor_bound_server _ _ _ _ _ _ _ _ (chance_ne_top _ _) (chance_ne_top _ _)
    viewW viewE final _ _ chainW chainE _ _ liftW liftE
  refine bound.trans ?_
  gcongr ?_ + _ + 2⁻¹ * (?_ + _) <;> exact ENNReal.ofReal_add_le

open Classical in
/-- **CE-LOR-L on Server peers**: `ce_lor_later` for the Server-side events (every admitted test handle a Server peer, `PeerTests`), with `ServerSlots` and no anomaly term: the sum over `g` in `Fin qAccept × Fin qCreate` of the bound of `ce_lor_server_later_target`, each with coefficient one. -/
theorem ce_lor_server_later (setup : Setup baseSpec KemSK)
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
    ENNReal.ofReal |(𝒟[(fun outcome => happens (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess
          filter) outcome) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
          runtime] {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => happens (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget
          filter) outcome) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
          runtime] {true}).toReal| ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
            (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second budget
            post (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc) runtime
            fallback caps qInit (serverSlotted setup codec budget
              (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
              (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second
              budget post (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc) runtime
              fallback caps qInit (serverSlotted setup codec budget
                (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim
                (g.1, g.2.castSucc)))) := by
  rw [PqxdhDeploymentLaterHeadlineChain.split_named_later setup codec checks route ensureInit phase1 phase2 bounds .P
      first second budget respects _ lorClaim runtime
      (PqxdhDeploymentHeadlineLor.lorWinPeer_named setup.source.crypto codec setup.serverKeyId budget guess filter),
    PqxdhDeploymentLaterHeadlineChain.split_named_later setup codec checks route ensureInit phase1 phase2 bounds .P
      first second budget respects _ lorClaim runtime
      (PqxdhDeploymentHeadlineLor.lorEligPeer_named setup.source.crypto codec setup.serverKeyId budget filter),
    ENNReal.toReal_sum (fun _ _ => chance_ne_top _ _), ENNReal.toReal_sum (fun _ _ => chance_ne_top _ _),
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
  exact Finset.sum_le_sum fun g _ => ce_lor_server_later_target setup functional codec checks route ensureInit phase1
    phase2 correct caps bounded qInit initBound bounds first second budget respects post postRespects runtime fallback
    guess filter (g.1, g.2.castSucc)

end BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineLor

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineLor.lor_final_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineLor.lor_final_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineLor.lor_peer_final_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineLor.lor_peer_final_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineLor.server_view_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineLor.server_view_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineLor.ce_lor_later_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineLor.ce_lor_later_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineLor.ce_lor_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineLor.ce_lor_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineLor.ce_lor_server_later_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineLor.ce_lor_server_later_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineLor.ce_lor_server_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineLor.ce_lor_server_later
