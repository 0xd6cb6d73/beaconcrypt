-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxModeBounds
import BeaconcryptCore.Computational.PqxdhComposition

/-!
# Record-lift CTX integrity half: the hybrid telescope (items 4 and 5, stage S4, X3)

**The reduction family.** `ctxReduction` is the explicit CTX reduction family of `PqxdhRecordLiftIdeal.CtxAuthLiftStatement`: hop `step`'s ordinary one-key CTX adversary is `PqxdhRecordLiftCtxModes.decisionClient` of the step client `stepClient`, the key-free link client of `PqxdhRecordLiftCtxLink` for the step's coordinate `PqxdhRecordLiftChainOrder.entryAt step` under the modes of the hybrid before the step.

**The hops.** `game cut` is the hybrid `cut` of `PqxdhRecordLiftCtxHybrid` under a decision on the view. By the selected-key law (`PqxdhRecordLiftKeyCut.key_cut_measure`) and the link, the hybrid before step `step` has the law of the challenger's real game and the hybrid after it the law of its replay game against the step client (`game_real`, `game_replay`), so `PqxdhRecordLiftCtxModeBounds.selected_integrity` bounds every hop by the step's `integrityLoss` (`hop_bound`). The first hybrid is `idealChains` (`PqxdhRecordLiftCtxHybrid.allReal_decision`) and the last is `idealAuth` (`PqxdhRecordLiftCtxAvailability.hybrid_last`); `PqxdhComposition.finiteHybridBound_of_hop_bounds` telescopes the hops with coefficient one, the factor 2 on INT-CTXT staying inside each `integrityLoss`.

**Statement.** `ctxAuthLiftBool_of_billed` proves the Boolean form `CtxAuthLiftBool` for `ctxReduction`, every bill record and every refusal term, and `ctxAuthLiftTarget_of_billed` the zero-refusal target `CtxAuthLiftTarget` (both forms, through `ctxAuthLiftStatement_of_bool`), from `StepBilled bills`: every step client stays within the bills' uniform, shared-hash, seal (below `2^96`) and raw caps. `StepBilled` is a property of the explicit construction, not an assumption or contract; `PqxdhRecordLiftCtxBills` proves it for the explicit bills `ctxBills` (X4).

**Contracts.** No theorem of this module has an assumption or contract hypothesis: the premises of `hop_bound`, `ctxAuthLiftBool_of_billed` and `ctxAuthLiftTarget_of_billed` (the adversary's budget, the step client's query bounds, `StepBilled bills`) are budget facts and properties of the construction. From the brief's H-7 list these three theorems use: functional AEAD correctness, that is the fields `aead_open_seal` (reached through `PqxdhRecordLiftCtxModeBounds.selected_integrity`, whose replay coupling maintains the invariant `AdaptiveRawNonceAead.HistoryCorrect` with it) and `aeadSeal_tag_length` (16-byte tags) of the primitive record `Pqxdh.Crypto`; the modified-nonce AEAD IND$ and INT-CTXT games, only as the advantage terms of `integrityLoss`; and the BLAKE2b random-oracle model as the world model, within which the terms `qHash / 2^128` and `qRaw / 2^512` of `integrityLoss` are stated. `game_real`, `game_replay` and `advantage_congr` use no contract. New Claude work; nothing adapted from Codex WIP.
-/

open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftCtx
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftCtxHybrid PqxdhRecordLiftCtxLink
open PqxdhRecordLiftCtxAvailability PqxdhRecordLiftKeyCut
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds Budget)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftCtxModeBounds (UniformRoute PrivateRoute HashRoute TargetClass)
open AdaptiveCtxQueryBounds (SourceSeal)
open CtxRomAuth AdaptiveCtxReceive
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

section Hops
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (serverKid : Std.U64) (bounds : FreshBounds)

/-- The one-key adversary of hybrid step `step`, against the dynamic known-key challenger: the key-free link client of the step's coordinate under the modes before the step. -/
noncomputable def stepClient (env : Environment n E) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (decision : View n E X → ProbComp Bool) (budget : Budget) (step : Fin (hops n budget)) :
    OracleComp PqxdhRecordLiftCtxModes.Spec Bool :=
  linkClient (PqxdhRecordLiftChainOrder.entryAt (positions := positions budget) step)
    (hybridModes (positions budget) step.val) setup codec route env serverKid bounds mode adversary decision

/-- The explicit CTX reduction family: hop `step`'s ordinary one-key CTX adversary is its step client with the known-key work run inside (`PqxdhRecordLiftCtxModes.decisionClient`). -/
noncomputable def ctxReduction : CtxReduction n := fun env mode adversary decision budget step =>
  PqxdhRecordLiftCtxModes.decisionClient setup.source.crypto
    (stepClient setup codec route serverKid bounds env mode adversary decision budget step)

/-- The game of hybrid `cut` under a decision on the view. -/
noncomputable def game (env : Environment n E) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (decision : View n E X → ProbComp Bool) (budget : Budget) (cut : Nat) : ProbComp Bool :=
  ctxRun (hybridModes (positions budget) cut) id setup codec route env serverKid bounds mode adversary >>= fun result =>
    decision (ctxView result)

/-- The hybrid before step `step` has the law of the challenger's real game against the step client. -/
theorem game_real (env : Environment n E) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (decision : View n E X → ProbComp Bool) (budget : Budget) (respects : budget.Respects adversary)
    (step : Fin (hops n budget)) :
    𝒟[game setup codec route serverKid bounds env mode adversary decision budget step.val] =
      𝒟[Prod.fst <$> PqxdhRecordLiftCtxModes.sourceGame true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto (stepClient setup codec route serverKid bounds env mode adversary decision budget step)] := by
  rw [stepClient, link _ (hybridModes (positions budget) step.val) (fun label _ => hybridModes_notRandom _ _ label),
    selectedModes_hybrid_real (n := n) (positions budget) step]
  exact key_cut_measure _ _ id setup codec route env serverKid bounds mode adversary budget respects decision

/-- The hybrid after step `step` has the law of the challenger's replay game against the step client. -/
theorem game_replay (env : Environment n E) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (decision : View n E X → ProbComp Bool) (budget : Budget) (respects : budget.Respects adversary)
    (step : Fin (hops n budget)) :
    𝒟[game setup codec route serverKid bounds env mode adversary decision budget (step.val + 1)] =
      𝒟[Prod.fst <$> PqxdhRecordLiftCtxModes.sourceGame false (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto (stepClient setup codec route serverKid bounds env mode adversary decision budget step)] := by
  rw [stepClient, link _ (hybridModes (positions budget) step.val) (fun label _ => hybridModes_notRandom _ _ label),
    selectedModes_hybrid_replay (n := n) (positions budget) step]
  exact key_cut_measure _ _ id setup codec route env serverKid bounds mode adversary budget respects decision

/-- Equal laws give equal distinguishing advantages. -/
theorem advantage_congr (left right left' right' : ProbComp Bool) (sameLeft : 𝒟[left] = 𝒟[left'])
    (sameRight : 𝒟[right] = 𝒟[right']) : left.boolDistAdvantage right = left'.boolDistAdvantage right' := by
  unfold ProbComp.boolDistAdvantage
  rw [sameLeft, sameRight]

/-- **One hop.** The hybrids before and after step `step` differ by at most the step's integrity loss, at every hash and raw cap of its step client and every seal cap below `2^96`. -/
theorem hop_bound (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (env : Environment n E) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (decision : View n E X → ProbComp Bool) (budget : Budget)
    (respects : budget.Respects adversary) (step : Fin (hops n budget)) (qHash qSeal qRaw : Nat)
    (hashBound : (stepClient setup codec route serverKid bounds env mode adversary decision budget step).IsQueryBoundP
      HashRoute qHash)
    (sealBound : (stepClient setup codec route serverKid bounds env mode adversary decision budget step).IsQueryBoundP
      (TargetClass SourceSeal) qSeal)
    (rawBound : (stepClient setup codec route serverKid bounds env mode adversary decision budget step).IsQueryBoundP
      (TargetClass IsRawQuery) qRaw)
    (small : qSeal < 2 ^ 96) :
    ENNReal.ofReal ((game setup codec route serverKid bounds env mode adversary decision budget step.val).boolDistAdvantage
      (game setup codec route serverKid bounds env mode adversary decision budget (step.val + 1))) ≤
      integrityLoss (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto fallback
        (ctxReduction setup codec route serverKid bounds env mode adversary decision budget step) qHash qRaw := by
  rw [advantage_congr _ _ _ _ (game_real setup codec route serverKid bounds env mode adversary decision budget respects step)
    (game_replay setup codec route serverKid bounds env mode adversary decision budget respects step)]
  exact PqxdhRecordLiftCtxModeBounds.selected_integrity _ _ fallback _ qHash qSeal qRaw hashBound sealBound rawBound small

end Hops

section Statement
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (serverKid : Std.U64) (bounds : FreshBounds)

/-- The step clients respect `bills`: for every environment with `Frame`, adversary within its budget and decision with its coin cost, the step client of every hop makes at most `bills.uniform` coin-equivalent random requests (a private 64-byte cache fill counting 64), `bills.hash` shared-hash requests, `bills.seals` selected seals (below `2^96`) and `bills.raw` selected raw requests. -/
def StepBilled (bills : CtxBills) : Prop :=
  ∀ {E X : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget), budget.Respects adversary →
  ∀ (decision : View n E X → ProbComp Bool) (cost : Nat), (∀ view, (decision view).IsTotalQueryBound cost) →
  ∀ step : Fin (hops n budget),
    (∃ qUniform qPrivate, qUniform + 64 * qPrivate ≤ bills.uniform ⟨budget, startup, allowance, bounds, n, cost⟩ ∧
      (stepClient setup codec route serverKid bounds env mode adversary decision budget step).IsQueryBoundP
        UniformRoute qUniform ∧
      (stepClient setup codec route serverKid bounds env mode adversary decision budget step).IsQueryBoundP
        PrivateRoute qPrivate) ∧
    (stepClient setup codec route serverKid bounds env mode adversary decision budget step).IsQueryBoundP
      HashRoute (bills.hash ⟨budget, startup, allowance, bounds, n, cost⟩) ∧
    (stepClient setup codec route serverKid bounds env mode adversary decision budget step).IsQueryBoundP
      (TargetClass SourceSeal) (bills.seals ⟨budget, startup, allowance, bounds, n, cost⟩) ∧
    bills.seals ⟨budget, startup, allowance, bounds, n, cost⟩ < 2 ^ 96 ∧
    (stepClient setup codec route serverKid bounds env mode adversary decision budget step).IsQueryBoundP
      (TargetClass IsRawQuery) (bills.raw ⟨budget, startup, allowance, bounds, n, cost⟩)

/-- **`ctx_lift`, integrity half, from the step bills.** With the explicit reduction family `ctxReduction`, the Boolean form holds for every refusal term as soon as the step clients respect the bills. -/
theorem ctxAuthLiftBool_of_billed (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (bills : CtxBills)
    (refusal : BillInput → ℝ≥0∞) (billed : StepBilled (n := n) setup codec route serverKid bounds bills) :
    CtxAuthLiftBool setup codec route serverKid bounds n fallback (ctxReduction setup codec route serverKid bounds)
      bills refusal := by
  intro E X env startup allowance frame mode adversary budget respects decision cost costBound
  have stepBills := fun step : Fin (hops n budget) =>
    billed env startup allowance frame mode adversary budget respects decision cost costBound step
  refine ⟨?_, fun step => ?_⟩
  · have first : (idealChains setup codec route env serverKid bounds mode adversary >>= fun result =>
        decision (chainView result)) = game setup codec route serverKid bounds env mode adversary decision budget 0 := by
      unfold game
      rw [hybridModes_zero, allReal_decision]
    have last : (idealAuth setup codec route env serverKid bounds mode adversary >>= fun result =>
        decision (ctxView result)) =
        game setup codec route serverKid bounds env mode adversary decision budget (hops n budget) := by
      rw [← hybrid_last setup codec route env serverKid bounds mode adversary budget respects]
      rfl
    rw [first, last]
    have telescope := PqxdhComposition.finiteHybridBound_of_hop_bounds
      (game setup codec route serverKid bounds env mode adversary decision budget) (hops n budget)
      (fun cut => (game setup codec route serverKid bounds env mode adversary decision budget cut).boolDistAdvantage
        (game setup codec route serverKid bounds env mode adversary decision budget (cut + 1))) (fun _ _ => le_refl _)
    calc ENNReal.ofReal ((game setup codec route serverKid bounds env mode adversary decision budget 0).boolDistAdvantage
          (game setup codec route serverKid bounds env mode adversary decision budget (hops n budget)))
        ≤ ENNReal.ofReal (∑ cut ∈ Finset.range (hops n budget),
            (game setup codec route serverKid bounds env mode adversary decision budget cut).boolDistAdvantage
              (game setup codec route serverKid bounds env mode adversary decision budget (cut + 1))) :=
          ENNReal.ofReal_le_ofReal telescope
      _ = ∑ cut ∈ Finset.range (hops n budget), ENNReal.ofReal
            ((game setup codec route serverKid bounds env mode adversary decision budget cut).boolDistAdvantage
              (game setup codec route serverKid bounds env mode adversary decision budget (cut + 1))) :=
          ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)
      _ = ∑ step : Fin (hops n budget), ENNReal.ofReal
            ((game setup codec route serverKid bounds env mode adversary decision budget step.val).boolDistAdvantage
              (game setup codec route serverKid bounds env mode adversary decision budget (step.val + 1))) :=
          (Fin.sum_univ_eq_sum_range (fun cut => ENNReal.ofReal
            ((game setup codec route serverKid bounds env mode adversary decision budget cut).boolDistAdvantage
              (game setup codec route serverKid bounds env mode adversary decision budget (cut + 1)))) _).symm
      _ ≤ ∑ step : Fin (hops n budget), integrityLoss (RawCtxUniversalDecoder.decoder codec.frameRead)
            setup.source.crypto fallback
            (ctxReduction setup codec route serverKid bounds env mode adversary decision budget step)
            (bills.hash ⟨budget, startup, allowance, bounds, n, cost⟩)
            (bills.raw ⟨budget, startup, allowance, bounds, n, cost⟩) :=
          Finset.sum_le_sum (fun step _ => hop_bound setup codec route serverKid bounds fallback env mode adversary
            decision budget respects step _ _ _ (stepBills step).2.1 (stepBills step).2.2.1 (stepBills step).2.2.2.2
            (stepBills step).2.2.2.1)
      _ ≤ _ := le_self_add
  · obtain ⟨⟨qUniform, qPrivate, cap, uniformBound, privateBound⟩, hashBound, sealBound, _, rawBound⟩ := stepBills step
    have budgets := PqxdhRecordLiftCtxModeBounds.decision_budgets setup.source.crypto _ qUniform qPrivate _ _ _
      uniformBound privateBound hashBound sealBound rawBound
    exact ⟨budgets.1.mono cap, budgets.2.1, budgets.2.2.1, budgets.2.2.2⟩

/-- **`ctx_lift`, integrity half, from the step bills**, both forms and the zero-refusal target. -/
theorem ctxAuthLiftTarget_of_billed (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (bills : CtxBills)
    (billed : StepBilled (n := n) setup codec route serverKid bounds bills) :
    CtxAuthLiftTarget setup codec route serverKid bounds n fallback (ctxReduction setup codec route serverKid bounds)
      bills :=
  ctxAuthLiftStatement_of_bool setup codec route serverKid bounds n fallback _ bills noTerm
    (ctxAuthLiftBool_of_billed setup codec route serverKid bounds fallback bills noTerm billed)

end Statement

end BeaconcryptCore.Computational.PqxdhRecordLiftCtx

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtx.game_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtx.game_real

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtx.game_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtx.game_replay

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtx.advantage_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtx.advantage_congr

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtx.hop_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtx.hop_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtx.ctxAuthLiftBool_of_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtx.ctxAuthLiftBool_of_billed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtx.ctxAuthLiftTarget_of_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtx.ctxAuthLiftTarget_of_billed
