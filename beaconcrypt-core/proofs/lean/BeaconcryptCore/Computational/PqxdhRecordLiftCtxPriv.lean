-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivLink
import BeaconcryptCore.Computational.PqxdhRecordLiftCtx

/-!
# Record-lift CTX privacy half: hybrids, per-key hops and telescope (items 4 and 5, stage S4)

**The hybrids.** `privModes positions cut` puts a coordinate in random mode exactly when `PqxdhRecordLiftChainOrder.selected positions cut` selects it, and in replay mode otherwise: the same hybrid order and index set as the integrity half (`PqxdhRecordLiftCtxHybrid.hybridModes`), with replay in place of real and random in place of replay. `game cut` is the CTX world under these modes followed by a decision on the view. The first hybrid is `idealAuth` (`privModes_zero`, `game_first`); after all `hops n budget` steps exactly the bounded coordinates are in random mode (`privModes_last`), and since no CTX world reaches another coordinate (`PqxdhRecordLiftCtxAvailability.ctxRunWith_congr`) the last hybrid is `randomRecords` (`game_last`). One step changes only its own coordinate, from replay to random (`privModes_unchanged`, `privModes_step`).

**The hops.** `stepClient` is the key-free link client of `PqxdhRecordLiftCtxPrivLink` for the step's coordinate under the modes before the step, and `privReduction` is the explicit CTX reduction family of the target: hop `step`'s ordinary one-key adversary is `PqxdhRecordLiftCtxPrivModes.decisionClient` of the step client, with the single-coin sampler. By the selected-key law (`PqxdhRecordLiftKeyCut.key_cut_measure`, which holds in every mode) and the link, the hybrid before the step has the law of the challenger's replay game and the hybrid after it that of the challenger's random game (`game_replay`, `game_random`, `selectedModesM_replay`, `selectedModesM_random`), so by `PqxdhRecordLiftCtxPrivModes.hop_advantage` each hop is exactly the IND$ advantage of `AdaptiveCtxPrivacyGuard.viewReduction` of the step's adversary (`hop_eq`), that is its `privacyLoss` (`hop_loss`).

**Statement.** `ctxPrivLiftBool_of_billed` telescopes the hops with `PqxdhComposition.finiteHybridBound_of_hop_bounds` (coefficient one) and proves the Boolean form `PqxdhRecordLiftIdeal.CtxPrivLiftBool` for `privReduction` and every bill record from `StepBilled bills` (every hop's adversary is `CtxBounded` by the bills); `ctxPrivLiftStatement_of_billed` gives `CtxPrivLiftStatement` (both forms, through `ctxPrivLiftStatement_of_bool`). `StepBilled` is a property of the explicit construction, not an assumption or contract; `PqxdhRecordLiftCtxPrivBills` proves it for explicit bills.

**Contracts.** No theorem of this module has an assumption or contract hypothesis; the contracts of the brief's H-7 list used by each theorem are listed in `doc/impl/record-lift-ctx-priv.md`. New Claude work; nothing adapted from Codex WIP.
-/

open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftCtxHybrid PqxdhRecordLiftCtxLink
open PqxdhRecordLiftCtxPrivLink PqxdhRecordLiftCtxAvailability PqxdhRecordLiftKeyCut
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds Budget)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)
open CtxRomAuth AdaptiveCtxReceive
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

/-! ### The privacy hybrid family -/

/-- The privacy hybrid with cut `cut`: random mode exactly on the coordinates that `PqxdhRecordLiftChainOrder.selected` selects, replay mode elsewhere. -/
noncomputable def privModes (positions cut : Nat) (label : Label n) : KeyMode :=
  if PqxdhRecordLiftChainOrder.selected positions cut label then .random else .replay

/-- The first privacy hybrid is all replay, that is `idealAuth`'s modes. -/
theorem privModes_zero (positions : Nat) : (privModes positions 0 : Label n → KeyMode) = fun _ => .replay := by
  funext label
  simp only [privModes, PqxdhRecordLiftChainOrder.selected_zero, Bool.false_eq_true, ite_false]

/-- After all steps exactly the bounded coordinates are in random mode. -/
theorem privModes_last (positions : Nat) (label : Label n) :
    privModes positions (positions * (n * 2)) label = .random ↔ PqxdhRecordLiftChainOrder.Bounded positions label := by
  rw [← PqxdhRecordLiftChainOrder.selected_last (positions := positions) label, privModes]
  cases PqxdhRecordLiftChainOrder.selected positions (positions * (n * 2)) label <;> simp

/-- One step changes the mode of no coordinate other than its own. -/
theorem privModes_unchanged (positions : Nat) (step : Fin (positions * (n * 2))) (label : Label n)
    (different : label ≠ PqxdhRecordLiftChainOrder.entryAt step) :
    privModes positions (step.val + 1) label = privModes positions step.val label := by
  rw [privModes, privModes, PqxdhRecordLiftChainOrder.selected_unchanged step label different]

/-- The step's own coordinate is in replay mode before the step and in random mode after it. -/
theorem privModes_step (positions : Nat) (step : Fin (positions * (n * 2))) :
    privModes positions step.val (PqxdhRecordLiftChainOrder.entryAt step) = .replay ∧
      privModes positions (step.val + 1) (PqxdhRecordLiftChainOrder.entryAt step) = .random := by
  obtain ⟨before, after⟩ := PqxdhRecordLiftChainOrder.selected_step step
  simp only [privModes, before, after, Bool.false_eq_true, ite_false, ite_true, and_self]

/-- With the step's coordinate in replay mode, the challenger's replay game is the hybrid before the step. -/
theorem selectedModesM_replay (positions : Nat) (step : Fin (positions * (n * 2))) :
    selectedModesM (PqxdhRecordLiftChainOrder.entryAt step) .replay (privModes positions step.val) =
      privModes positions step.val := by
  funext label
  by_cases same : label = PqxdhRecordLiftChainOrder.entryAt step
  · subst same
    simp only [selectedModesM, ite_true, (privModes_step positions step).1]
  · simp only [selectedModesM, same, ite_false]

/-- With the step's coordinate in random mode, the challenger's random game is the hybrid after the step. -/
theorem selectedModesM_random (positions : Nat) (step : Fin (positions * (n * 2))) :
    selectedModesM (PqxdhRecordLiftChainOrder.entryAt step) .random (privModes positions step.val) =
      privModes positions (step.val + 1) := by
  funext label
  by_cases same : label = PqxdhRecordLiftChainOrder.entryAt step
  · subst same
    simp only [selectedModesM, ite_true, (privModes_step positions step).2]
  · simp only [selectedModesM, same, ite_false, privModes_unchanged positions step label same]

/-! ### The hops -/

section Hops
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (serverKid : Std.U64) (bounds : FreshBounds)

/-- The three-mode client of privacy step `step`: the link client of the step's coordinate under the modes before the step. -/
noncomputable def stepClient (env : Environment n E) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (decision : View n E X → ProbComp Bool) (budget : Budget) (step : Fin (hops n budget)) :
    OracleComp PqxdhRecordLiftCtxPrivModes.Spec Bool :=
  linkClient (PqxdhRecordLiftChainOrder.entryAt (positions := positions budget) step)
    (privModes (positions budget) step.val) setup codec route env serverKid bounds mode adversary decision

/-- The explicit privacy reduction family: hop `step`'s ordinary one-key CTX adversary is its step client with the known-key work run inside and random-mode records drawn by the single-coin sampler. -/
noncomputable def privReduction : CtxReduction n := fun env mode adversary decision budget step =>
  PqxdhRecordLiftCtxPrivModes.decisionClient PqxdhRecordLiftCtxPrivModes.bytesSample setup.source.crypto
    (stepClient setup codec route serverKid bounds env mode adversary decision budget step)

/-- The game of privacy hybrid `cut` under a decision on the view. -/
noncomputable def game (env : Environment n E) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (decision : View n E X → ProbComp Bool) (budget : Budget) (cut : Nat) : ProbComp Bool :=
  ctxRun (privModes (positions budget) cut) id setup codec route env serverKid bounds mode adversary >>= fun result =>
    decision (ctxView result)

/-- The hybrid before step `step` has the law of the challenger's replay game against the step client. -/
theorem game_replay (env : Environment n E) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (decision : View n E X → ProbComp Bool) (budget : Budget) (respects : budget.Respects adversary)
    (step : Fin (hops n budget)) :
    𝒟[game setup codec route serverKid bounds env mode adversary decision budget step.val] =
      𝒟[Prod.fst <$> PqxdhRecordLiftCtxPrivModes.sourceGame PqxdhRecordLiftCtxPrivModes.uniformBytes .replay
        (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
        (stepClient setup codec route serverKid bounds env mode adversary decision budget step)] := by
  rw [stepClient, link _ (privModes (positions budget) step.val) .replay, selectedModesM_replay (n := n) (positions budget) step]
  exact key_cut_measure _ _ id setup codec route env serverKid bounds mode adversary budget respects decision

/-- The hybrid after step `step` has the law of the challenger's random game against the step client. -/
theorem game_random (env : Environment n E) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (decision : View n E X → ProbComp Bool) (budget : Budget) (respects : budget.Respects adversary)
    (step : Fin (hops n budget)) :
    𝒟[game setup codec route serverKid bounds env mode adversary decision budget (step.val + 1)] =
      𝒟[Prod.fst <$> PqxdhRecordLiftCtxPrivModes.sourceGame PqxdhRecordLiftCtxPrivModes.uniformBytes .random
        (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
        (stepClient setup codec route serverKid bounds env mode adversary decision budget step)] := by
  rw [stepClient, link _ (privModes (positions budget) step.val) .random, selectedModesM_random (n := n) (positions budget) step]
  exact key_cut_measure _ _ id setup codec route env serverKid bounds mode adversary budget respects decision

/-- **One privacy hop.** The hybrids before and after step `step` differ by exactly the step's IND$ advantage. -/
theorem hop_eq (env : Environment n E) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (decision : View n E X → ProbComp Bool) (budget : Budget) (respects : budget.Respects adversary)
    (step : Fin (hops n budget)) :
    (game setup codec route serverKid bounds env mode adversary decision budget step.val).boolDistance
        (game setup codec route serverKid bounds env mode adversary decision budget (step.val + 1)) =
      CtxNonceAeadIndDollarValidation.modifiedNonceAeadINDDollarAdvantage setup.source.crypto
        (AdaptiveCtxPrivacyGuard.viewReduction (RawCtxUniversalDecoder.decoder codec.frameRead)
          (privReduction setup codec route serverKid bounds env mode adversary decision budget step)) := by
  rw [PqxdhRecordLiftCtx.advantage_congr _ _ _ _
    (game_replay setup codec route serverKid bounds env mode adversary decision budget respects step)
    (game_random setup codec route serverKid bounds env mode adversary decision budget respects step)]
  exact PqxdhRecordLiftCtxPrivModes.hop_advantage _ _ _

/-- One privacy hop, in the loss form of the target: exactly the step's `privacyLoss`. -/
theorem hop_loss (env : Environment n E) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (decision : View n E X → ProbComp Bool) (budget : Budget) (respects : budget.Respects adversary)
    (step : Fin (hops n budget)) :
    ENNReal.ofReal ((game setup codec route serverKid bounds env mode adversary decision budget step.val).boolDistance
        (game setup codec route serverKid bounds env mode adversary decision budget (step.val + 1))) =
      privacyLoss (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
        (privReduction setup codec route serverKid bounds env mode adversary decision budget step) := by
  rw [hop_eq setup codec route serverKid bounds env mode adversary decision budget respects step]
  rfl

/-- The first privacy hybrid is `idealAuth`. -/
theorem game_first (env : Environment n E) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (decision : View n E X → ProbComp Bool) (budget : Budget) :
    (idealAuth setup codec route env serverKid bounds mode adversary >>= fun result => decision (ctxView result)) =
      game setup codec route serverKid bounds env mode adversary decision budget 0 := by
  unfold game
  rw [privModes_zero]
  rfl

/-- The last privacy hybrid is `randomRecords`: the bounded coordinates are in random mode, and no other coordinate is reached. -/
theorem game_last (env : Environment n E) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (decision : View n E X → ProbComp Bool) (budget : Budget) (respects : budget.Respects adversary) :
    (randomRecords setup codec route env serverKid bounds mode adversary >>= fun result => decision (ctxView result)) =
      game setup codec route serverKid bounds env mode adversary decision budget (hops n budget) := by
  unfold game randomRecords
  rw [← ctxRunWith_tableKey, ← ctxRunWith_tableKey]
  rw [ctxRunWith_congr tableKey tableKey (fun _ => .random) (privModes (positions budget) (hops n budget)) budget
    (fun _ _ _ _ => rfl) (fun label bounded => ((privModes_last _ label).mpr bounded).symm) id setup codec route env
    serverKid bounds mode adversary respects]

end Hops


/-! ### The telescope -/

section Statement
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (serverKid : Std.U64) (bounds : FreshBounds)

/-- The privacy reductions respect `bills`: for every environment with `Frame`, adversary within its budget and decision with its coin cost, every hop's one-key adversary stays within the bills' uniform, shared-hash, seal and raw caps. -/
def StepBilled (bills : CtxBills) : Prop :=
  ∀ {E X : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget), budget.Respects adversary →
  ∀ (decision : View n E X → ProbComp Bool) (cost : Nat), (∀ view, (decision view).IsTotalQueryBound cost) →
  ∀ step : Fin (hops n budget),
    CtxBounded (privReduction setup codec route serverKid bounds env mode adversary decision budget step) bills
      ⟨budget, startup, allowance, bounds, n, cost⟩

/-- **`ctx_lift`, privacy half, from the step bills.** With the explicit reduction family `privReduction`, the Boolean form holds as soon as the reductions respect the bills: `idealAuth` and `randomRecords` differ by at most the exact sum of the per-key IND$ losses, every term with coefficient one. -/
theorem ctxPrivLiftBool_of_billed (bills : CtxBills) (billed : StepBilled (n := n) setup codec route serverKid bounds bills) :
    CtxPrivLiftBool setup codec route serverKid bounds n (privReduction setup codec route serverKid bounds) bills := by
  intro E X env startup allowance frame mode adversary budget respects decision cost costBound
  refine ⟨?_, fun step => billed env startup allowance frame mode adversary budget respects decision cost costBound step⟩
  rw [game_first setup codec route serverKid bounds env mode adversary decision budget,
    game_last setup codec route serverKid bounds env mode adversary decision budget respects]
  have telescope := PqxdhComposition.finiteHybridBound_of_hop_bounds
    (game setup codec route serverKid bounds env mode adversary decision budget) (hops n budget)
    (fun cut => (game setup codec route serverKid bounds env mode adversary decision budget cut).boolDistance
      (game setup codec route serverKid bounds env mode adversary decision budget (cut + 1))) (fun _ _ => le_refl _)
  calc ENNReal.ofReal ((game setup codec route serverKid bounds env mode adversary decision budget 0).boolDistance
        (game setup codec route serverKid bounds env mode adversary decision budget (hops n budget)))
      ≤ ENNReal.ofReal (∑ cut ∈ Finset.range (hops n budget),
          (game setup codec route serverKid bounds env mode adversary decision budget cut).boolDistance
            (game setup codec route serverKid bounds env mode adversary decision budget (cut + 1))) :=
        ENNReal.ofReal_le_ofReal telescope
    _ = ∑ cut ∈ Finset.range (hops n budget), ENNReal.ofReal
          ((game setup codec route serverKid bounds env mode adversary decision budget cut).boolDistance
            (game setup codec route serverKid bounds env mode adversary decision budget (cut + 1))) :=
        ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)
    _ = ∑ step : Fin (hops n budget), ENNReal.ofReal
          ((game setup codec route serverKid bounds env mode adversary decision budget step.val).boolDistance
            (game setup codec route serverKid bounds env mode adversary decision budget (step.val + 1))) :=
        (Fin.sum_univ_eq_sum_range (fun cut => ENNReal.ofReal
          ((game setup codec route serverKid bounds env mode adversary decision budget cut).boolDistance
            (game setup codec route serverKid bounds env mode adversary decision budget (cut + 1)))) _).symm
    _ = ∑ step : Fin (hops n budget), privacyLoss (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
          (privReduction setup codec route serverKid bounds env mode adversary decision budget step) :=
        Finset.sum_congr rfl (fun step _ =>
          hop_loss setup codec route serverKid bounds env mode adversary decision budget respects step)

/-- **`ctx_lift`, privacy half, from the step bills**, both forms. -/
theorem ctxPrivLiftStatement_of_billed (bills : CtxBills)
    (billed : StepBilled (n := n) setup codec route serverKid bounds bills) :
    CtxPrivLiftStatement setup codec route serverKid bounds n (privReduction setup codec route serverKid bounds) bills :=
  ctxPrivLiftStatement_of_bool setup codec route serverKid bounds n _ bills
    (ctxPrivLiftBool_of_billed setup codec route serverKid bounds bills billed)

end Statement

end BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.privModes_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.privModes_zero

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.privModes_last' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.privModes_last

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.privModes_unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.privModes_unchanged

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.privModes_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.privModes_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.selectedModesM_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.selectedModesM_replay

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.selectedModesM_random' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.selectedModesM_random

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.game_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.game_replay

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.game_random' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.game_random

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.hop_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.hop_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.hop_loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.hop_loss

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.game_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.game_first

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.game_last' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.game_last

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.ctxPrivLiftBool_of_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.ctxPrivLiftBool_of_billed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.ctxPrivLiftStatement_of_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv.ctxPrivLiftStatement_of_billed
