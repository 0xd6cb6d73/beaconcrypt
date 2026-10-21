-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff
import BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransfer
import BeaconcryptCore.Computational.PqxdhRecordLift

/-!
# The per-target chain of the CE-12 headlines (CE-12 P1, design-v2 section 3)

The generic per-target chain from the deployment experiment (`PqxdhDeploymentSecrecy.game`, Server identity index 0, generated seed, `supplied = none`) to the record lift's ideal worlds, stated in CE-11b unit U7's names. For one target `g = (i, k)`, an event and a claim, `D_g` is the experiment's event with the claim's budgeted designation equal to `g` (`PqxdhDeploymentKemTransfer.designated`), and `dec_g` is the same decision read on a record-lift view (`PqxdhDeploymentIdealHandoff.decisionOn` on `viewObserved`).

- Losses (design-v2 section 2): `kemLoss` (one IND-CCA advantage of the per-target certified raw-ordinal KEM adversary plus the ML-KEM correctness error, CE-9) and `slotLoss` (item 2's stage S7 with stage T at two slots, `PqxdhRegistrationJointKemKeyTransfer.allIdealLoss` at the transported caps); `authLoss` and `recLoss`, the record-lift losses of `PqxdhRecordLiftComposition.record_auth_lift` and `PqxdhRecordLift.record_lift` at the ideal environment of the target with the frame of `PqxdhDeploymentIdealFrame.frame_idealD` (bill input `inputG`).
- C1-C2 (`chain_slot`, `chain_slot_close`): the experiment's `D_g` against item 2's two-slot world, one-sided and two-sided, from `PqxdhDeploymentKemTransfer.kem_transfer`, `PqxdhDeploymentKemTwoSided.kem_transfer_two_sided`, `PqxdhRegistrationJointKemKeyTransfer.allIdeal_loss` and `PqxdhRegistrationJointBeaconFinishOnce.slotGame_two`.
- C3 (`chain_ideal`, `chain_ideal_close`): to CE's un-compiled ideal game `PqxdhDeploymentIdealSteps.idealGame` (`PqxdhDeploymentIdealCompile.ideal_compile`); this is the probe `kt_le` and its two-sided form.
- C3-C5 (`chain_view`, `chain_close`): to `dec_g` on the record lift's view of the all-real chain world with the ideal environment of the target (`PqxdhDeploymentIdealHandoff.ideal_world_view`).
- C6: `chain_slots` (with `IdealSlots` conjoined, plus the Beacon-side anomaly on the record world, `PqxdhDeploymentIdealHandoff.ideal_world_view_slots`), `real_slots_server` (the three Server-side conjuncts `ServerSlots` on every outcome of the chain world, under `Phase1ReadBack` alone), `chain_server` (with `ServerSlots` conjoined and no anomaly term), `anomaly_view` (the anomaly on the view has the probability of the anomaly on the record world) and `view_unslotted` (an event without `IdealSlots` on the view is within the anomaly).
- C7: `auth_close`, `auth_le`, `records_close`, `records_le`, the event forms of the two record lifts at the frame of `frame_idealD`.
- The exact split over the tight target domain for an event that names a designated claim (`split_named`, from `PqxdhDeploymentKemTwoSided.split_create`).

These are compositions of existing theorems; no assumption or contract is added.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated decision selectedKem)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealTrace (IdealSlots Anomaly peerOf)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentCompileSecrecy (compileFull)
open PqxdhRecordLiftIdeal (View chainView ctxView realChains idealAuth idealRecords)
open PqxdhRecordLiftInterface (Slot)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentEnvironment (allowanceG baseAllowance ceFirstTouch)

/-! ### Notation -/

section Notation
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The environment state of the ideal environment of a target of a budget (`PqxdhDeploymentIdealEnv.envGD`). -/
abbrev EnvG (KemSK : Type) (budget : Budget) :=
  PqxdhDeploymentEnvironment.EnvState KemSK
    (PqxdhDeploymentIdealParams.Params KemSK budget.create × PqxdhDeploymentIdealSteps.SplitBk)

/-- `kemLoss g d_g` (design-v2 section 2): the IND-CCA advantage of the per-target certified raw-ordinal KEM adversary of the decision `d_g(event, claim)` (CE-9, `PqxdhDeploymentKemTransfer.kem_transfer`) plus the ML-KEM correctness error, each with coefficient one. -/
noncomputable def kemLoss (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (event : Observed X → Bool)
    (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) : ℝ :=
  setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl
      (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
    (PqxdhRegistrationJointKemRawCertified.adversary setup codec checks ensureInit none
      (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
      (compileFull setup codec route bounds mode adversary) runtime budget.create (selectedKem budget g)
      g.1.val).toINDCCA +
    PqxdhRegistrationJointKemRawGame.correctnessError setup

/-- `slotLoss g d_g` (design-v2 section 2): item 2's stage S7 with stage T at two slots for the decision `d_g(event, claim)` (`PqxdhRegistrationJointKemKeyTransfer.allIdealLoss` at the caps transported from the budget): the R1 statistical term, two HMAC-PRF advantages and the two key-schedule bounds. -/
noncomputable def slotLoss (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (event : Observed X → Bool)
    (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) : ℝ :=
  PqxdhRegistrationJointKemKeyTransfer.allIdealLoss setup codec checks ensureInit none
    (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
    (compileFull setup codec route bounds mode adversary) runtime budget.create (selectedKem budget g) g.1.val
    (PqxdhDeploymentCompileCaps.transported bounds budget)

/-- The startup coin bound of the ideal environment of a target (`PqxdhDeploymentIdealFrame.frame_idealD` at `count = budget.create`). -/
def startupG (caps : KemCaps) (qInit : ℕ) (budget : Budget) : ℕ :=
  qInit + 32 + (budget.create + 1) * caps.keygenCost + caps.encapsCost

/-- `BI_g` (design-v2 section 2): the bill input of the record lift at the ideal environment of a target, with the startup bound and the first-touch allowance of `frame_idealD`, two slots and no decision coins. -/
def inputG (caps : KemCaps) (qInit : ℕ) (budget : Budget) (bounds : FreshBounds) : PqxdhRecordLiftIdeal.BillInput :=
  ⟨budget, startupG caps qInit budget, allowanceG (baseAllowance caps) ceFirstTouch, bounds, 2, 0⟩

/-- `authLoss_g e` (design-v2 section 2): the integrity record-lift loss (`PqxdhRecordLiftIdeal.recordAuthLoss`) of the explicit chain and integrity reductions of `PqxdhRecordLiftComposition.record_auth_lift` at the ideal environment of the target of `g`, for the view event `e`, with zero aliasing and refusal terms. -/
noncomputable def authLoss (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (caps : KemCaps) (qInit : ℕ)
    (event : View 2 (EnvG KemSK budget) X → Bool) : ℝ≥0∞ :=
  PqxdhRecordLiftIdeal.recordAuthLoss setup codec 2 setup.hmac fallback
    (PqxdhRecordLiftChainLift.chainReduction setup codec route setup.serverKeyId bounds 2)
    (PqxdhRecordLiftCtx.ctxReduction setup codec route setup.serverKeyId bounds) PqxdhRecordLiftCtxBills.ctxBills
    PqxdhRecordLiftIdeal.noTerm PqxdhRecordLiftIdeal.noTerm PqxdhRecordLiftIdeal.noTerm
    (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime) mode adversary
    (fun view => pure (event view)) budget (inputG caps qInit budget bounds)

/-- `recLoss_g e` (design-v2 section 2): the record-lift loss (`PqxdhRecordLiftIdeal.recordLoss`) of the explicit chain, integrity and privacy reductions of `PqxdhRecordLift.record_lift` at the ideal environment of the target of `g`, for the view event `e`, with zero aliasing and refusal terms. -/
noncomputable def recLoss (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (caps : KemCaps) (qInit : ℕ)
    (event : View 2 (EnvG KemSK budget) X → Bool) : ℝ≥0∞ :=
  PqxdhRecordLiftIdeal.recordLoss setup codec 2 setup.hmac fallback
    (PqxdhRecordLiftChainLift.chainReduction setup codec route setup.serverKeyId bounds 2)
    (PqxdhRecordLiftCtx.ctxReduction setup codec route setup.serverKeyId bounds)
    (PqxdhRecordLiftCtxPriv.privReduction setup codec route setup.serverKeyId bounds) PqxdhRecordLiftCtxBills.ctxBills
    PqxdhRecordLiftIdeal.noTerm PqxdhRecordLiftIdeal.noTerm PqxdhRecordLiftIdeal.noTerm
    (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime) mode adversary
    (fun view => pure (event view)) budget (inputG caps qInit budget bounds)

/-- The three Server-side conjuncts of `PqxdhDeploymentIdealTrace.IdealSlots` (`ISs_g`, design-v2 section 2): the Server restriction, the Beacon restriction and the Server converse. -/
def ServerSlots {count : ℕ} (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Aeneas.Std.U64)
    (t : Target count) (slots : Handle → Option (Slot 2)) (transcript : List PqxdhDeploymentInterface.Entry) : Prop :=
  (∀ keyId slot, slots (.peer keyId) = some slot → slot = 0 ∧ peerOf t transcript = some keyId) ∧
    (∀ owner slot, slots (.owner owner) = some slot → owner = t.kem.val) ∧
    ∀ keyId, PqxdhDeploymentTranscript.designate crypto codec serverKid transcript (.peer keyId) =
      some (t.accept, t.kem.val) → slots (.peer keyId) = some 0

/-- `IdealSlots` implies its Server-side conjuncts. -/
theorem idealSlots_server {count : ℕ} (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (serverKid : Aeneas.Std.U64) (t : Target count) (slots : Handle → Option (Slot 2))
    (transcript : List PqxdhDeploymentInterface.Entry)
    (slotted : IdealSlots crypto codec serverKid t slots transcript) :
    ServerSlots crypto codec serverKid t slots transcript :=
  ⟨slotted.1, slotted.2.1, slotted.2.2.1⟩

open Classical in
/-- `dec_g ∧ IS_g` on a record-lift view: the per-target decision on the view's observation and `IdealSlots` of the target of `g` for the view's handle-to-slot map. -/
noncomputable def slotted (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (budget : Budget)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    {E : Type} (view : View 2 E X) : Bool :=
  decide ((viewObserved view).any (decisionOn setup codec budget event claim g) = true ∧
    ∀ value, view.result = some value →
      IdealSlots setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) view.slots value.2.1.transcript)

open Classical in
/-- `dec_g ∧ ISs_g` on a record-lift view: the per-target decision and the Server-side conjuncts `ServerSlots`. -/
noncomputable def serverSlotted (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (budget : Budget)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    {E : Type} (view : View 2 E X) : Bool :=
  decide ((viewObserved view).any (decisionOn setup codec budget event claim g) = true ∧
    ∀ value, view.result = some value →
      ServerSlots setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) view.slots value.2.1.transcript)

end Notation

/-! ### Real-number helpers -/

section Helpers

/-- If two finite values differ by at most `c` in absolute value of their real numbers, the first is at most the second plus `c`. -/
theorem le_add_of_ofReal_abs {a b c : ℝ≥0∞} (finiteA : a ≠ ⊤) (finiteB : b ≠ ⊤)
    (close : ENNReal.ofReal |a.toReal - b.toReal| ≤ c) : a ≤ b + c := by
  calc a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal finiteA).symm
    _ ≤ ENNReal.ofReal (b.toReal + |a.toReal - b.toReal|) := by
        refine ENNReal.ofReal_le_ofReal ?_
        linarith [le_abs_self (a.toReal - b.toReal)]
    _ ≤ ENNReal.ofReal b.toReal + ENNReal.ofReal |a.toReal - b.toReal| := ENNReal.ofReal_add_le
    _ ≤ b + c := by
        rw [ENNReal.ofReal_toReal finiteB]
        exact add_le_add le_rfl close

/-- The two-sided form of `le_add_of_ofReal_abs`: the second is at most the first plus `c`. -/
theorem le_add_of_ofReal_abs_symm {a b c : ℝ≥0∞} (finiteA : a ≠ ⊤) (finiteB : b ≠ ⊤)
    (close : ENNReal.ofReal |a.toReal - b.toReal| ≤ c) : b ≤ a + c := by
  rw [abs_sub_comm] at close
  exact le_add_of_ofReal_abs finiteB finiteA close

/-- The probability that a Boolean observation of a run is true is finite. -/
theorem chance_ne_top {α : Type} (run : ProbComp α) (event : α → Bool) : 𝒟[event <$> run] {true} ≠ ⊤ :=
  UniformTargetSelection.chance_ne_top run event

end Helpers

/-! ### C1-C5: the per-target chain -/

section Chain
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- C1-C2, one-sided (design-v2 section 3): for a budget-respecting adversary and a target `g`, the probability that the deployment experiment ends with the event and the claim designating `g` is at most the probability of item 2's two-slot world of `g`'s decision plus `kemLoss` and `slotLoss`. -/
theorem chain_slot (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      𝒟[PqxdhRegistrationJointKemSecondEntry.slotGame setup codec checks ensureInit none
        (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (compileFull setup codec route bounds mode adversary) runtime budget.create (selectedKem budget g) g.1.val 2]
          {true} +
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget event claim g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget event claim g runtime) := by
  have kem := PqxdhDeploymentKemTransfer.kem_transfer setup functional codec checks route ensureInit phase1 phase2
    bounds mode adversary budget respects event claim g runtime
  have item2 := PqxdhRegistrationJointKemKeyTransfer.allIdeal_loss setup codec checks ensureInit none
    (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
    (compileFull setup codec route bounds mode adversary) runtime budget.create
    (selectedKem budget g) g.1.val (PqxdhDeploymentCompileCaps.transported bounds budget)
    (PqxdhDeploymentCompileCaps.compile_full_certified setup codec route bounds mode adversary budget respects) correct
  rw [← PqxdhRegistrationJointBeaconFinishOnce.slotGame_two] at item2
  set opq := PqxdhRegistrationJointKemRawOpaque.opaqueBranch setup codec checks ensureInit none
    (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
    (compileFull setup codec route bounds mode adversary) runtime budget.create
    (selectedKem budget g) g.1.val false with hopq
  set slot := PqxdhRegistrationJointKemSecondEntry.slotGame setup codec checks ensureInit none
    (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
    (compileFull setup codec route bounds mode adversary) runtime budget.create
    (selectedKem budget g) g.1.val 2 with hslot
  have step := ProbComp.evalDist_apply_true_le_add_ofReal_boolDistAdvantage opq slot
  refine kem.trans ?_
  calc _ ≤ (𝒟[slot] {true} + ENNReal.ofReal (opq.boolDistAdvantage slot)) +
        ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget event claim g
          runtime) := add_le_add step le_rfl
    _ ≤ _ := by
        rw [add_right_comm]
        exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal item2)

/-- C1-C2, two-sided (design-v2 section 3): the probability that the deployment experiment ends with the event and the claim designating `g` and the probability of item 2's two-slot world of `g`'s decision differ by at most `kemLoss + slotLoss`. -/
theorem chain_slot_close (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    |(𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime]
        {true}).toReal -
      (𝒟[PqxdhRegistrationJointKemSecondEntry.slotGame setup codec checks ensureInit none
        (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (compileFull setup codec route bounds mode adversary) runtime budget.create (selectedKem budget g) g.1.val 2]
          {true}).toReal| ≤
      kemLoss setup codec checks route ensureInit bounds mode adversary budget event claim g runtime +
        slotLoss setup codec checks route ensureInit bounds mode adversary budget event claim g runtime := by
  have kem := PqxdhDeploymentKemTwoSided.kem_transfer_two_sided setup functional codec checks route ensureInit phase1
    phase2 bounds mode adversary budget respects event claim g runtime
  have item2 := PqxdhRegistrationJointKemKeyTransfer.allIdeal_loss setup codec checks ensureInit none
    (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
    (compileFull setup codec route bounds mode adversary) runtime budget.create
    (selectedKem budget g) g.1.val (PqxdhDeploymentCompileCaps.transported bounds budget)
    (PqxdhDeploymentCompileCaps.compile_full_certified setup codec route bounds mode adversary budget respects) correct
  rw [← PqxdhRegistrationJointBeaconFinishOnce.slotGame_two] at item2
  exact (abs_sub_le _ _ _).trans (add_le_add kem item2)

/-- C1-C3, one-sided (design-v2 section 3, the probe `kt_le`): the probability that the deployment experiment ends with the event and the claim designating `g` is at most the probability of the same decision on CE's un-compiled ideal game of `g` (`PqxdhDeploymentIdealSteps.idealGame`, item 2's two hidden entries uniform), plus `kemLoss` and `slotLoss`. -/
theorem chain_ideal (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      𝒟[(fun outcome => decide (happens event (PqxdhDeploymentIdealBranch.classicalOf outcome) = true ∧
          designated setup.source.crypto codec setup.serverKeyId budget claim
            (PqxdhDeploymentIdealBranch.classicalOf outcome) = some g)) <$>
        (PqxdhDeploymentIdealSteps.idealGame setup codec route checks budget g ensureInit bounds mode adversary).run
          runtime] {true} +
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget event claim g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget event claim g runtime) := by
  rw [← PqxdhDeploymentIdealCompile.ideal_compile setup codec route checks phase1 phase2 ensureInit bounds mode
    adversary budget respects event claim g runtime]
  exact chain_slot setup functional codec checks route ensureInit phase1 phase2 correct bounds mode adversary budget
    respects event claim g runtime

/-- C1-C3, two-sided (design-v2 section 3): the probability that the deployment experiment ends with the event and the claim designating `g` and the probability of the same decision on CE's un-compiled ideal game of `g` differ by at most `kemLoss + slotLoss`. -/
theorem chain_ideal_close (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    |(𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime]
        {true}).toReal -
      (𝒟[(fun outcome => decide (happens event (PqxdhDeploymentIdealBranch.classicalOf outcome) = true ∧
          designated setup.source.crypto codec setup.serverKeyId budget claim
            (PqxdhDeploymentIdealBranch.classicalOf outcome) = some g)) <$>
        (PqxdhDeploymentIdealSteps.idealGame setup codec route checks budget g ensureInit bounds mode adversary).run
          runtime] {true}).toReal| ≤
      kemLoss setup codec checks route ensureInit bounds mode adversary budget event claim g runtime +
        slotLoss setup codec checks route ensureInit bounds mode adversary budget event claim g runtime := by
  rw [← PqxdhDeploymentIdealCompile.ideal_compile setup codec route checks phase1 phase2 ensureInit bounds mode
    adversary budget respects event claim g runtime]
  exact chain_slot_close setup functional codec checks route ensureInit phase1 phase2 correct bounds mode adversary
    budget respects event claim g runtime

/-- C1-C5, one-sided (design-v2 section 3): the probability that the deployment experiment ends with the event and the claim designating `g` is at most the probability of `dec_g` on the record lift's view of the all-real chain world with the ideal environment of the target of `g`, plus `kemLoss` and `slotLoss` (`PqxdhDeploymentIdealHandoff.ideal_world_view`). -/
theorem chain_view (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      𝒟[(fun view => (viewObserved view).any (decisionOn setup codec budget event claim g)) <$>
        (chainView <$> realChains setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary)] {true} +
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget event claim g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget event claim g runtime) := by
  rw [← PqxdhDeploymentIdealHandoff.ideal_world_view setup codec route checks phase1 phase2 ensureInit bounds mode
    adversary budget respects event claim g runtime]
  exact chain_slot setup functional codec checks route ensureInit phase1 phase2 correct bounds mode adversary budget
    respects event claim g runtime

/-- C1-C5, two-sided (design-v2 section 3, `chain_close`): the probability that the deployment experiment ends with the event and the claim designating `g` and the probability of `dec_g` on the record lift's view of the all-real chain world with the ideal environment of the target of `g` differ by at most `kemLoss + slotLoss`. -/
theorem chain_close (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    |(𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime]
        {true}).toReal -
      (𝒟[(fun view => (viewObserved view).any (decisionOn setup codec budget event claim g)) <$>
        (chainView <$> realChains setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary)] {true}).toReal| ≤
      kemLoss setup codec checks route ensureInit bounds mode adversary budget event claim g runtime +
        slotLoss setup codec checks route ensureInit bounds mode adversary budget event claim g runtime := by
  rw [← PqxdhDeploymentIdealHandoff.ideal_world_view setup codec route checks phase1 phase2 ensureInit bounds mode
    adversary budget respects event claim g runtime]
  exact chain_slot_close setup functional codec checks route ensureInit phase1 phase2 correct bounds mode adversary
    budget respects event claim g runtime

end Chain

/-! ### C6: the slot conjunction on the view -/

section Slots
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

open Classical in
/-- C1-C6, one-sided with `IdealSlots` (design-v2 section 3, step C6, Beacon-capable claims): the probability that the deployment experiment ends with the event and the claim designating `g` is at most the probability of `dec_g ∧ IS_g` (`slotted`) on the record lift's view of the all-real chain world with the ideal environment of the target of `g`, plus the probability of the Beacon-side anomaly of that target on the record world (`PqxdhDeploymentIdealHandoff.ideal_world_view_slots`), plus `kemLoss` and `slotLoss`. -/
theorem chain_slots (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      𝒟[slotted setup codec budget event claim g <$>
        (chainView <$> realChains setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary)] {true} +
      𝒟[(fun result => decide (∃ value, result.1 = some value ∧
          Anomaly setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) value.2.1.2.transcript)) <$>
        PqxdhRecordLiftWorld.run setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary] {true} +
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget event claim g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget event claim g runtime) :=
  (chain_slot setup functional codec checks route ensureInit phase1 phase2 correct bounds mode adversary budget respects
    event claim g runtime).trans (add_le_add (add_le_add
      (PqxdhDeploymentIdealHandoff.ideal_world_view_slots setup codec route checks phase1 phase2 ensureInit bounds mode
        adversary budget respects event claim g runtime) le_rfl) le_rfl)

/-- `real_slots_server` (design-v2 section 3): under `Phase1ReadBack`, on every outcome of the all-real chain world with the ideal environment of a target, the view's handle-to-slot map satisfies the three Server-side conjuncts of `IdealSlots` (`ServerSlots`). From `PqxdhDeploymentIdealHandoff.realChains_support` and `PqxdhDeploymentIdealProvenance.ideal_slots_server`; it is `PqxdhDeploymentIdealHandoff.ideal_view_slots`'s proof without the Beacon converse. -/
theorem real_slots_server (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    {count : ℕ} (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    ∀ result ∈ support (realChains setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
          mode adversary),
      ∀ value, (chainView result).result = some value →
        ServerSlots setup.source.crypto codec setup.serverKeyId t (chainView result).slots value.2.1.transcript := by
  intro result member value found
  obtain ⟨annotated, annotatedMember, same⟩ := PqxdhDeploymentIdealHandoff.realChains_support setup codec route _
    setup.serverKeyId bounds mode adversary result member
  rw [same] at found ⊢
  rcases annotated with ⟨_ | inner, state⟩
  · exact absurd found (by simp [PqxdhDeploymentIdealHandoff.annotatedView])
  · simp only [PqxdhDeploymentIdealHandoff.annotatedView, Option.map_some, Option.some.injEq] at found
    subst found
    have slots := PqxdhDeploymentIdealProvenance.ideal_slots_server setup codec route checks phase1 t ensureInit
      identityIndex runtime bounds mode adversary _ annotatedMember inner rfl
    rw [← PqxdhDeploymentIdealHandoff.originMap_two] at slots
    exact slots

open Classical in
/-- C1-C6 for Server-side claims (design-v2 section 3, step C6, peer claims): under `Phase1ReadBack` alone at C6, the probability that the deployment experiment ends with the event and the claim designating `g` is at most the probability of `dec_g ∧ ISs_g` (`serverSlotted`) on the record lift's view of the all-real chain world with the ideal environment of the target of `g`, plus `kemLoss` and `slotLoss`; no anomaly term. -/
theorem chain_server (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      𝒟[serverSlotted setup codec budget event claim g <$>
        (chainView <$> realChains setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary)] {true} +
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget event claim g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget event claim g runtime) := by
  refine (chain_view setup functional codec checks route ensureInit phase1 phase2 correct bounds mode adversary budget
    respects event claim g runtime).trans_eq ?_
  congr 3
  rw [Functor.map_map, Functor.map_map]
  congr 1
  refine PqxdhDeploymentKemTransfer.map_support_congr _ _ _ fun result member => ?_
  simp only [serverSlotted]
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact ⟨fun held => ⟨held, real_slots_server setup codec checks route phase1 (Target.ofCE budget g) ensureInit 0
    runtime bounds mode adversary result member⟩, And.left⟩

open Classical in
/-- `anomaly_view` (design-v2 section 3): the Beacon-side anomaly of a target read on the record lift's view of the all-real chain world with the ideal environment of the target has the probability of the anomaly on the record world with that environment (`PqxdhDeploymentIdealHandoff.realChains_view`, `PqxdhDeploymentIdealOrigins.annotatedRun_erase`). -/
theorem anomaly_view (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) {count : ℕ} (t : Target count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (runtime : A) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    𝒟[(fun view => decide (∃ value, view.result = some value ∧
          Anomaly setup.source.crypto codec setup.serverKeyId t value.2.1.transcript)) <$>
        (chainView <$> realChains setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime)
          setup.serverKeyId bounds mode adversary)] {true} =
      𝒟[(fun result => decide (∃ value, result.1 = some value ∧
          Anomaly setup.source.crypto codec setup.serverKeyId t value.2.1.2.transcript)) <$>
        PqxdhRecordLiftWorld.run setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime)
          setup.serverKeyId bounds mode adversary] {true} := by
  rw [PqxdhDeploymentIdealHandoff.realChains_view, ← PqxdhDeploymentIdealOrigins.annotatedRun_erase, Functor.map_map,
    Functor.map_map]
  congr 3
  funext annotated
  rcases annotated with ⟨_ | inner, state⟩
  · simp [PqxdhDeploymentIdealHandoff.annotatedView]
  · simp [PqxdhDeploymentIdealHandoff.annotatedView]

open Classical in
/-- An event on the record lift's view without `IdealSlots` (design-v2 section 4.5's `E ∧ ¬IS ⊆ Anom`): under `Phase1ReadBack` and `Phase2ReadBack`, the probability that a view event holds while `IdealSlots` of the target fails is at most the probability of the Beacon-side anomaly on the record world (`PqxdhDeploymentIdealHandoff.ideal_view_slots`, `anomaly_view`). -/
theorem view_unslotted (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) {count : ℕ} (t : Target count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X)
    (event : View 2 (PqxdhDeploymentEnvironment.EnvState KemSK (PqxdhDeploymentIdealParams.Params KemSK count ×
      PqxdhDeploymentIdealSteps.SplitBk)) X → Bool) :
    𝒟[(fun view => decide (event view = true ∧ ¬∀ value, view.result = some value →
          IdealSlots setup.source.crypto codec setup.serverKeyId t view.slots value.2.1.transcript)) <$>
        (chainView <$> realChains setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime)
          setup.serverKeyId bounds mode adversary)] {true} ≤
      𝒟[(fun result => decide (∃ value, result.1 = some value ∧
          Anomaly setup.source.crypto codec setup.serverKeyId t value.2.1.2.transcript)) <$>
        PqxdhRecordLiftWorld.run setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime)
          setup.serverKeyId bounds mode adversary] {true} := by
  rw [← anomaly_view setup codec checks route t ensureInit identityIndex runtime bounds mode adversary]
  rw [UniformTargetSelection.chance_eq, UniformTargetSelection.chance_eq]
  refine prEvent_mono_of_support _ _ _ fun view member held => ?_
  rw [support_map] at member
  obtain ⟨result, resultMember, rfl⟩ := member
  obtain ⟨value, unslotted⟩ := Classical.not_forall.mp held.2
  obtain ⟨found, failed⟩ := Classical.not_imp.mp unslotted
  exact ⟨value, found, (PqxdhDeploymentIdealHandoff.ideal_view_slots setup codec route checks phase1 phase2 t
    ensureInit identityIndex runtime bounds mode adversary result resultMember value found).resolve_left failed⟩

end Slots

/-! ### C7: the record lifts at the ideal environment of a target -/

section Lift
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- C7, integrity form (design-v2 section 3): for every view event, the probabilities on the record lift's views of the all-real chain world and of the integrity-ideal world `idealAuth`, both with the ideal environment of the target of `g`, differ by at most `authLoss_g`. The frame is `PqxdhDeploymentIdealFrame.frame_idealD` (premises `KemBound setup caps` and the total query bound `qInit` of the runtime initializer); the lift is `PqxdhRecordLiftComposition.record_auth_lift` (contract `SourceFullCorrect`). -/
theorem auth_close (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (event : View 2 (EnvG KemSK budget) X → Bool) :
    ENNReal.ofReal |(𝒟[event <$> (chainView <$> realChains setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary)] {true}).toReal -
        (𝒟[event <$> (ctxView <$> idealAuth setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary)] {true}).toReal| ≤
      authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit event := by
  have lift := (PqxdhRecordLiftComposition.record_auth_lift setup codec route setup.serverKeyId bounds 2 setup.hmac
    fallback).2 correct (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
    (startupG caps qInit budget) (allowanceG (baseAllowance caps) ceFirstTouch)
    (PqxdhDeploymentIdealFrame.frame_idealD setup codec checks caps bounded (Target.ofCE budget g) ensureInit qInit
      initBound 0 runtime) mode adversary budget respects event
  rw [Functor.map_map, Functor.map_map]
  exact lift.1

/-- C7, integrity form, one-sided: a view event on the all-real chain world has at most its probability on `idealAuth` plus `authLoss_g`. -/
theorem auth_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (event : View 2 (EnvG KemSK budget) X → Bool) :
    𝒟[event <$> (chainView <$> realChains setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode adversary)] {true} ≤
      𝒟[event <$> (ctxView <$> idealAuth setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode adversary)] {true} +
      authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit event :=
  le_add_of_ofReal_abs (chance_ne_top _ _) (chance_ne_top _ _)
    (auth_close setup codec checks route correct caps bounded ensureInit qInit initBound bounds mode adversary budget
      respects g runtime fallback event)

/-- C7, full form (design-v2 section 3): for every view event, the probabilities on the record lift's views of the all-real chain world and of the record-ideal world `idealRecords`, both with the ideal environment of the target of `g`, differ by at most `recLoss_g`. Frame from `frame_idealD`; lift `PqxdhRecordLift.record_lift` (contract `SourceFullCorrect`). -/
theorem records_close (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (event : View 2 (EnvG KemSK budget) X → Bool) :
    ENNReal.ofReal |(𝒟[event <$> (chainView <$> realChains setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary)] {true}).toReal -
        (𝒟[event <$> (ctxView <$> idealRecords setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary)] {true}).toReal| ≤
      recLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit event := by
  have lift := (PqxdhRecordLift.record_lift setup codec route setup.serverKeyId bounds 2 setup.hmac fallback).2 correct
    (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
    (startupG caps qInit budget) (allowanceG (baseAllowance caps) ceFirstTouch)
    (PqxdhDeploymentIdealFrame.frame_idealD setup codec checks caps bounded (Target.ofCE budget g) ensureInit qInit
      initBound 0 runtime) mode adversary budget respects event
  rw [Functor.map_map, Functor.map_map]
  exact lift.1

/-- C7, full form, one-sided: a view event on the all-real chain world has at most its probability on `idealRecords` plus `recLoss_g`. -/
theorem records_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (event : View 2 (EnvG KemSK budget) X → Bool) :
    𝒟[event <$> (chainView <$> realChains setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode adversary)] {true} ≤
      𝒟[event <$> (ctxView <$> idealRecords setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode adversary)] {true} +
      recLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit event :=
  le_add_of_ofReal_abs (chance_ne_top _ _) (chance_ne_top _ _)
    (records_close setup codec checks route correct caps bounded ensureInit qInit initBound bounds mode adversary budget
      respects g runtime fallback event)

end Lift

/-! ### The exact split over the tight target domain -/

section Split
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The exact split for an event that names a designated claim (design-v2 section 4): if the event implies that the claim's handle has a budgeted designation, then for a budget-respecting adversary the probability that the deployment experiment ends with the event is the sum over `g` in `Fin qAccept × Fin qCreate` (with `k` read in `Fin (qCreate + 1)`) of the probability that it ends with the event and the claim designating `g` (`PqxdhDeploymentKemTwoSided.split_create`). -/
theorem split_named (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (runtime : A)
    (named : ∀ observed, event observed = true →
      (PqxdhDeploymentKemTransfer.target setup.source.crypto codec setup.serverKeyId budget claim observed).isSome) :
    𝒟[(fun outcome => happens event outcome) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} =
      ∑ g : Fin budget.accept × Fin budget.create,
        𝒟[(fun outcome => decide (happens event outcome = true ∧
          designated setup.source.crypto codec setup.serverKeyId budget claim outcome =
            some ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity))) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime]
          {true} := by
  rw [← PqxdhDeploymentKemTwoSided.split_create setup codec checks route ensureInit phase1 phase2 bounds mode adversary
    budget respects event claim runtime]
  congr 3
  funext outcome
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  refine ⟨fun held => ⟨held, ?_⟩, And.left⟩
  unfold happens at held
  unfold PqxdhDeploymentTargetRange.eligible
  cases found : PqxdhDeploymentKemTransfer.observeGame outcome.1 with
  | none => simp [found] at held
  | some observed =>
      rw [found, Option.any_some] at held
      have targeted := named observed held
      simp only [Option.bind_some]
      unfold PqxdhDeploymentKemTransfer.target at targeted
      cases named : claim observed with
      | none => simp [named] at targeted
      | some handle =>
          rw [named, Option.bind_some] at targeted
          simp only [Option.bind_some]
          unfold PqxdhDeploymentTranscript.designateIn at targeted
          cases chosen : PqxdhDeploymentTranscript.designate setup.source.crypto codec setup.serverKeyId
              observed.2.1.transcript handle with
          | none => simp [chosen] at targeted
          | some _ => rfl

end Split

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.idealSlots_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.idealSlots_server

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.le_add_of_ofReal_abs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.le_add_of_ofReal_abs

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.le_add_of_ofReal_abs_symm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.le_add_of_ofReal_abs_symm

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.chance_ne_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.chance_ne_top

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.chain_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.chain_slot

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.chain_slot_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.chain_slot_close

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.chain_ideal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.chain_ideal

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.chain_ideal_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.chain_ideal_close

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.chain_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.chain_view

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.chain_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.chain_close

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.chain_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.chain_slots

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.real_slots_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.real_slots_server

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.chain_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.chain_server

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.anomaly_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.anomaly_view

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.view_unslotted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.view_unslotted

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.auth_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.auth_close

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.auth_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.auth_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.records_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.records_close

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.records_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.records_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.split_named' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain.split_named
