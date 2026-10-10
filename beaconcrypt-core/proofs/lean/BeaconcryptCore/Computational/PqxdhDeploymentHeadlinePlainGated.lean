-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBillsFull

/-!
# The CE-12 P4 s2b plaintext headlines with `β_g`, billed (CE-12 P4 review fix pass; design-v2 section 9)

CE-12 P2b restated every frozen headline whose bound carries the anomaly term `β_g` together with the bills of the reductions behind its terms (`PqxdhDeploymentHeadlineGated`), and P4 step 1 applied the same rule to the later headlines (`PqxdhDeploymentLaterHeadlineGated`). Step 3 of P4 added five forms whose bound carries `β_g`, the s2b plaintext headlines of `PqxdhDeploymentHeadlinePlain`. Each theorem below restates one of them unchanged and conjoins `PqxdhDeploymentHeadlineBillsFull.TargetBills` at the same adversary, proved by P2b's `PqxdhDeploymentHeadlineBillsFull.target_bills`:

- `ce_plain_s2b_target_billed`, `ce_plain_s2b_billed`: the s2b plaintext failure, per target and summed (`kemLoss + slotLoss + β_g + authLoss_g(dec_g ∧ IS_g)` per target).
- `ce_or_plain_s2b_target_billed`, `ce_or_plain_s2b_billed`: the s2b origin failure or plaintext failure, per target and summed (`kemLoss`, `slotLoss` and `authLoss_g` at the combined event and claim; `β_g` and `publicationTerm budget` are the same terms as in `ce_or_s2b`).
- `ce_plain_every_s2b_billed`: the every-production reading, with the bound of `ce_plain_s2b`.

The fields of `TargetBills` are quantified over every event, claim and target (`kem`, `slot`, `auth`) and over every target (`beta`), so they cover the terms at the plaintext event, the combined event and their claims; `beta` is `ptc_bills` at the deployment adversary. The bounds are the step-3 theorems' own, with the same premises; `target_bills` takes only binders the source theorems already have (`SourceFullCorrect`, `KemBound`, the initializer's query bound, `budget.Respects adversary`, the runtime and the AEAD forgery fallback), so no premise is added. The step-2 and step-3 forms without `β_g` (`ce_pin_b2s`, `ce_or_pin_b2s`, `ce_plain_b2s`, `ce_or_plain_b2s`, `ce_plain_every_b2s` and `ce_or_fields_b2s`, each with its per-target form where it has one) are not restated, as P2b did not restate `ce_or_b2s`: the bills of their terms (`kemLoss`, `slotLoss`, `authLoss_g`) are the fields `kem`, `slot` and `auth` of the same `target_bills`. No assumption or contract is added. No `PqxdhBoundary*` module is imported.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainGated
open PqxdhDeploymentHeadlinePlain
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentTranscript (designateIn)
open PqxdhDeploymentHeadlineEvents (Direction cpart firstHandle receivedHandle firstHandle_some firstHandle_isSome)
open PqxdhRecordLiftIdeal (View ctxView idealAuth handleSlot publicationTerm receivingHandle Counterpart)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentHeadlineChain (ServerSlots slotted serverSlotted kemLoss slotLoss authLoss)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineAgree (AgreeFailure agreeEvent)
open PqxdhDeploymentHeadlinePlainSend (Sent PublishedPlain)
open PqxdhDeploymentHeadlinePin (chance_mono_support chance_or_le decision_transfer)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- `ce_plain_s2b_target` (`PqxdhDeploymentHeadlinePlain.ce_plain_s2b_target`, R2 s2b per target: `kemLoss + slotLoss + β_g + authLoss_g(dec_g ∧ IS_g)`) with its bills: the same bound, together with the per-target bills (`PqxdhDeploymentHeadlineBillsFull.TargetBills`: `kemLoss`, `slotLoss`, `β_g` through `ptc_bills`, `authLoss_g` and `recLoss_g`, each field for every target and, except the field of `β_g`, for every event), so that every advantage term of the bound, including `β_g`, cites a reduction whose query caps are proved at the deployment budget. The bill conjunct adds no premise: `target_bills` takes only binders the source theorem already has. -/
theorem ce_plain_s2b_target_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (g : Fin budget.accept × Fin budget.capacity) :
    (𝒟[(fun outcome => decide (happens (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        outcome = true ∧ designated setup.source.crypto codec setup.serverKeyId budget
          (plainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        (plainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        (plainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g runtime) +
      beta setup codec route checks ensureInit bounds mode adversary budget g runtime +
      authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (slotted setup codec budget (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
          (plainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g)) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds mode
        adversary budget runtime :=
  ⟨PqxdhDeploymentHeadlinePlain.ce_plain_s2b_target setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound frameReadBack bounds mode adversary budget respects runtime fallback g,
   PqxdhDeploymentHeadlineBillsFull.target_bills setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds mode adversary budget respects runtime fallback⟩

/-- `ce_plain_s2b` (`PqxdhDeploymentHeadlinePlain.ce_plain_s2b`, R2 s2b: the sum over the targets of `kemLoss + slotLoss + β_g + authLoss_g(dec_g ∧ IS_g)`) with its bills: the same bound, together with the per-target bills (`PqxdhDeploymentHeadlineBillsFull.TargetBills`: `kemLoss`, `slotLoss`, `β_g` through `ptc_bills`, `authLoss_g` and `recLoss_g`, each field for every target and, except the field of `β_g`, for every event), so that every advantage term of the bound, including `β_g`, cites a reduction whose query caps are proved at the deployment budget. The bill conjunct adds no premise: `target_bills` takes only binders the source theorem already has. -/
theorem ce_plain_s2b_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    (𝒟[(fun outcome => happens (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b) outcome) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        (plainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        (plainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc) runtime) +
          beta setup codec route checks ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime +
          authLoss setup codec checks route ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime
              fallback caps qInit
        (slotted setup codec budget (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
          (plainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc)))) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds mode
        adversary budget runtime :=
  ⟨PqxdhDeploymentHeadlinePlain.ce_plain_s2b setup functional codec checks route ensureInit phase1 phase2 correct caps
    bounded qInit initBound frameReadBack bounds mode adversary budget respects runtime fallback,
   PqxdhDeploymentHeadlineBillsFull.target_bills setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds mode adversary budget respects runtime fallback⟩

/-- `ce_or_plain_s2b_target` (`PqxdhDeploymentHeadlinePlain.ce_or_plain_s2b_target`, CE-OR s2b with the plaintext field per target: `kemLoss + slotLoss + β_g + authLoss_g(dec_g ∧ IS_g) + publicationTerm budget`, with `kemLoss`, `slotLoss` and `authLoss_g` at the combined event and claim; `β_g`, which depends only on the target, and `publicationTerm budget` are the same terms as in `ce_or_s2b`) with its bills: the same bound, together with the per-target bills (`PqxdhDeploymentHeadlineBillsFull.TargetBills`: `kemLoss`, `slotLoss`, `β_g` through `ptc_bills`, `authLoss_g` and `recLoss_g`, each field for every target and, except the field of `β_g`, for every event), so that every advantage term of the bound, including `β_g`, cites a reduction whose query caps are proved at the deployment budget. The bill conjunct adds no premise: `target_bills` takes only binders the source theorem already has. -/
theorem ce_or_plain_s2b_target_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (g : Fin budget.accept × Fin budget.capacity) :
    (𝒟[(fun outcome => decide (happens (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        outcome = true ∧ designated setup.source.crypto codec setup.serverKeyId budget
          (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
        (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
        (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g runtime) +
      beta setup codec route checks ensureInit bounds mode adversary budget g runtime +
      authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (slotted setup codec budget (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
          (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g) +
      publicationTerm budget) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds mode
        adversary budget runtime :=
  ⟨PqxdhDeploymentHeadlinePlain.ce_or_plain_s2b_target setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound frameReadBack bounds mode adversary budget respects runtime fallback g,
   PqxdhDeploymentHeadlineBillsFull.target_bills setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds mode adversary budget respects runtime fallback⟩

/-- `ce_or_plain_s2b` (`PqxdhDeploymentHeadlinePlain.ce_or_plain_s2b`, CE-OR s2b with the plaintext field: the sum over the targets of `kemLoss + slotLoss + β_g + authLoss_g(dec_g ∧ IS_g) + publicationTerm budget`, with `kemLoss`, `slotLoss` and `authLoss_g` at the combined event and claim; `β_g`, which depends only on the target, and `publicationTerm budget` are the same terms as in `ce_or_s2b`) with its bills: the same bound, together with the per-target bills (`PqxdhDeploymentHeadlineBillsFull.TargetBills`: `kemLoss`, `slotLoss`, `β_g` through `ptc_bills`, `authLoss_g` and `recLoss_g`, each field for every target and, except the field of `β_g`, for every event), so that every advantage term of the bound, including `β_g`, cites a reduction whose query caps are proved at the deployment budget. The bill conjunct adds no premise: `target_bills` takes only binders the source theorem already has. -/
theorem ce_or_plain_s2b_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    (𝒟[(fun outcome => happens (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        outcome) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
            (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
            (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc)
                runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
            (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
            (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc)
                runtime) +
          beta setup codec route checks ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime +
          authLoss setup codec checks route ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime
              fallback caps qInit
            (slotted setup codec budget (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
              (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc)) +
          publicationTerm budget)) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds mode
        adversary budget runtime :=
  ⟨PqxdhDeploymentHeadlinePlain.ce_or_plain_s2b setup functional codec checks route ensureInit phase1 phase2 correct
    caps bounded qInit initBound frameReadBack bounds mode adversary budget respects runtime fallback,
   PqxdhDeploymentHeadlineBillsFull.target_bills setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds mode adversary budget respects runtime fallback⟩

/-- `ce_plain_every_s2b` (`PqxdhDeploymentHeadlinePlain.ce_plain_every_s2b`, R2 s2b with every production: the bound of `ce_plain_s2b`) with its bills: the same bound, together with the per-target bills (`PqxdhDeploymentHeadlineBillsFull.TargetBills`: `kemLoss`, `slotLoss`, `β_g` through `ptc_bills`, `authLoss_g` and `recLoss_g`, each field for every target and, except the field of `β_g`, for every event), so that every advantage term of the bound, including `β_g`, cites a reduction whose query caps are proved at the deployment budget. The bill conjunct adds no premise: `target_bills` takes only binders the source theorem already has. -/
theorem ce_plain_every_s2b_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    (𝒟[(fun outcome => happens (plainEveryEvent setup.source.crypto codec setup.serverKeyId budget route .s2b) outcome)
        <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
            (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
            (plainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
            (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
            (plainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc) runtime) +
          beta setup codec route checks ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime +
          authLoss setup codec checks route ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime
              fallback caps qInit
            (slotted setup codec budget (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
              (plainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc)))) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds mode
        adversary budget runtime :=
  ⟨PqxdhDeploymentHeadlinePlain.ce_plain_every_s2b setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound frameReadBack bounds mode adversary budget respects runtime fallback,
   PqxdhDeploymentHeadlineBillsFull.target_bills setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds mode adversary budget respects runtime fallback⟩

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainGated

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainGated.ce_plain_s2b_target_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainGated.ce_plain_s2b_target_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainGated.ce_plain_s2b_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainGated.ce_plain_s2b_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainGated.ce_or_plain_s2b_target_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainGated.ce_or_plain_s2b_target_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainGated.ce_or_plain_s2b_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainGated.ce_or_plain_s2b_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainGated.ce_plain_every_s2b_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainGated.ce_plain_every_s2b_billed
