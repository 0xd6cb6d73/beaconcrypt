-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills

/-!
# Bills of the later-quantum CE-12 headlines (CE-12 P3, design.md section 9.1)

The query bills of every reduction behind the terms of the later headlines (CE-KT-L, CE-APP-L, CE-LOR-L and their symbolic corollaries), with the post budget `post` (`qCoin₂`, `qHmac₂`, `qHash₂`) of the post adversary on every input:

- `slotLossL_eq`: `slotLossL` (`PqxdhDeploymentLaterHeadlineChain`) is `(qAccept + qFinish + (qHmac + qHmac₂))/2^256` plus the two HMAC-PRF advantages and the key-schedule bounds of the two hidden entries (`PqxdhDeploymentLaterServerItemTargets.slotLossL_transported`): the post-run HMAC budget enters the R1 guessing term with coefficient one.
- `kem_bills_later`: the logged per-target KEM adversary of `kemLossL` makes at most the queries of `PqxdhDeploymentLaterServerTransfer.kem_transfer_server_bills` (`PqxdhDeploymentLaterServerBills.adversary_bound` at the transported caps of the compiled LQ-F program; the post budget enters only the uniform allowance, the Server read costs nothing).
- `slot_bills_later`: the HMAC-PRF reductions and the key-schedule distinguishers of `slotLossL` respect bills built from `rootBillL` at `laterTransported bounds budget post` (`PqxdhDeploymentLaterServerItemBills.laterSlot_bills_compiled`).
- `records_bills_later`: the later chain, integrity and privacy reductions of `recLossL` respect their bills `laterChainBills`, `laterCtxBills`, `laterPrivBills` at the later bill input `inputL` (`PqxdhRecordLiftLaterTargets.LaterRecordBounded`, the bill conjunct of `PqxdhRecordLiftLaterLift.later_record_lift` at the frame of `frame_idealD`); `records_hash_later`: the integrity and privacy hash bills at `inputL` are the run-phase shared-hash total of `BI_g` plus the post phase's shared-hash work `postHash` (`qHash₂`, `laterCtx_hash_bill`, `laterPriv_hash_bill`).
- `hash_route_later`: on every outcome of the later record world with the ideal environment of a target and the environment's reveal, the BLAKE2b routes are within `qHash + S + R + qBuild + qFinish + qHash₂` and the record derivations within `S + 51 R` (`PqxdhDeploymentIdealFrame.c4_ideal_later`).
- `beta_decapsulations_later`: phase 1 of `β_g`'s adversary, built from the run-phase adversary `first`, makes at most `qFinish + 1` logical decapsulation queries (`PqxdhDeploymentHeadlineAnomaly.beta_decapsulations`); the anomaly is a run-phase event and its term is the classical one of `first`.
- `later_target_bills`: the conjunction of the five per-target bills.

Not here: the uniform and base-query bill of phase 1 of `β_g`'s adversary (`ptc_bills` with `guessBill`), which CE-12 P2b proves for every run-phase adversary on its own branch (not on central); since `β_g` of the later headlines is the classical `β_g` of `first`, that bill applies unchanged once it is integrated. The bills of the symbolic terms are those of CE-12 P2 at `first` (`ce_a1_billed`, `a2_bills`). No assumption is added: these are resource bounds in the existing cost model, under `KemBound setup caps`, the total query bound `qInit` of the runtime initializer, the run budget and the post budget.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineBills
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
open PqxdhDeploymentEnvironment (allowanceG baseAllowance ceFirstTouch)
open PqxdhDeploymentHeadlineChain (EnvG startupG inputG)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL inputL)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Out : Type}

/-- `slotLossL` in closed form (U-L1 at the transported caps, `PqxdhDeploymentLaterServerItemTargets.slotLossL_transported`): the R1 guessing term `(qAccept + qFinish + (qHmac + qHmac₂))/2^256` with the post-run HMAC budget at coefficient one, the two HMAC-SHA-512 PRF advantages of the indexed reductions of `rootClientL`, and the key-schedule bounds of the two entry distinguishers `entryDkL`. -/
theorem slotLossL_eq (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (post : PostBudget) (event : Observed Out → Bool) (claim : Observed Out → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    slotLossL (Reader := Reader) setup codec checks route ensureInit bounds mode first second budget post event claim g
        runtime =
      ((budget.accept + budget.finish + (budget.hmac + post.hmac) : ℕ) : ℝ) / 2 ^ 256 +
        ∑ slot ∈ Finset.range 2,
          (PqxdhSecretInputKdf.hmacPrfRealGame setup.hmac
            (PqxdhCorrelatedExpandHybrid.indexedReduction setup.hmac
              (PqxdhDeploymentLaterServerItemTargets.rootClientL (Reader := Reader) setup codec checks ensureInit none
                (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
                (compileServer setup codec route bounds mode first second) runtime budget.create (selectedKem budget g)
                g.1.val) slot)).boolDistAdvantage
            (PqxdhSecretInputKdf.hmacPrfRandomGame (PqxdhCorrelatedExpandHybrid.indexedReduction setup.hmac
              (PqxdhDeploymentLaterServerItemTargets.rootClientL (Reader := Reader) setup codec checks ensureInit none
                (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
                (compileServer setup codec route bounds mode first second) runtime budget.create (selectedKem budget g)
                g.1.val) slot)) +
        ∑ k ∈ Finset.range 2, PqxdhRegistrationJointKemSecondEntry.keyScheduleBound setup.source setup.hmac
          (PqxdhDeploymentLaterServerItemTargets.entryDkL (Reader := Reader) setup codec checks ensureInit none
            (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
            (compileServer setup codec route bounds mode first second) runtime budget.create (selectedKem budget g)
            g.1.val k) :=
  PqxdhDeploymentLaterServerItemTargets.slotLossL_transported setup codec checks ensureInit none
    (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
    (compileServer setup codec route bounds mode first second) runtime budget.create (selectedKem budget g) g.1.val
    bounds budget post

/-- The bill of `kemLossL`'s adversary (`PqxdhDeploymentLaterServerTransfer.kem_transfer_server_bills`): prechallenge at most `(qInit + 32) + (keygenCost · qCreate + V)` uniform queries, `decapsBase · qFinish` base queries and `qFinish` logical decapsulations; postchallenge `V`, `decapsBase · qFinish` and `qFinish`, where `V = uniformCap caps qCreate qFinish (OpenUniform.total caps (laterTransported bounds budget post)) qAccept`. -/
theorem kem_bills_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (caps : KemCaps) (bounded : KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
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
      (caps.decapsBase * budget.finish) budget.finish :=
  PqxdhDeploymentLaterServerTransfer.kem_transfer_server_bills setup codec checks route caps bounded ensureInit qInit
    initBound bounds mode first second budget respects post postRespects event claim g runtime

/-- The bills of `slotLossL`'s reductions (`PqxdhDeploymentLaterServerItemBills.laterSlot_bills_compiled`): the two indexed HMAC-PRF reductions of `rootClientL` respect `PrfBills` at `rootBillL caps qInit none qCreate (laterTransported bounds budget post)`, and the two entry distinguishers `entryDkL` respect `EntryComponentBills` at that bill plus 216. -/
theorem slot_bills_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (caps : KemCaps) (bounded : KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
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
        (laterTransported bounds budget post) + 216) :=
  PqxdhDeploymentLaterServerItemBills.laterSlot_bills_compiled setup codec route checks caps bounded ensureInit qInit
    initBound bounds mode first second budget respects post postRespects event claim g runtime

/-- The bills of `recLossL`'s reductions: the later chain observers, integrity adversaries and (mode P) privacy adversaries of `PqxdhRecordLiftLaterLift.later_record_lift` at the ideal environment of the target of `g`, the environment's reveal and the post adversary respect `laterChainBills`, `laterCtxBills` and `laterPrivBills` at the later bill input `inputL` (`LaterRecordBounded`), with the frame of `frame_idealD`. -/
theorem records_bills_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (event : View 2 (EnvG KemSK budget) Out → Bool) :
    PqxdhRecordLiftLaterTargets.LaterRecordBounded 2
      (PqxdhRecordLiftLaterChain.laterChainReduction setup codec route setup.serverKeyId bounds 2)
      (PqxdhRecordLiftLaterCtx.laterCtxReduction setup codec route setup.serverKeyId bounds)
      (PqxdhRecordLiftLaterPriv.laterPrivReduction setup codec route setup.serverKeyId bounds)
      PqxdhRecordLiftLaterChain.laterChainBills PqxdhRecordLiftLaterCtx.laterCtxBills
      PqxdhRecordLiftLaterPriv.laterPrivBills
      (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime) mode envReveal
      first second (fun view => pure (event view)) budget post (inputL caps qInit budget bounds post) :=
  ((PqxdhRecordLiftLaterLift.later_record_lift setup codec route setup.serverKeyId bounds 2 setup.hmac fallback).2
    correct (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
    (startupG caps qInit budget) (allowanceG (baseAllowance caps) ceFirstTouch)
    (PqxdhDeploymentIdealFrame.frame_idealD setup codec checks caps bounded (Target.ofCE budget g) ensureInit qInit
      initBound 0 runtime) mode envReveal first second budget post respects postRespects event).2

/-- The hash route of `recLossL`'s integrity and privacy bills (`qHash₂`): at the later bill input `inputL`, the shared-hash bills of `laterCtxBills` and `laterPrivBills` are the run-phase shared-hash total of `BI_g` plus the post phase's shared-hash work (`PqxdhRecordLiftLaterTargets.postHash`: the post BLAKE2b requests and the environment's class-six hash allowance per post HMAC request). -/
theorem records_hash_later (caps : KemCaps) (qInit : ℕ) (budget : Budget) (bounds : FreshBounds)
    (post : PostBudget) :
    PqxdhRecordLiftLaterCtx.laterCtxBills.hash (inputL caps qInit budget bounds post) =
        PqxdhRecordLiftIdeal.sharedHashTotal (inputG caps qInit budget bounds) +
          PqxdhRecordLiftLaterTargets.postHash (inputL caps qInit budget bounds post) ∧
      PqxdhRecordLiftLaterPriv.laterPrivBills.hash (inputL caps qInit budget bounds post) =
        PqxdhRecordLiftIdeal.sharedHashTotal (inputG caps qInit budget bounds) +
          PqxdhRecordLiftLaterTargets.postHash (inputL caps qInit budget bounds post) :=
  ⟨PqxdhRecordLiftLaterCtx.laterCtx_hash_bill _, PqxdhRecordLiftLaterPriv.laterPriv_hash_bill _⟩

/-- The later C4 hash route at the ideal environment of a target (`PqxdhDeploymentIdealFrame.c4_ideal_later`): on every outcome of the later record world with `envGD` at the target of `g` and the environment's reveal, for a run-phase adversary within its budget and a post adversary within its post budget, the BLAKE2b routes are within `qHash + S + R + qBuild + qFinish + qHash₂` and the record derivations within `S + 51 R`. -/
theorem hash_route_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (caps : KemCaps) (bounded : KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    ∀ result ∈ support (PqxdhRecordLiftLater.run setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode envReveal first second),
      result.2.primitive.1.effects .hash + result.2.primitive.1.native .hash ≤
          budget.hash + budget.sends + budget.receives + budget.build + budget.finish + post.hash ∧
        result.2.primitive.1.native .kdf ≤ budget.sends + 51 * budget.receives :=
  PqxdhDeploymentIdealFrame.c4_ideal_later setup codec route checks caps bounded (Target.ofCE budget g) ensureInit
    qInit initBound 0 runtime setup.serverKeyId bounds mode budget post envReveal first second respects postRespects

/-- The decapsulation count of `β_g`'s adversary for the later headlines (`PqxdhDeploymentHeadlineAnomaly.beta_decapsulations` at the run-phase adversary `first`): phase 1 makes at most `qFinish + 1` logical decapsulation queries. -/
theorem beta_decapsulations_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (first : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects first)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) (pk : PqxdhKemIndCca.MlKem768PublicKey) :
    ((PqxdhDeploymentHeadlineAnomaly.ptc setup.kem (PqxdhDeploymentIdealAnomalyGuesser.anomalyGuesser setup codec route
        checks (Target.ofCE budget g) ensureInit 0 runtime bounds mode first)).preChallenge pk).IsQueryBoundP
      PqxdhKemIndCca.IsMlKemLogicalDecapsulationQuery (budget.finish + 1) :=
  PqxdhDeploymentHeadlineAnomaly.beta_decapsulations setup codec route checks ensureInit bounds mode first budget
    respects g runtime pk

/-- The per-target bills of the later headlines: the KEM adversary of `kemLossL` (`kem_bills_later`), the reductions of `slotLossL` (`slot_bills_later`), the later record-lift reductions of `recLossL` for the view event (`records_bills_later`), the later C4 hash route (`hash_route_later`) and the decapsulation count of `β_g`'s adversary (`beta_decapsulations_later`), under `KemBound setup caps`, the total query bound `qInit`, the run budget and the post budget. -/
theorem later_target_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (viewEvent : View 2 (EnvG KemSK budget) Out → Bool) :
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
      (caps.decapsBase * budget.finish) budget.finish ∧
    ((∀ slot ∈ Finset.range 2, PqxdhRegistrationJointKemKeyTransfer.PrfBills setup.hmac
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
        (laterTransported bounds budget post) + 216)) ∧
    PqxdhRecordLiftLaterTargets.LaterRecordBounded 2
      (PqxdhRecordLiftLaterChain.laterChainReduction setup codec route setup.serverKeyId bounds 2)
      (PqxdhRecordLiftLaterCtx.laterCtxReduction setup codec route setup.serverKeyId bounds)
      (PqxdhRecordLiftLaterPriv.laterPrivReduction setup codec route setup.serverKeyId bounds)
      PqxdhRecordLiftLaterChain.laterChainBills PqxdhRecordLiftLaterCtx.laterCtxBills
      PqxdhRecordLiftLaterPriv.laterPrivBills
      (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime) mode envReveal
      first second (fun view => pure (viewEvent view)) budget post (inputL caps qInit budget bounds post) ∧
    (∀ result ∈ support (PqxdhRecordLiftLater.run setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode envReveal first second),
      result.2.primitive.1.effects .hash + result.2.primitive.1.native .hash ≤
          budget.hash + budget.sends + budget.receives + budget.build + budget.finish + post.hash ∧
        result.2.primitive.1.native .kdf ≤ budget.sends + 51 * budget.receives) ∧
    ∀ pk, ((PqxdhDeploymentHeadlineAnomaly.ptc setup.kem (PqxdhDeploymentIdealAnomalyGuesser.anomalyGuesser setup codec
        route checks (Target.ofCE budget g) ensureInit 0 runtime bounds mode first)).preChallenge pk).IsQueryBoundP
      PqxdhKemIndCca.IsMlKemLogicalDecapsulationQuery (budget.finish + 1) :=
  ⟨kem_bills_later setup codec checks route caps bounded ensureInit qInit initBound bounds mode first second budget
      respects post postRespects event claim g runtime,
    slot_bills_later setup codec checks route caps bounded ensureInit qInit initBound bounds mode first second budget
      respects post postRespects event claim g runtime,
    records_bills_later setup codec checks route correct caps bounded ensureInit qInit initBound bounds mode first second
      budget respects post postRespects g runtime fallback viewEvent,
    hash_route_later setup codec checks route caps bounded ensureInit qInit initBound bounds mode first second budget
      respects post postRespects g runtime,
    beta_decapsulations_later setup codec checks route ensureInit bounds mode first budget respects g runtime⟩

end BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineBills

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineBills.slotLossL_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineBills.slotLossL_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineBills.kem_bills_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineBills.kem_bills_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineBills.slot_bills_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineBills.slot_bills_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineBills.records_bills_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineBills.records_bills_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineBills.records_hash_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineBills.records_hash_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineBills.hash_route_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineBills.hash_route_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineBills.beta_decapsulations_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineBills.beta_decapsulations_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineBills.later_target_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineBills.later_target_bills
