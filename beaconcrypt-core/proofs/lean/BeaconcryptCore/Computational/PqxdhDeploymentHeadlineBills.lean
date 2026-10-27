-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision

/-!
# Bills of the CE-12 headline reductions (CE-12 P2, design-v2 section 9, in part)

Query bills of reductions behind the CE-12 terms that the existing theorems do not already state at the deployment budget.

- `pair_bills`: `pairAdversary` (the encapsulate-and-compare adversary of `pair_cp_le`) makes no query before the challenge and, after it, at most `caps.encapsUniform` uniform and `caps.encapsBase` base queries (one encapsulation to the challenge public key, `KemBound`) and no decapsulation query (`OneKeyAdversary.MakesAtMostQueries 0 0 0 caps.encapsUniform caps.encapsBase 0`). `liftBase_bound`, `uniform_lifted` and `base_lifted` carry query caps of a base computation through the lifting handler `liftBase`.
- `auth_bills` and `records_bills`: the bill conjuncts of `PqxdhRecordLiftComposition.record_auth_lift` and `PqxdhRecordLift.record_lift` at the ideal environment of a target with the frame of `PqxdhDeploymentIdealFrame.frame_idealD`, that is at the bill input `BI_g = PqxdhDeploymentHeadlineChain.inputG caps qInit budget bounds` (`RecordAuthBounded`, `RecordBounded`): the reductions behind `authLoss_g` and `recLoss_g`, which P1 states without their bills.

The other bills of the CE-12 terms are existing theorems: `PqxdhDeploymentKemTransfer.kem_transfer_bills` (`kemLoss`), `PqxdhRegistrationJointKemKeyTransferBills.allIdeal_bills` and `prf_bills` (`slotLoss`), `PqxdhDeploymentServerAuthBills.ce_a1_billed` (`ε_A1`, restated by `ce_a1_linked`), `PqxdhDeploymentProvenance.a2_bills` (`ε_A2pub`), `PqxdhDeploymentServerAuthInjective.collider_bills` (`ε_inj`) and `PqxdhDeploymentHeadlineAnomaly.beta_decapsulations` (`β_g`'s decapsulation count). Not here: the uniform and base-query bill of `ptc`'s phase 1 (`guessBill` through `splitStep_uniform`, the per-step uniform bound of the anomaly guesser's split handler) and the aggregate `HeadlineBills`; both are open points of P2. No assumption is added: these are resource bounds in the existing cost model.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBills
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext MlKemSharedSecret MlKemCCAOracleSpec OneKeyAdversary
  IsMlKemUniformQuery IsMlKemBaseQuery IsMlKemLogicalDecapsulationQuery)
open PqxdhServerAuthSourceCosts (KemCaps KemBound IsAmbientUniform IsAmbientBase)
open PqxdhDeploymentHeadlineCollision (liftBase pairAdversary)

/-! ### `pairAdversary`'s bill -/

section Pair
variable {ι : Type} {baseSpec : OracleSpec ι} {SK : Type}

/-- A lifted base computation makes on the IND-CCA query surface exactly the queries it makes on the base surface: a cap on the base queries of a class is a cap on the lifted queries of the corresponding class. -/
theorem liftBase_bound (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (base : (unifSpec + baseSpec).Domain → Prop) [DecidablePred base]
    (lifted : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred lifted]
    (same : ∀ q, lifted (.inl q) ↔ base q) {α : Type} :
    ∀ (oa : OracleComp (unifSpec + baseSpec) α) (n : ℕ), oa.IsQueryBoundP base n →
      (simulateQ (liftBase kem) oa).IsQueryBoundP lifted n := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure x => exact fun _ _ => isQueryBoundP_pure _ _ _
  | query_bind q f ih =>
      intro n bounded
      rw [isQueryBoundP_query_bind_iff] at bounded
      obtain ⟨allowed, rest⟩ := bounded
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, liftBase]
      by_cases counted : base q
      · have positive : 0 < n := allowed.resolve_left (not_not.mpr counted)
        have first : (id <$> (query (spec := kem.IND_CCA_oracleSpec) (Sum.inl q) :
            OracleComp kem.IND_CCA_oracleSpec _)).IsQueryBoundP lifted 1 := by
          simp
        have next : ∀ u, (simulateQ (liftBase kem) (f u)).IsQueryBoundP lifted (n - 1) := fun u => by
          have := rest u
          simp only [counted, ite_true] at this
          exact ih u _ this
        have total := isQueryBoundP_bind (n := 1) (m := n - 1) first fun x _ => next x
        rwa [show 1 + (n - 1) = n by omega] at total
      · have first : (id <$> (query (spec := kem.IND_CCA_oracleSpec) (Sum.inl q) :
            OracleComp kem.IND_CCA_oracleSpec _)).IsQueryBoundP lifted 0 := by
          simp [(same q).not.mpr counted]
        have next : ∀ u, (simulateQ (liftBase kem) (f u)).IsQueryBoundP lifted n := fun u => by
          have := rest u
          simp only [counted, ite_false] at this
          exact ih u _ this
        have total := isQueryBoundP_bind (n := 0) (m := n) first fun x _ => next x
        rwa [Nat.zero_add] at total

/-- The uniform class of the IND-CCA query surface is the ambient uniform class on lifted base queries. -/
theorem uniform_lifted (q : (unifSpec + baseSpec).Domain) :
    IsMlKemUniformQuery (Sum.inl q : (MlKemCCAOracleSpec baseSpec).Domain) ↔ IsAmbientUniform q := by
  rcases q with coin | base <;> simp [IsMlKemUniformQuery, IsAmbientUniform]

/-- The base class of the IND-CCA query surface is the ambient base class on lifted base queries. -/
theorem base_lifted (q : (unifSpec + baseSpec).Domain) :
    IsMlKemBaseQuery (Sum.inl q : (MlKemCCAOracleSpec baseSpec).Domain) ↔ IsAmbientBase q := by
  rcases q with coin | base <;> simp [IsMlKemBaseQuery, IsAmbientBase]

end Pair

section PairBill
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- `pairAdversary`'s bill (design-v2 section 9): phase 1 makes no query; phase 2 makes at most the uniform and base queries of one encapsulation to the challenge public key (`caps.encapsUniform` and `caps.encapsBase`, `KemBound`) and no decapsulation query. -/
theorem pair_bills (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (caps : KemCaps)
    (bounded : KemBound setup caps) :
    (pairAdversary setup.kem).MakesAtMostQueries 0 0 0 caps.encapsUniform caps.encapsBase 0 := by
  refine ⟨fun pk => ⟨PqxdhDeploymentHeadlineCollision.pair_pre setup.kem pk _,
    PqxdhDeploymentHeadlineCollision.pair_pre setup.kem pk _, PqxdhDeploymentHeadlineCollision.pair_pre setup.kem pk _⟩,
    fun transcript kStar => ⟨?_, ?_, PqxdhDeploymentHeadlineCollision.pair_post_decapsulations setup.kem transcript kStar⟩⟩
  · change (simulateQ (liftBase setup.kem) (setup.kem.encaps transcript.publicKey) >>= fun mine =>
      pure (decide (mine.1 = transcript.ciphertext ∧ mine.2 = kStar))).IsQueryBoundP IsMlKemUniformQuery _
    exact isQueryBoundP_bind (n := caps.encapsUniform) (m := 0) (liftBase_bound setup.kem _ _ uniform_lifted _ _
      (bounded.encapsUniform transcript.publicKey)) fun _ _ => isQueryBoundP_pure _ _ _
  · change (simulateQ (liftBase setup.kem) (setup.kem.encaps transcript.publicKey) >>= fun mine =>
      pure (decide (mine.1 = transcript.ciphertext ∧ mine.2 = kStar))).IsQueryBoundP IsMlKemBaseQuery _
    exact isQueryBoundP_bind (n := caps.encapsBase) (m := 0) (liftBase_bound setup.kem _ _ base_lifted _ _
      (bounded.encapsBase transcript.publicKey)) fun _ _ => isQueryBoundP_pure _ _ _

end PairBill

/-! ### The record lifts' bills at `BI_g` -/

section Records
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentHeadlineChain (EnvG startupG inputG)
open PqxdhDeploymentEnvironment (allowanceG baseAllowance ceFirstTouch)
open PqxdhRecordLiftIdeal (View)

/-- The bills of the integrity record lift at the ideal environment of a target with the frame of `frame_idealD` (bill input `BI_g = inputG caps qInit budget bounds`): every chain observer of `record_auth_lift` within `chainBills.observer BI_g` total queries and every integrity reduction within `ctxBills` at `BI_g`, for every view event. These are the bill conjuncts behind `authLoss_g` that P1 does not restate. Premises: `SourceFullCorrect`, `KemBound`, the total query bound `qInit` of the runtime initializer and the budget. -/
theorem auth_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (event : View 2 (EnvG KemSK budget) X → Bool) :
    PqxdhRecordLiftIdeal.RecordAuthBounded 2
      (PqxdhRecordLiftChainLift.chainReduction setup codec route setup.serverKeyId bounds 2)
      (PqxdhRecordLiftCtx.ctxReduction setup codec route setup.serverKeyId bounds) PqxdhRecordLiftChainBills.chainBills
      PqxdhRecordLiftCtxBills.ctxBills
      (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime) mode adversary
      (fun view => pure (event view)) budget (inputG caps qInit budget bounds) :=
  ((PqxdhRecordLiftComposition.record_auth_lift setup codec route setup.serverKeyId bounds 2 setup.hmac fallback).2
    correct (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
    (startupG caps qInit budget) (allowanceG (baseAllowance caps) ceFirstTouch)
    (PqxdhDeploymentIdealFrame.frame_idealD setup codec checks caps bounded (Target.ofCE budget g) ensureInit qInit
      initBound 0 runtime) mode adversary budget respects event).2

/-- The bills of the full record lift at the ideal environment of a target with the frame of `frame_idealD` (`BI_g`): the chain observers, the integrity reductions and, in mode P, the privacy reductions of `record_lift` within their bills at `BI_g`, for every view event. These are the bill conjuncts behind `recLoss_g`. Premises: those of `auth_bills`. -/
theorem records_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (event : View 2 (EnvG KemSK budget) X → Bool) :
    PqxdhRecordLiftIdeal.RecordBounded 2
      (PqxdhRecordLiftChainLift.chainReduction setup codec route setup.serverKeyId bounds 2)
      (PqxdhRecordLiftCtx.ctxReduction setup codec route setup.serverKeyId bounds)
      (PqxdhRecordLiftCtxPriv.privReduction setup codec route setup.serverKeyId bounds)
      PqxdhRecordLiftChainBills.chainBills PqxdhRecordLiftCtxBills.ctxBills PqxdhRecordLiftCtxPrivBills.privBills
      (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime) mode adversary
      (fun view => pure (event view)) budget (inputG caps qInit budget bounds) :=
  ((PqxdhRecordLift.record_lift setup codec route setup.serverKeyId bounds 2 setup.hmac fallback).2 correct
    (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
    (startupG caps qInit budget) (allowanceG (baseAllowance caps) ceFirstTouch)
    (PqxdhDeploymentIdealFrame.frame_idealD setup codec checks caps bounded (Target.ofCE budget g) ensureInit qInit
      initBound 0 runtime) mode adversary budget respects event).2

end Records

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBills

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBills.liftBase_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBills.liftBase_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBills.uniform_lifted' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBills.uniform_lifted

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBills.base_lifted' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBills.base_lifted

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBills.pair_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBills.pair_bills

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBills.auth_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBills.auth_bills

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBills.records_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBills.records_bills
