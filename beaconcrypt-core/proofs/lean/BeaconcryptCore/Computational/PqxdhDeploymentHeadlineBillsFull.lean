-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBills
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransferBills

/-!
# `HeadlineBills`: every reduction bill of the CE-12 headline terms at the deployment budget (CE-12 P2b, design-v2 section 9)

Each term of the CE-12 headlines is an advantage of an explicit reduction (or a statistical or final-world term). This module collects the query bills of all of them, each instantiated at the deployment budget `B` (the caps transported from `B`, `PqxdhDeploymentCompileCaps.transported`, the bill input `BI_g = inputG caps qInit B bounds`, the CE-A1 caps `coinCap`, `romCap`, `hashCap` and `totalCap`, and `B.create`), and proves them from resource premises only.

- `TargetBills`, the per-target terms, for every event, claim, target `g` and view event: `kem` (`kemLoss`, `PqxdhDeploymentKemTransfer.kem_transfer_bills`; `transported_total` gives its uniform allowance in closed form), `slot` (`slotLoss`, `PqxdhRegistrationJointKemKeyTransfer.allIdeal_bills` at the compiled program with `compile_full_certified`: both HMAC-PRF reductions, as `prf_bills`, and both key-schedule reductions), `beta` (`β_g`, `PqxdhDeploymentHeadlineGuessBill.ptc_bills`), `auth` and `records` (`authLoss_g` and `recLoss_g`, `PqxdhDeploymentHeadlineBills.auth_bills` and `records_bills` at `BI_g`).
- `A1Bills` (`ε_A1`): the bills of every `R_c` at the transported CE-A1 caps, as the second conjunct of `PqxdhDeploymentServerAuthBills.ce_a1_billed`; `a1_bills` proves them from `KemBound` and the budget alone, without CE-A1's security premises (`reduction_caps`, then the bill halves of `common_authentication_with_resources`: `PqxdhServerAuthPublicationResources.reduction_bills` and `PqxdhServerAuthJointIdentityUniformCosts.source_bound_with_resources`).
- `A2Bills` (`ε_A2pub`): `PqxdhDeploymentProvenance.a2_bills` for every identity position. `InjBills` (`ε_inj`): `PqxdhDeploymentServerAuthInjective.collider_bills` for every identity position. `PairBills` (the advantage of `pair_cp_le`): `PqxdhDeploymentHeadlineBills.pair_bills`.
- `HeadlineBills` collects all of them; `headline_bills` proves it.

Premises: `KemBound setup caps`, the total query bound `qInit` of the runtime initializer, `budget.Respects adversary`, and, for the record-lift bills, `SourceFullCorrect setup.source setup.hmac` (the premise under which `record_auth_lift` and `record_lift` state their bills). No cryptographic premise and no assumption is added; these are resource bounds in the existing cost model.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBillsFull
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed decision selectedKem)
open PqxdhDeploymentCompileSecrecy (compileFull)
open PqxdhDeploymentIdealParams (Target)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (EnvG inputG)
open PqxdhRecordLiftIdeal (View)
open PqxdhDeploymentServerAuthBills (coinCap romCap hashCap totalCap)
open PqxdhDeploymentHeadlineGuessBill (guessBill)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

section A1

/-- The bills of the CE-A1 reduction `R_c` at the caps transported from the budget, from `KemBound setup caps` and the budget alone: the same `ReductionBills` that `ce_a1_billed` states under CE-A1's security premises. -/
theorem a1_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) (caps : KemCaps)
    (bounded : KemBound setup caps) (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (c : ℕ)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    PqxdhServerAuthCommonAuthentication.ReductionBills setup codec checks caps
      (PqxdhDeploymentServerAuth.serverAuthAdversary setup codec route bounds mode adversary c)
      (coinCap caps bounds budget) budget.accept (romCap budget) (hashCap budget) (totalCap caps bounds budget)
      budget.finish a1Fallback signatureFallback := by
  have reductionCaps := PqxdhDeploymentServerAuthBills.reduction_caps setup codec caps bounded route bounds mode adversary
    budget respects c
  set work := PqxdhDeploymentServerAuth.reduction (KemSK := KemSK) setup codec route bounds mode adversary c
  have joint := PqxdhServerAuthJointIdentityUniformCosts.source_bound_with_resources setup codec checks caps bounded
    (PqxdhDeploymentServerAuth.serverAuthAdversary setup codec route bounds mode adversary c) (totalCap caps bounds budget)
    budget.finish
    (fun input => by
      simpa only [PqxdhDeploymentServerAuth.serverAuthAdversary, PqxdhRegistrationR1Authentication.unitWork,
        IsTotalQueryBound, isQueryBound_map_iff] using reductionCaps.total input)
    (fun input => (PqxdhRegistrationR1Authentication.unit_queries work input _ _).mpr (reductionCaps.finish input))
    signatureFallback
  exact ⟨PqxdhServerAuthPublicationResources.reduction_bills setup codec checks caps bounded
    (PqxdhDeploymentServerAuth.serverAuthAdversary setup codec route bounds mode adversary c) (coinCap caps bounds budget)
    budget.accept (romCap budget) (hashCap budget)
    ((PqxdhRegistrationR1Authentication.budget_iff work budget.accept (romCap budget) (hashCap budget)).mpr
      reductionCaps.source)
    (fun input => (PqxdhRegistrationR1Authentication.unit_queries work input _ _).mpr (reductionCaps.coins input))
    (PqxdhServerAuthSessionRecord.observers codec budget.accept) a1Fallback,
    joint.2.1, joint.2.2.1, joint.2.2.2.1, joint.2.2.2.2⟩

end A1

section Collect

/-- The bills of the per-target reductions of the CE-12 headlines at the deployment budget: the certified raw-ordinal KEM adversary of `kemLoss`, the HMAC-PRF and key-schedule reductions of `slotLoss`, the predict-then-compare adversary of `β_g`, and the chain, integrity and privacy reductions of `authLoss_g` and `recLoss_g` at `BI_g`. -/
structure TargetBills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (caps : KemCaps) (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (runtime : A) :
    Prop where
  kem : ∀ (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity),
    (PqxdhRegistrationJointKemRawCertified.adversary setup codec checks ensureInit none
        (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (compileFull setup codec route bounds mode adversary) runtime budget.create (selectedKem budget g)
        g.1.val).MakesAtMostQueries
      ((qInit + 32) + (caps.keygenCost * budget.create + PqxdhRegistrationJointKemPostBills.uniformCap caps budget.create
        budget.finish (PqxdhRegistrationJointOpenUniform.total caps (PqxdhDeploymentCompileCaps.transported bounds budget))
        budget.accept))
      (caps.decapsBase * budget.finish) budget.finish
      (PqxdhRegistrationJointKemPostBills.uniformCap caps budget.create budget.finish
        (PqxdhRegistrationJointOpenUniform.total caps (PqxdhDeploymentCompileCaps.transported bounds budget))
        budget.accept)
      (caps.decapsBase * budget.finish) budget.finish
  slot : ∀ (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity),
    (∀ slot ∈ Finset.range 2, PqxdhRegistrationJointKemKeyTransfer.PrfBills setup.hmac
      (PqxdhRegistrationJointKemRootExpand.rootClient (Reader := Reader) setup codec checks ensureInit none
        (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (compileFull setup codec route bounds mode adversary) runtime budget.create (selectedKem budget g) g.1.val) slot
      (PqxdhRegistrationJointKemRootCosts.rootBill caps qInit none budget.create
        (PqxdhDeploymentCompileCaps.transported bounds budget))) ∧
    ∀ k ∈ Finset.range 2, PqxdhServerAuthEntryFactor.EntryComponentBills setup.source setup.hmac
      (PqxdhRegistrationJointKemSecondEntry.entryDk (Reader := Reader) setup codec checks ensureInit none
        (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (compileFull setup codec route bounds mode adversary) runtime budget.create (selectedKem budget g) g.1.val k)
      (PqxdhRegistrationJointKemRootCosts.rootBill caps qInit none budget.create
        (PqxdhDeploymentCompileCaps.transported bounds budget) + 216)
  beta : ∀ g : Fin budget.accept × Fin budget.capacity,
    (PqxdhDeploymentHeadlineAnomaly.ptc setup.kem (PqxdhDeploymentIdealAnomalyGuesser.anomalyGuesser setup codec route
      checks (Target.ofCE budget g) ensureInit 0 runtime bounds mode adversary)).MakesAtMostQueries
        (guessBill caps qInit budget bounds) 0 (budget.finish + 1) 0 0 0
  auth : ∀ (g : Fin budget.accept × Fin budget.capacity) (event : View 2 (EnvG KemSK budget) X → Bool),
    PqxdhRecordLiftIdeal.RecordAuthBounded 2
      (PqxdhRecordLiftChainLift.chainReduction setup codec route setup.serverKeyId bounds 2)
      (PqxdhRecordLiftCtx.ctxReduction setup codec route setup.serverKeyId bounds) PqxdhRecordLiftChainBills.chainBills
      PqxdhRecordLiftCtxBills.ctxBills
      (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime) mode adversary
      (fun view => pure (event view)) budget (inputG caps qInit budget bounds)
  records : ∀ (g : Fin budget.accept × Fin budget.capacity) (event : View 2 (EnvG KemSK budget) X → Bool),
    PqxdhRecordLiftIdeal.RecordBounded 2
      (PqxdhRecordLiftChainLift.chainReduction setup codec route setup.serverKeyId bounds 2)
      (PqxdhRecordLiftCtx.ctxReduction setup codec route setup.serverKeyId bounds)
      (PqxdhRecordLiftCtxPriv.privReduction setup codec route setup.serverKeyId bounds)
      PqxdhRecordLiftChainBills.chainBills PqxdhRecordLiftCtxBills.ctxBills PqxdhRecordLiftCtxPrivBills.privBills
      (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime) mode adversary
      (fun view => pure (event view)) budget (inputG caps qInit budget bounds)

/-- The bills of every CE-A1 reduction `R_c` (`ε_A1`) at the CE-A1 caps transported from the budget. -/
def A1Bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (caps : KemCaps) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    Prop :=
  ∀ c : ℕ, PqxdhServerAuthCommonAuthentication.ReductionBills setup codec checks caps
    (PqxdhDeploymentServerAuth.serverAuthAdversary setup codec route bounds mode adversary c)
    (coinCap caps bounds budget) budget.accept (romCap budget) (hashCap budget) (totalCap caps bounds budget)
    budget.finish a1Fallback signatureFallback

/-- The bills of every CE-A2pub reduction (`ε_A2pub`), for every identity position. -/
def A2Bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (caps : KemCaps) (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (runtime : A)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    Prop :=
  ∀ target : Fin (budget.create + 1),
    (∀ jointPublic : PqxdhJointIdentity.PublicIdentity,
      (PqxdhDeploymentProvenance.reduction setup codec checks route ensureInit bounds mode adversary budget.create runtime
        identityFallback ordinaryFallback target jointPublic).IsQueryBoundP (PqxdhJointIdentityFamily.IsClass .sign)
        (3 * budget.bundle) ∧
      (PqxdhDeploymentProvenance.reduction setup codec checks route ensureInit bounds mode adversary budget.create runtime
        identityFallback ordinaryFallback target jointPublic).IsQueryBoundP (PqxdhJointIdentityFamily.IsClass .staticDh)
        (budget.finish + budget.accept) ∧
      (PqxdhDeploymentProvenance.reduction setup codec checks route ensureInit bounds mode adversary budget.create runtime
        identityFallback ordinaryFallback target jointPublic).IsQueryBoundP (PqxdhJointIdentityFamily.IsClass .uniform)
        (32 * budget.create + PqxdhRegistrationJointIdentityUniform.total caps qInit
          (PqxdhDeploymentCompileCaps.transported bounds budget))) ∧
    (PqxdhJointIdentity.game setup.joint (PqxdhDeploymentProvenance.reduction setup codec checks route ensureInit bounds
      mode adversary budget.create runtime identityFallback ordinaryFallback target)).IsTotalQueryBound
      (32 * (budget.create + 1) + PqxdhRegistrationJointIdentityUniform.total caps qInit
        (PqxdhDeploymentCompileCaps.transported bounds budget))

/-- The bills of every identity-collision reduction `collider` (`ε_inj`), for every identity position. -/
def InjBills (setup : Setup baseSpec KemSK) (budget : Budget) : Prop :=
  ∀ target : Fin (budget.create + 1),
    (∀ jointPublic, (PqxdhDeploymentServerAuthInjective.collider setup.joint budget.create target jointPublic).IsQueryBoundP
      (PqxdhJointIdentityFamily.IsClass .uniform) (32 * budget.create)) ∧
    (∀ jointPublic, (PqxdhDeploymentServerAuthInjective.collider setup.joint budget.create target jointPublic).IsQueryBoundP
      (PqxdhJointIdentityFamily.IsClass .sign) 0) ∧
    (∀ jointPublic, (PqxdhDeploymentServerAuthInjective.collider setup.joint budget.create target jointPublic).IsQueryBoundP
      (PqxdhJointIdentityFamily.IsClass .staticDh) 0) ∧
    (PqxdhJointIdentity.game setup.joint (PqxdhDeploymentServerAuthInjective.collider setup.joint budget.create
      target)).IsTotalQueryBound (32 * (budget.create + 1))

/-- The bill of the encapsulate-and-compare adversary `pairAdversary` of `pair_cp_le`. -/
def PairBills (setup : Setup baseSpec KemSK) (caps : KemCaps) : Prop :=
  (PqxdhDeploymentHeadlineCollision.pairAdversary setup.kem).MakesAtMostQueries 0 0 0 caps.encapsUniform
    caps.encapsBase 0

/-- `HeadlineBills` (design-v2 section 9): the bills of every reduction behind the CE-12 headline terms at the deployment budget. -/
structure HeadlineBills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (caps : KemCaps) (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (runtime : A)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    Prop where
  target : TargetBills setup codec checks route caps ensureInit qInit bounds mode adversary budget runtime
  a1 : A1Bills setup codec checks route caps bounds mode adversary budget a1Fallback signatureFallback
  a2 : A2Bills setup codec checks route caps ensureInit qInit bounds mode adversary budget runtime identityFallback
    ordinaryFallback
  inj : InjBills setup budget
  pair : PairBills setup caps

/-- The per-target bills hold. Premises: `SourceFullCorrect`, `KemBound`, `initBound` and the budget. -/
theorem target_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    TargetBills setup codec checks route caps ensureInit qInit bounds mode adversary budget runtime where
  kem event claim g := PqxdhDeploymentKemTransfer.kem_transfer_bills setup codec checks route caps bounded ensureInit qInit
    initBound bounds mode adversary budget respects event claim g runtime
  slot event claim g := PqxdhRegistrationJointKemKeyTransfer.allIdeal_bills setup codec checks caps bounded ensureInit
    qInit initBound none (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
    (compileFull setup codec route bounds mode adversary) (PqxdhDeploymentCompileCaps.transported bounds budget)
    (PqxdhDeploymentCompileCaps.compile_full_certified setup codec route bounds mode adversary budget respects) runtime
    budget.create (selectedKem budget g) g.1.val
  beta g := PqxdhDeploymentHeadlineGuessBill.ptc_bills setup codec route checks caps bounded ensureInit qInit initBound
    bounds mode adversary budget respects g runtime
  auth g event := PqxdhDeploymentHeadlineBills.auth_bills setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds mode adversary budget respects g runtime fallback event
  records g event := PqxdhDeploymentHeadlineBills.records_bills setup codec checks route correct caps bounded ensureInit
    qInit initBound bounds mode adversary budget respects g runtime fallback event

/-- The CE-A1 bills hold for every creation index. Premises: `KemBound` and the budget. -/
theorem a1_bills_all (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) (caps : KemCaps)
    (bounded : KemBound setup caps) (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    A1Bills setup codec checks route caps bounds mode adversary budget a1Fallback signatureFallback :=
  fun c => a1_bills setup codec checks caps bounded route bounds mode adversary budget respects c a1Fallback
    signatureFallback

/-- The CE-A2pub bills hold for every identity position. Premises: `KemBound`, `initBound` and the budget. -/
theorem a2_bills_all (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (caps : KemCaps) (bounded : KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    A2Bills setup codec checks route caps ensureInit qInit bounds mode adversary budget runtime identityFallback
      ordinaryFallback :=
  fun target => PqxdhDeploymentProvenance.a2_bills setup codec checks route ensureInit qInit initBound caps bounded bounds
    mode adversary budget respects runtime identityFallback ordinaryFallback target

/-- The identity-collision bills hold for every identity position (no premise). -/
theorem inj_bills (setup : Setup baseSpec KemSK) (budget : Budget) : InjBills setup budget :=
  fun target => PqxdhDeploymentServerAuthInjective.collider_bills setup.joint budget.create target

/-- `HeadlineBills` holds. Premises: `SourceFullCorrect`, `KemBound`, `initBound` and `budget.Respects adversary`. -/
theorem headline_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    HeadlineBills setup codec checks route caps ensureInit qInit bounds mode adversary budget runtime identityFallback
      ordinaryFallback a1Fallback signatureFallback where
  target := target_bills setup codec checks route correct caps bounded ensureInit qInit initBound bounds mode adversary
    budget respects runtime fallback
  a1 := a1_bills_all setup codec checks caps bounded route bounds mode adversary budget respects a1Fallback
    signatureFallback
  a2 := a2_bills_all setup codec checks route caps bounded ensureInit qInit initBound bounds mode adversary budget respects
    runtime identityFallback ordinaryFallback
  inj := inj_bills setup budget
  pair := PqxdhDeploymentHeadlineBills.pair_bills setup caps bounded

end Collect

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBillsFull

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBillsFull.a1_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBillsFull.a1_bills

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBillsFull.target_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBillsFull.target_bills

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBillsFull.a1_bills_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBillsFull.a1_bills_all

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBillsFull.a2_bills_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBillsFull.a2_bills_all

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBillsFull.inj_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBillsFull.inj_bills

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBillsFull.headline_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBillsFull.headline_bills
