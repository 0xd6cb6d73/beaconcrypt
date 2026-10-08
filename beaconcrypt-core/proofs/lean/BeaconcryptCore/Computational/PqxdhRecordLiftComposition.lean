-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftChainLift
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills

/-!
# Record-lift composition: `record_lift` from `chain_lift` and the two halves of `ctx_lift` (items 4 and 5, stage S5)

**Integrity form (unconditional).** `record_auth_lift` proves the target `PqxdhRecordLiftIdeal.RecordAuthLiftTarget` (both forms, zero aliasing and refusal terms) for the explicit chain reductions `PqxdhRecordLiftChainLift.chainReduction` with the bills `PqxdhRecordLiftChainBills.chainBills` and the explicit CTX reductions `PqxdhRecordLiftCtx.ctxReduction` with the bills `PqxdhRecordLiftCtxBills.ctxBills`: in either observation mode, for every environment with `Frame`, every adversary within its `Budget` and every cache-free decision on the permitted view, the real record world `realChains` and the integrity-ideal world `idealAuth` differ by at most the sum of the chain loss (Extract-on-`uniform32` plus HMAC-PRF per ordered hybrid index) and the integrity loss (IND$ validation, `qHash/2^128`, twice the attempt-indexed INT-CTXT sum and `qRaw/2^512` per target key), every advantage with coefficient one. It is `PqxdhRecordLiftIdeal.recordAuthLiftBool_of_parts` applied to `PqxdhRecordLiftChainLift.chain_lift_bool` and the Boolean half of `PqxdhRecordLiftCtxBills.ctxAuthLiftTarget`; `record_auth_lift_terms` restates it for arbitrary alias and refusal terms.

**Privacy form (conditional on the privacy half).** `PqxdhRecordLiftIdeal.CtxPrivLiftStatement` (the privacy half of `ctx_lift`, decision D1) is not yet proved. `record_lift_of_priv` and `record_lift_bool_of_priv` take it as an explicit hypothesis parameter `privLift` for an arbitrary privacy reduction family `privacy` with bills `privacyBills`, and give the full target `PqxdhRecordLiftIdeal.RecordLiftTarget` (the real world against `idealRecords`, adding the privacy loss in mode P) for the same chain and integrity reductions; `ctx_lift_of_priv` gives `PqxdhRecordLiftIdeal.CtxLiftTarget` the same way. The hypothesis is a theorem parameter, not an assumption or contract: nothing is claimed about the privacy half, and the full `record_lift` follows by instantiating `privLift` once the privacy track proves `CtxPrivLiftStatement`. `record_lift_O` is the mode-O instance, which needs no privacy hypothesis because `idealRecords` is `idealAuth` in mode O (`PqxdhRecordLiftIdeal.idealRecords_O`) and the record loss has no privacy summand there.

**Contracts.** The theorems that apply `chain_lift_bool` use `SourceFullCorrect` as the explicit premise of the target (it is the first premise of `RecordAuthLiftBool` and `RecordLiftBool`); through `ctxAuthLiftTarget` they use functional AEAD correctness (`aead_open_seal` and `aeadSeal_tag_length` of `Pqxdh.Crypto`), the modified-nonce AEAD IND$ and INT-CTXT games and the HMAC-PRF and Extract-on-`uniform32` games as advantage terms of the losses, and the BLAKE2b random-oracle model as the world model; `ctx_lift_of_priv` uses only the CTX part of this list. These are the contracts of `chain_lift` and `ctxAuthLiftTarget`, all from the brief's H-7 list; no assumption or contract is added. New Claude work.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftComposition
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds Budget)
open PqxdhServerAuthExperiment (Setup Codec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (serverKid : Aeneas.Std.U64) (bounds : FreshBounds)

/-- The integrity record lift, Boolean form, with zero aliasing and refusal terms, the explicit chain and integrity reductions and their explicit bills. Contracts: those of `chain_lift_bool` (`SourceFullCorrect`) and `ctxAuthLiftTarget`. -/
theorem record_auth_lift_bool (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    RecordAuthLiftBool setup codec route serverKid bounds n hmac fallback
      (PqxdhRecordLiftChainLift.chainReduction setup codec route serverKid bounds n)
      (PqxdhRecordLiftCtx.ctxReduction setup codec route serverKid bounds) PqxdhRecordLiftChainBills.chainBills
      PqxdhRecordLiftCtxBills.ctxBills noTerm noTerm noTerm :=
  recordAuthLiftBool_of_parts setup codec route serverKid bounds n hmac fallback _ _ _ _ _ _ _
    (PqxdhRecordLiftChainLift.chain_lift_bool setup codec route serverKid bounds n hmac)
    (PqxdhRecordLiftCtxBills.ctxAuthLiftTarget setup codec route serverKid bounds fallback).1

/-- **The integrity record lift (H-5 `record_lift` to `idealAuth`, decision D1), delivered.** The target `RecordAuthLiftTarget` (Boolean and event forms, zero aliasing and refusal terms) for the explicit chain reductions `chainReduction` with `chainBills` and the explicit integrity reductions `ctxReduction` with `ctxBills`, for every slot count, HMAC, forgery fallback and setup. Contracts: those of `chain_lift` (`SourceFullCorrect`) and `ctxAuthLiftTarget`. -/
theorem record_auth_lift (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    RecordAuthLiftTarget setup codec route serverKid bounds n hmac fallback
      (PqxdhRecordLiftChainLift.chainReduction setup codec route serverKid bounds n)
      (PqxdhRecordLiftCtx.ctxReduction setup codec route serverKid bounds) PqxdhRecordLiftChainBills.chainBills
      PqxdhRecordLiftCtxBills.ctxBills :=
  recordAuthLiftStatement_of_bool setup codec route serverKid bounds n hmac fallback _ _ _ _ _ _ _
    (record_auth_lift_bool setup codec route serverKid bounds n hmac fallback)

/-- The integrity record lift for arbitrary aliasing and refusal terms: nonnegative extra terms only weaken the zero-term target. Contracts: those of `record_auth_lift`. -/
theorem record_auth_lift_terms (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (aliasing chainRefusal ctxRefusal : BillInput → ℝ≥0∞) :
    RecordAuthLiftStatement setup codec route serverKid bounds n hmac fallback
      (PqxdhRecordLiftChainLift.chainReduction setup codec route serverKid bounds n)
      (PqxdhRecordLiftCtx.ctxReduction setup codec route serverKid bounds) PqxdhRecordLiftChainBills.chainBills
      PqxdhRecordLiftCtxBills.ctxBills aliasing chainRefusal ctxRefusal :=
  recordAuthLiftStatement_of_bool setup codec route serverKid bounds n hmac fallback _ _ _ _ _ _ _
    (recordAuthLiftBool_of_parts setup codec route serverKid bounds n hmac fallback _ _ _ _ _ _ _
      ((PqxdhRecordLiftChainLift.chain_lift_terms setup codec route serverKid bounds n hmac aliasing chainRefusal).1)
      ((PqxdhRecordLiftCtxBills.ctxAuthLiftStatement setup codec route serverKid bounds fallback ctxRefusal).1))

/-- `ctx_lift` (H-5, item 4), given the privacy half as the hypothesis parameter `privLift` for any privacy reduction family and bills: the target `CtxLiftTarget` (the chain-ideal world against `idealRecords`, both forms, zero refusal term) for the explicit integrity reductions `ctxReduction` with `ctxBills`. Contracts: those of `ctxAuthLiftTarget`; `privLift` is a parameter, not an assumption. -/
theorem ctx_lift_of_priv (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (privacy : CtxReduction n) (privacyBills : CtxBills)
    (privLift : CtxPrivLiftStatement setup codec route serverKid bounds n privacy privacyBills) :
    CtxLiftTarget setup codec route serverKid bounds n fallback
      (PqxdhRecordLiftCtx.ctxReduction setup codec route serverKid bounds) privacy PqxdhRecordLiftCtxBills.ctxBills
      privacyBills :=
  ctxLiftStatement_of_bool setup codec route serverKid bounds n fallback _ _ _ _ _
    (ctxLiftBool_of_parts setup codec route serverKid bounds n fallback _ _ _ _ _
      (PqxdhRecordLiftCtxBills.ctxAuthLiftTarget setup codec route serverKid bounds fallback).1 privLift.1)

/-- `record_lift`, Boolean form, given the Boolean privacy half as the hypothesis parameter `privLift`: zero aliasing and refusal terms, the explicit chain and integrity reductions with their bills, and any privacy reductions with their bills. Contracts: those of `record_auth_lift_bool`; `privLift` is a parameter, not an assumption. -/
theorem record_lift_bool_of_priv (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (privacy : CtxReduction n) (privacyBills : CtxBills)
    (privLift : CtxPrivLiftBool setup codec route serverKid bounds n privacy privacyBills) :
    RecordLiftBool setup codec route serverKid bounds n hmac fallback
      (PqxdhRecordLiftChainLift.chainReduction setup codec route serverKid bounds n)
      (PqxdhRecordLiftCtx.ctxReduction setup codec route serverKid bounds) privacy PqxdhRecordLiftChainBills.chainBills
      PqxdhRecordLiftCtxBills.ctxBills privacyBills noTerm noTerm noTerm :=
  recordLiftBool_of_parts setup codec route serverKid bounds n hmac fallback _ _ _ _ _ _ _ _ _
    (PqxdhRecordLiftChainLift.chain_lift_bool setup codec route serverKid bounds n hmac)
    (PqxdhRecordLiftCtxBills.ctxAuthLiftTarget setup codec route serverKid bounds fallback).1 privLift

/-- **`record_lift` (H-5), given the privacy half.** With the privacy half `CtxPrivLiftStatement` as the hypothesis parameter `privLift` (for any privacy reduction family `privacy` and bills `privacyBills`), the full target `RecordLiftTarget` holds (Boolean and event forms, zero aliasing and refusal terms) for the explicit chain reductions `chainReduction` with `chainBills`, the explicit integrity reductions `ctxReduction` with `ctxBills`, and `privacy` with `privacyBills`. Contracts: those of `record_auth_lift`; `privLift` is a parameter, not an assumption. -/
theorem record_lift_of_priv (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (privacy : CtxReduction n) (privacyBills : CtxBills)
    (privLift : CtxPrivLiftStatement setup codec route serverKid bounds n privacy privacyBills) :
    RecordLiftTarget setup codec route serverKid bounds n hmac fallback
      (PqxdhRecordLiftChainLift.chainReduction setup codec route serverKid bounds n)
      (PqxdhRecordLiftCtx.ctxReduction setup codec route serverKid bounds) privacy PqxdhRecordLiftChainBills.chainBills
      PqxdhRecordLiftCtxBills.ctxBills privacyBills :=
  recordLiftStatement_of_bool setup codec route serverKid bounds n hmac fallback _ _ _ _ _ _ _ _ _
    (record_lift_bool_of_priv setup codec route serverKid bounds n hmac fallback privacy privacyBills privLift.1)

/-- `record_lift` in observation mode O, with no privacy hypothesis: for every environment with `Frame`, adversary within its budget and cache-free decision, the real world and `idealRecords` (which is `idealAuth` in mode O) differ by at most the record loss, which has no privacy summand in mode O, so the privacy reductions do not enter it. Contracts: those of `record_auth_lift_bool`. -/
theorem record_lift_O (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (privacy : CtxReduction n)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac) {E X : Type} (env : Environment n E)
    (startup : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance)
    (adversary : OracleComp (ModeSpec .O) X) (budget : Budget) (respects : budget.Respects adversary)
    (decision : View n E X → ProbComp Bool) (cost : Nat) (costBound : ∀ view, (decision view).IsTotalQueryBound cost) :
    ENNReal.ofReal
        ((realChains setup codec route env serverKid bounds .O adversary >>= fun result =>
            decision (chainView result)).boolDistAdvantage
          (idealRecords setup codec route env serverKid bounds .O adversary >>= fun result =>
            decision (ctxView result))) ≤
      recordLoss setup codec n hmac fallback (PqxdhRecordLiftChainLift.chainReduction setup codec route serverKid bounds n)
        (PqxdhRecordLiftCtx.ctxReduction setup codec route serverKid bounds) privacy PqxdhRecordLiftCtxBills.ctxBills
        noTerm noTerm noTerm env .O adversary decision budget ⟨budget, startup, allowance, bounds, n, cost⟩ := by
  have bound := (record_auth_lift_bool setup codec route serverKid bounds n hmac fallback correct env startup allowance
    framed .O adversary budget respects decision cost costBound).1
  rw [idealRecords_O]
  calc _ ≤ _ := bound
    _ = _ := by simp only [recordAuthLoss, recordLoss, reduceCtorEq, ite_false, add_zero]

end BeaconcryptCore.Computational.PqxdhRecordLiftComposition

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftComposition.record_auth_lift_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftComposition.record_auth_lift_bool

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftComposition.record_auth_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftComposition.record_auth_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftComposition.record_auth_lift_terms' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftComposition.record_auth_lift_terms

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftComposition.ctx_lift_of_priv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftComposition.ctx_lift_of_priv

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftComposition.record_lift_bool_of_priv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftComposition.record_lift_bool_of_priv

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftComposition.record_lift_of_priv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftComposition.record_lift_of_priv

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftComposition.record_lift_O' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftComposition.record_lift_O
