-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftComposition
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills

/-!
# Record lift: `ctx_lift` and `record_lift` (items 4 and 5, final assembly)

**Statements.** `ctx_lift` proves the target `PqxdhRecordLiftIdeal.CtxLiftTarget` (the brief's `ctx_lift`, both forms, zero refusal term) for the explicit integrity reductions `PqxdhRecordLiftCtx.ctxReduction` with the bills `PqxdhRecordLiftCtxBills.ctxBills` and the explicit privacy reductions `PqxdhRecordLiftCtxPriv.privReduction` with the bills `PqxdhRecordLiftCtxPrivBills.privBills`: in either observation mode, for every environment with `Frame`, every adversary within its `Budget` and every cache-free decision or event on the permitted view, the chain-ideal world `idealChains` and the record-ideal world `idealRecords` differ by at most the integrity loss summed over the target key indices plus, in mode P, the privacy loss (the IND$ advantage of `AdaptiveCtxPrivacyGuard.viewReduction`) summed over the same indices, every advantage with coefficient one. `record_lift` proves the target `PqxdhRecordLiftIdeal.RecordLiftTarget` (the brief's `record_lift`, both forms, zero aliasing and refusal terms) for the explicit chain reductions `PqxdhRecordLiftChainLift.chainReduction` with `PqxdhRecordLiftChainBills.chainBills` and the same CTX reductions: the real record world `realChains` and `idealRecords` differ by at most the chain loss plus the CTX loss. `record_lift_bool` is its Boolean form.

**Proof.** Each theorem instantiates the explicit privacy-half parameter of the corresponding conditional theorem of `PqxdhRecordLiftComposition` (`ctx_lift_of_priv`, `record_lift_bool_of_priv`, `record_lift_of_priv`) with `PqxdhRecordLiftCtxPrivBills.ctxPrivLiftStatement`, the privacy half `CtxPrivLiftStatement` proved for `privReduction` and `privBills`. No new argument.

**Contracts.** `record_lift_bool` and `record_lift` state targets whose first premise is `SourceFullCorrect` (the chain lift's contract); `ctx_lift` has no contract premise. Through `ctxAuthLiftTarget` all three use functional AEAD correctness (`aead_open_seal` and `aeadSeal_tag_length` of `Pqxdh.Crypto`), and through `ctxPrivLiftStatement` the tag length again; the modified-nonce AEAD IND$ and INT-CTXT games, and for `record_lift_bool` and `record_lift` also the HMAC-PRF and Extract-on-`uniform32` games, enter only as advantage terms of the losses; the BLAKE2b random-oracle model is the world model. All are on the brief's H-7 list; no assumption or contract is added. New Claude work.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLift
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal
open PqxdhDeploymentInterface (FreshBounds)
open PqxdhServerAuthExperiment (Setup Codec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (serverKid : Aeneas.Std.U64) (bounds : FreshBounds)

/-- **`ctx_lift` (H-5, item 4), delivered.** The target `CtxLiftTarget` (Boolean and event forms, zero refusal term): `idealChains` against `idealRecords` within the integrity loss of the explicit reductions `ctxReduction` (bills `ctxBills`) plus, in mode P, the privacy loss of the explicit reductions `privReduction` (bills `privBills`), for every slot count, forgery fallback and setup. Contracts: those of `ctxAuthLiftTarget` and `ctxPrivLiftStatement`. -/
theorem ctx_lift (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    CtxLiftTarget setup codec route serverKid bounds n fallback
      (PqxdhRecordLiftCtx.ctxReduction setup codec route serverKid bounds)
      (PqxdhRecordLiftCtxPriv.privReduction setup codec route serverKid bounds) PqxdhRecordLiftCtxBills.ctxBills
      PqxdhRecordLiftCtxPrivBills.privBills :=
  PqxdhRecordLiftComposition.ctx_lift_of_priv setup codec route serverKid bounds n fallback _ _
    (PqxdhRecordLiftCtxPrivBills.ctxPrivLiftStatement setup codec route serverKid bounds)

/-- `record_lift`, Boolean form, with zero aliasing and refusal terms and the explicit chain, integrity and privacy reductions with their bills. Contracts: `SourceFullCorrect` (the target's first premise) and those of `ctxAuthLiftTarget` and `ctxPrivLiftStatement`. -/
theorem record_lift_bool (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    RecordLiftBool setup codec route serverKid bounds n hmac fallback
      (PqxdhRecordLiftChainLift.chainReduction setup codec route serverKid bounds n)
      (PqxdhRecordLiftCtx.ctxReduction setup codec route serverKid bounds)
      (PqxdhRecordLiftCtxPriv.privReduction setup codec route serverKid bounds) PqxdhRecordLiftChainBills.chainBills
      PqxdhRecordLiftCtxBills.ctxBills PqxdhRecordLiftCtxPrivBills.privBills noTerm noTerm noTerm :=
  PqxdhRecordLiftComposition.record_lift_bool_of_priv setup codec route serverKid bounds n hmac fallback _ _
    (PqxdhRecordLiftCtxPrivBills.ctxPrivLiftStatement setup codec route serverKid bounds).1

/-- **`record_lift` (H-5, items 4 and 5), delivered.** The target `RecordLiftTarget` (Boolean and event forms, zero aliasing and refusal terms): `realChains` against `idealRecords` within the chain loss of the explicit reductions `chainReduction` (bills `chainBills`) plus the integrity loss of `ctxReduction` (bills `ctxBills`) plus, in mode P, the privacy loss of `privReduction` (bills `privBills`), for every slot count, HMAC, forgery fallback and setup. Contracts: `SourceFullCorrect` (the target's first premise) and those of `ctxAuthLiftTarget` and `ctxPrivLiftStatement`. -/
theorem record_lift (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    RecordLiftTarget setup codec route serverKid bounds n hmac fallback
      (PqxdhRecordLiftChainLift.chainReduction setup codec route serverKid bounds n)
      (PqxdhRecordLiftCtx.ctxReduction setup codec route serverKid bounds)
      (PqxdhRecordLiftCtxPriv.privReduction setup codec route serverKid bounds) PqxdhRecordLiftChainBills.chainBills
      PqxdhRecordLiftCtxBills.ctxBills PqxdhRecordLiftCtxPrivBills.privBills :=
  PqxdhRecordLiftComposition.record_lift_of_priv setup codec route serverKid bounds n hmac fallback _ _
    (PqxdhRecordLiftCtxPrivBills.ctxPrivLiftStatement setup codec route serverKid bounds)

end BeaconcryptCore.Computational.PqxdhRecordLift

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLift.ctx_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLift.ctx_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLift.record_lift_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLift.record_lift_bool

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLift.record_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLift.record_lift
