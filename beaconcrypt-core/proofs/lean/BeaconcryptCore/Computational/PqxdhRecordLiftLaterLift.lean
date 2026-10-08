-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain
import BeaconcryptCore.Computational.PqxdhRecordLiftLaterPriv
import BeaconcryptCore.Computational.PqxdhRecordLiftLaterHiding

/-!
# Record-lift later lifts: the composed R6 forms (items 4 and 5, stage S6, R6)

**Statements.** The later forms of the composed record-lift targets, for the explicit reductions and bills of `PqxdhRecordLiftLaterChain`, `PqxdhRecordLiftLaterCtx` and `PqxdhRecordLiftLaterPriv`, with zero aliasing and refusal terms: `later_record_auth_lift` proves `LaterRecordAuthLiftTarget` (the later real world against `laterIdealAuth`, in either observation mode: the later chain loss plus the later integrity loss), `later_ctx_lift` proves `LaterCtxLiftTarget` (the later chain-ideal world against `laterIdealRecords`: the later integrity loss and, in mode P, the later privacy loss) and `later_record_lift` proves `LaterRecordLiftTarget` (the later real world against `laterIdealRecords`: all three), each two-sided in Boolean and event form, every term with coefficient one, by the composition lemmas of `PqxdhRecordLiftLaterTargets`. Together with `PqxdhRecordLiftLaterChain.later_chain_lift`, `PqxdhRecordLiftLaterCtx.later_ctx_auth_lift`, `PqxdhRecordLiftLaterPriv.later_ctx_priv_lift` and `PqxdhRecordLiftLaterHiding.later_idealRecords_hiding` these are the R6 forms of the brief's lifts and hiding. No later origin, binding or authentication fact is stated: the later mode claims confidentiality only, and run-phase origin carries over to the later real world by `PqxdhRecordLiftLaterWorlds.laterReal_event`. The record lifts are distributional facts about the later worlds, used for confidentiality; `later_record_auth_lift` is the integrity-ideal part of `later_record_lift`, not an authentication claim.

**Contracts.** No theorem of this module has an assumption or contract hypothesis. `later_record_auth_lift_bool`, `later_record_auth_lift`, `later_record_lift_bool` and `later_record_lift` use `SourceFullCorrect` (a premise of the targets), functional AEAD correctness (`aead_open_seal`, `aeadSeal_tag_length`), the Extract-on-`uniform32`, HMAC-PRF, IND$ and INT-CTXT games as advantage terms and the BLAKE2b random-oracle model; `later_ctx_lift_bool` and `later_ctx_lift` the same without `SourceFullCorrect`, Extract and HMAC-PRF (per-theorem closure probe). New Claude work; nothing adapted from Codex WIP.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftLaterLift
open PqxdhRecordLiftInterface PqxdhRecordLiftLaterTargets
open PqxdhRecordLiftLaterChain (laterChainReduction laterChainBills later_chain_lift_bool)
open PqxdhRecordLiftLaterCtx (laterCtxReduction laterCtxBills later_ctx_auth_lift_bool)
open PqxdhRecordLiftLaterPriv (laterPrivReduction laterPrivBills later_ctx_priv_lift_bool)
open PqxdhServerAuthExperiment (Setup Codec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (serverKid : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)

/-- The later integrity record lift, Boolean form: the later chain lift at the cache-free decision and the later integrity half, by the triangle inequality, every term with coefficient one. Contract: `SourceFullCorrect`. -/
theorem later_record_auth_lift_bool (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    LaterRecordAuthLiftBool setup codec route serverKid bounds n hmac fallback
      (laterChainReduction setup codec route serverKid bounds n) (laterCtxReduction setup codec route serverKid bounds)
      laterChainBills laterCtxBills laterNoTerm laterNoTerm laterNoTerm :=
  laterRecordAuthLiftBool_of_parts setup codec route serverKid bounds n hmac fallback _ _ _ _ _ _ _
    (later_chain_lift_bool setup codec route serverKid bounds n hmac)
    (later_ctx_auth_lift_bool setup codec route serverKid bounds n fallback)

/-- **The later integrity record lift (R6), delivered.** `LaterRecordAuthLiftTarget` (Boolean and event forms, zero aliasing and refusal terms): in either observation mode, the later real world and `laterIdealAuth` differ by at most the later chain loss plus the later integrity loss, for the explicit reductions and bills. A distributional fact; the later mode claims no authentication. Contract: `SourceFullCorrect`. -/
theorem later_record_auth_lift (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    LaterRecordAuthLiftTarget setup codec route serverKid bounds n hmac fallback
      (laterChainReduction setup codec route serverKid bounds n) (laterCtxReduction setup codec route serverKid bounds)
      laterChainBills laterCtxBills :=
  laterRecordAuthLiftStatement_of_bool setup codec route serverKid bounds n hmac fallback _ _ _ _ _ _ _
    (later_record_auth_lift_bool setup codec route serverKid bounds n hmac fallback)

/-- Later `ctx_lift`, Boolean form: the later integrity half and, in mode P, the later privacy half. -/
theorem later_ctx_lift_bool (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    LaterCtxLiftBool setup codec route serverKid bounds n fallback (laterCtxReduction setup codec route serverKid bounds)
      (laterPrivReduction setup codec route serverKid bounds) laterCtxBills laterPrivBills laterNoTerm :=
  laterCtxLiftBool_of_parts setup codec route serverKid bounds n fallback _ _ _ _ _
    (later_ctx_auth_lift_bool setup codec route serverKid bounds n fallback)
    (later_ctx_priv_lift_bool setup codec route serverKid bounds n)

/-- **Later `ctx_lift` (R6, item 4), delivered.** `LaterCtxLiftTarget` (Boolean and event forms, zero refusal term): the later chain-ideal world and `laterIdealRecords` differ by at most the later integrity loss and, in mode P, the later privacy loss, for the explicit reductions and bills. -/
theorem later_ctx_lift (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    LaterCtxLiftTarget setup codec route serverKid bounds n fallback (laterCtxReduction setup codec route serverKid bounds)
      (laterPrivReduction setup codec route serverKid bounds) laterCtxBills laterPrivBills :=
  laterCtxLiftStatement_of_bool setup codec route serverKid bounds n fallback _ _ _ _ _
    (later_ctx_lift_bool setup codec route serverKid bounds n fallback)

/-- Later `record_lift`, Boolean form: the later chain lift at the cache-free decision, the later integrity half and, in mode P, the later privacy half. Contract: `SourceFullCorrect`. -/
theorem later_record_lift_bool (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    LaterRecordLiftBool setup codec route serverKid bounds n hmac fallback
      (laterChainReduction setup codec route serverKid bounds n) (laterCtxReduction setup codec route serverKid bounds)
      (laterPrivReduction setup codec route serverKid bounds) laterChainBills laterCtxBills laterPrivBills laterNoTerm
      laterNoTerm laterNoTerm :=
  laterRecordLiftBool_of_parts setup codec route serverKid bounds n hmac fallback _ _ _ _ _ _ _ _ _
    (later_chain_lift_bool setup codec route serverKid bounds n hmac)
    (later_ctx_auth_lift_bool setup codec route serverKid bounds n fallback)
    (later_ctx_priv_lift_bool setup codec route serverKid bounds n)

/-- **Later `record_lift` (R6), delivered.** `LaterRecordLiftTarget` (Boolean and event forms, zero aliasing and refusal terms): the later real world and `laterIdealRecords` differ by at most the later chain loss, the later integrity loss and, in mode P, the later privacy loss, for the explicit reductions and bills. Contract: `SourceFullCorrect`. -/
theorem later_record_lift (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    LaterRecordLiftTarget setup codec route serverKid bounds n hmac fallback
      (laterChainReduction setup codec route serverKid bounds n) (laterCtxReduction setup codec route serverKid bounds)
      (laterPrivReduction setup codec route serverKid bounds) laterChainBills laterCtxBills laterPrivBills :=
  laterRecordLiftStatement_of_bool setup codec route serverKid bounds n hmac fallback _ _ _ _ _ _ _ _ _
    (later_record_lift_bool setup codec route serverKid bounds n hmac fallback)

end BeaconcryptCore.Computational.PqxdhRecordLiftLaterLift

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterLift.later_record_auth_lift_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterLift.later_record_auth_lift_bool

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterLift.later_record_auth_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterLift.later_record_auth_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterLift.later_ctx_lift_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterLift.later_ctx_lift_bool

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterLift.later_ctx_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterLift.later_ctx_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterLift.later_record_lift_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterLift.later_record_lift_bool

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterLift.later_record_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterLift.later_record_lift
