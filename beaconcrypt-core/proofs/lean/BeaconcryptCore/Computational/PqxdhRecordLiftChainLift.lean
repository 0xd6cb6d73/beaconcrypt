-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftChainBills
import BeaconcryptCore.Computational.PqxdhRecordLiftChainAlias

/-! `chain_lift` (item 5, H-5) as fixed by `PqxdhRecordLiftIdeal`: the delivered target `ChainLiftTarget` for the explicit reduction family `chainReduction` (the full76 observers of the ordered chain hybrid, `PqxdhRecordLiftChainHybrid.observerAt`) and the explicit bills `PqxdhRecordLiftChainBills.chainBills`. For every environment with `Frame`, every adversary within its `Budget`, and every decision on the permitted view and the final shared BLAKE2b cache (Boolean form) or every Boolean event of them (event form), the real record world `realChains` and the chain-ideal world `idealChains` differ by at most the sum over the `hops n budget = (sends + 51 * receives) * (n * 2)` ordered indices of the Extract-on-`uniform32` plus HMAC-PRF advantages of the explicit observers, each with coefficient one, with zero aliasing and refusal terms (decision D3, `PqxdhRecordLiftChainAlias`); every observer makes at most `2 * programCoins + 44 + cost` uniform queries. The bound is two-sided (an absolute difference). Contract: `SourceFullCorrect` only. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftChainLift
open PqxdhRecordLiftInterface
open PqxdhServerAuthExperiment (Setup Codec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The explicit chain reduction family: for every environment, adversary, chain decision and budget, the full76 observer of each ordered hybrid index, built from the actual compiled protocol, the actual seed or parent cut and the decision. -/
noncomputable def chainReduction (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Aeneas.Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (n : Nat) : PqxdhRecordLiftIdeal.ChainReduction n :=
  fun env mode adversary decision budget step =>
    PqxdhRecordLiftChainHybrid.observerAt setup codec route env serverKid bounds mode adversary decision budget step

variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (serverKid : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)

/-- `chain_lift`, Boolean form, with zero aliasing and refusal terms, the explicit reductions and the explicit bills. Contract: `SourceFullCorrect`. -/
theorem chain_lift_bool (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512) :
    PqxdhRecordLiftIdeal.ChainLiftBool setup codec route serverKid bounds n hmac
      (chainReduction setup codec route serverKid bounds n) PqxdhRecordLiftChainBills.chainBills
      PqxdhRecordLiftIdeal.noTerm PqxdhRecordLiftIdeal.noTerm := by
  intro correct E X env startup allowance framed mode adversary budget respects decision cost decisionBound
  refine ⟨?_, fun step context output => PqxdhRecordLiftChainBills.observerAt_total setup codec route env startup
    allowance framed serverKid bounds mode budget adversary respects decision cost decisionBound step context output⟩
  simpa only [PqxdhRecordLiftIdeal.noTerm, add_zero, chainReduction] using PqxdhRecordLiftChainHybrid.chain_loss setup codec route env
    serverKid bounds mode adversary hmac correct budget respects decision

/-- `chain_lift` (H-5, item 5), delivered: the target `ChainLiftTarget` of `PqxdhRecordLiftIdeal` (Boolean and event forms, zero aliasing and refusal terms) for the explicit reductions `chainReduction` and bills `chainBills`, for every slot count, HMAC and setup. Contract: `SourceFullCorrect`. -/
theorem chain_lift (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512) :
    PqxdhRecordLiftIdeal.ChainLiftTarget setup codec route serverKid bounds n hmac
      (chainReduction setup codec route serverKid bounds n) PqxdhRecordLiftChainBills.chainBills :=
  PqxdhRecordLiftIdeal.chainLiftStatement_of_bool setup codec route serverKid bounds n hmac _ _ _ _
    (chain_lift_bool setup codec route serverKid bounds n hmac)

/-- `chain_lift` with any explicit aliasing and refusal terms: the zero terms of the target only strengthen the statement. Contract: `SourceFullCorrect`. -/
theorem chain_lift_terms (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (aliasing refusal : PqxdhRecordLiftIdeal.BillInput → ℝ≥0∞) :
    PqxdhRecordLiftIdeal.ChainLiftStatement setup codec route serverKid bounds n hmac
      (chainReduction setup codec route serverKid bounds n) PqxdhRecordLiftChainBills.chainBills aliasing refusal :=
  PqxdhRecordLiftChainAlias.statement_of_target setup codec route serverKid bounds n hmac _ _
    (chain_lift setup codec route serverKid bounds n hmac) aliasing refusal

end BeaconcryptCore.Computational.PqxdhRecordLiftChainLift

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainLift.chain_lift_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainLift.chain_lift_bool

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainLift.chain_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainLift.chain_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainLift.chain_lift_terms' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainLift.chain_lift_terms
