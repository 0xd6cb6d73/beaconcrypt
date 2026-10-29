-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordLiftBounds

/-! The actual reduction observers for the raw cursor client retain the original explicit chain and CTX bills. Every bound covers all possible primitive replies and adaptive continuations, including send refusal and failed writers. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordLiftReductions
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Environment EffectKind Frame)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhRecordLiftIdeal (View hops)
open CborRawRecordLiftBounds (client)
open AdaptiveCtxQueryBounds (SourceUniform SourceHash SourceSeal)
open AdaptiveCtxReceive (IsRawQuery)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}
section Bills
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : Frame env startup allowance) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (decision : View n E X → ProbComp Bool) (cost : Nat)
    (coins : ∀ view, (decision view).IsTotalQueryBound cost)

include framed respects coins in
/-- Each real chain observer draws at most the exact original two-pass service bill and its retained 44 bytes. -/
theorem chain_bills (step : Fin (hops n budget)) (context : Unit) (output : PqxdhFullSecretInputKdf.FullOutput) :
    (PqxdhRecordLiftLaterChain.observerOf setup codec route
      (client env setup.source.crypto codec serverKid bounds mode adversary) (fun view _ => decision view) budget step
        context output).IsTotalQueryBound
      (2 * PqxdhRecordLiftChainBills.programCoins ⟨budget, startup, allowance, bounds, n, cost⟩ + 44 + cost) :=
  PqxdhRecordLiftLaterChain.observerOf_total setup codec route _ _
    (CborRawRecordLiftBounds.chain_coins env startup allowance framed setup.source.crypto codec route serverKid bounds
      mode budget adversary respects cost) (fun view _ => decision view) cost (fun view _ => coins view) budget step
        context output

include framed respects coins in
/-- Integrity reduction bills cover uniform/private work, the shared cache, one selected seal and every raw attempt. -/
theorem auth_bills (step : Fin (hops n budget)) :
    let reduction := PqxdhRecordLiftCtxModes.decisionClient setup.source.crypto
      (PqxdhRecordLiftLaterCtx.stepClientOf setup codec route
        (client env setup.source.crypto codec serverKid bounds mode adversary) decision budget step)
    reduction.IsQueryBoundP SourceUniform
        (PqxdhRecordLiftCtxBills.programBill .uniform ⟨budget, startup, allowance, bounds, n, cost⟩ + cost +
          64 * PqxdhRecordLiftCtxBills.programBill .hash ⟨budget, startup, allowance, bounds, n, cost⟩) ∧
      reduction.IsQueryBoundP SourceHash
        (PqxdhRecordLiftCtxBills.programBill .hash ⟨budget, startup, allowance, bounds, n, cost⟩) ∧
      reduction.IsQueryBoundP SourceSeal 1 ∧
      reduction.IsQueryBoundP IsRawQuery
        (PqxdhRecordLiftCtxBills.programBill .raw ⟨budget, startup, allowance, bounds, n, cost⟩) := by
  have program := fun kind => CborRawRecordLiftBounds.ctx_categories env startup allowance framed setup.source.crypto
    codec route serverKid bounds mode budget adversary respects cost kind
  obtain ⟨⟨qUniform, qPrivate, cap, uniformBound, privateBound⟩, hashBound, sealBound, rawBound⟩ :=
    PqxdhRecordLiftLaterCtx.step_bills_of setup codec route _ _ program decision cost coins budget step
  have budgets := PqxdhRecordLiftCtxModeBounds.decision_budgets setup.source.crypto _ qUniform qPrivate _ _ _
    uniformBound privateBound hashBound sealBound rawBound
  exact ⟨budgets.1.mono cap, budgets.2.1, budgets.2.2.1, budgets.2.2.2⟩

include framed respects coins in
/-- Privacy reduction bills retain the concrete 66 uniform draws per keyed shared-cache call. -/
theorem privacy_bills (step : Fin (hops n budget)) :
    let reduction := PqxdhRecordLiftCtxPrivModes.decisionClient PqxdhRecordLiftCtxPrivModes.bytesSample setup.source.crypto
      (PqxdhRecordLiftLaterPriv.stepClientOf setup codec route
        (client env setup.source.crypto codec serverKid bounds mode adversary) decision budget step)
    reduction.IsQueryBoundP SourceUniform
        (PqxdhRecordLiftCtxBills.programBill .uniform ⟨budget, startup, allowance, bounds, n, cost⟩ + cost +
          66 * PqxdhRecordLiftCtxBills.programBill .hash ⟨budget, startup, allowance, bounds, n, cost⟩) ∧
      reduction.IsQueryBoundP SourceHash
        (PqxdhRecordLiftCtxBills.programBill .hash ⟨budget, startup, allowance, bounds, n, cost⟩) ∧
      reduction.IsQueryBoundP SourceSeal 1 ∧
      reduction.IsQueryBoundP IsRawQuery
        (PqxdhRecordLiftCtxBills.programBill .raw ⟨budget, startup, allowance, bounds, n, cost⟩) :=
  PqxdhRecordLiftLaterPriv.priv_step_bills_of setup codec route _ _
    (fun kind => CborRawRecordLiftBounds.ctx_categories env startup allowance framed setup.source.crypto codec route
      serverKid bounds mode budget adversary respects cost kind) decision cost coins budget step

end Bills
end BeaconcryptCore.Computational.CborRawRecordLiftReductions

/-- info: 'BeaconcryptCore.Computational.CborRawRecordLiftReductions.chain_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordLiftReductions.chain_bills
/-- info: 'BeaconcryptCore.Computational.CborRawRecordLiftReductions.auth_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordLiftReductions.auth_bills
/-- info: 'BeaconcryptCore.Computational.CborRawRecordLiftReductions.privacy_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordLiftReductions.privacy_bills
