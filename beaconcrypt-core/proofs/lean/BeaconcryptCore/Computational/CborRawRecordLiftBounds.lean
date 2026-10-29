-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRecordWorldClient
import BeaconcryptCore.Computational.PqxdhRecordLiftLaterPriv
import BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain

/-! Native CBOR admission forwards at most one original World request and therefore preserves arbitrary weighted service bills. The compiled raw World client retains the complete original secrecy program below which admission runs, including rejected fresh and test sends. Actual record, chain and CTX budgets follow from the existing environment frame and adversary budget. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordLiftBounds
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Environment WorldSpec EffectKind Frame)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_run)
open PqxdhRecordLiftCtxProtocolBounds (BudgetKind categoryCost)
open PqxdhRecordLiftProtocol (schedule initialControl)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

theorem handler_weighted (cost : (WorldSpec n).Domain → Nat) (query : (WorldSpec n).Domain)
    (shell : CborRecordWorldClient.Shell) :
    Weighted cost ((CborRecordWorldClient.handler query).run shell) (cost query) := by
  cases refused : CborRecordWorldClient.refusal query shell with
  | some reply => simp only [CborRecordWorldClient.handler, StateT.run, refused, Weighted, isQueryBound_pure]
  | none =>
      simp only [CborRecordWorldClient.handler, StateT.run, refused, CborRecordWorldClient.forward,
        Weighted, isQueryBound_map_iff, isQueryBound_query_iff]
      exact Nat.le_refl _

/-- Every weighted category is preserved on every reply branch, including a complete refusal. -/
theorem client_weighted {Result : Type} (cost : (WorldSpec n).Domain → Nat)
    (work : OracleComp (WorldSpec n) Result) (bound : Nat) (bounded : Weighted cost work bound)
    (shell : CborRecordWorldClient.Shell := CborRecordWorldClient.initial) :
    Weighted cost (CborRecordWorldClient.client work shell) bound := by
  unfold CborRecordWorldClient.client Weighted
  rw [OracleComp.isQueryBound_map_iff]
  exact weighted_run cost cost CborRecordWorldClient.handler work bound shell bounded (handler_weighted cost)

noncomputable def client (env : Environment n E) (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :=
  CborRecordWorldClient.client (PqxdhRecordLiftInterface.program env crypto codec serverKid bounds mode adversary)

section Program
variable (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : Frame env startup allowance) (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary) (cost : Nat)

include respects in
theorem record_bounded : PqxdhRecordLiftLaterWorlds.RecordBounded budget
    (client env crypto codec serverKid bounds mode adversary) :=
  CborRecordWorldClient.program_record_bound env crypto codec serverKid bounds mode budget adversary respects

include framed respects in
/-- The complete raw client has exactly the original chain-component bills. -/
theorem chain_categories (kind : BudgetKind) :
    Weighted (categoryCost kind)
      (schedule codec.frameRead route (client env crypto codec serverKid bounds mode adversary) initialControl)
      (PqxdhRecordLiftChainBills.programBill kind ⟨budget, startup, allowance, bounds, n, cost⟩) :=
  weighted_run (PqxdhRecordLiftChainBills.worldBill kind) (categoryCost kind) _ _ _ _
    (client_weighted _ _ _
      (PqxdhRecordLiftChainBills.interface_weighted kind env startup allowance framed crypto codec serverKid bounds mode
        budget adversary respects cost))
    (PqxdhRecordLiftChainBills.handler_weighted kind codec.frameRead route)

include framed respects in
/-- The complete raw client has exactly the original CTX-component bills. -/
theorem ctx_categories (kind : BudgetKind) :
    Weighted (categoryCost kind)
      (schedule codec.frameRead route (client env crypto codec serverKid bounds mode adversary) initialControl)
      (PqxdhRecordLiftCtxBills.programBill kind ⟨budget, startup, allowance, bounds, n, cost⟩) :=
  weighted_run (PqxdhRecordLiftCtxBills.worldBill kind) (categoryCost kind) _ _ _ _
    (client_weighted _ _ _
      (PqxdhRecordLiftCtxBills.world_categories kind env startup allowance framed crypto codec serverKid bounds mode
        budget adversary respects cost))
    (fun query control => PqxdhRecordLiftCtxBills.handler_categories kind codec.frameRead route query control)

include framed respects in
/-- Native admission does not increase the actual uniform-byte service bill used by every chain observer. -/
theorem chain_coins :
    Weighted PqxdhRecordLiftChainBills.coinCost
      (schedule codec.frameRead route (client env crypto codec serverKid bounds mode adversary) initialControl)
      (PqxdhRecordLiftChainBills.programCoins ⟨budget, startup, allowance, bounds, n, cost⟩) := by
  have combined := PqxdhRecordLiftCtxProgramBounds.weighted_add _ _ _ _ _
    (chain_categories env startup allowance framed crypto codec route serverKid bounds mode budget adversary respects
      cost .uniform)
    (PqxdhRecordLiftChainBills.weighted_scale _ 64 _ _
      (chain_categories env startup allowance framed crypto codec route serverKid bounds mode budget adversary respects
        cost .hash))
  exact PqxdhRecordLiftChainBills.weighted_cost_mono _ _ _ _ combined
    (fun query => (PqxdhRecordLiftChainBills.coinCost_categories query).le)

end Program
end BeaconcryptCore.Computational.CborRawRecordLiftBounds

/-- info: 'BeaconcryptCore.Computational.CborRawRecordLiftBounds.handler_weighted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordLiftBounds.handler_weighted
/-- info: 'BeaconcryptCore.Computational.CborRawRecordLiftBounds.client_weighted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordLiftBounds.client_weighted
/-- info: 'BeaconcryptCore.Computational.CborRawRecordLiftBounds.record_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordLiftBounds.record_bounded
/-- info: 'BeaconcryptCore.Computational.CborRawRecordLiftBounds.chain_categories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordLiftBounds.chain_categories
/-- info: 'BeaconcryptCore.Computational.CborRawRecordLiftBounds.ctx_categories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordLiftBounds.ctx_categories
/-- info: 'BeaconcryptCore.Computational.CborRawRecordLiftBounds.chain_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordLiftBounds.chain_coins
