-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedEffectBounds
import BeaconcryptCore.Computational.CborRawRecordLiftReductions
/-! The same gated World client has concrete chain and CTX reduction bills. A narrow public reserve coin cap contributes qReserve times the joint send budget to the uniform ledger only. Failed sends, test/fresh alternatives and the common platform state are retained; hash/raw/seal allowances are the original source ones. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBills
open PqxdhRecordLiftInterface (Environment WorldSpec EffectKind Frame)
open PqxdhRecordLiftIdeal (BillInput)
open PqxdhRecordLiftCtxBills (effectTotal)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_indicator weighted_add weighted_run operationBill)
open PqxdhRecordLiftCtxProtocolBounds (BudgetKind categoryCost)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhServerAuthExperiment (Codec)
open RegistrationNativePlatformGatedRecordInterface (program client)
variable {n : Nat} {E Failure X Reader Response : Type}

def ctxBill (coins : Nat) (kind : BudgetKind) (input : BillInput) : Nat :=
  PqxdhRecordLiftCtxBills.programBill kind input +
    PqxdhRecordLiftCtxBills.effectBill kind .coin * coins * input.budget.sends

def chainBill (coins : Nat) (kind : BudgetKind) (input : BillInput) : Nat :=
  PqxdhRecordLiftChainBills.programBill kind input +
    (match kind with | .uniform => 1 | _ => 0) * coins * input.budget.sends

section Source
variable (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : Frame env startup allowance)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (coins : Nat)
    (bounded : ∀ amount before, ((reserve amount).run before).IsTotalQueryBound coins)
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (serverKid : U64) (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary) (cost : Nat)

include framed bounded respects in
/-- Each actual World request retains the original CTX bill plus the separately declared public uniform allowance. -/
theorem world_ctx (kind : BudgetKind) :
    Weighted (PqxdhRecordLiftCtxBills.worldBill kind)
      (program env reserve crypto codec serverKid bounds mode adversary)
      (ctxBill coins kind ⟨budget, startup, allowance, bounds, n, cost⟩) := by
  have effect := fun effect : EffectKind => weighted_indicator (PqxdhRecordLiftBudget.WorldEffect effect)
    (PqxdhRecordLiftCtxBills.effectBill kind effect) _ _
      (RegistrationNativePlatformGatedEffectBounds.program_bound env startup allowance framed reserve coins bounded
        crypto codec serverKid bounds mode ⟨budget, 0⟩ adversary respects effect)
  have record := fun record : PqxdhRecordLiftBudget.RecordKind => weighted_indicator (PqxdhRecordLiftBudget.WorldRecord record)
    (operationBill kind record) _ _ (RegistrationNativePlatformGatedRecordBounds.program_bound env reserve crypto
      codec serverKid bounds mode budget adversary respects record)
  have joint := weighted_add _ _ _ _ _ (weighted_add _ _ _ _ _ (weighted_add _ _ _ _ _
    (weighted_add _ _ _ _ _ (effect .coin) (effect .hash)) (effect .administrative)) (record .send)) (record .raw)
  rw [PqxdhRecordLiftCtxBills.worldBill_split]
  cases kind <;> simpa [ctxBill, PqxdhRecordLiftCtxBills.programBill, effectTotal,
    PqxdhRecordLiftCtxBills.effectBill, RegistrationNativePlatformGatedEffectBounds.reserveCost,
    PqxdhRecordLiftBudget.recordBudget, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using joint

include framed bounded respects in
/-- Cursor admission and actual record compilation preserve every CTX component bill of the same gated client. -/
theorem ctx (kind : BudgetKind) :
    Weighted (categoryCost kind)
      (PqxdhRecordLiftProtocol.schedule codec.frameRead route
        (client env reserve crypto codec serverKid bounds mode adversary) PqxdhRecordLiftProtocol.initialControl)
      (ctxBill coins kind ⟨budget, startup, allowance, bounds, n, cost⟩) :=
  weighted_run (PqxdhRecordLiftCtxBills.worldBill kind) (categoryCost kind) _ _ _ _
    (CborRawRecordLiftBounds.client_weighted _ _ _
      (world_ctx env startup allowance framed reserve coins bounded crypto codec serverKid bounds mode budget adversary respects cost kind))
    (fun query control => PqxdhRecordLiftCtxBills.handler_categories kind codec.frameRead route query control)

include framed bounded respects in
/-- The full chain-ledger bill derives from the actual environment and record caps, with no additional protocol-cost premise. -/
theorem world_chain (kind : BudgetKind) :
    Weighted (PqxdhRecordLiftChainBills.worldBill kind)
      (program env reserve crypto codec serverKid bounds mode adversary)
      (chainBill coins kind ⟨budget, startup, allowance, bounds, n, cost⟩) := by
  have classBound := fun effect : EffectKind =>
    RegistrationNativePlatformGatedEffectBounds.program_bound env startup allowance framed reserve coins bounded
      crypto codec serverKid bounds mode ⟨budget, 0⟩ adversary respects effect
  have combined := weighted_add _ _ _ _ _ (weighted_add _ _ _ _ _ (weighted_add _ _ _ _ _
    (weighted_add _ _ _ _ _
      (weighted_indicator _ (match kind with | .uniform => 1 | _ => 0) _ _ (classBound .coin))
      (weighted_indicator _ (match kind with | .hash => 1 | _ => 0) _ _ (classBound .hash)))
      (weighted_indicator _ (match kind with | .uniform => 64 | _ => 0) _ _ (classBound .administrative)))
      (weighted_indicator _ (operationBill kind .send) _ _
        (RegistrationNativePlatformGatedRecordBounds.program_bound env reserve crypto codec serverKid bounds mode budget adversary respects .send)))
      (weighted_indicator _ (operationBill kind .raw) _ _
        (RegistrationNativePlatformGatedRecordBounds.program_bound env reserve crypto codec serverKid bounds mode budget adversary respects .raw))
  have smaller := PqxdhRecordLiftChainBills.weighted_cost_mono _ _ _ _ combined
    (PqxdhRecordLiftChainBills.worldBill_classes kind)
  cases kind <;> simpa [chainBill, PqxdhRecordLiftChainBills.programBill, PqxdhRecordLiftChainBills.effectTotal,
    RegistrationNativePlatformGatedEffectBounds.reserveCost, PqxdhRecordLiftBudget.recordBudget,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using smaller

include framed bounded respects in
/-- Every chain reduction runs the concrete cursor/gate client under the original complete stateful service. -/
theorem chain (kind : BudgetKind) :
    Weighted (categoryCost kind)
      (PqxdhRecordLiftProtocol.schedule codec.frameRead route
        (client env reserve crypto codec serverKid bounds mode adversary) PqxdhRecordLiftProtocol.initialControl)
      (chainBill coins kind ⟨budget, startup, allowance, bounds, n, cost⟩) :=
  weighted_run (PqxdhRecordLiftChainBills.worldBill kind) (categoryCost kind) _ _ _ _
    (CborRawRecordLiftBounds.client_weighted _ _ _
      (world_chain env startup allowance framed reserve coins bounded crypto codec serverKid bounds mode budget adversary respects cost kind))
    (PqxdhRecordLiftChainBills.handler_weighted kind codec.frameRead route)

include framed bounded respects in
/-- The explicit public-service allowance is added once to the whole chain observer input bill. -/
theorem chain_coins :
    Weighted PqxdhRecordLiftChainBills.coinCost
      (PqxdhRecordLiftProtocol.schedule codec.frameRead route
        (client env reserve crypto codec serverKid bounds mode adversary) PqxdhRecordLiftProtocol.initialControl)
      (PqxdhRecordLiftChainBills.programCoins ⟨budget, startup, allowance, bounds, n, cost⟩ + coins * budget.sends) := by
  have combined := weighted_add _ _ _ _ _
    (chain env startup allowance framed reserve coins bounded crypto codec route serverKid bounds mode budget adversary respects cost .uniform)
    (PqxdhRecordLiftChainBills.weighted_scale _ 64 _ _
      (chain env startup allowance framed reserve coins bounded crypto codec route serverKid bounds mode budget adversary respects cost .hash))
  have smaller := PqxdhRecordLiftChainBills.weighted_cost_mono _ _ _ _ combined
    (fun query => (PqxdhRecordLiftChainBills.coinCost_categories query).le)
  simpa [chainBill, PqxdhRecordLiftChainBills.programCoins, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using smaller

end Source
end BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBills

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBills.world_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBills.world_ctx

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBills.ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBills.ctx

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBills.world_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBills.world_chain

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBills.chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBills.chain

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBills.chain_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBills.chain_coins
