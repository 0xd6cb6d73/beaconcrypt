-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceBills
/-! An explicit reduction sampler prefix has its own coin bill and no record allowance. The subsequent actual source-derived bills are added once; these are reduction costs and do not alter the claimed original runtime budget. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPrefixBounds
open PqxdhRecordLiftInterface (WorldSpec coinLift)
open PqxdhRecordLiftBudget (WorldRecord RecordKind recordBudget)
open PqxdhRecordLiftCtxProtocolBounds (BudgetKind categoryCost)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_indicator weighted_simulate weighted_bind weighted_run)
open PqxdhRecordLiftCtxBills (effectBill worldBill)
variable {n : Nat} {A B Reader Response : Type}

/-- Reduction-owned prefix coins have their literal weighted World cost. -/
theorem sample_bound (sample : ProbComp A) (coins : Nat) (bounded : sample.IsTotalQueryBound coins) (kind : BudgetKind) :
    Weighted (worldBill kind) (simulateQ (coinLift (n := n)) sample) (effectBill kind .coin * coins) := by
  have first := weighted_indicator (fun (_ : unifSpec.Domain) => True) (effectBill kind .coin) sample coins
    ((isQueryBoundP_true_iff _ _).mpr bounded)
  simp only [ite_true] at first
  apply weighted_simulate (fun (_ : unifSpec.Domain) => effectBill kind .coin) (worldBill kind) coinLift sample _ first
  intro query
  simp only [coinLift,Weighted,isQueryBound_query_iff,worldBill]
  cases kind <;> simp [effectBill, PqxdhRecordLiftInterface.effectKind]

/-- The actual coin prefix makes no send or raw-receive request. -/
theorem record_bound (sample : ProbComp A) (next : A → OracleComp (WorldSpec n) B)
    (kind : RecordKind) (cap : Nat) (bounded : ∀ value, (next value).IsQueryBoundP (WorldRecord kind) cap) :
    ((simulateQ coinLift sample) >>= next).IsQueryBoundP (WorldRecord kind) cap := by
  simpa only [Nat.zero_add] using isQueryBoundP_bind
    (RegistrationNativeSelectiveRecordStartup.coins_record kind sample) (fun value _ => bounded value)

/-- The same cursor-aware compiled client adds the reduction sampler's explicit category bill exactly once. -/
theorem program_bound (sample : ProbComp A) (next : A → OracleComp (WorldSpec n) B)
    (coins : Nat) (sampleBound : sample.IsTotalQueryBound coins)
    (kind : BudgetKind) (bodyBill : Nat) (bounded : ∀ value, Weighted (worldBill kind) (next value) bodyBill)
    (frameRead : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder) :
    Weighted (categoryCost kind)
      (PqxdhRecordLiftProtocol.schedule frameRead route
        (CborRecordWorldClient.client ((simulateQ coinLift sample) >>= next)) PqxdhRecordLiftProtocol.initialControl)
      (effectBill kind .coin * coins + bodyBill) := by
  apply weighted_run (worldBill kind) (categoryCost kind)
  · apply CborRawRecordLiftBounds.client_weighted
    exact weighted_bind (worldBill kind) _ _ _ _ (sample_bound sample coins sampleBound kind) bounded
  · exact fun query control => PqxdhRecordLiftCtxBills.handler_categories kind frameRead route query control
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPrefixBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPrefixBounds.sample_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPrefixBounds.sample_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPrefixBounds.record_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPrefixBounds.record_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPrefixBounds.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPrefixBounds.program_bound
