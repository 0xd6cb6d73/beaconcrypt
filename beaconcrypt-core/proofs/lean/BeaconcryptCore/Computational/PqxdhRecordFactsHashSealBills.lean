-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills

/-! Total hidden sealing attempts in the complete adaptive source program. -/
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordFactsHashSealBills
open PqxdhRecordLiftInterface
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_indicator weighted_run)
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds Budget)
variable {n : Nat}

/-- Count each hidden sealing service request, before its optional reply or writer outcome. -/
def sealCost : PqxdhRecordLiftProtocol.Service n → Nat
  | .sealing _ => 1
  | _ => 0

/-- This is precisely the existing source seal ledger, without a selected target. -/
theorem sealCost_category : (sealCost : PqxdhRecordLiftProtocol.Service n → Nat) =
    PqxdhRecordLiftCtxProtocolBounds.categoryCost .seal := rfl

/-- The corresponding World bill counts record-send requests and no other command. -/
theorem world_seal_cost : (PqxdhRecordLiftCtxBills.worldBill .seal : (WorldSpec n).Domain → Nat) =
    fun query => if PqxdhRecordLiftBudget.WorldRecord .send query then 1 else 0 := by
  funext query
  rcases query with _ | effect | record
  · rfl
  · simp [PqxdhRecordLiftCtxBills.worldBill, PqxdhRecordLiftCtxBills.effectBill,
      PqxdhRecordLiftBudget.WorldRecord]
  · cases selected : PqxdhRecordLiftBudget.recordKind record <;>
      simp [PqxdhRecordLiftCtxBills.worldBill, PqxdhRecordLiftCtxProgramBounds.operationBill,
        PqxdhRecordLiftCtxProgramBounds.lookupCost, PqxdhRecordLiftCtxProgramBounds.sealingCost,
        PqxdhRecordLiftCtxProgramBounds.openingCost, PqxdhRecordLiftBudget.WorldRecord, selected]

/-- Every World request causes at most one hidden sealing attempt exactly when it is a send. -/
theorem handler_seals (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (control : PqxdhRecordLiftProtocol.Control n) :
    Weighted sealCost ((PqxdhRecordLiftProtocol.handler decode route query).run control)
      (if PqxdhRecordLiftBudget.WorldRecord .send query then 1 else 0) := by
  rw [sealCost_category]
  have bounded := PqxdhRecordLiftCtxBills.handler_categories .seal decode route query control
  rwa [world_seal_cost] at bounded

/-- The complete adaptive source program makes at most `budget.sends` hidden sealing attempts, retaining all typed reply branches. -/
theorem program_seals {E X Reader Response : Type} (env : Environment n E)
    (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Aeneas.Std.U64)
    (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary) :
    Weighted sealCost (PqxdhRecordLiftProtocol.program env crypto codec route serverKid bounds mode adversary)
      budget.sends := by
  apply weighted_run (fun query => if PqxdhRecordLiftBudget.WorldRecord .send query then 1 else 0)
    sealCost _ _ _ _
  · simpa only [Nat.one_mul, PqxdhRecordLiftBudget.recordBudget] using
      weighted_indicator (PqxdhRecordLiftBudget.WorldRecord .send) 1 _ _
        (PqxdhRecordLiftBudget.program_record_bound env crypto codec serverKid bounds mode budget
          adversary respects .send)
  · exact handler_seals codec.frameRead route

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashSealBills.sealCost_category' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sealCost_category
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashSealBills.world_seal_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms world_seal_cost
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashSealBills.handler_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms handler_seals
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashSealBills.program_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms program_seals

end BeaconcryptCore.Computational.PqxdhRecordFactsHashSealBills
