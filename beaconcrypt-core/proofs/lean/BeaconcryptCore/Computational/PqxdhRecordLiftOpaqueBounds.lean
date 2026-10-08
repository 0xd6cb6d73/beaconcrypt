-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueDrivers
import BeaconcryptCore.Computational.RawCtxChainReceiveBounds

/-! Literal category bounds for the opaque source drivers, before any private interpreter or callback replies are chosen. These syntax bounds do not discard parser, writer or primitive work. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds
open PqxdhRecordLiftMaterialTable PqxdhRecordLiftChainState PqxdhRecordLiftChainTable PqxdhRecordLiftChainCompiler PqxdhRecordLiftOpaqueDrivers
variable {Slot OpenContext Plaintext SealContext Output : Type}

/-- Query domains do not contain the opening/sealing reply types; Unit here fixes only those unused range parameters. -/
abbrev Domain (Slot OpenContext SealContext : Type) :=
  (ServiceSpec Slot OpenContext Unit SealContext Unit).Domain

def IsLookup (query : Domain Slot OpenContext SealContext) : Prop := query.isLeft = true

def IsOpening : Domain Slot OpenContext SealContext → Prop
  | .inr (.inl _) => True
  | _ => False

def IsSealing : Domain Slot OpenContext SealContext → Prop
  | .inr (.inr _) => True
  | _ => False

open Classical

/-- Every recursive receive lookup consumes one unit of the exact source max(1, remaining) allowance. -/
theorem receive_lookup (effect : Effect Slot OpenContext) :
    (receiveProgram (Plaintext := Plaintext) (SealContext := SealContext) (Output := Output) effect).IsQueryBoundP
      IsLookup (RawCtxChainReceiveBounds.kdfCost effect) := by
  generalize hdepth : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
    cases effect with
    | rejected entry context => simp [receiveProgram]
    | openRequested pending =>
        rw [receiveProgram, isQueryBoundP_query_bind_iff]
        simp [IsLookup, RawCtxChainReceiveBounds.kdfCost]
    | kdfRequested pending =>
        rw [receiveProgram, isQueryBoundP_query_bind_iff]
        simp only [IsLookup, Sum.isLeft, not_true_eq_false, false_or, ite_true]
        refine ⟨by simp [RawCtxChainReceiveBounds.kdfCost], fun _ => ?_⟩
        apply (ih _ (hdepth ▸ RawCtxChainReceive.normalResume_rank pending
          (advance pending.request 1, pending.request)) _ rfl).mono
        have cost := RawCtxChainReceiveBounds.resume_cost pending (advance pending.request 1, pending.request)
        omega

/-- The complete receive driver invokes at most one opening, after all cached or future derivation paths. -/
theorem receive_opening (effect : Effect Slot OpenContext) :
    (receiveProgram (Plaintext := Plaintext) (SealContext := SealContext) (Output := Output) effect).IsQueryBoundP
      IsOpening 1 := by
  generalize hdepth : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
    cases effect with
    | rejected entry context => simp [receiveProgram]
    | openRequested pending =>
        rw [receiveProgram, isQueryBoundP_query_bind_iff]
        simp [IsOpening]
    | kdfRequested pending =>
        rw [receiveProgram, isQueryBoundP_query_bind_iff]
        simpa [IsOpening] using ih _ (hdepth ▸ RawCtxChainReceive.normalResume_rank pending
          (advance pending.request 1, pending.request)) _ rfl

/-- A receive never invokes the sealing service, regardless of its opening reply. -/
theorem receive_sealing (effect : Effect Slot OpenContext) :
    (receiveProgram (Plaintext := Plaintext) (SealContext := SealContext) (Output := Output) effect).IsQueryBoundP
      IsSealing 0 := by
  generalize hdepth : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
    cases effect with
    | rejected entry context => simp [receiveProgram]
    | openRequested pending =>
        rw [receiveProgram, isQueryBoundP_query_bind_iff]
        simp [IsSealing]
    | kdfRequested pending =>
        rw [receiveProgram, isQueryBoundP_query_bind_iff]
        simpa [IsSealing] using ih _ (hdepth ▸ RawCtxChainReceive.normalResume_rank pending
          (advance pending.request 1, pending.request)) _ rfl

/-- A send performs at most one private lookup, with none on source counter exhaustion. -/
theorem send_lookup (start : Start Slot SealContext) :
    (sendProgram (OpenContext := OpenContext) (Plaintext := Plaintext) (Output := Output) start).IsQueryBoundP
      IsLookup 1 := by
  cases start <;> simp [sendProgram, isQueryBoundP_query_bind_iff, IsLookup]

/-- A send never invokes the opening service. -/
theorem send_opening (start : Start Slot SealContext) :
    (sendProgram (OpenContext := OpenContext) (Plaintext := Plaintext) (Output := Output) start).IsQueryBoundP
      IsOpening 0 := by
  cases start <;> simp [sendProgram, isQueryBoundP_query_bind_iff, IsOpening]

/-- A send invokes at most one sealing service, keeping the source advancement even when its optional reply is none. -/
theorem send_sealing (start : Start Slot SealContext) :
    (sendProgram (OpenContext := OpenContext) (Plaintext := Plaintext) (Output := Output) start).IsQueryBoundP
      IsSealing 1 := by
  cases start <;> simp [sendProgram, isQueryBoundP_query_bind_iff, IsSealing]

/-- Source admission gives at most 51 private derivation calls for every entry and target. -/
theorem admitted_receive_lookup (entry : LabeledKernel Slot) (target : Std.U64) (context : OpenContext) :
    (admittedReceive (Plaintext := Plaintext) (SealContext := SealContext) (Output := Output)
      entry target context).IsQueryBoundP IsLookup 51 :=
  (receive_lookup _).mono (RawCtxChainReceiveBounds.begin_cost entry target context)

/-- Source admission retains the single-opening bound, including cached and rejected paths. -/
theorem admitted_receive_opening (entry : LabeledKernel Slot) (target : Std.U64) (context : OpenContext) :
    (admittedReceive (Plaintext := Plaintext) (SealContext := SealContext) (Output := Output)
      entry target context).IsQueryBoundP IsOpening 1 := receive_opening _

/-- No admitted receive can emit a sealing query. -/
theorem admitted_receive_sealing (entry : LabeledKernel Slot) (target : Std.U64) (context : OpenContext) :
    (admittedReceive (Plaintext := Plaintext) (SealContext := SealContext) (Output := Output)
      entry target context).IsQueryBoundP IsSealing 0 := receive_sealing _

/-- Source send admission preserves the one-lookup cap. -/
theorem admitted_send_lookup (entry : LabeledKernel Slot) (context : SealContext) :
    (admittedSend (OpenContext := OpenContext) (Plaintext := Plaintext) (Output := Output)
      entry context).IsQueryBoundP IsLookup 1 := send_lookup _

/-- No admitted send can emit an opening query. -/
theorem admitted_send_opening (entry : LabeledKernel Slot) (context : SealContext) :
    (admittedSend (OpenContext := OpenContext) (Plaintext := Plaintext) (Output := Output)
      entry context).IsQueryBoundP IsOpening 0 := send_opening _

/-- Source send admission preserves the one-sealing cap, without assuming writer success. -/
theorem admitted_send_sealing (entry : LabeledKernel Slot) (context : SealContext) :
    (admittedSend (OpenContext := OpenContext) (Plaintext := Plaintext) (Output := Output)
      entry context).IsQueryBoundP IsSealing 1 := send_sealing _

end BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds.receive_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds.receive_lookup

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds.receive_opening' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds.receive_opening

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds.receive_sealing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds.receive_sealing

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds.send_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds.send_lookup

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds.send_opening' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds.send_opening

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds.send_sealing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds.send_sealing

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds.admitted_receive_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds.admitted_receive_lookup

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds.admitted_receive_opening' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds.admitted_receive_opening

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds.admitted_receive_sealing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds.admitted_receive_sealing

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds.admitted_send_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds.admitted_send_lookup

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds.admitted_send_opening' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds.admitted_send_opening

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds.admitted_send_sealing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds.admitted_send_sealing
