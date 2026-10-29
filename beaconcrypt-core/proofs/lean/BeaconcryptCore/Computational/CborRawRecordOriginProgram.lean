-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordLiftBounds
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginSourceProbability
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned

/-! The literal raw guarded service schedule retains all actual hidden sealing attempts and their complete continuations. Its freshness and exact send/raw caps follow from generic source scheduling and the proved cursor budget transport, before any writer outcome is known. -/
open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordOriginProgram
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Environment EffectKind Frame)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhRecordLiftProtocol (ServiceSpec Service schedule initialControl)
open PqxdhRecordLiftIdeal (Client CtxPrivate KeyMode)
open PqxdhRecordLiftProtocolHistory (annotated Fresh)
open PqxdhRecordFactsPrivateCacheSource (Reach FreshPoint)
open PqxdhRecordLiftWorldCompiler (Label)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

noncomputable def program (env : Environment n E) (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) : OracleComp (ServiceSpec n) (Client n E X) :=
  schedule codec.frameRead route (CborRawRecordLiftBounds.client env crypto codec serverKid bounds mode adversary) initialControl

/-- Source freshness is derived for the exact guarded program and every typed reply branch. -/
theorem program_fresh (env : Environment n E) (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    (annotated (program env crypto codec route serverKid bounds mode adversary) []).AllQueriesSatisfy Fresh :=
  PqxdhRecordLiftProtocolHistory.initial_schedule_fresh codec.frameRead route _

/-- Every attempted hidden seal is counted before its optional writer result. -/
theorem program_seals (env : Environment n E) (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary) :
    PqxdhRecordLiftCtxProgramBounds.Weighted PqxdhRecordFactsHashSealBills.sealCost
      (program env crypto codec route serverKid bounds mode adversary) budget.sends := by
  apply PqxdhRecordLiftCtxProgramBounds.weighted_run
    (fun query => if PqxdhRecordLiftBudget.WorldRecord .send query then 1 else 0)
    PqxdhRecordFactsHashSealBills.sealCost _ _ _ _
  · simpa only [CborRawRecordLiftBounds.client, Nat.one_mul, PqxdhRecordLiftBudget.recordBudget] using
      PqxdhRecordLiftCtxProgramBounds.weighted_indicator (PqxdhRecordLiftBudget.WorldRecord .send) 1 _ _
        (CborRecordWorldClient.program_record_bound env crypto codec serverKid bounds mode budget adversary respects .send)
  · exact PqxdhRecordFactsHashSealBills.handler_seals codec.frameRead route

/-- Every literal hidden opening callback stays within the actual receive budget. -/
theorem program_raw (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : Frame env startup allowance) (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary) :
    (program env crypto codec route serverKid bounds mode adversary).IsQueryBoundP
      (fun query => PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query = 1) budget.receives := by
  apply PqxdhRecordFactsOriginRawBounds.raw_queries
  simpa only [PqxdhRecordLiftCtxBills.programBill, PqxdhRecordLiftCtxBills.effectBill,
    PqxdhRecordLiftCtxProgramBounds.operationBill, PqxdhRecordLiftCtxProgramBounds.lookupCost,
    PqxdhRecordLiftCtxProgramBounds.sealingCost, PqxdhRecordLiftCtxProgramBounds.openingCost, Nat.zero_mul,
    Nat.zero_add, Nat.add_zero, Nat.one_mul, Nat.mul_zero, program] using
      CborRawRecordLiftBounds.ctx_categories env startup allowance framed crypto codec route serverKid bounds mode budget
        adversary respects 0 .raw

/-- The actual guarded schedule retains the generated sequence/coordinate relation for each hidden attempt. -/
theorem program_aligned (env : Environment n E) (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    (program env crypto codec route serverKid bounds mode adversary).AllQueriesSatisfy
      PqxdhRecordFactsOriginSealingAligned.SealingAligned :=
  PqxdhRecordFactsOriginSealingAligned.schedule codec.frameRead route _ _
    PqxdhRecordLiftProtocolHistory.initial_safe

section Prefix
variable (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X)

/-- Every reached raw source endpoint sees the actual unused private suffix state. -/
theorem prefix_fresh (query : Service n)
    (next : (ServiceSpec n).Range query → OracleComp (ServiceSpec n) (Client n E X))
    (state : CtxPrivate n) (past : List (Label n))
    (reached : Reach (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (program env setup.source.crypto codec route serverKid bounds mode adversary)
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []
      ((ServiceSpec n).query query >>= next) state past) : FreshPoint state query := by
  have good := PqxdhRecordFactsPrivateCacheSource.reach_virgin modes replace setup codec
    PqxdhRecordFactsPrivateCacheSource.initial_virgin reached
  have fresh := PqxdhRecordFactsPrivateCacheSource.reach_fresh _
    (program_fresh env setup.source.crypto codec route serverKid bounds mode adversary) reached
  rw [PqxdhRecordLiftProtocolHistory.annotated_query_bind, allQueriesSatisfy_query_bind_iff] at fresh
  exact PqxdhRecordFactsPrivateCacheSource.freshPoint query state past good fresh.1

/-- The selected seal's original dictionary is empty even when its writer will fail. -/
theorem prefix_empty (pending : PqxdhRecordLiftProtocol.Sealing n)
    (next : (ServiceSpec n).Range (.sealing pending) → OracleComp (ServiceSpec n) (Client n E X))
    (state : CtxPrivate n) (past : List (Label n))
    (reached : Reach (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (program env setup.source.crypto codec route serverKid bounds mode adversary)
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []
      ((ServiceSpec n).query (.sealing pending) >>= next) state past) :
    (state.keys pending.material).1.successfulSeals = [] := by
  have fresh := PqxdhRecordFactsPrivateCacheSource.reach_fresh _
    (program_fresh env setup.source.crypto codec route serverKid bounds mode adversary) reached
  rw [PqxdhRecordLiftProtocolHistory.annotated_query_bind, allQueriesSatisfy_query_bind_iff] at fresh
  exact PqxdhRecordFactsOriginOrdinalReach.reach_unattempted_empty modes
    (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
    (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace pending.material rfl reached fresh.1

end Prefix
end BeaconcryptCore.Computational.CborRawRecordOriginProgram

/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginProgram.program_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginProgram.program_fresh
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginProgram.program_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginProgram.program_seals
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginProgram.program_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginProgram.program_raw
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginProgram.prefix_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginProgram.prefix_fresh
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginProgram.prefix_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginProgram.prefix_empty

/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginProgram.program_aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginProgram.program_aligned
