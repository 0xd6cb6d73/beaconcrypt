-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordViewIntegrity
import BeaconcryptCore.Computational.CborRawRecordOriginCallback

/-! Source scheduling and failed-writer guessing for the complete actual native World AST. The native constructor, ML-pin hash and all later callbacks remain inside one cursor/Protocol/CTX schedule; no pure-Environment startup substitution or warmed-cache reset is used. These structural and probability facts do not assume a native origin event inclusion. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeRecordOriginProgram
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftProtocol (ServiceSpec schedule initialControl)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode Client)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftCtxProgramBounds (Weighted)
open PqxdhRecordLiftCtxProtocolBounds (categoryCost)
open PqxdhRecordFactsPrivateCacheSource (Reach)
open RegistrationNativeRecordPackage (Extra client)
variable {n : Nat} {ι KemSK Reader Response E Value : Type} {base : OracleSpec ι}
local instance : MeasurableSpace ((Client n (Extra E) Value × CtxPrivate n) × Bool) := ⊤
local instance : DiscreteMeasurableSpace ((Client n (Extra E) Value × CtxPrivate n) × Bool) := ⟨fun _ => trivial⟩

noncomputable def program (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value)) :
    OracleComp (ServiceSpec n) (Client n (Extra E) Value) := schedule codec.frameRead route (client work) initialControl

/-- The entire native AST, including actual shared-cache startup, has the source one-use hidden-coordinate freshness law. -/
theorem fresh (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value)) :
    (PqxdhRecordLiftProtocolHistory.annotated (program codec route work) []).AllQueriesSatisfy PqxdhRecordLiftProtocolHistory.Fresh :=
  PqxdhRecordLiftProtocolHistory.initial_schedule_fresh codec.frameRead route _

/-- Actual cursor-admitted hidden sealing attempts are counted before writer success is known. -/
theorem seals (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value))
    (budget : PqxdhDeploymentInterface.Budget) (bounded : PqxdhRecordLiftLaterWorlds.RecordBounded budget (client work)) :
    Weighted PqxdhRecordFactsHashSealBills.sealCost (program codec route work) budget.sends := by
  apply PqxdhRecordLiftCtxProgramBounds.weighted_run
    (fun query => if PqxdhRecordLiftBudget.WorldRecord .send query then 1 else 0)
    PqxdhRecordFactsHashSealBills.sealCost _ _ _ _
  · simpa only [Nat.one_mul, PqxdhRecordLiftBudget.recordBudget] using
      PqxdhRecordLiftCtxProgramBounds.weighted_indicator (PqxdhRecordLiftBudget.WorldRecord .send) 1 _ _ (bounded .send)
  · exact PqxdhRecordFactsHashSealBills.handler_seals codec.frameRead route

/-- The ordinary native receive category bill is the exact all-reply hidden opening allowance. -/
theorem raw (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value)) (cap : Nat)
    (bounded : Weighted (categoryCost .raw) (program codec route work) cap) :
    (program codec route work).IsQueryBoundP (fun query => categoryCost .raw query = 1) cap :=
  PqxdhRecordFactsOriginRawBounds.raw_queries _ cap bounded

/-- The same full native schedule retains the actual sequence/coordinate relationship on every sealing branch. -/
theorem aligned (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value)) :
    (program codec route work).AllQueriesSatisfy PqxdhRecordFactsOriginSealingAligned.SealingAligned :=
  PqxdhRecordFactsOriginSealingAligned.schedule codec.frameRead route _ _ PqxdhRecordLiftProtocolHistory.initial_safe

variable (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
variable (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
variable (work : OracleComp (WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value))
local notation "service" => PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec
local notation "start" => PqxdhRecordFactsCounter.zeroCtx (CtxPrivate.initial (n := n))

/-- Every reached original native callback retains its unused private suffix state, including all startup hash entries. -/
theorem prefix_fresh (query : PqxdhRecordLiftProtocol.Service n)
    (next : (ServiceSpec n).Range query → OracleComp (ServiceSpec n) (Client n (Extra E) Value))
    (state : CtxPrivate n) (past : List (Label n))
    (reached : Reach service (program codec route work) start [] ((ServiceSpec n).query query >>= next) state past) :
    PqxdhRecordFactsPrivateCacheSource.FreshPoint state query := by
  have virgin := PqxdhRecordFactsPrivateCacheSource.reach_virgin modes replace setup codec
    PqxdhRecordFactsPrivateCacheSource.initial_virgin reached
  have unused := PqxdhRecordFactsPrivateCacheSource.reach_fresh _ (fresh codec route work) reached
  rw [PqxdhRecordLiftProtocolHistory.annotated_query_bind, allQueriesSatisfy_query_bind_iff] at unused
  exact PqxdhRecordFactsPrivateCacheSource.freshPoint query state past virgin unused.1

/-- The selected native seal has no earlier successful dictionary entry even when its original writer will fail. -/
theorem prefix_empty (pending : PqxdhRecordLiftProtocol.Sealing n)
    (next : (ServiceSpec n).Range (.sealing pending) → OracleComp (ServiceSpec n) (Client n (Extra E) Value))
    (state : CtxPrivate n) (past : List (Label n))
    (reached : Reach service (program codec route work) start [] ((ServiceSpec n).query (.sealing pending) >>= next) state past) :
    (state.keys pending.material).1.successfulSeals = [] := by
  have unused := PqxdhRecordFactsPrivateCacheSource.reach_fresh _ (fresh codec route work) reached
  rw [PqxdhRecordLiftProtocolHistory.annotated_query_bind, allQueriesSatisfy_query_bind_iff] at unused
  exact PqxdhRecordFactsOriginOrdinalReach.reach_unattempted_empty modes
    (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
    (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace pending.material rfl reached unused.1

/-- A real reached native failed-writer continuation satisfies the two-guess bound at its actual receive allowance, with freshness and future exclusion derived from the source program. -/
theorem reached_bound (cap : Nat) (bounded : Weighted (categoryCost .raw) (program codec route work) cap)
    (cut : PqxdhRecordFactsOriginOrdinalCut.Cut n (Client n (Extra E) Value)) (ideal : modes cut.pending.material ≠ .real)
    (reached : Reach service (program codec route work) start []
      ((ServiceSpec n).query (.sealing cut.pending) >>= cut.next) cut.state cut.past) :
    𝒟[PqxdhRecordFactsOriginFailedResume.resumeMarked modes setup codec replace cut] {result | result.2 = true} ≤
      2 * cap * ((2 ^ 512 : Nat) : ℝ≥0∞)⁻¹ := by
  apply PqxdhRecordFactsOriginFailedCallback.marked_bound modes setup codec replace cut ideal
  · exact prefix_fresh modes replace setup codec route work (.sealing cut.pending) cut.next cut.state cut.past reached
  · exact prefix_empty modes replace setup codec route work cut.pending cut.next cut.state cut.past reached
  · exact PqxdhRecordFactsOriginMuteFresh.after_seal_noSeal cut.past cut.pending cut.next
      (PqxdhRecordFactsPrivateCacheSource.reach_fresh _ (fresh codec route work) reached) none
  · have suffix := PqxdhRecordFactsOriginRawBounds.reach_queries service
      (fun query => categoryCost .raw query = 1) cap (raw codec route work cap bounded) reached
    rw [isQueryBoundP_query_bind_iff] at suffix
    exact (suffix.2 none).mono (by split_ifs <;> omega)

end BeaconcryptCore.Computational.RegistrationNativeRecordOriginProgram
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordOriginProgram.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordOriginProgram.fresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordOriginProgram.seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordOriginProgram.seals

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordOriginProgram.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordOriginProgram.raw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordOriginProgram.aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordOriginProgram.aligned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordOriginProgram.prefix_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordOriginProgram.prefix_fresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordOriginProgram.prefix_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordOriginProgram.prefix_empty

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordOriginProgram.reached_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordOriginProgram.reached_bound
