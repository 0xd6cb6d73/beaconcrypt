-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordOriginProgram
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalFinalPrefix
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealAlignment

/-! Exact chronological cut witnesses for the raw guarded source program, including failed writers and attempted ordinals. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordOriginPath
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode Client)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhRecordFactsPrivateCacheSource (Reach)
open PqxdhRecordFactsOriginOrdinalCut (Cut)
open PqxdhRecordFactsOriginOrdinalPath (Prefix Path)
open PqxdhRecordFactsOriginOrdinalTrace (Result)
open PqxdhRecordFactsOriginOrdinalPathEntries (prefix_entry_sealing prefix_length)
open PqxdhRecordFactsOriginOrdinalFinalPrefix (path_prefix)
open PqxdhRecordFactsOriginSealAlignment (prefix_queries sealing_entry_sequence)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhRecordLiftInterface (Environment)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- Every attempted guarded source seal has a strict send-budget ordinal. -/
theorem source_seal_index (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (pending : PqxdhRecordLiftProtocol.Sealing n)
    (next : (ServiceSpec n).Range (.sealing pending) → OracleComp (ServiceSpec n) (PqxdhRecordLiftIdeal.Client n E X))
    (state : CtxPrivate n) (past : List (Label n))
    (reached : Reach (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (CborRawRecordOriginProgram.program env setup.source.crypto codec route serverKid bounds mode adversary)
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []
      ((liftM ((ServiceSpec n).query (.sealing pending)) : OracleComp (ServiceSpec n) _) >>= next) state past) :
    past.length < budget.sends := by
  simpa only [List.length_nil, Nat.zero_add] using PqxdhRecordFactsOriginOrdinal.seal_index_lt _ budget.sends
    (CborRawRecordOriginProgram.program_seals env setup.source.crypto codec route serverKid bounds mode budget adversary respects)
    pending next reached


/-- A retained dictionary entry selects its exact earlier guarded callback and complete chronological prefix. -/
theorem source_prefix_entry (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (client : OracleComp (ServiceSpec n) (PqxdhRecordLiftIdeal.Client n E X))
    (state : CtxPrivate n) (past : List (Label n))
    (cuts : List (Cut n (PqxdhRecordLiftIdeal.Client n E X)))
    (reached : Prefix (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (CborRawRecordOriginProgram.program env setup.source.crypto codec route serverKid bounds mode adversary)
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) [] client state past cuts)
    (label : Label n) (entry : CtxSuccessfulSeal) (present : entry ∈ (state.keys label).1.successfulSeals) :
    ∃ (cut : Cut n (PqxdhRecordLiftIdeal.Client n E X))
      (reply : (ServiceSpec n).Range (.sealing cut.pending) × CtxPrivate n)
      (earlier later : List (Cut n (PqxdhRecordLiftIdeal.Client n E X))),
      Prefix (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
        (CborRawRecordOriginProgram.program env setup.source.crypto codec route serverKid bounds mode adversary)
        (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []
        ((ServiceSpec n).query (.sealing cut.pending) >>= cut.next) cut.state cut.past earlier ∧
      reply ∈ support ((PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.sealing cut.pending)).run cut.state) ∧
      cut.pending.material = label ∧ cut.past.length = earlier.length ∧ cut.past.length < budget.sends ∧
      (cut.state.keys label).1.successfulSeals = [] ∧
      PqxdhRecordFactsPrivateCacheSource.FreshPoint cut.state (.sealing cut.pending) ∧
      entry ∈ (reply.2.keys label).1.successfulSeals ∧
      Prefix (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) (cut.next reply.1) reply.2
        (cut.past ++ [cut.pending.material]) client state past later ∧
      cuts = earlier ++ cut :: later := by
  obtain ⟨cut, reply, earlier, later, prior, answered, material, notYet, inserted, suffix, same⟩ :=
    prefix_entry_sealing modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
      (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace
      label entry (by exact List.not_mem_nil) reached present
  have priorReach := PqxdhRecordFactsOriginOrdinalPath.prefix_reach _ prior
  refine ⟨cut, reply, earlier, later, prior, answered, material, ?_,
    source_seal_index modes replace setup codec route env serverKid bounds mode budget adversary respects cut.pending cut.next cut.state cut.past priorReach,
    ?_, CborRawRecordOriginProgram.prefix_fresh modes replace setup codec route env serverKid bounds mode adversary (.sealing cut.pending) cut.next cut.state cut.past priorReach,
    inserted, suffix, same⟩
  · simpa only [List.length_nil, Nat.zero_add] using prefix_length _ prior
  · simpa only [material] using CborRawRecordOriginProgram.prefix_empty modes replace setup codec route env serverKid bounds mode adversary cut.pending cut.next cut.state cut.past priorReach


/-- Every final retained seal has its insertion callback on this same complete guarded path. -/
theorem source_final_entry (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (result : Result n (PqxdhRecordLiftIdeal.Client n E X))
    (path : Path (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (CborRawRecordOriginProgram.program env setup.source.crypto codec route serverKid bounds mode adversary)
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) [] result)
    (label : Label n) (entry : CtxSuccessfulSeal) (present : entry ∈ (result.2.2.keys label).1.successfulSeals) :
    ∃ (cut : Cut n (PqxdhRecordLiftIdeal.Client n E X))
      (reply : (ServiceSpec n).Range (.sealing cut.pending) × CtxPrivate n)
      (earlier later : List (Cut n (PqxdhRecordLiftIdeal.Client n E X))) (finalPast : List (Label n)),
      Prefix (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
        (CborRawRecordOriginProgram.program env setup.source.crypto codec route serverKid bounds mode adversary)
        (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []
        ((ServiceSpec n).query (.sealing cut.pending) >>= cut.next) cut.state cut.past earlier ∧
      reply ∈ support ((PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.sealing cut.pending)).run cut.state) ∧
      cut.pending.material = label ∧ cut.past.length = earlier.length ∧ cut.past.length < budget.sends ∧
      (cut.state.keys label).1.successfulSeals = [] ∧
      PqxdhRecordFactsPrivateCacheSource.FreshPoint cut.state (.sealing cut.pending) ∧
      entry ∈ (reply.2.keys label).1.successfulSeals ∧
      Prefix (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) (cut.next reply.1) reply.2
        (cut.past ++ [cut.pending.material]) (pure result.2.1) result.2.2 finalPast later ∧
      result.1 = earlier ++ cut :: later := by
  obtain ⟨finalPast, reached⟩ := path_prefix _ path
  obtain ⟨cut, reply, earlier, later, rest⟩ :=
    source_prefix_entry modes replace setup codec route env serverKid
      bounds mode budget adversary respects (pure result.2.1) result.2.2 finalPast result.1 reached label entry present
  exact ⟨cut, reply, earlier, later, finalPast, rest⟩


/-- Actual guarded source entries retain their physical sealing coordinate sequence. -/
theorem source_prefix_sequence (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (budget : Budget) (adversary : OracleComp (ModeSpec mode) X)
    (respects : budget.Respects adversary) (client : OracleComp (ServiceSpec n) (Client n E X))
    (state : CtxPrivate n) (past : List (Label n)) (cuts : List (Cut n (Client n E X)))
    (reached : Prefix (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (CborRawRecordOriginProgram.program env setup.source.crypto codec route serverKid bounds mode adversary)
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) [] client state past cuts)
    (label : Label n) (entry : CtxSuccessfulSeal) (present : entry ∈ (state.keys label).1.successfulSeals) :
    entry.input.context.ad.seq = label.position + 1 := by
  obtain ⟨cut, reply, earlier, later, prior, answered, material, _, _, empty, _, inserted, _, _⟩ :=
    source_prefix_entry modes replace setup codec route env serverKid bounds mode budget adversary respects client state past cuts reached label entry present
  have aligned := prefix_queries _ PqxdhRecordFactsOriginSealingAligned.SealingAligned
    (CborRawRecordOriginProgram.program_aligned env setup.source.crypto codec route serverKid bounds mode adversary) prior
  subst label
  rw [allQueriesSatisfy_query_bind_iff] at aligned
  exact sealing_entry_sequence modes ideal replace setup codec cut.pending cut.state reply answered empty aligned.1 entry inserted


end BeaconcryptCore.Computational.CborRawRecordOriginPath

/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginPath.source_seal_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginPath.source_seal_index
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginPath.source_prefix_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginPath.source_prefix_entry
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginPath.source_final_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginPath.source_final_entry
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginPath.source_prefix_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginPath.source_prefix_sequence
