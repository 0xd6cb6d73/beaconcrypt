-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealFacts
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve

/-! Exact generated entries, literal failed writers and source sealing-sequence correspondence. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealAlignment
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftProtocol (Service ServiceSpec Private)
open PqxdhRecordFactsOriginReplay (Matches matches_selected)
open PqxdhRecordFactsOriginSealFacts (erased_sealing_trace)
variable {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- A fresh selected dictionary entry is the callback's own exact generated input and record, with its actual writer reply. -/
theorem sealing_entry (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (before : CtxPrivate n)
    (result : Option RawCtxSourceSend.Encrypted × CtxPrivate n)
    (supported : result ∈ support ((PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.sealing pending)).run before))
    (empty : (before.keys pending.material).1.successfulSeals = [])
    (entry : CtxSuccessfulSeal) (present : entry ∈ (result.2.keys pending.material).1.successfulSeals) :
    ∃ (width : pending.context.associatedData.length = 281) (record : CtxRomRecord),
      entry = ⟨RawCtxSelectedMessageSealing.selectedInput (materialAt before.base.chain pending.material).2
        pending.sequence (replaceContext replace pending.context) width, record⟩ ∧
      result.1 = (codec.frameWrite ⟨pending.sequence, pending.context.senderId, record.encode⟩).map
        (fun ciphertext => ⟨ciphertext, pending.context.targetId, pending.sequence⟩) := by
  obtain ⟨_, unchanged | generated⟩ := erased_sealing_trace modes ideal replace setup codec pending before result supported
  · simp only [unchanged.2.2 pending.material, empty, List.not_mem_nil] at present
  · obtain ⟨width, record, dictionary, _, writer⟩ := generated
    refine ⟨width, record, ?_, writer⟩
    simpa only [dictionary, empty, List.mem_singleton] using present

/-- A failed writer for the decoded matching frame is the literal optional reply of this fresh sealing callback. -/
theorem sealing_failed (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (before : CtxPrivate n)
    (result : Option RawCtxSourceSend.Encrypted × CtxPrivate n)
    (supported : result ∈ support ((PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.sealing pending)).run before))
    (empty : (before.keys pending.material).1.successfulSeals = [])
    (entry : CtxSuccessfulSeal) (present : entry ∈ (result.2.keys pending.material).1.successfulSeals)
    (frame : RawCtxReceive.DecodedFrame) (matched : Matches frame entry) (failed : codec.frameWrite frame = none) :
    result.1 = none := by
  obtain ⟨width, record, rfl, writer⟩ := sealing_entry modes ideal replace setup codec pending before result supported empty entry present
  have frameEq := matches_selected frame (materialAt before.base.chain pending.material).2 pending.sequence
    (replaceContext replace pending.context) width record matched
  change frame = ⟨pending.sequence, pending.context.senderId, record.encode⟩ at frameEq
  simpa only [← frameEq, failed, Option.map_none] using writer

/-- A later matching dictionary witness forces this actual fresh callback's writer failure when the continuation makes no further selected seal. -/
theorem suffix_failed {X : Type} (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (before : CtxPrivate n)
    (reply : Option RawCtxSourceSend.Encrypted × CtxPrivate n)
    (supported : reply ∈ support ((PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.sealing pending)).run before))
    (empty : (before.keys pending.material).1.successfulSeals = [])
    (work : OracleComp (ServiceSpec n) X)
    (noSeal : work.IsQueryBoundP (PqxdhRecordFactsOriginMuteServices.IsTargetSealing pending.material) 0)
    (result : X × CtxPrivate n)
    (finished : result ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) work).run reply.2))
    (entry : CtxSuccessfulSeal) (present : entry ∈ (result.2.keys pending.material).1.successfulSeals)
    (frame : RawCtxReceive.DecodedFrame) (matched : Matches frame entry) (failed : codec.frameWrite frame = none) :
    reply.1 = none := by
  apply sealing_failed modes ideal replace setup codec pending before reply supported empty entry ?_ frame matched failed
  simpa only [PqxdhRecordFactsOriginOrdinalPreserve.erased_program pending.material modes
    (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
    (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace work noSeal reply.2 result finished] using present

/-- An exact chronological source prefix preserves every all-reply query predicate of its remaining continuation. -/
theorem prefix_queries {X : Type} (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (predicate : Service n → Prop) {initial work : OracleComp (ServiceSpec n) X}
    {start state : CtxPrivate n} {past0 past : List (Label n)}
    {cuts : List (PqxdhRecordFactsOriginOrdinalCut.Cut n X)}
    (good : initial.AllQueriesSatisfy predicate)
    (before : PqxdhRecordFactsOriginOrdinalPath.Prefix service initial start past0 work state past cuts) :
    work.AllQueriesSatisfy predicate := by
  induction before with
  | initial => exact good
  | step before supported ih =>
    rw [allQueriesSatisfy_query_bind_iff] at ih
    exact ih.2 _

/-- The source-aligned callback stores exactly its selected coordinate's wire sequence in every fresh dictionary entry. -/
theorem sealing_entry_sequence (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (before : CtxPrivate n)
    (result : Option RawCtxSourceSend.Encrypted × CtxPrivate n)
    (supported : result ∈ support ((PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.sealing pending)).run before))
    (empty : (before.keys pending.material).1.successfulSeals = [])
    (aligned : PqxdhRecordFactsOriginSealingAligned.SealingAligned (.sealing pending))
    (entry : CtxSuccessfulSeal) (present : entry ∈ (result.2.keys pending.material).1.successfulSeals) :
    entry.input.context.ad.seq = pending.material.position + 1 := by
  obtain ⟨width, record, rfl, _⟩ := sealing_entry modes ideal replace setup codec pending before result supported empty entry present
  exact aligned

open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhRecordLiftInterface (Environment)
open PqxdhRecordFactsOriginOrdinalCut (Cut)
open PqxdhRecordFactsOriginOrdinalPath (Prefix)

/-- Every selected dictionary entry along an initialized actual source prefix has the wire sequence of its own material coordinate. -/
theorem source_prefix_sequence {E X : Type} (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (budget : Budget) (adversary : OracleComp (ModeSpec mode) X)
    (respects : budget.Respects adversary) (client : OracleComp (ServiceSpec n) (Client n E X))
    (state : CtxPrivate n) (past : List (Label n)) (cuts : List (Cut n (Client n E X)))
    (reached : Prefix (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) [] client state past cuts)
    (label : Label n) (entry : CtxSuccessfulSeal) (present : entry ∈ (state.keys label).1.successfulSeals) :
    entry.input.context.ad.seq = label.position + 1 := by
  obtain ⟨cut, reply, earlier, later, prior, answered, material, _, _, empty, _, inserted, _, _⟩ :=
    PqxdhRecordFactsOriginOrdinalPathEntries.source_prefix_entry modes replace setup codec route env serverKid bounds mode budget adversary respects client state past cuts reached label entry present
  have aligned := prefix_queries _ PqxdhRecordFactsOriginSealingAligned.SealingAligned
    (PqxdhRecordFactsOriginSealingAligned.program env setup.source.crypto codec route serverKid bounds mode adversary) prior
  subst label
  rw [allQueriesSatisfy_query_bind_iff] at aligned
  exact sealing_entry_sequence modes ideal replace setup codec cut.pending cut.state reply answered empty aligned.1 entry inserted

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealAlignment

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealAlignment.sealing_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealAlignment.sealing_entry

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealAlignment.sealing_failed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealAlignment.sealing_failed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealAlignment.suffix_failed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealAlignment.suffix_failed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealAlignment.prefix_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealAlignment.prefix_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealAlignment.sealing_entry_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealAlignment.sealing_entry_sequence

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealAlignment.source_prefix_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealAlignment.source_prefix_sequence
