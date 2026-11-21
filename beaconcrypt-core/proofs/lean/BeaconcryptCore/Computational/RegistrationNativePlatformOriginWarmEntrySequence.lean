-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmPrefixFacts
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealFacts
/-! Every actual erased seal dictionary entry retains the source wire sequence belonging to its material coordinate. The source program supplies alignment, while arbitrary warm base caches and counters remain intact. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmEntrySequence
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordFactsOriginOrdinalPath (Prefix)
open PqxdhRecordFactsOriginSealingAligned (SealingAligned)
variable {n : Nat} {I KemSK Reader Response E Value X : Type} {base : OracleSpec I}
variable (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (PqxdhRecordLiftInterface.WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value))
    (extended : OracleComp (ServiceSpec n) X)
    (erase : X → PqxdhRecordLiftIdeal.Client n (RegistrationNativeRecordPackage.Extra E) Value)
    (erasure : erase <$>extended=RegistrationNativeRecordOriginProgram.program codec route work)
include erasure in
/-- Actual pure instrumentation inherits source sealing alignment for every possible reply. -/
theorem aligned : extended.AllQueriesSatisfy SealingAligned := by
  have original := RegistrationNativeRecordOriginProgram.aligned codec route work
  rw [←erasure,allQueriesSatisfy_def,isQueryBound_map_iff] at original
  rw [allQueriesSatisfy_def]
  exact original

variable (modes : Label n →KeyMode) (ideal : ∀label,modes label≠.real)
    (replace : Pqxdh.Bytes →Pqxdh.Bytes) (setup : Setup base KemSK)
local notation "service"=>PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec
private def Consistent (state : CtxPrivate n) : Prop := ∀label entry,
  entry∈(state.keys label).1.successfulSeals→entry.input.context.ad.seq=label.position+1

include ideal in
private theorem prefix_consistent (sourceAligned : extended.AllQueriesSatisfy SealingAligned)
    (start : CtxPrivate n) (empty : ∀label,(start.keys label).1.successfulSeals=[])
    (rest : OracleComp (ServiceSpec n) X) (state : CtxPrivate n) (past : List (Label n))
    (cuts : List (PqxdhRecordFactsOriginOrdinalCut.Cut n X))
    (called : Prefix service extended start [] rest state past cuts) : Consistent state := by
  classical
  have kept : rest.AllQueriesSatisfy SealingAligned ∧Consistent state := by
    induction called with
    | initial=>
      refine ⟨sourceAligned,?_⟩
      intro label entry member
      simp only [empty,List.not_mem_nil] at member
    | @step query next before history cuts reply prior supported ih=>
      obtain ⟨head,following⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp ih.1
      refine ⟨following reply.1,?_⟩
      intro label entry member
      by_cases sealing : ∃pending,query=.sealing pending
      · obtain ⟨pending,rfl⟩ := sealing
        change pending.sequence.val=pending.material.position+1 at head
        by_cases same : label=pending.material
        · subst label
          obtain ⟨_produced,unchanged|generated⟩ :=
            PqxdhRecordFactsOriginSealFacts.erased_sealing_trace modes ideal replace setup codec pending before reply supported
          · rw [unchanged.2.2 pending.material] at member
            exact ih.2 pending.material entry member
          · obtain ⟨width,record,dictionary,_pending,_returned⟩ := generated
            rw [dictionary,List.mem_cons] at member
            rcases member with added|old
            · subst entry
              exact head
            · exact ih.2 pending.material entry old
        · have unchanged := PqxdhRecordFactsOriginOrdinalServices.service_sealing_other modes
            (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
            (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace pending before reply supported label same
          rw [unchanged] at member
          exact ih.2 label entry member
      · have unchanged := PqxdhRecordFactsOriginOrdinalServices.service_nonSeal modes
          (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
          (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace query
          (fun pending equal=>sealing ⟨pending,equal⟩) before reply supported label
        rw [unchanged] at member
        exact ih.2 label entry member
  exact kept.2

include erasure ideal in
/-- Every entry at the actual erased source prefix has its material coordinate's exact wire sequence, from the real warm start. -/
theorem entry_sequence (start : CtxPrivate n) (empty : ∀label,(start.keys label).1.successfulSeals=[])
    (rest : OracleComp (ServiceSpec n) X) (state : CtxPrivate n) (past : List (Label n))
    (cuts : List (PqxdhRecordFactsOriginOrdinalCut.Cut n X))
    (called : Prefix service extended start [] rest state past cuts)
    (label : Label n) (entry : CtxRomAuth.CtxSuccessfulSeal) (member : entry∈(state.keys label).1.successfulSeals) :
    entry.input.context.ad.seq=label.position+1 :=
  prefix_consistent codec extended modes ideal replace setup (aligned codec route work extended erase erasure)
    start empty rest state past cuts called label entry member
include erasure ideal in
/-- The same sequence invariant holds at the complete supported result of the actual warm source execution. -/
theorem run (start : CtxPrivate n) (empty : ∀label,(start.keys label).1.successfulSeals=[])
    (result : X ×CtxPrivate n) (supported : result∈support ((simulateQ service extended).run start))
    (label : Label n) (entry : CtxRomAuth.CtxSuccessfulSeal) (member : entry∈(result.2.keys label).1.successfulSeals) :
    entry.input.context.ad.seq=label.position+1 := by
  rw [←PqxdhRecordFactsOriginOrdinalTrace.track_drop service extended start [],support_map] at supported
  obtain ⟨tracked,called,equal⟩ := supported
  have path := PqxdhRecordFactsOriginOrdinalPath.support_path service extended start [] tracked called
  obtain ⟨past,ending⟩ := PqxdhRecordFactsOriginOrdinalFinalPrefix.path_prefix service path
  change tracked.2=result at equal
  rw [equal] at ending
  exact entry_sequence codec route work extended erase erasure modes ideal replace setup start empty
    (pure result.1) result.2 past tracked.1 ending label entry member
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmEntrySequence
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmEntrySequence.aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmEntrySequence.aligned
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmEntrySequence.entry_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmEntrySequence.entry_sequence

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmEntrySequence.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmEntrySequence.run
