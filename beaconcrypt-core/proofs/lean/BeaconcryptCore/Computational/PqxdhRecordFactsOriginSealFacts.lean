-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPathEntries
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginServices

/-! Exact dictionary and writer effects of the erased source sealing callback. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealFacts
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftProtocol (Service ServiceSpec Private)
open PqxdhRecordFactsOriginDictionary (SealStep QueryStep key_step)
variable {n : Nat}

/-- Actual source sealing coordinates name the allocated wire sequence. -/
def SealingAligned : Service n → Prop
  | .sealing pending => pending.sequence.val = pending.material.position + 1
  | _ => True

/-- An erased local sealing request still records exactly the actual input and optional returned record. -/
theorem erased_local_seal_step (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (mode : KeyMode) (ideal : mode ≠ .real) (input : CtxSealInput)
    (before : PqxdhRecordFactsPrivateCache.State)
    (result : Option CtxRomRecord × PqxdhRecordFactsPrivateCache.State)
    (supported : result ∈ support ((PqxdhRecordFactsPrivateCacheRandom.erased decode crypto key mode
      (.inl (.inr (.inr input)))).run before)) :
    SealStep input before.1 (result.1, result.2.1) := by
  simp only [PqxdhRecordFactsPrivateCacheRandom.erased,
    PqxdhRecordFactsPrivateCacheRandom.modePointed, StateT.run_map,
    Functor.map_map] at supported
  apply key_step decode crypto key mode ideal (.inl (.inr (.inr input))) before.1 (result.1, result.2.1)
  apply PqxdhRecordLiftFlat.support_run_fst AdaptiveCtxSharedHash.hashImpl _ before.2 ((result.1, result.2.1), result.2.2)
  simp only [PqxdhRecordFactsPrivateCacheRandom.linked, QueryImpl.flattenStateT,
    QueryImpl.mapStateTBase, StateT.run, StateT.mk,
    Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact reached

/-- The exact erased keyed seal preserves its own input/record update and all nonselected dictionaries and source writer fields. -/
theorem erased_keyed_seal_step (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (label : Label n) (ideal : modes label ≠ .real) (input : CtxSealInput)
    (before : CtxPrivate n) (result : Option CtxRomRecord × CtxPrivate n)
    (supported : result ∈ support ((PqxdhRecordFactsPrivateCacheFamily.erasedKeyed modes decode crypto
      (label, .inl (.inr (.inr input)))).run before)) :
    SealStep input (before.keys label) (result.1, result.2.keys label) ∧
      result.2.base.chain = before.base.chain ∧ result.2.base.produced = before.base.produced ∧
      result.2.base.pending = before.base.pending ∧
      ∀ other, other ≠ label → result.2.keys other = before.keys other := by
  obtain ⟨localState, reached, keys, baseKept⟩ := PqxdhRecordFactsPrivateCacheSource.erasedKeyed_witness
    modes decode crypto (label, .inl (.inr (.inr input))) before result supported
  simp only [keys, Function.update_self, baseKept]
  exact ⟨erased_local_seal_step decode crypto (materialAt before.base.chain label).1 (modes label) ideal input
    (before.keys label, before.base.primitive.2) (result.1, localState) reached,
    True.intro, True.intro, True.intro, fun other different => Function.update_of_ne different _ _⟩

variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Erased source sealing retains the exact generated dictionary entry, buffered frame and literal optional writer outcome. -/
theorem erased_sealing_trace (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (before : CtxPrivate n)
    (result : Option RawCtxSourceSend.Encrypted × CtxPrivate n)
    (supported : result ∈ support ((PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.sealing pending)).run before)) :
    PqxdhRecordFactsOriginServices.SealingTrace codec.frameWrite replace pending before result := by
  change result ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheServices.erased modes
    (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
    (PqxdhRecordFactsPrivateCacheCompiler.base (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec)))
    (PqxdhRecordFactsPrivateCacheCompiler.compile codec.frameWrite replace (.sealing pending))).run before) at supported
  rw [PqxdhRecordFactsPrivateCacheSource.erased_sealing] at supported
  simp only [bind_pure_comp, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  by_cases width : pending.context.associatedData.length = 153
  · rw [PqxdhRecordFactsOriginServices.hiddenSealing_call codec.frameWrite before.base.chain replace pending before.base.pending width] at member
    simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at member
    obtain ⟨keyedResult, keyedMember, rfl⟩ := member
    obtain ⟨step, chain, produced, oldPending, others⟩ := erased_keyed_seal_step modes
      (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto pending.material (ideal pending.material)
      (RawCtxSelectedMessageSealing.selectedInput (materialAt before.base.chain pending.material).2 pending.sequence
        (replaceContext replace pending.context) width) before keyedResult keyedMember
    refine ⟨produced, ?_⟩
    cases reply : keyedResult.1 with
    | none =>
      simp only [PqxdhRecordLiftCtxHybrid.sealedReply, reply]
      refine Or.inl ⟨True.intro, True.intro, fun label => ?_⟩
      by_cases same : label = pending.material
      · simpa only [same, SealStep, reply] using step
      · exact congrArg (fun entry : KeyEntry => entry.1.successfulSeals) (others label same)
    | some record =>
      simp only [PqxdhRecordLiftCtxHybrid.sealedReply, reply]
      refine Or.inr ⟨width, record, ?_, rfl, rfl⟩
      simpa only [SealStep, reply] using step
  · have width' : ¬ (replaceContext replace pending.context).associatedData.length = 153 := width
    simp only [hiddenSealing, StateT.run, dite_eq_right width', simulateQ_pure] at member
    subst inner
    exact ⟨rfl, Or.inl ⟨rfl, rfl, fun _ => rfl⟩⟩

/-- Every actual erased service retains every previously generated seal entry, including failed writers and opening attempts. -/
theorem erased_service_mono (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : Service n) (before : CtxPrivate n) (result : (ServiceSpec n).Range query × CtxPrivate n)
    (supported : result ∈ support ((PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec query).run before))
    (label : Label n) (entry : CtxSuccessfulSeal) (present : entry ∈ (before.keys label).1.successfulSeals) :
    entry ∈ (result.2.keys label).1.successfulSeals := by
  by_cases sealed : ∃ pending, query = .sealing pending
  · obtain ⟨pending, rfl⟩ := sealed
    by_cases same : label = pending.material
    · obtain ⟨_, unchanged | generated⟩ := erased_sealing_trace modes ideal replace setup codec pending before result supported
      · exact (unchanged.2.2 label).symm ▸ present
      · obtain ⟨width, record, dictionary, _, _⟩ := generated
        simpa only [same, dictionary, List.mem_cons] using (Or.inr (same ▸ present))
    · simpa only [PqxdhRecordFactsOriginOrdinalServices.service_sealing_other modes
        (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
        (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace pending before result supported label same] using present
  · simpa only [PqxdhRecordFactsOriginOrdinalServices.service_nonSeal modes
      (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
      (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace query
      (fun pending same => sealed ⟨pending, same⟩) before result supported label] using present

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealFacts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealFacts.erased_local_seal_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealFacts.erased_local_seal_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealFacts.erased_keyed_seal_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealFacts.erased_keyed_seal_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealFacts.erased_sealing_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealFacts.erased_sealing_trace

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealFacts.erased_service_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealFacts.erased_service_mono
