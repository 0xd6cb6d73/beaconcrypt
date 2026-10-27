-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginDictionary
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability

/-! Source callback witnesses for ideal record origin. These proofs retain the actual parsers, selected coordinates, optional plaintexts and writer buffers. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginServices
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal PqxdhRecordFactsOriginReplay PqxdhRecordFactsOriginDictionary
variable {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Every accepted hidden opening in an ideal mode refers to a pre-existing coordinate dictionary entry with the actual returned plaintext. -/
theorem opening_frame (modes : PqxdhRecordLiftWorldCompiler.Label n → KeyMode)
    (ideal : ∀ label, modes label ≠ .real) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (pending : PqxdhRecordLiftProtocol.Opening n) (before after : CtxPrivate n)
    (opened : RawCtxWholeOwner.Decrypted)
    (supported : (.Some opened, after) ∈ support
      ((ctxInterpreter modes replace setup codec (.opening pending)).run before)) :
    ∃ label, RawCtxInterpretedOpening.material pending = .ok (.Some label) ∧
      ∃ frame, codec.frameRead pending.context.raw = some frame ∧
      ∃ entry ∈ (before.keys label).1.successfulSeals,
        Matches frame entry ∧ entry.input.plaintext = opened.plaintext := by
  change (.Some opened, after) ∈ support ((simulateQ
    (keyed modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto)
    (hiddenOpening (PqxdhRecordLiftProtocol.cachedSeeds before.base) before.base.chain pending)).run before) at supported
  unfold hiddenOpening at supported
  split at supported
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    cases congrArg Prod.fst supported
  · split at supported
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases congrArg Prod.fst supported
    · rename_i input arguments
      split at supported
      · rename_i width
        simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at supported
        obtain ⟨⟨reply, secret⟩, reached, equal⟩ := supported
        cases reply with
        | none => cases congrArg Prod.fst equal
        | some plaintext =>
          have replyEq : RawCtxSharedOpeningConsumer.apiReply input.sequence input.context (some plaintext) = .Some opened := congrArg Prod.fst equal
          cases replyEq
          have contextEq : input.context = pending.context :=
            (PqxdhRecordLiftCtxHybrid.openArguments_facts _ input arguments).2
          obtain ⟨frame, readFrame, entry, member, matched, message⟩ :=
            keyed_frame modes codec.frameRead setup.source.crypto input.material (ideal input.material)
              (RawCtxUniversalDecoder.envelope (materialAt before.base.chain input.material).2 input.context width)
              before secret plaintext reached
          refine ⟨input.material, ?_, frame, by simpa only [RawCtxUniversalDecoder.envelope, contextEq] using readFrame,
            entry, member, matched, message⟩
          simpa only [RawCtxChainInterpretation.opening_material_chains] using
            PqxdhRecordLiftCtxAvailability.openArguments_material _ input arguments
      · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        cases congrArg Prod.fst supported

/-- Raw keyed requests preserve every coordinate's seal dictionary. -/
theorem keyed_raw_seals (modes : PqxdhRecordLiftWorldCompiler.Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto) (label : PqxdhRecordLiftWorldCompiler.Label n)
    (ideal : modes label ≠ .real) (raw : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : Option Pqxdh.Bytes × CtxPrivate n)
    (supported : result ∈ support ((keyed modes decode crypto (label, .inr raw)).run before)) :
    ∀ other, (result.2.keys other).1.successfulSeals = (before.keys other).1.successfulSeals := by
  have facts := keyed_step modes decode crypto (label, .inr raw) ideal before result supported
  intro other
  by_cases same : other = label
  · exact same ▸ facts.1
  · exact congrArg (fun entry : KeyEntry => entry.1.successfulSeals) (facts.2 other same)

/-- Actual hidden openings preserve every seal dictionary through all parser and validation refusals. -/
theorem opening_seals (modes : PqxdhRecordLiftWorldCompiler.Label n → KeyMode)
    (ideal : ∀ label, modes label ≠ .real) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (pending : PqxdhRecordLiftProtocol.Opening n) (before : CtxPrivate n)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × CtxPrivate n)
    (supported : result ∈ support ((ctxInterpreter modes replace setup codec (.opening pending)).run before)) :
    ∀ label, (result.2.keys label).1.successfulSeals = (before.keys label).1.successfulSeals := by
  change result ∈ support ((simulateQ
    (keyed modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto)
    (hiddenOpening (PqxdhRecordLiftProtocol.cachedSeeds before.base) before.base.chain pending)).run before) at supported
  unfold hiddenOpening at supported
  split at supported
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact fun _ => rfl
  · split at supported
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact fun _ => rfl
    · rename_i input arguments
      split at supported
      · rename_i width
        simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at supported
        obtain ⟨inner, reached, rfl⟩ := supported
        exact keyed_raw_seals modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
          input.material (ideal input.material) _ before inner reached
      · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact fun _ => rfl

/-- The hidden sealing client makes exactly its selected keyed request and then retains the source writer result and frame log. -/
theorem hiddenSealing_call (writer : RawCtxMixedShared.Writer)
    (table : PqxdhRecordLiftChainTable.Table (PqxdhRecordLiftInterface.Slot n))
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (pending : PqxdhRecordLiftProtocol.Sealing n)
    (frames : PqxdhRecordLiftLoggedAdapters.Frames) (width : pending.context.associatedData.length = 281) :
    (hiddenSealing writer table replace pending).run frames =
      PqxdhRecordLiftCtxHybrid.sealedReply writer pending frames <$>
        ((KeyedSpec n).query (pending.material, .inl (.inr (.inr
          (RawCtxSelectedMessageSealing.selectedInput (materialAt table pending.material).2 pending.sequence
            (replaceContext replace pending.context) width)))) : OracleComp (KeyedSpec n) (Option CtxRomRecord)) := by
  change (if width' : (replaceContext replace pending.context).associatedData.length = 281 then _ else _) = _
  have width' : (replaceContext replace pending.context).associatedData.length = 281 := width
  rw [dite_eq_left_of_eq_true (eq_true width'), map_eq_bind_pure_comp]
  congr 1
  funext reply
  cases reply <;> rfl

/-- Exact seal-dictionary and pending-frame effects, including a generated record whose writer refuses it. -/
def SealingTrace (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (before : CtxPrivate n)
    (result : Option RawCtxSourceSend.Encrypted × CtxPrivate n) : Prop :=
  result.2.base.produced = before.base.produced ∧
    ((result.1 = none ∧ result.2.base.pending = before.base.pending ∧
        ∀ label, (result.2.keys label).1.successfulSeals = (before.keys label).1.successfulSeals) ∨
      ∃ (width : pending.context.associatedData.length = 281) (record : CtxRomRecord),
        (result.2.keys pending.material).1.successfulSeals =
          ⟨RawCtxSelectedMessageSealing.selectedInput (materialAt before.base.chain pending.material).2
            pending.sequence (replaceContext replace pending.context) width, record⟩ ::
            (before.keys pending.material).1.successfulSeals ∧
        result.2.base.pending = before.base.pending ++ [⟨pending.sequence, pending.context.senderId, record.encode⟩] ∧
        result.1 = (writer ⟨pending.sequence, pending.context.senderId, record.encode⟩).map
          (fun ciphertext => ⟨ciphertext, pending.context.targetId, pending.sequence⟩))

/-- A supported hidden sealing has exactly the seal and writer effects specified by `SealingTrace`. -/
theorem sealing_trace (modes : PqxdhRecordLiftWorldCompiler.Label n → KeyMode)
    (ideal : ∀ label, modes label ≠ .real) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (before : CtxPrivate n)
    (result : Option RawCtxSourceSend.Encrypted × CtxPrivate n)
    (supported : result ∈ support ((ctxInterpreter modes replace setup codec (.sealing pending)).run before)) :
    SealingTrace codec.frameWrite replace pending before result := by
  change result ∈ support (do
    let inner ← (simulateQ (keyed modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto)
      ((hiddenSealing codec.frameWrite before.base.chain replace pending).run before.base.pending)).run before
    pure (inner.1.1, { inner.2 with base := { inner.2.base with pending := inner.1.2 } })) at supported
  simp only [bind_pure_comp, support_map, Set.mem_image] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  by_cases width : pending.context.associatedData.length = 281
  · rw [hiddenSealing_call codec.frameWrite before.base.chain replace pending before.base.pending width] at member
    simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map, Set.mem_image] at member
    obtain ⟨keyedResult, keyedMember, rfl⟩ := member
    obtain ⟨localAfter, reached, keys, chain, seeds, produced, oldPending⟩ :=
      keyed_witness modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
        (pending.material, .inl (.inr (.inr (RawCtxSelectedMessageSealing.selectedInput
          (materialAt before.base.chain pending.material).2 pending.sequence
          (replaceContext replace pending.context) width)))) before keyedResult keyedMember
    have step := keyed_step modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
      (pending.material, .inl (.inr (.inr (RawCtxSelectedMessageSealing.selectedInput
        (materialAt before.base.chain pending.material).2 pending.sequence
        (replaceContext replace pending.context) width))))
      (ideal pending.material) before keyedResult keyedMember
    refine ⟨produced, ?_⟩
    cases reply : keyedResult.1 with
    | none =>
      left
      refine ⟨rfl, rfl, ?_⟩
      intro label
      by_cases same : label = pending.material
      · subst label
        simpa only [QueryStep, SealStep, reply] using step.1
      · exact congrArg (fun entry : KeyEntry => entry.1.successfulSeals) (step.2 label same)
    | some record =>
      right
      refine ⟨width, record, ?_, rfl, rfl⟩
      simpa only [QueryStep, SealStep, reply] using step.1
  · have width' : ¬ (replaceContext replace pending.context).associatedData.length = 281 := width
    simp only [hiddenSealing, StateT.run, dite_eq_right width', simulateQ_pure] at member
    subst inner
    exact ⟨rfl, Or.inl ⟨rfl, rfl, fun _ => rfl⟩⟩

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginServices


/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginServices.opening_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginServices.opening_frame

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginServices.keyed_raw_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginServices.keyed_raw_seals

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginServices.opening_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginServices.opening_seals

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginServices.hiddenSealing_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginServices.hiddenSealing_call

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginServices.sealing_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginServices.sealing_trace
