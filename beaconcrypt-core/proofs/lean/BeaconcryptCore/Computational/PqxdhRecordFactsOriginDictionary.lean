-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginReplay

/-! Exact replay-dictionary update laws. Rejected raw calls retain their private suffix caches; only a successful seal appends a dictionary record. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginDictionary
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxReplayDictionary
open PqxdhRecordLiftIdeal PqxdhRecordFactsOriginReplay

/-- Raw decoding and verification preserve every existing dictionary seal, whether accepted or rejected. -/
theorem localRaw_seals (decode : RawDecoder) (raw : Pqxdh.Bytes) (before : KeyEntry)
    (result : Option Pqxdh.Bytes × KeyEntry)
    (supported : result ∈ support (AdaptiveCtxSharedReplay.localRaw decode raw before)) :
    result.2.1.successfulSeals = before.1.successfulSeals := by
  unfold AdaptiveCtxSharedReplay.localRaw at supported
  cases decoded : decode raw <;> simp only [decoded, support_pure, Set.mem_singleton_iff,
    bind_pure_comp, support_map] at supported
  · exact congrArg (fun value : Option Pqxdh.Bytes × KeyEntry => value.2.1.successfulSeals) supported
  · obtain ⟨inner, reached, rfl⟩ := supported
    exact localPrivate_seals _ ({ before.1 with rawAttempts := before.1.rawAttempts + 1 }, before.2) inner reached

/-- Successful sealing adds its exact input and returned record; refusal adds nothing. -/
def SealStep (input : CtxSealInput) (before : KeyEntry) (result : Option CtxRomRecord × KeyEntry) : Prop :=
  result.2.1.successfulSeals = match result.1 with
    | none => before.1.successfulSeals
    | some record => ⟨input, record⟩ :: before.1.successfulSeals

/-- Replay-mode sealing records the actual primitive ciphertext and persistent private commitment. -/
theorem localSeal_step (crypto : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput)
    (before : KeyEntry) (result : Option CtxRomRecord × KeyEntry)
    (supported : result ∈ support (AdaptiveCtxSharedReplay.localSeal crypto key input before)) :
    SealStep input before result := by
  unfold AdaptiveCtxSharedReplay.localSeal at supported
  split at supported <;> simp only [support_pure, Set.mem_singleton_iff, bind_pure_comp, support_map] at supported
  · exact supported ▸ rfl
  · obtain ⟨inner, reached, rfl⟩ := supported
    exact congrArg (List.cons _) (localPrivate_seals _ before inner reached)

/-- Random-mode sealing records the same exact input and returned record after its private lookup. -/
theorem randomSeal_step (input : CtxSealInput) (before : KeyEntry)
    (result : Option CtxRomRecord × KeyEntry) (supported : result ∈ support (randomSeal input before)) :
    SealStep input before result := by
  unfold randomSeal at supported
  split at supported <;> simp only [support_pure, Set.mem_singleton_iff, mem_support_bind_iff] at supported
  · exact supported ▸ rfl
  · obtain ⟨body, _, tag, _, inner, reached, rfl⟩ := supported
    exact congrArg (List.cons _) (localPrivate_seals _ before inner reached)

/-- Exact seal-list update for each request, with the reply's own dependent type. -/
def QueryStep (query : ReceiveSpec.Domain) (before : KeyEntry) : ReceiveSpec.Range query → KeyEntry → Prop :=
  match query with
  | .inl (.inr (.inr input)) => fun reply after => SealStep input before (reply, after)
  | _ => fun _ after => after.1.successfulSeals = before.1.successfulSeals

/-- Every ideal-key service changes its seal dictionary only by recording its own successful seal. -/
theorem key_step (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (mode : KeyMode) (ideal : mode ≠ .real) (query : ReceiveSpec.Domain) (before : KeyEntry)
    (result : ReceiveSpec.Range query × KeyEntry)
    (supported : result ∈ support ((keyImpl decode crypto key mode query).run before)) :
    QueryStep query before result.1 result.2 := by
  cases mode with
  | real => exact False.elim (ideal rfl)
  | replay | random =>
    rcases query with ((coin | (hash | input)) | raw)
    all_goals first
    | exact localSeal_step crypto key _ before result supported
    | exact randomSeal_step _ before result supported
    | exact localRaw_seals decode _ before result supported
    | skip
    all_goals simp only [keyImpl, StateT.run, AdaptiveCtxSharedModes.localImpl, Bool.false_eq_true,
      ite_false, AdaptiveCtxSharedReplay.localImpl, randomImpl, bind_pure_comp, support_map] at supported
    all_goals obtain ⟨_, _, rfl⟩ := supported; rfl

variable {n : Nat}

/-- Counted shared-ROM interpretation retains a supported one-key result with the same optional reply and exact updated coordinate state. -/
theorem keyed_witness (modes : PqxdhRecordLiftWorldCompiler.Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto) (query : (KeyedSpec n).Domain)
    (before : CtxPrivate n) (result : (KeyedSpec n).Range query × CtxPrivate n)
    (supported : result ∈ support ((keyed modes decode crypto query).run before)) :
    ∃ after, (result.1, after) ∈ support
      ((keyImpl decode crypto (materialAt before.base.chain query.1).1 (modes query.1) query.2).run
        (before.keys query.1)) ∧
      result.2.keys = Function.update before.keys query.1 after ∧
      result.2.base.chain = before.base.chain ∧ result.2.base.seeds = before.base.seeds ∧
      result.2.base.produced = before.base.produced ∧ result.2.base.pending = before.base.pending := by
  simp only [keyed, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨sampled, reached, rfl⟩ := supported
  simp only [PqxdhRecordLiftProtocol.sampled, StateT.run, bind_pure_comp, support_map] at reached
  obtain ⟨counted, countedSupport, rfl⟩ := reached
  refine ⟨counted.1.1.2, ?_, rfl, rfl, rfl, rfl, rfl⟩
  exact PqxdhRecordLiftFlat.support_run_fst AdaptiveCtxSharedHash.hashImpl _ before.base.primitive.2 counted.1
    (PqxdhRecordLiftFlat.support_run_fst PqxdhRecordLiftWorld.countCoin _ before.base.primitive.1.uniform counted countedSupport)

/-- The coordinate interpreter obeys the exact dictionary rule, and all other coordinate dictionaries are retained. -/
theorem keyed_step (modes : PqxdhRecordLiftWorldCompiler.Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto) (query : (KeyedSpec n).Domain)
    (ideal : modes query.1 ≠ .real) (before : CtxPrivate n)
    (result : (KeyedSpec n).Range query × CtxPrivate n)
    (supported : result ∈ support ((keyed modes decode crypto query).run before)) :
    QueryStep query.2 (before.keys query.1) result.1 (result.2.keys query.1) ∧
      ∀ label, label ≠ query.1 → result.2.keys label = before.keys label := by
  obtain ⟨after, reached, keys, _⟩ := keyed_witness modes decode crypto query before result supported
  simp only [keys, Function.update_self]
  exact ⟨key_step decode crypto (materialAt before.base.chain query.1).1 (modes query.1) ideal
    query.2 (before.keys query.1) (result.1, after) reached,
    fun label different => Function.update_of_ne different _ _⟩

/-- A successful global keyed receive has a matching source frame in the selected coordinate's existing dictionary. -/
theorem keyed_frame (modes : PqxdhRecordLiftWorldCompiler.Label n → KeyMode)
    (read : RawCtxReceive.FrameDecoder) (crypto : Pqxdh.Crypto)
    (label : PqxdhRecordLiftWorldCompiler.Label n) (ideal : modes label ≠ .real)
    (envelope : RawCtxUniversalDecoder.Envelope) (before after : CtxPrivate n) (plaintext : Pqxdh.Bytes)
    (supported : (some plaintext, after) ∈ support
      ((keyed modes (RawCtxUniversalDecoder.decoder read) crypto
        (label, .inr (RawCtxUniversalDecoder.pack envelope))).run before)) :
    ∃ frame, read envelope.raw = some frame ∧ ∃ entry ∈ (before.keys label).1.successfulSeals,
      Matches frame entry ∧ entry.input.plaintext = plaintext := by
  obtain ⟨localAfter, reached, _⟩ := keyed_witness modes (RawCtxUniversalDecoder.decoder read) crypto
    (label, .inr (RawCtxUniversalDecoder.pack envelope)) before (some plaintext, after) supported
  exact keyRaw_frame read crypto (materialAt before.base.chain label).1 (modes label) ideal
    envelope (before.keys label) plaintext localAfter reached

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginDictionary

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginDictionary.localRaw_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginDictionary.localRaw_seals

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginDictionary.localSeal_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginDictionary.localSeal_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginDictionary.randomSeal_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginDictionary.randomSeal_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginDictionary.key_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginDictionary.key_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginDictionary.keyed_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginDictionary.keyed_witness

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginDictionary.keyed_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginDictionary.keyed_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginDictionary.keyed_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginDictionary.keyed_frame
