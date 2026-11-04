-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeExperiment
import BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation

/-! The actual source receiver is instantiated on the exact instrumented primitive interpreter used by RegistrationNativeExperiment's record World. Its bounded slice requests and the primitive's successful-plaintext length law justify source Vec representation. The same primitive counters, uniform-query counts and CTX cache survive unchanged. Outer raw decoding, sender/owner routing and concrete codec/wrapper correspondence remain explicit separate obligations. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.RegistrationNativeExtractedReceive
open PqxdhServerAuthExperiment (Setup Codec)
open BeaconcryptCore.Refinement
variable {ι KemSK Reader Response : Type} {base : OracleSpec ι}

/-- A primitive functional law: successful detached AEAD opening does not enlarge its ciphertext body. -/
def AeadLength (crypto : Pqxdh.Crypto) : Prop :=
  ∀ key nonce ad ciphertext tag plaintext,
    crypto.aeadOpen key nonce ad ciphertext tag = some plaintext → plaintext.length ≤ ciphertext.length

/-- The ordinary detached primitive length law implies the exact combined-ciphertext law used by the source receiver. -/
theorem baseOpen_length (crypto : Pqxdh.Crypto) (length : AeadLength crypto)
    (input : RawCtxSourceOpen.BaseInput) (plaintext : Pqxdh.Bytes)
    (opened : RawCtxSourceOpen.baseOpen crypto input = some plaintext) :
    plaintext.length ≤ input.ciphertext.length := by
  unfold RawCtxSourceOpen.baseOpen at opened
  split at opened
  · exact ((length _ _ _ _ _ _ opened).trans (List.length_take_le _ _)).trans (Nat.sub_le _ _)
  · cases opened

/-- The source and abstract interpretations share precisely the World's original receive primitive operations. -/
noncomputable def primitives (setup : Setup base KemSK) (codec : Codec Reader Response) :
    QueryImpl RawCtxSourceOpen.NativeSpec (StateT PqxdhRecordLiftWorld.Primitive ProbComp) :=
  PqxdhRecordLiftWorld.primitives setup codec ∘ₛ RawCtxMixedOwner.receiveLift

/-- Instrumentation retains an actually supported primitive reply; counting coins and categories never fabricates a primitive result. -/
theorem primitive_supported (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain)
    (before after : PqxdhRecordLiftWorld.Primitive) (reply : RawCtxMixedOwner.NativeSpec.Range query)
    (reached : (reply, after) ∈ support ((PqxdhRecordLiftWorld.primitives setup codec query).run before)) :
    ∃ shared, (reply, shared) ∈ support
      ((PqxdhDeploymentNative.primitives setup codec query).run ((), before.2)) := by
  simp only [PqxdhRecordLiftWorld.primitives, StateT.run, mem_support_bind_iff] at reached
  obtain ⟨result, sampled, returned⟩ := reached
  have possible : result.1 ∈ support
      ((PqxdhDeploymentNative.primitives setup codec query).run ((), before.2)) := by
    apply OracleComp.support_simulateQ_run'_subset PqxdhRecordLiftWorld.countCoin _ before.1.uniform
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst sampled
  have same := (mem_support_pure_iff _ _).mp returned
  refine ⟨result.1.2, ?_⟩
  have replySame : reply = result.1.1 := congrArg Prod.fst same
  rw [replySame]
  exact possible

/-- The concrete shared CTX interpreter returns its actual fixed-width digest, including existing cache hits. -/
theorem hash_width (setup : Setup base KemSK) (codec : Codec Reader Response)
    (input : Pqxdh.Bytes) (before after : RawCtxSharedPrimitive.SharedState Unit) (bytes : Pqxdh.Bytes)
    (reached : (some bytes, after) ∈ support
      ((PqxdhDeploymentNative.primitives setup codec (.inr (.inr (.inr (.inl input))))).run before)) :
    bytes.length = 64 := by
  rw [PqxdhDeploymentNative.primitives, RawCtxMixedShared.shared_hash] at reached
  obtain ⟨⟨digest, cache⟩, _, returned⟩ := (mem_support_bind_iff _ _ _).mp reached
  have same := congrArg Prod.fst ((mem_support_pure_iff _ _).mp returned)
  have bytesSame := Option.some.inj same
  rw [bytesSame]
  simp

/-- The existing native ordinary opening returns the primitive's actual optional plaintext and its original shared state. -/
theorem opening_run (setup : Setup base KemSK) (codec : Codec Reader Response)
    (input : RawCtxSourceOpen.BaseInput) (before : RawCtxSharedPrimitive.SharedState Unit) :
    (PqxdhDeploymentNative.primitives setup codec (.inr (.inr (.inl input)))).run before =
      pure (RawCtxSourceOpen.baseOpen setup.source.crypto input, before) := by
  rfl

/-- The actual World interpreter meets the source reply-representation contracts from only the primitive AEAD length law. No codec or source-simulation law is assumed. -/
theorem functional (setup : Setup base KemSK) (codec : Codec Reader Response)
    (length : AeadLength setup.source.crypto) :
    AdapterRecordNativeRepresentation.Functional (primitives setup codec) := by
  constructor
  · intro input before after bytes reached
    have forwarded : (some bytes, after) ∈ support
        ((PqxdhRecordLiftWorld.primitives setup codec (.inr (.inr (.inr (.inl input))))).run before) := by
      simpa only [primitives, QueryImpl.apply_compose, RawCtxMixedOwner.receiveLift,
        simulateQ_spec_query] using reached
    obtain ⟨shared, original⟩ := primitive_supported setup codec (.inr (.inr (.inr (.inl input)))) before after (some bytes) forwarded
    exact hash_width setup codec input ((), before.2) shared bytes original
  · intro input before after bytes reached
    have forwarded : (some bytes, after) ∈ support
        ((PqxdhRecordLiftWorld.primitives setup codec (.inr (.inr (.inl input)))).run before) := by
      simpa only [primitives, QueryImpl.apply_compose, RawCtxMixedOwner.receiveLift,
        simulateQ_spec_query] using reached
    obtain ⟨shared, original⟩ := primitive_supported setup codec (.inr (.inr (.inl input))) before after (some bytes) forwarded
    rw [opening_run] at original
    have same := congrArg Prod.fst ((mem_support_pure_iff _ _).mp original)
    exact baseOpen_length setup.source.crypto length input bytes same.symm

/-- The source controller uses the World's exact instrumented primitive service, including its original cache and every primitive/uniform counter. -/
theorem controller_world (setup : Setup base KemSK) (codec : Codec Reader Response)
    (length : AeadLength setup.source.crypto) (erased : Array Std.U8 357#usize)
    (effect : record_effects.RecordReceiveEffect) (before : PqxdhRecordLiftWorld.Primitive) :
    (simulateQ (AdapterRecordNativeRepresentation.typed (primitives setup codec))
      ((fun result => AdapterRecordReceive.decodeResult <$> result) <$>
        AdapterRecordStatefulReceive.interpret erased
          (AdapterRecordStatefulReceive.drive (RecordEffectsReceiveRank.rank effect + 2) effect))).run before =
      (simulateQ (primitives setup codec) (RecordEffectsReceiveProgram.execute erased effect)).run before :=
  AdapterRecordNativeRepresentation.controller_native (primitives setup codec)
    (functional setup codec length) erased effect before

/-- Actual extracted admission and complete source receive execution preserve the exact World primitive state jointly with the full returned protocol kernel. -/
theorem receive_world (setup : Setup base KemSK) (codec : Codec Reader Response)
    (length : AeadLength setup.source.crypto) (erased : Array Std.U8 357#usize)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (sequence : Std.U64)
    (payload : Slice Std.U8) (ad : Array Std.U8 281#usize) (sender : Std.U64)
    (before : PqxdhRecordLiftWorld.Primitive) :
    (AdapterRecordNativeRepresentation.receive (primitives setup codec)
      erased kernel sequence payload ad sender).run before =
      (simulateQ (primitives setup codec)
        (RecordEffectsReceiveProgram.receive erased kernel sequence payload ad sender)).run before :=
  AdapterRecordNativeRepresentation.receive_native (primitives setup codec)
    (functional setup codec length) erased kernel sequence payload ad sender before

/-- The existing decoded sender check surrounds the source-selected inner controller. This is a typed model context, with outer Rust parser/routing correspondence left separate. -/
noncomputable def afterDecode (setup : Setup base KemSK) (codec : Codec Reader Response)
    (erased : Array Std.U8 357#usize) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (expected : Std.U64) (frame : RawCtxReceive.DecodedFrame)
    (payload : Slice Std.U8) (ad : Array Std.U8 281#usize) :
    StateT PqxdhRecordLiftWorld.Primitive ProbComp (RustM RecordEffectsReceiveProgram.Result) :=
  if frame.sender = expected then
    AdapterRecordNativeRepresentation.receive (primitives setup codec)
      erased kernel frame.sequence payload ad frame.sender
  else pure (.ok (kernel, none))

/-- Exact post-decode equality includes wrong-sender refusal, malformed protected payload, every optional primitive failure and all World counters/cache effects. -/
theorem afterDecode_native (setup : Setup base KemSK) (codec : Codec Reader Response)
    (length : AeadLength setup.source.crypto) (erased : Array Std.U8 357#usize)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (expected : Std.U64)
    (frame : RawCtxReceive.DecodedFrame) (payload : Slice Std.U8)
    (ad : Array Std.U8 281#usize) (before : PqxdhRecordLiftWorld.Primitive) :
    (afterDecode setup codec erased kernel expected frame payload ad).run before =
      (simulateQ (primitives setup codec)
        (RecordEffectsReceiveProgram.decoded erased kernel expected frame payload ad)).run before := by
  unfold afterDecode RecordEffectsReceiveProgram.decoded
  split
  · exact receive_world setup codec length erased kernel frame.sequence payload ad frame.sender before
  · rfl

/-- The selected source receive stage reaches the original World-owner receive interface with the exact represented payload and AD. These byte equalities do not assume a parser law or any security property. -/
theorem owner_native (setup : Setup base KemSK) (codec : Codec Reader Response)
    (length : AeadLength setup.source.crypto) (erased : Array Std.U8 357#usize)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (expected : Std.U64) (raw : Pqxdh.Bytes)
    (frame : RawCtxReceive.DecodedFrame) (associatedData : Pqxdh.Bytes)
    (payload : Slice Std.U8) (ad : Array Std.U8 281#usize)
    (payloadBytes : RawCtxNativeFramePrelude.sliceBytes payload = frame.payload)
    (adBytes : PqxdhRefinement.absBytes ad = associatedData) (before : PqxdhRecordLiftWorld.Primitive) :
    (afterDecode setup codec erased kernel expected frame payload ad).run before =
      (simulateQ (primitives setup codec)
        ((fun result => .ok result) <$> simulateQ RawCtxSourceOpen.nativeAdapter
          (if RawCtxReceive.ValidFrame expected associatedData frame then
            simulateQ RawCtxWholeOwner.adapter
              (RawCtxOwnerOracle.receive (Plaintext := RawCtxWholeOwner.Decrypted) kernel frame.sequence
                ⟨raw, frame, associatedData⟩)
          else pure (kernel, none)))).run before := by
  rw [afterDecode_native setup codec length,
    RecordEffectsReceiveBridge.decoded_native_model erased kernel expected raw frame associatedData payload ad
      payloadBytes adBytes]

end BeaconcryptCore.Computational.RegistrationNativeExtractedReceive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExtractedReceive.baseOpen_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExtractedReceive.baseOpen_length

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExtractedReceive.primitive_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExtractedReceive.primitive_supported

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExtractedReceive.hash_width' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExtractedReceive.hash_width

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExtractedReceive.opening_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExtractedReceive.opening_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExtractedReceive.functional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExtractedReceive.functional

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExtractedReceive.controller_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExtractedReceive.controller_world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExtractedReceive.receive_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExtractedReceive.receive_world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExtractedReceive.afterDecode_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExtractedReceive.afterDecode_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExtractedReceive.owner_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExtractedReceive.owner_native
