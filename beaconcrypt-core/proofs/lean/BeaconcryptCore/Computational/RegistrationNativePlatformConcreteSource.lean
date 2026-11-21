-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeConcreteReaders
import BeaconcryptCore.Computational.RegistrationNativePlatformWriter
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWriterTotal
/-! The selected source dictionaries use the actual registration decoders/serializers and finite three-chunk frame dispatcher. The sole external writer effects are public capacity reservations with their full common platform poststate and fallible result. No codec or whole-controller law is a premise. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource
open BeaconcryptCore.Refinement
variable {Platform E : Type}

noncomputable def wire : RegistrationNativeWire.Wire := RegistrationNativeConcreteCodec.wire

@[instance_reducible] def fallbackOperations : FrameDispatchFallback.Operations where
  many _ _ _ _ := .fail .panic

def serializer (sequence sender : U64) (parts : Std.Array (Slice U8) 3#usize) (output : Slice U8) :
    StateT Platform ProbComp (RustM (Usize × Slice U8)) :=
  @AdapterRecordFrameBytes.serializer (StateT Platform ProbComp) _ fallbackOperations sequence sender parts output

def rawAllocation (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (_before : alloc.vec.Vec U8) (capacity : Usize) : StateT Platform ProbComp (RustM (core.result.Result Unit E)) :=
  .ok <$> reserve capacity.val

def helper (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) :
    QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp) :=
  AdapterRecordRawBytes.helper (rawAllocation reserve) serializer

def writer (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E)) :
    QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp) :=
  RegistrationSourceWriterBody.platform reserve
    RegistrationNativeConcreteCodec.writerOperations.encodeInit
    RegistrationNativeConcreteCodec.writerOperations.encodeResponse

/-- Both source registration readback laws hold with the concrete actual decoder, without a codec premise. -/
theorem init_readback : RegistrationNativeWire.InitReadBack wire := RegistrationNativeConcreteCodec.init_readback

theorem response_readback : RegistrationNativeWire.ResponseReadBack wire := RegistrationNativeConcreteCodec.response_readback

/-- Fixed three-chunk source serialization never reaches the chosen fallback, on any array or output. -/
theorem serializer_source (sequence sender : U64) (parts : Std.Array (Slice U8) 3#usize) (output : Slice U8) :
    ∃ first second third, parts.to_slice = FrameDispatch.three first second third ∧
      serializer (Platform := Platform) sequence sender parts output =
        pure (beaconcrypt_parse.frame.encode_three sequence sender first second third output) := by
  obtain ⟨first, second, third, exactParts, source⟩ := @FrameDispatch.selected_array fallbackOperations sequence sender parts output
  refine ⟨first, second, third, exactParts, ?_⟩
  unfold serializer AdapterRecordFrameBytes.serializer
  rw [source]

/-- Literal Init request interpretation preserves every public reservation failure and returned platform state. -/
theorem init_writer (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E)) (view : registration.InitView) :
    simulateQ (writer reserve)
      (AdapterRegistrationWriterRequestExtraction.encodeInit
        (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E)
        (RegistrationNativePlatformWriter.initPacket view)).run =
      (fun allocation => (RustM.ok (match allocation with
        | .Err _ => core.option.Option.None
        | .Ok _ => .Some (RegistrationNativeSourceWriterReadback.initVector view)))) <$> reserve 1490#usize := by
  exact RegistrationNativeSourceWriterReadback.init_source reserve RegistrationNativeConcreteCodec.serializerBranches view

/-- Response size refusal is checked before allocation, and every admitted reservation failure remains observable. -/
theorem response_writer (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (view : registration.SignedResponseView)
    (admitted : RegistrationSerializerResponseBytes.totalLength (RegistrationNativeSourceEncoders.responseSyntax view) ≤ CborSizing.maxMessageSize) :
    ∃ capacity, capacity.val = RegistrationSerializerResponseBytes.totalLength (RegistrationNativeSourceEncoders.responseSyntax view) ∧
      simulateQ (writer reserve)
        (AdapterRegistrationWriterRequestExtraction.encodeResponse
          (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E)
          (RegistrationNativePlatformWriter.responsePacket view)).run =
        (fun allocation => (RustM.ok (match allocation with
          | .Err _ => core.option.Option.None
          | .Ok _ => .Some (RegistrationNativeSourceWriterReadback.responseVector view admitted)))) <$> reserve capacity := by
  exact RegistrationNativeSourceWriterReadback.response_source reserve RegistrationNativeConcreteCodec.serializerBranches view admitted

theorem response_rejected (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (view : registration.SignedResponseView)
    (outside : CborSizing.maxMessageSize < RegistrationSerializerResponseBytes.totalLength (RegistrationNativeSourceEncoders.responseSyntax view)) :
    simulateQ (writer reserve)
      (AdapterRegistrationWriterRequestExtraction.encodeResponse
        (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E)
        (RegistrationNativePlatformWriter.responsePacket view)).run = pure (RustM.ok core.option.Option.None) := by
  exact RegistrationNativeSourceWriterReadback.response_rejected reserve RegistrationNativeConcreteCodec.serializerBranches view outside

/-- Full source Frame3 execution retains the actual public capacity reservation across all inputs and arithmetic refusals. -/
theorem frame_writer (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (sequence sender : U64) (first second third : Slice U8) :
    RegistrationNativeExtractedAllocation.abstractResult <$>
      AdapterRecordFrameBytes.frame (rawAllocation reserve) serializer sequence sender first second third =
      .ok <$> RegistrationNativePlatformOrdinaryWriter.write reserve
        (RegistrationNativePlatformOrdinaryWriterTotal.frame sequence sender first second third) := by
  exact @RegistrationNativePlatformOrdinaryWriterTotal.source (StateT Platform ProbComp) _ _ E fallbackOperations
    reserve sequence sender first second third
end BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource.init_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource.init_readback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource.response_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource.response_readback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource.serializer_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource.serializer_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource.init_writer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource.init_writer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource.response_writer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource.response_writer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource.response_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource.response_rejected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource.frame_writer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource.frame_writer
