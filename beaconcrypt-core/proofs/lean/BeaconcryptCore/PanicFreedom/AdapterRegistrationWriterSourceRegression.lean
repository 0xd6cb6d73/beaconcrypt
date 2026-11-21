-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterRegistrationWriterSource

/-! Executable source-boundary controls: allocation can succeed while unreachable serializer branches fail or diverge. Conversely, reservation refusal returns None before an arbitrary callback is invoked. These mathematical dictionaries are regression models, not a native allocation or primitive correspondence claim. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.PanicFreedom.AdapterRegistrationWriterSourceRegression
open Refinement AdapterNormal
open BeaconcryptCore.Computational
open RegistrationNativeSourceEncoders (sourceOperations initSyntax responseSyntax)

def hostile : RegistrationSerializerReachableSource.OtherBranches where
  deepSerialize _ _ _ := .div
  otherSerialize _ _ _ := .fail .panic
  deepSize _ _ := .div
  otherSize _ _ := .fail .panic
  textFactory _ := .div
  utf8Correct _ := .fail .panic

@[instance_reducible] def accepted : AdapterWirePrimitive.Operations where
  ReserveError := Unit
  reserve before _ := ok (.Ok (), before)

@[instance_reducible] def refused : AdapterWirePrimitive.Operations where
  ReserveError := Unit
  reserve before _ := ok (.Err (), before)

theorem accepted_contracts : @AdapterWire.Contracts accepted := by
  let _ := accepted
  exact ⟨fun _ _ => ⟨.Ok (), rfl⟩⟩

theorem refused_contracts : @AdapterWire.Contracts refused := by
  let _ := refused
  exact ⟨fun _ _ => ⟨.Err (), rfl⟩⟩

/-- This positive allocation model actually exposes the source serializer to the initialized buffer. -/
theorem init_callback_returns_bytes (view : registration.InitView) :
    ∃ after, (sourceOperations hostile).encodeInit (initSyntax view)
      (AdapterWireVector.zeros 1490#usize) = ok (1490#usize, after) := by
  obtain ⟨after, actual, _, _⟩ := RegistrationSerializerInitBytes.public_bytes hostile
    (initSyntax view) (AdapterWireVector.zeros 1490#usize)
    (RegistrationNativeSourceEncoders.init_shape view)
    (by simp only [AdapterWireVector.zeros, Slice.length, List.length_replicate]; decide)
  exact ⟨after, actual⟩

theorem source_init_normal (view : registration.InitView) :
    letI := accepted
    letI := sourceOperations hostile
    Normal (beaconcrypt_registration_writer.wire.encode_init (initSyntax view)) :=
  @AdapterRegistrationWriterSource.init_view_total accepted accepted_contracts hostile view

theorem source_response_normal (view : registration.SignedResponseView) :
    letI := accepted
    letI := sourceOperations hostile
    Normal (beaconcrypt_registration_writer.wire.encode_response (responseSyntax view)) :=
  @AdapterRegistrationWriterSource.response_view_total accepted accepted_contracts hostile view

/-- No callback execution contract is needed on the allocation-refusal branch. -/
theorem refused_before_callback {T : Type} (serializer : AdapterWirePrimitive.Serializer T)
    (capacity : Usize) (value : T) :
    @beaconcrypt.wire.encode_record refused T serializer capacity value = ok .None := by
  let _ := refused
  have reserved : refused.reserve (Slice.new U8) capacity = ok (.Err (), Slice.new U8) := rfl
  simp! only [beaconcrypt.wire.encode_record, alloc.vec.Vec.new,
    rust_primitives.sequence.seq_empty, alloc.vec.Vec.try_reserve_exact,
    reserved, core.result.Result.ok,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
    bind_tc_ok]

theorem refused_with_divergent_callback (capacity : Usize) :
    @beaconcrypt.wire.encode_record refused Unit ⟨fun _ _ => .div⟩ capacity () = ok .None :=
  refused_before_callback _ capacity ()

theorem refused_with_panicking_callback (capacity : Usize) :
    @beaconcrypt.wire.encode_record refused Unit ⟨fun _ _ => .fail .panic⟩ capacity () = ok .None :=
  refused_before_callback _ capacity ()

end BeaconcryptCore.PanicFreedom.AdapterRegistrationWriterSourceRegression
