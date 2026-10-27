-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.RecordEffects

/-! Unconditional normal returns for send admission and complete-record write requests. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete

set_option autoImplicit false

namespace BeaconcryptCore.PanicFreedom.RecordEffectsSend

theorem begin_record_send_total (kernel : ConcreteRatchetKernel)
    (context : record_effects.SealFrameContext) :
    ∃ result, record_effects.begin_record_send kernel context = ok result := by
  obtain ⟨empty, emptyRun⟩ : ∃ result, core.slice.Slice.is_empty context.plaintext = ok result := ⟨_, rfl⟩
  obtain ⟨selected, selectedRun⟩ := begin_send_total kernel context
  cases empty <;> cases prefixRun : context.prefix <;> cases selected <;>
    simp [record_effects.begin_record_send, emptyRun, core.option.Option.is_none, core.option.Option.is_some, prefixRun, selectedRun]

theorem SealWrite_request_total (self : record_effects.SealWrite) :
    ∃ result, record_effects.SealWrite.request self = ok result := by
  cases encodingRun : self.seal.context.encoding <;>
    simp [record_effects.SealWrite.request, ratchet.concrete.SendSeal.impl.context,
      ratchet.concrete.SendSeal.impl.sequence, core.array.Array.as_slice, rust_primitives.slice.array_as_slice, encodingRun]

end BeaconcryptCore.PanicFreedom.RecordEffectsSend

/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffectsSend.begin_record_send_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffectsSend.begin_record_send_total

/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffectsSend.SealWrite_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffectsSend.SealWrite_request_total
