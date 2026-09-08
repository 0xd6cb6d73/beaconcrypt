import BeaconcryptCore.Refinement.NativeRecordWrapper
import BeaconcryptCore.PanicFreedom.Effects

/-!
Unconditional normal-return certificates cover every new extracted record operation. The statements quantify arbitrary represented inputs, including malformed private receive slots and every optional primitive reply. The phase proofs reuse the exact wrapper equations and the existing receive publication totality; none restricts inputs to successful or previously authenticated records.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open BeaconcryptCore.Refinement.NativeRecordWrapper

set_option autoImplicit false
namespace BeaconcryptCore.PanicFreedom.Record

/-- The fixed payload overhead addition cannot overflow. -/
theorem overhead_total : ∃ result, record.MESSAGE_OVERHEAD = ok result := by
  refine ⟨80#usize, ?_⟩
  unfold record.MESSAGE_OVERHEAD record.COMMITMENT_SIZE commitment.AEAD_TAG_SIZE
  exact PqxdhRefinement.usize_add_eq _ _ _ (by simp)

/-- Complete-input admission returns normally for every remainder and message. -/
theorem complete_total {Message : Type} (remaining : Slice Std.U8) (message : Message) :
    ∃ result, record.finish_frame_read remaining message = ok result :=
  ⟨_, complete_input remaining message⟩

/-- Every payload view construction returns a normal optional result. -/
theorem payload_total (payload : Slice Std.U8) (ad : Std.Array Std.U8 153#usize)
    (sender : Std.U64) : ∃ result, record.OpenFrameContext.from_frame payload ad sender = ok result := by
  obtain ⟨result, equation, _⟩ := payload_views payload ad sender
  exact ⟨result, equation⟩

/-- Both missing and present selected material yield a normal initial phase. -/
theorem begin_total (opening : ReceiveOpen record.OpenFrameContext) :
    ∃ result, record.begin_open opening = ok result := by
  obtain ⟨⟨material, hmaterial⟩, ⟨sequence, hsequence⟩⟩ := getters_normal opening
  cases material with
  | none => exact ⟨_, begin_missing opening hmaterial⟩
  | some material => exact ⟨_, begin_selected opening material sequence hmaterial hsequence⟩

/-- The original transcript borrow always returns normally. -/
theorem transcript_total (pending : record.OpenCommitment) :
    ∃ result, record.OpenCommitment.impl.transcript pending = ok result := ⟨_, rfl⟩

/-- The mutable transcript borrow and back-function always return normally. -/
theorem transcript_mut_total (pending : record.OpenCommitment) :
    ∃ result, record.OpenCommitment.transcript_mut pending = ok result := ⟨_, rfl⟩

/-- The retained supplied commitment borrow always returns normally. -/
theorem supplied_total (pending : record.OpenCommitment) :
    ∃ result, record.OpenCommitment.supplied_commitment pending = ok result := ⟨_, rfl⟩

/-- Every comparison Boolean produces a normal rejection or AEAD phase. -/
theorem resume_total (pending : record.OpenCommitment) (matched : Bool) :
    ∃ result, record.OpenCommitment.resume pending matched = ok result := ⟨_, resume_exact pending matched⟩

/-- The AEAD request getter returns normally even for malformed private material slots. -/
theorem request_total (opening : record.OpenAead) :
    ∃ result, record.OpenAead.request opening = ok result := by
  obtain ⟨⟨material, hmaterial⟩, _⟩ := getters_normal opening.opening
  cases material with
  | none => exact ⟨.None, by simp [record.OpenAead.request, hmaterial]⟩
  | some material => exact ⟨_, request_selected opening material hmaterial⟩

/-- Every optional plaintext yields a normal original receive publication. -/
theorem finish_total {Plaintext : Type} (opening : record.OpenAead)
    (reply : core.option.Option Plaintext) :
    ∃ result, record.OpenAead.finish opening reply = ok result := by
  obtain ⟨_, ⟨sequence, hsequence⟩⟩ := getters_normal opening.opening
  rw [finish_selected opening sequence hsequence reply]
  exact ReceiveOpen.finish_total _ _

end BeaconcryptCore.PanicFreedom.Record

/--
info: 'BeaconcryptCore.PanicFreedom.Record.overhead_total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Record.overhead_total

/--
info: 'BeaconcryptCore.PanicFreedom.Record.complete_total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Record.complete_total

/--
info: 'BeaconcryptCore.PanicFreedom.Record.payload_total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Record.payload_total

/--
info: 'BeaconcryptCore.PanicFreedom.Record.begin_total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Record.begin_total

/--
info: 'BeaconcryptCore.PanicFreedom.Record.transcript_total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Record.transcript_total

/--
info: 'BeaconcryptCore.PanicFreedom.Record.transcript_mut_total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Record.transcript_mut_total

/--
info: 'BeaconcryptCore.PanicFreedom.Record.supplied_total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Record.supplied_total

/--
info: 'BeaconcryptCore.PanicFreedom.Record.resume_total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Record.resume_total

/--
info: 'BeaconcryptCore.PanicFreedom.Record.request_total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Record.request_total

/--
info: 'BeaconcryptCore.PanicFreedom.Record.finish_total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Record.finish_total
