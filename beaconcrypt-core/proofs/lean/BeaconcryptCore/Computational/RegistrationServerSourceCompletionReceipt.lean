-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerRecordSourcePath
import BeaconcryptCore.Computational.RegistrationServerPublicationSnapshot
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
/-! The literal source first-record and response publication sequence retains the original candidate rollback snapshot and derives the complete successful binding, sequence-one kernel and associated data. Every leaf may return absence, enclosing failure or divergence, with the same reached external state. -/
namespace BeaconcryptCore.Computational.RegistrationServerSourceCompletionReceipt
variable {Encoded State : Type}
noncomputable def program
    (record : QueryImpl RegistrationRecordPrimitives.Spec (StateT State ProbComp))
    (sealing : record_effects.AeadSealRequest → StateT State ProbComp (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → StateT State ProbComp RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → StateT State ProbComp (RustM (core.option.Option (Slice U8))))
    (signing : QueryImpl RegistrationSigningShared.Spec (StateT State ProbComp))
    (encode : registration.SignedResponseView → StateT State ProbComp (RustM (core.option.Option Encoded)))
    (initial : registration.ServerInitialKdf) : StateT State ProbComp (RustM (RegistrationWorldServerPublication.Result Encoded)) := do
  let recorded ← RegistrationNativePlatformSourceRecord.fromInitialWithHash record sealing hash write initial
  RegistrationNativePlatformServerPublication.continueResult recorded
    (RegistrationNativePlatformServerPublication.program signing encode)

def Post (initial : registration.ServerInitialKdf) : RustM (RegistrationWorldServerPublication.Result Encoded) → Prop
  | .fail _ | .div => True
  | .ok (.Err previous) => previous = initial.candidate.previous_state
  | .ok (.Ok published) => published.control = initial.candidate.next_state ∧
      published.binding = BeaconcryptCore.Refinement.RegistrationPublication.completedBinding initial.binding initial.candidate.key_id ∧
      ∃ selected : ratchet.concrete.SendSeal record_effects.SealFrameContext,
        published.kernel = selected.advanced ∧ selected.sequence.val = 1 ∧
        selected.context.associated_data = initial.binding.associated_data

theorem stateful
    (record : QueryImpl RegistrationRecordPrimitives.Spec (StateT State ProbComp))
    (sealing : record_effects.AeadSealRequest → StateT State ProbComp (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → StateT State ProbComp RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → StateT State ProbComp (RustM (core.option.Option (Slice U8))))
    (signing : QueryImpl RegistrationSigningShared.Spec (StateT State ProbComp))
    (encode : registration.SignedResponseView → StateT State ProbComp (RustM (core.option.Option Encoded)))
    (initial : registration.ServerInitialKdf) (output : RustM (RegistrationWorldServerPublication.Result Encoded)) (before after : State)
    (supported : (output, after) ∈ support ((program record sealing hash write signing encode initial).run before)) :
    Post initial output := by
  simp only [program, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨recorded, middle⟩, reached, continued⟩ := supported
  have rollback := RegistrationServerRecordRollback.stateful record sealing hash write initial recorded before middle reached
  cases recorded with
  | fail error | div =>
    simp only [RegistrationNativePlatformServerPublication.continueResult, StateT.run_pure,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at continued
    cases continued.1
    trivial
  | ok result =>
    cases result with
    | Err previous =>
      simp only [RegistrationNativePlatformServerPublication.continueResult, StateT.run_pure,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at continued
      cases continued.1
      exact rollback
    | Ok pending =>
      have retained := RegistrationServerRecordSourcePath.stateful_retains record sealing hash write initial pending before middle reached
      change (output, after) ∈ support ((RegistrationNativePlatformServerPublication.program signing encode pending).run middle) at continued
      have published := RegistrationServerPublicationSnapshot.stateful signing encode pending output middle after continued
      cases output with
      | fail error | div => trivial
      | ok result =>
        cases result with
        | Err previous => exact published.trans (congrArg (fun candidate => candidate.previous_state) retained.2.1)
        | Ok result =>
          obtain ⟨selected, kernelSame, sequence, adSame⟩ := retained.2.2
          exact ⟨published.1.trans (congrArg (fun candidate => candidate.next_state) retained.2.1),
            by simpa only [retained.1, retained.2.1] using published.2.1,
            selected, published.2.2.trans kernelSame, sequence, adSame⟩

theorem identity (initial : registration.ServerInitialKdf) (published : registration.PublishedServerResponse Encoded)
    (retained : Post initial (.ok (.Ok published))) :
    published.binding.beacon_identity_public_key = initial.binding.beacon_identity_public_key := by
  rw [retained.2.1]
  rfl
end BeaconcryptCore.Computational.RegistrationServerSourceCompletionReceipt

/-- info: 'BeaconcryptCore.Computational.RegistrationServerSourceCompletionReceipt.stateful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerSourceCompletionReceipt.stateful

/-- info: 'BeaconcryptCore.Computational.RegistrationServerSourceCompletionReceipt.identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerSourceCompletionReceipt.identity
