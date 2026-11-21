-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawMiddleCounter
import BeaconcryptCore.Computational.CborRawMiddleRecords
import BeaconcryptCore.Computational.CborRawMiddleRegistration

/-! The public raw compiler's complete middle invariant is derived from its exact source syntax. Registration uses the old checked hidden-root invariant with the reply-derived allocation counter; records use the actual local decoder, optional writer and admission rule. No invariant preservation or event-handoff premise is supplied by a caller. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawMiddleInvariant
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealPostSource (Mid sourceMid)
open CborRawMiddleRegistration (request assignment request_kind assignment_other)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

def Good (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) {count : Nat}
    (target : Target count) (memory : CborAdmissionCompiler.Local) (state : Mid KemSK) : Prop :=
  CborAdmissionCompiler.Good setup (CborRawCompile.sourceCodec wire parse) memory
      (PqxdhRegistrationJointSchedule.source state.joint) ∧
    target.accept < state.backend.2.2.accepts

section Middle
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit)

/-- Public assignment bookkeeping matches hidden and ordinary registration even after an optional failed outer write. -/
theorem registration_clock (query : Spec.Domain) (registration : CborSplitCompiler.recordCommand query = false)
    (memory : CborAdmissionCompiler.Local) (state : Mid KemSK)
    (clock : memory.lastId = state.joint.shared.2.server.control.last_key_id)
    (value : (Spec.Range query × CborAdmissionCompiler.Local) × Mid KemSK)
    (supported : value ∈ support ((simulateQ (sourceMid setup (CborRawCompile.sourceCodec wire parse)
      (CborRawCompile.route parse) checks target parameters created)
      ((CborRawCompile.compileImpl setup wire parse query).run memory)).run state)) :
    value.1.2.lastId = value.2.joint.shared.2.server.control.last_key_id := by
  rw [CborRawMiddleRegistration.middle_run setup wire parse checks target parameters created query registration
    memory state, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  by_cases build : PqxdhDeploymentCompileBudget.commandKind query = 4
  · rcases query with coin | command
    · simp [PqxdhDeploymentCompileBudget.commandKind] at build
    · cases command
      all_goals try simp [PqxdhDeploymentCompileBudget.commandKind] at build
      rename_i session data
      change inner ∈ support ((simulateQ (sourceMid setup (CborRawCompile.sourceCodec wire parse)
        (CborRawCompile.route parse) checks target parameters created)
        ((PqxdhDeploymentCompile.forwardLogged
          (.build session (CborAdmissionCompiler.buildPayload memory.lastId data))
          (.build session (CborAdmissionCompiler.buildPayload memory.lastId data)) id).run memory.copies)).run state)
        at member
      rw [PqxdhDeploymentIdealPostSource.compiledMid_forward, support_map] at member
      obtain ⟨stepped, reached, rfl⟩ := member
      change (stepped.1.map PqxdhServerRegistrationPublication.Response.keyId).getD memory.lastId =
        stepped.2.joint.shared.2.server.control.last_key_id
      have assigned := CborRawMiddleCounter.sourceMid_assignment setup (CborRawCompile.sourceCodec wire parse)
        (CborRawCompile.route parse) checks target parameters created
        (.inl (.inr (.build session (CborAdmissionCompiler.buildPayload memory.lastId data)))) state stepped reached
      exact (congrArg (fun previous : Std.U64 =>
        (stepped.1.map PqxdhServerRegistrationPublication.Response.keyId).getD previous) clock).trans assigned
  · change assignment memory query inner.1.1 = inner.2.joint.shared.2.server.control.last_key_id
    rw [assignment_other memory query build]
    have kept := CborRawMiddleCounter.sourceMid_noBuild setup (CborRawCompile.sourceCodec wire parse)
      (CborRawCompile.route parse) checks target parameters created
      ((PqxdhDeploymentCompile.compileImpl setup (CborRawCompile.sourceCodec wire parse)
        (CborRawCompile.route parse) (request memory query)).run memory.copies)
      (CborAdmissionInvariant.existing_no_build_bound setup (CborRawCompile.sourceCodec wire parse)
        (CborRawCompile.route parse) (request memory query)
        (by rwa [request_kind memory query]) memory.copies) state inner member
    exact clock.trans kept.symm

/-- Every actual raw command preserves all copied kernels, public owner/peer reconstruction, the reply-derived assignment counter and the selected-accept ordering. -/
theorem good_step
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (query : Spec.Domain) (memory : CborAdmissionCompiler.Local) (state : Mid KemSK)
    (good : Good setup wire parse target memory state)
    (value : (Spec.Range query × CborAdmissionCompiler.Local) × Mid KemSK)
    (supported : value ∈ support ((simulateQ (sourceMid setup (CborRawCompile.sourceCodec wire parse)
      (CborRawCompile.route parse) checks target parameters created)
      ((CborRawCompile.compileImpl setup wire parse query).run memory)).run state)) :
    Good setup wire parse target value.1.2 value.2 := by
  cases record : CborSplitCompiler.recordCommand query with
  | false =>
      have old := CborRawMiddleRegistration.good_registration setup wire parse checks phase1 phase2 target
        parameters created query record memory state ⟨good.1.nativeGood, good.2⟩ value supported
      exact ⟨⟨old.1, registration_clock setup wire parse checks target parameters created query record memory
        state good.1.lastId value supported⟩, old.2⟩
  | true =>
      obtain ⟨native, backend, _⟩ := CborRawMiddleRecords.good_record setup wire parse checks phase1 phase2
        target parameters created query record memory state good.1 value supported
      exact ⟨native, by rw [backend]; exact good.2⟩

end Middle
end BeaconcryptCore.Computational.CborRawMiddleInvariant

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleInvariant.good_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleInvariant.good_step

-- Exact dependency observations for all public helper theorems.

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleInvariant.registration_clock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleInvariant.registration_clock
