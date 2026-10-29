-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawCompile
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood

/-! Registration in the public raw compiler is an exact lifted invocation of the existing compiler. Only the publicly selected request, response envelope and assignment-counter bookkeeping differ. This gives the old middle invariant for registration without assuming a new hidden-root or event-simulation theorem. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawMiddleRegistration
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentRecordCache (SourceSpec)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealPostSource (Mid sourceMid)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The source registration request is chosen entirely from the compiler's public reconstruction state. -/
def request (memory : CborAdmissionCompiler.Local) : Spec.Domain → Spec.Domain
  | .inr (.build session payload) =>
      .inr (.build session (CborAdmissionCompiler.buildPayload memory.lastId payload))
  | .inr (.finish owner raw) =>
      .inr (.finish owner (CborTaggedCodec.tag (CborPublicPin.pin memory owner) raw))
  | query => query

theorem request_kind (memory : CborAdmissionCompiler.Local) (query : Spec.Domain) :
    PqxdhDeploymentCompileBudget.commandKind (request memory query) =
      PqxdhDeploymentCompileBudget.commandKind query := by
  rcases query with coin | command
  · rfl
  · cases command <;> simp only [request, PqxdhDeploymentCompileBudget.commandKind]

def reply (memory : CborAdmissionCompiler.Local) (query : Spec.Domain) :
    Spec.Range (request memory query) → Spec.Range query := by
  rcases query with coin | command
  · exact id
  · cases command
    case build => exact Option.map CborPublicClient.strip
    all_goals exact id

def assignment (memory : CborAdmissionCompiler.Local) (query : Spec.Domain) :
    Spec.Range (request memory query) → Aeneas.Std.U64 := by
  rcases query with coin | command
  · exact fun _ => memory.lastId
  · cases command
    case build => exact fun response =>
      (response.map PqxdhServerRegistrationPublication.Response.keyId).getD memory.lastId
    all_goals exact fun _ => memory.lastId

theorem assignment_other (memory : CborAdmissionCompiler.Local) (query : Spec.Domain)
    (other : PqxdhDeploymentCompileBudget.commandKind query ≠ 4)
    (answer : Spec.Range (request memory query)) : assignment memory query answer = memory.lastId := by
  rcases query with coin | command
  · rfl
  · cases command
    all_goals first | rfl | exact absurd rfl other

def result (memory : CborAdmissionCompiler.Local) (query : Spec.Domain)
    (value : Spec.Range (request memory query) × PqxdhDeploymentCompile.Local) :
    Spec.Range query × CborAdmissionCompiler.Local :=
  (reply memory query value.1, ⟨value.2, assignment memory query value.1⟩)

/-- Every non-record step delegates once to the original source compiler, including oversized moved-token builds and finishes with mismatching creation pins. -/
theorem compile_run (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (query : Spec.Domain) (registration : CborSplitCompiler.recordCommand query = false)
    (memory : CborAdmissionCompiler.Local) :
    (CborRawCompile.compileImpl setup wire parse query).run memory =
      result memory query <$>
        (PqxdhDeploymentCompile.compileImpl setup (CborRawCompile.sourceCodec wire parse)
          (CborRawCompile.route parse) (request memory query)).run memory.copies := by
  rcases query with coin | command
  · rfl
  · cases command
    case build session payload =>
      simp only [CborRawCompile.compileImpl, CborSplitCompiler.compileImpl,
        CborSplitCompiler.selected, CborSplitCompiler.recordCommand, Bool.false_eq_true, ite_false,
        CborAdmissionCompiler.compileImpl, StateT.run]
      rfl
    all_goals first | rfl | simp [CborSplitCompiler.recordCommand] at registration

/-- The hidden-root middle interpreter sees the same delegated query and its actual optional response before public envelope stripping. -/
theorem middle_run (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : Spec.Domain) (registration : CborSplitCompiler.recordCommand query = false)
    (memory : CborAdmissionCompiler.Local) (state : Mid KemSK) :
    (simulateQ (sourceMid setup (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)
        checks target parameters created) ((CborRawCompile.compileImpl setup wire parse query).run memory)).run state =
      (fun value => (result memory query value.1, value.2)) <$>
        (simulateQ (sourceMid setup (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)
          checks target parameters created)
          ((PqxdhDeploymentCompile.compileImpl setup (CborRawCompile.sourceCodec wire parse)
            (CborRawCompile.route parse) (request memory query)).run memory.copies)).run state := by
  rw [compile_run setup wire parse query registration memory, simulateQ_map, StateT.run_map]

/-- All registration commands preserve the existing full middle invariant on copied kernels and public ownership. The added assignment counter is not part of this statement. -/
theorem good_registration (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse)) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : Spec.Domain) (registration : CborSplitCompiler.recordCommand query = false)
    (memory : CborAdmissionCompiler.Local) (state : Mid KemSK)
    (good : PqxdhDeploymentIdealPostGood.GoodMid setup (CborRawCompile.sourceCodec wire parse)
      target memory.copies state)
    (value : (Spec.Range query × CborAdmissionCompiler.Local) × Mid KemSK)
    (supported : value ∈ support ((simulateQ (sourceMid setup (CborRawCompile.sourceCodec wire parse)
      (CborRawCompile.route parse) checks target parameters created)
      ((CborRawCompile.compileImpl setup wire parse query).run memory)).run state)) :
    PqxdhDeploymentIdealPostGood.GoodMid setup (CborRawCompile.sourceCodec wire parse)
      target value.1.2.copies value.2 := by
  rw [middle_run setup wire parse checks target parameters created query registration memory state,
    support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  have compiled : (inner.1.1, (inner.1.2, inner.2)) ∈ support
      ((PqxdhDeploymentIdealPostSource.compiledMid setup (CborRawCompile.sourceCodec wire parse)
        (CborRawCompile.route parse) checks target parameters created (request memory query)).run
          (memory.copies, state)) := by
    change _ ∈ support ((fun answer :
      (Spec.Range (request memory query) × PqxdhDeploymentCompile.Local) × Mid KemSK =>
        (answer.1.1, (answer.1.2, answer.2))) <$> _)
    rw [support_map]
    exact ⟨inner, reached, rfl⟩
  exact (PqxdhDeploymentIdealPostGood.middleInv setup (CborRawCompile.sourceCodec wire parse)
    (CborRawCompile.route parse) checks phase1 phase2 target parameters created).preserved
      (request memory query) memory.copies state good _ compiled

end BeaconcryptCore.Computational.CborRawMiddleRegistration

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleRegistration.good_registration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleRegistration.good_registration

-- Exact dependency observations for all public helper theorems.

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleRegistration.request_kind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleRegistration.request_kind

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleRegistration.assignment_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleRegistration.assignment_other

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleRegistration.compile_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleRegistration.compile_run

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleRegistration.middle_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleRegistration.middle_run
