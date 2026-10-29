-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawMiddleMerge
import BeaconcryptCore.Computational.CborRawInitializedCut

/-! Before the selected raw accept, the raw compiler runs the actual annotated pool source. The only additional state is the concrete accept counter of the ideal backend. This step shape retains the complete raw memory, private source state, rejection replies and native record writer. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawPreSource
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealPostSource (Mid sourceMid mergeX RealAt)
open PqxdhDeploymentIdealCut (bump)
open CborRawMiddleRegistration (request)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- No selected accept has activated or marked a session. -/
def Pre (state : Mid KemSK) : Prop := state.backend.2.2.active = false ∧ state.backend.2.2.marks = none

theorem bump_request (memory : CborAdmissionCompiler.Local) (query : Spec.Domain)
    (backend : PqxdhDeploymentIdealSteps.IdealBk PqxdhDeploymentIdealSteps.TableState) :
    bump (request memory query) backend = bump query backend := by
  rcases query with coin | command
  · rfl
  · cases command <;> simp only [request, bump]

private theorem bump_record (query : Spec.Domain) (record : CborSplitCompiler.recordCommand query = true)
    (backend : PqxdhDeploymentIdealSteps.IdealBk PqxdhDeploymentIdealSteps.TableState) : bump query backend = backend := by
  rcases query with coin | command
  · rfl
  · cases command
    case accept => simp [CborSplitCompiler.recordCommand] at record
    all_goals rfl

section Prefix
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)

theorem real_request (query : Spec.Domain) (memory : CborAdmissionCompiler.Local) (state : Mid KemSK)
    (pre : Pre state) (notSelected : ∀ raw, query = .inr (.accept raw) → state.backend.2.2.accepts ≠ target.accept) :
    RealAt target (request memory query) (mergeX memory.copies state) := by
  rcases query with coin | command
  · trivial
  · cases command
    case accept raw => exact notSelected raw rfl
    case build session payload =>
      intro index coords found
      change state.backend.2.2.marks = some (index, coords) at found
      rw [pre.2] at found
      cases found
    case finish owner raw =>
      rintro ⟨active, _, _⟩
      change state.backend.2.2.active = true at active
      rw [pre.1] at active
      cases active
    all_goals trivial

/-- The raw pre-cut compiler is the real annotated pool source, with only the actual raw-accept counter advanced. -/
theorem shape (query : Spec.Domain) (memory : CborAdmissionCompiler.Local) (state : Mid KemSK)
    (pre : Pre state) (notSelected : ∀ raw, query = .inr (.accept raw) → state.backend.2.2.accepts ≠ target.accept) :
    (simulateQ (sourceMid setup (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)
        checks target parameters created) ((CborRawCompile.compileImpl setup wire parse query).run memory)).run state =
      (fun value => (value.1, { state with joint := value.2, backend := bump query state.backend })) <$>
        (simulateQ (PqxdhDeploymentIdealPoolSource.sourcePool setup (CborRawCompile.sourceCodec wire parse) checks
          created.seed created.server.server.metadata.identityIndex (parameters.pool target))
          ((CborRawCompile.compileImpl setup wire parse query).run memory)).run state.joint := by
  cases record : CborSplitCompiler.recordCommand query with
  | true =>
      rw [bump_record query record]
      exact CborRawMiddleRecords.middle_quiet_frame setup (CborRawCompile.sourceCodec wire parse)
        (CborRawCompile.route parse) checks target parameters created _
        (CborSplitIdealInterpreters.raw_record_quiet setup wire parse query record memory) state
  | false =>
      rw [CborRawMiddleRegistration.middle_run setup wire parse checks target parameters created query record memory state,
        PqxdhDeploymentIdealPostGood.real_shape setup (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)
          checks target parameters created (request memory query) memory.copies state
          (real_request target query memory state pre notSelected),
        CborRawMiddleRegistration.compile_run setup wire parse query record memory, simulateQ_map, StateT.run_map,
        Functor.map_map, Functor.map_map, bump_request]

/-- Every reached pre-cut step retains the full raw reconstruction and assignment invariant, derived through the actual pool execution. -/
theorem good_step
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (query : Spec.Domain) (memory : CborAdmissionCompiler.Local) (state : Mid KemSK)
    (pre : Pre state) (notSelected : ∀ raw, query = .inr (.accept raw) → state.backend.2.2.accepts ≠ target.accept)
    (good : CborAdmissionCompiler.Good setup (CborRawCompile.sourceCodec wire parse) memory
      (PqxdhRegistrationJointSchedule.source state.joint))
    (value : (Spec.Range query × CborAdmissionCompiler.Local) × Mid KemSK)
    (supported : value ∈ support ((simulateQ (sourceMid setup (CborRawCompile.sourceCodec wire parse)
      (CborRawCompile.route parse) checks target parameters created)
      ((CborRawCompile.compileImpl setup wire parse query).run memory)).run state)) :
    CborAdmissionCompiler.Good setup (CborRawCompile.sourceCodec wire parse) value.1.2
      (PqxdhRegistrationJointSchedule.source value.2.joint) ∧ Pre value.2 := by
  rw [shape setup wire parse checks target parameters created query memory state pre notSelected, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  refine ⟨?_, ?_⟩
  · exact CborRawCutPrefix.good_program setup wire parse checks created.seed created.server.server.metadata.identityIndex
      (parameters.pool target) phase1 phase2 (Spec.query query : OracleComp Spec _) memory state.joint good inner
      (by simpa only [simulateQ_spec_query, CborRawCutPrefix.source] using reached)
  · rcases query with coin | command
    · exact pre
    · cases command <;> exact pre

end Prefix
end BeaconcryptCore.Computational.CborRawPreSource

/-- info: 'BeaconcryptCore.Computational.CborRawPreSource.bump_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPreSource.bump_request
/-- info: 'BeaconcryptCore.Computational.CborRawPreSource.real_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPreSource.real_request
/-- info: 'BeaconcryptCore.Computational.CborRawPreSource.shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPreSource.shape
/-- info: 'BeaconcryptCore.Computational.CborRawPreSource.good_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPreSource.good_step
