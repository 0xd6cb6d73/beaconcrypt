-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborSplitIdealInterpreters
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource

/-! Record portions of the actual raw compiler can run below the existing middle source interpreter. Their canonical registration profile is fixed; their local record reader, writer and exact admission rule remain native. The equalities retain cache and native poststates and keep the ideal backend and seed table. No whole-game slot provenance is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawMiddleRecords
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRegistrationJointRevealCosts (sourceKind)
open PqxdhDeploymentRecordCache (SourceSpec)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealPostSource (Mid sourceMid realMid)
open PqxdhDeploymentInterface (Spec)
open CborSplitCompiler (RecordKind)
variable {ι KemSK Reader Response X : Type} {baseSpec : OracleSpec ι}

theorem pool_native_record_query (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (pairs : List (PqxdhLiveKemReservation.Pair KemSK)) (query : (SourceSpec KemSK).Domain)
    (permitted : RecordKind (sourceKind (KemSK := KemSK) query)) :
    PqxdhDeploymentIdealPool.revealPool setup codec checks seed pairs query =
      PqxdhRegistrationJointRevealSchedule.native setup codec checks seed query := by
  rcases query with (coin | command) | ⟨address, field⟩
  · simp [RecordKind, sourceKind, PqxdhRegistrationSchedule.sourceKind] at permitted
  · cases command
    all_goals try simp [RecordKind, sourceKind, PqxdhRegistrationSchedule.sourceKind] at permitted
    all_goals rfl
  · rfl

section Middle
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit)

theorem middle_record_query (query : (SourceSpec KemSK).Domain)
    (permitted : RecordKind (sourceKind (KemSK := KemSK) query)) :
    sourceMid setup codec route checks target parameters created query =
      realMid setup codec checks target parameters created query := by
  apply PqxdhDeploymentIdealPostSource.sourceMid_other
  intro hidden
  rcases hidden with hidden | hidden | hidden
  all_goals rw [hidden] at permitted
  all_goals simp [RecordKind] at permitted

/-- A record-only source program leaves the full ideal backend and seed table intact while running the actual annotated pooled source. -/
theorem middle_quiet_frame (work : OracleComp (SourceSpec KemSK) X)
    (quiet : ∀ kind, ¬RecordKind kind →
      work.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = kind) 0) (state : Mid KemSK) :
    (simulateQ (sourceMid setup codec route checks target parameters created) work).run state =
      (fun result => (result.1, { state with joint := result.2 })) <$>
        (simulateQ (PqxdhDeploymentIdealPoolSource.sourcePool setup codec checks created.seed
          created.server.server.metadata.identityIndex (parameters.pool target)) work).run state.joint := by
  rw [CborSplitCompiler.simulate_quiet _ _
    (middle_record_query setup codec route checks target parameters created) work quiet]
  exact PqxdhDeploymentIdealPostSource.realMid_frame setup codec checks target parameters created work
    (quiet (.inl 3) (by simp [RecordKind])) state

/-- Erasing only private ownership annotations gives the exact native record interpretation, including every reached primitive cache state. -/
theorem middle_quiet_native (work : OracleComp (SourceSpec KemSK) X)
    (quiet : ∀ kind, ¬RecordKind kind →
      work.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = kind) 0) (state : Mid KemSK) :
    (fun result => (result.1, PqxdhRegistrationJointSchedule.source result.2.joint)) <$>
        (simulateQ (sourceMid setup codec route checks target parameters created) work).run state =
      (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks created.seed) work).run
        (PqxdhRegistrationJointSchedule.source state.joint) := by
  rw [middle_quiet_frame setup codec route checks target parameters created work quiet state, Functor.map_map]
  change (fun result => (result.1, PqxdhRegistrationJointSchedule.source result.2)) <$>
    (simulateQ (PqxdhDeploymentIdealPoolSource.sourcePool setup codec checks created.seed
      created.server.server.metadata.identityIndex (parameters.pool target)) work).run state.joint = _
  rw [PqxdhDeploymentIdealPoolSource.programPool_native]
  exact congrArg (fun action => action.run (PqxdhRegistrationJointSchedule.source state.joint))
    (CborSplitCompiler.simulate_quiet _ _
      (pool_native_record_query setup codec checks created.seed (parameters.pool target)) work quiet)

end Middle

/-- Record commands of the raw public compiler do not add proof tags or change registration replies. -/
theorem record_impl (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (query : Spec.Domain)
    (record : CborSplitCompiler.recordCommand query = true) :
    CborRawCompile.compileImpl setup wire parse query =
      CborSplitCompiler.compileImpl setup (CborRawCompile.sourceCodec wire parse)
        (CborTaggedSimulation.boundaryWire wire parse).frameRead wire.frameWrite (CborRawCompile.route parse) query := by
  rcases query with coin | command
  · simp [CborSplitCompiler.recordCommand] at record
  · cases command
    all_goals first | rfl | simp [CborSplitCompiler.recordCommand] at record

/-- The middle interpretation of any actual raw record step merges to its native reply and full native poststate. This includes failed optional writes and admission refusals, without a parser or AEAD-length premise. -/
theorem raw_record_middle (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : Spec.Domain) (record : CborSplitCompiler.recordCommand query = true)
    (memory : CborAdmissionCompiler.Local) (state : Mid KemSK)
    (good : CborAdmissionCompiler.Good setup (CborRawCompile.sourceCodec wire parse) memory
      (PqxdhRegistrationJointSchedule.source state.joint)) :
    (fun result => (result.1.1, CborAdmissionCompiler.merge result.1.2
        (PqxdhRegistrationJointSchedule.source result.2.joint))) <$>
      (simulateQ (sourceMid setup (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)
        checks target parameters created) ((CborRawCompile.compileImpl setup wire parse query).run memory)).run state =
      (CborProductionBoundary.handler setup wire parse checks created.seed query).run
        (CborAdmissionCompiler.merge memory (PqxdhRegistrationJointSchedule.source state.joint)) := by
  have equality := middle_quiet_native setup (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)
    checks target parameters created ((CborRawCompile.compileImpl setup wire parse query).run memory)
    (CborSplitIdealInterpreters.raw_record_quiet setup wire parse query record memory) state
  have projected := congrArg (fun work => (fun result =>
    (result.1.1, CborAdmissionCompiler.merge result.1.2 result.2)) <$> work) equality
  simp only [Functor.map_map] at projected
  rw [projected, record_impl setup wire parse query record]
  have splitStep := CborSplitCompiler.step_merge setup (CborRawCompile.sourceCodec wire parse)
    (CborTaggedSimulation.boundaryWire wire parse).frameRead wire.frameWrite checks (CborRawCompile.route parse)
    created.seed query memory (PqxdhRegistrationJointSchedule.source state.joint) good
  apply splitStep.trans
  exact CborRawCompile.other setup wire parse checks created.seed query (by
    rcases query with coin | command
    · simp [CborSplitCompiler.recordCommand] at record
    · cases command
      all_goals first | trivial | simp [CborSplitCompiler.recordCommand] at record)
    (CborAdmissionCompiler.merge memory (PqxdhRegistrationJointSchedule.source state.joint))

/-- The complete reconstruction and assignment invariant survives record steps in the middle interpreter. The selected-accept counter and lazy seed table are frames of those steps. -/
theorem good_record (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse)) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : Spec.Domain) (record : CborSplitCompiler.recordCommand query = true)
    (memory : CborAdmissionCompiler.Local) (state : Mid KemSK)
    (good : CborAdmissionCompiler.Good setup (CborRawCompile.sourceCodec wire parse) memory
      (PqxdhRegistrationJointSchedule.source state.joint))
    (value : (Spec.Range query × CborAdmissionCompiler.Local) × Mid KemSK)
    (supported : value ∈ support ((simulateQ (sourceMid setup (CborRawCompile.sourceCodec wire parse)
      (CborRawCompile.route parse) checks target parameters created)
      ((CborRawCompile.compileImpl setup wire parse query).run memory)).run state)) :
    CborAdmissionCompiler.Good setup (CborRawCompile.sourceCodec wire parse) value.1.2
      (PqxdhRegistrationJointSchedule.source value.2.joint) ∧
      value.2.backend = state.backend ∧ value.2.seeds = state.seeds := by
  have quiet := CborSplitIdealInterpreters.raw_record_quiet setup wire parse query record memory
  have nativeMember : (value.1, PqxdhRegistrationJointSchedule.source value.2.joint) ∈ support
      ((simulateQ (PqxdhRegistrationJointRevealSchedule.native setup (CborRawCompile.sourceCodec wire parse)
        checks created.seed) ((CborRawCompile.compileImpl setup wire parse query).run memory)).run
          (PqxdhRegistrationJointSchedule.source state.joint)) := by
    rw [← middle_quiet_native setup (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)
      checks target parameters created _ quiet state, support_map]
    exact ⟨value, supported, rfl⟩
  have compiledMember : (value.1.1, (value.1.2, PqxdhRegistrationJointSchedule.source value.2.joint)) ∈ support
      ((CborRawCompile.compiledImpl setup wire parse checks created.seed query).run
        (memory, PqxdhRegistrationJointSchedule.source state.joint)) := by
    rw [CborRawCompile.compiled_run, support_map]
    exact ⟨(value.1, PqxdhRegistrationJointSchedule.source value.2.joint), nativeMember, rfl⟩
  refine ⟨CborRawCompile.good_step setup wire parse checks created.seed phase1 phase2 query memory
    (PqxdhRegistrationJointSchedule.source state.joint) good _ compiledMember, ?_⟩
  rw [middle_quiet_frame setup (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)
    checks target parameters created _ quiet state, support_map] at supported
  obtain ⟨inner, _, rfl⟩ := supported
  exact ⟨rfl, rfl⟩

end BeaconcryptCore.Computational.CborRawMiddleRecords

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleRecords.raw_record_middle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleRecords.raw_record_middle

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleRecords.good_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleRecords.good_record

-- Exact dependency observations for all public helper theorems.

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleRecords.pool_native_record_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleRecords.pool_native_record_query

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleRecords.middle_record_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleRecords.middle_record_query

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleRecords.middle_quiet_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleRecords.middle_quiet_frame

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleRecords.middle_quiet_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleRecords.middle_quiet_native

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleRecords.record_impl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleRecords.record_impl
