-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawMiddleSimulation

/-! The single-step raw compiler/native merge needs the complete native reconstruction invariant, without a post-cut accept-ordinal assumption. This stronger form supports the initialized pre-cut prefix while the existing adaptive post-cut theorem retains its established interface. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawMiddleMerge
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealPostSource (Mid sourceMid mergeX)
open CborRawPublicState (Public ofMemory toMemory)
open CborRawMiddleRegistration (request reply assignment)
open CborRawMiddleSimulation (Native merge withBase registration records handler request_record registration_public_run)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
section Merge
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)

theorem registration_step (query : Spec.Domain) (onlyRegistration : CborSplitCompiler.recordCommand query = false)
    (memory : CborAdmissionCompiler.Local) (state : Mid KemSK)
    (good : CborAdmissionCompiler.Good setup (CborRawCompile.sourceCodec wire parse) memory
      (PqxdhRegistrationJointSchedule.source state.joint)) :
    (fun value => (value.1.1, merge value.1.2 value.2)) <$>
        (simulateQ (sourceMid setup (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)
          checks target parameters created) ((CborRawCompile.compileImpl setup wire parse query).run memory)).run state =
      (registration setup wire parse checks target parameters created query).run (merge memory state) := by
  let decorate := fun value : Spec.Range (request memory query) × Native KemSK =>
    (reply memory query value.1,
      ((⟨CborRegistrationPublicLog.update memory.copies.log (request memory query) value.1,
        assignment memory query value.1⟩ : Public), value.2))
  have original := PqxdhDeploymentIdealPostSource.step_mergeMid setup (CborRawCompile.sourceCodec wire parse)
    (CborRawCompile.route parse) checks target parameters created (request memory query) memory.copies state
    (PqxdhDeploymentCompileInvariant.good_inv setup (CborRawCompile.sourceCodec wire parse) memory.copies
      (PqxdhRegistrationJointSchedule.source state.joint) good.nativeGood)
  have decorated := congrArg (fun work => decorate <$> work) original
  simp only [PqxdhDeploymentIdealPostSource.compiledMid,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, Functor.map_map, Prod.map_apply, id_eq] at decorated
  have selectedRegistration : CborSplitCompiler.recordCommand (request memory query) = false := by
    rw [request_record, onlyRegistration]
  rw [CborRegistrationPublicLog.compile_registration setup (CborRawCompile.sourceCodec wire parse)
    (CborRawCompile.route parse) (request memory query) selectedRegistration memory.copies,
    simulateQ_map, StateT.run_map, Functor.map_map] at decorated
  rw [CborRawMiddleRegistration.middle_run setup wire parse checks target parameters created query onlyRegistration
    memory state, Functor.map_map,
    CborRegistrationPublicLog.compile_registration setup (CborRawCompile.sourceCodec wire parse)
      (CborRawCompile.route parse) (request memory query) selectedRegistration memory.copies,
    simulateQ_map, StateT.run_map, Functor.map_map]
  change _ = (registration setup wire parse checks target parameters created query).run
    (ofMemory memory, mergeX memory.copies state)
  rw [registration_public_run]
  simpa only [decorate, StateT.run, bind_pure_comp, Functor.map_map,
    merge, CborRawMiddleRegistration.result, ofMemory, Prod.map_apply, Prod.map_fst, Prod.map_snd, id_eq] using decorated

/-- Record steps preserve public registration state and all ideal backend fields, while their full native state follows the actual fallible record implementation. -/
theorem record_step (query : Spec.Domain) (record : CborSplitCompiler.recordCommand query = true)
    (memory : CborAdmissionCompiler.Local) (state : Mid KemSK)
    (good : CborAdmissionCompiler.Good setup (CborRawCompile.sourceCodec wire parse) memory
      (PqxdhRegistrationJointSchedule.source state.joint)) :
    (fun value => (value.1.1, merge value.1.2 value.2)) <$>
        (simulateQ (sourceMid setup (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)
          checks target parameters created) ((CborRawCompile.compileImpl setup wire parse query).run memory)).run state =
      (records setup wire parse checks created query).run (merge memory state) := by
  let source := (simulateQ (sourceMid setup (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)
    checks target parameters created) ((CborRawCompile.compileImpl setup wire parse query).run memory)).run state
  have framed : (fun value => (value.1.1, merge value.1.2 value.2)) <$> source =
      (fun value => (value.1.1, (ofMemory memory,
        withBase (mergeX memory.copies state) (CborAdmissionCompiler.merge value.1.2
          (PqxdhRegistrationJointSchedule.source value.2.joint))))) <$> source := by
    apply PqxdhDeploymentKemTransfer.map_support_congr
    intro value supported
    have publicFrame := CborRawPublicState.interpreted_record_public _ setup wire parse query record memory state
      value supported
    have middle := supported
    dsimp only [source] at middle
    rw [CborRawMiddleRecords.middle_quiet_frame setup (CborRawCompile.sourceCodec wire parse)
      (CborRawCompile.route parse) checks target parameters created _
      (CborSplitIdealInterpreters.raw_record_quiet setup wire parse query record memory) state,
      support_map] at middle
    obtain ⟨inner, _, same⟩ := middle
    rw [← same] at publicFrame ⊢
    simpa only [merge, publicFrame, withBase, mergeX, CborAdmissionCompiler.merge]
  rw [framed]
  have native := CborRawMiddleRecords.raw_record_middle setup wire parse checks target parameters created query
    record memory state good
  have wrapped := congrArg (fun work => (fun value => (value.1,
    (ofMemory memory, withBase (mergeX memory.copies state) value.2))) <$> work) native
  simpa only [Functor.map_map, source, records, StateT.run, merge, mergeX, CborAdmissionCompiler.merge] using wrapped

theorem step_merge (query : Spec.Domain) (memory : CborAdmissionCompiler.Local) (state : Mid KemSK)
    (good : CborAdmissionCompiler.Good setup (CborRawCompile.sourceCodec wire parse) memory
      (PqxdhRegistrationJointSchedule.source state.joint)) :
    (fun value => (value.1.1, merge value.1.2 value.2)) <$>
        (simulateQ (sourceMid setup (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)
          checks target parameters created) ((CborRawCompile.compileImpl setup wire parse query).run memory)).run state =
      (handler setup wire parse checks target parameters created query).run (merge memory state) := by
  cases record : CborSplitCompiler.recordCommand query with
  | false =>
      simpa only [handler, record, Bool.false_eq_true, ite_false] using
        registration_step setup wire parse checks target parameters created query record memory state good
  | true =>
      simpa only [handler, record, ite_true] using
        record_step setup wire parse checks target parameters created query record memory state good

end Merge
end BeaconcryptCore.Computational.CborRawMiddleMerge

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleMerge.registration_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleMerge.registration_step

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleMerge.record_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleMerge.record_step

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleMerge.step_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleMerge.step_merge
