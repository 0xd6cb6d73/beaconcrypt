-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawMiddleInvariant
import BeaconcryptCore.Computational.CborRegistrationPublicLog
import BeaconcryptCore.Computational.CborRawPublicState

/-! Post-cut simulation into an independently defined native ideal handler. The target retains public registration bookkeeping beside the merged native state, never the compiler's copied kernels. Registration uses the fixed canonical codec and its existing hidden-root service; records retain exact native CBOR admission and their fallible writer. This is the middle-execution handoff, not yet an initialized slot-game or headline-security theorem. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawMiddleSimulation
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealPostSource (Mid sourceMid mergeX)
open CborRawPublicState (Public ofMemory toMemory)
open CborRawMiddleRegistration (request reply assignment)
variable {ι KemSK Reader Response X : Type} {baseSpec : OracleSpec ι}

abbrev Native (KemSK : Type) :=
  PqxdhDeploymentBackend.XState KemSK (PqxdhDeploymentIdealSteps.IdealBk PqxdhDeploymentIdealSteps.TableState) 2

def merge (memory : CborAdmissionCompiler.Local) (state : Mid KemSK) : Public × Native KemSK :=
  (ofMemory memory, mergeX memory.copies state)

def withBase (state : Native KemSK) (base : PqxdhDeploymentNative.State KemSK) : Native KemSK :=
  ⟨base, state.backend, state.seeds, PqxdhDeploymentLater.Snap.empty, []⟩

theorem request_record (memory : CborAdmissionCompiler.Local) (query : Spec.Domain) :
    CborSplitCompiler.recordCommand (request memory query) = CborSplitCompiler.recordCommand query := by
  rcases query with coin | command
  · rfl
  · cases command <;> simp only [CborRawMiddleRegistration.request, CborSplitCompiler.recordCommand]

theorem request_public (memory : CborAdmissionCompiler.Local) (query : Spec.Domain) :
    request (toMemory (ofMemory memory)) query = request memory query := by
  rcases query with coin | command
  · rfl
  · cases command <;> rfl

theorem reply_public (memory : CborAdmissionCompiler.Local) (query : Spec.Domain)
    (value : Spec.Range (request memory query)) :
    reply (toMemory (ofMemory memory)) query value = reply memory query value := by
  rcases query with coin | command
  · rfl
  · cases command <;> rfl

theorem assignment_public (memory : CborAdmissionCompiler.Local) (query : Spec.Domain)
    (value : Spec.Range (request memory query)) :
    assignment (toMemory (ofMemory memory)) query value = assignment memory query value := by
  rcases query with coin | command
  · rfl
  · cases command <;> rfl

section Handler
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit)

/-- Public request adaptation surrounds the actual ideal registration step. The source's moved-token call remains present on an oversized build, with empty data, so its private slot bookkeeping is retained. -/
noncomputable def registration (query : Spec.Domain) : StateT (Public × Native KemSK) ProbComp (Spec.Range query) :=
  fun state => do
    let memory := toMemory state.1
    let selected := request memory query
    let value ← (PqxdhDeploymentBackend.handlerWith setup (CborRawCompile.sourceCodec wire parse)
      (CborRawCompile.route parse) (PqxdhDeploymentIdealSteps.idealReg setup (CborRawCompile.sourceCodec wire parse)
        (CborRawCompile.route parse) checks target parameters created) selected).run state.2
    pure (reply memory query value.1,
      (⟨CborRegistrationPublicLog.update state.1.log selected value.1, assignment memory query value.1⟩,
        PqxdhDeploymentIdealCut.unghost value.2))

/-- Native record admission is below the unchanged secrecy program and reads the actual current selected kernel. -/
noncomputable def records (query : Spec.Domain) : StateT (Public × Native KemSK) ProbComp (Spec.Range query) :=
  fun state => (fun value => (value.1, (state.1, withBase state.2 value.2))) <$>
    (CborProductionBoundary.handler setup wire parse checks created.seed query).run state.2.base

theorem registration_public_run (query : Spec.Domain) (memory : CborAdmissionCompiler.Local)
    (state : Native KemSK) :
    (registration setup wire parse checks target parameters created query).run (ofMemory memory, state) = (do
      let value ← (PqxdhDeploymentBackend.handlerWith setup (CborRawCompile.sourceCodec wire parse)
        (CborRawCompile.route parse) (PqxdhDeploymentIdealSteps.idealReg setup (CborRawCompile.sourceCodec wire parse)
          (CborRawCompile.route parse) checks target parameters created) (request memory query)).run state
      pure (reply memory query value.1,
        ((⟨CborRegistrationPublicLog.update memory.copies.log (request memory query) value.1,
          assignment memory query value.1⟩ : Public), PqxdhDeploymentIdealCut.unghost value.2))) := by
  simp only [registration, StateT.run, ]
  rfl

noncomputable def handler : QueryImpl Spec (StateT (Public × Native KemSK) ProbComp) :=
  fun query => if CborSplitCompiler.recordCommand query then records setup wire parse checks created query
    else registration setup wire parse checks target parameters created query

noncomputable def compiled : QueryImpl Spec
    (StateT (CborAdmissionCompiler.Local × Mid KemSK) ProbComp) :=
  ((sourceMid setup (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)
    checks target parameters created).mapStateTBase (CborRawCompile.compileImpl setup wire parse)).flattenStateT

theorem compiled_run (query : Spec.Domain) (memory : CborAdmissionCompiler.Local) (state : Mid KemSK) :
    (compiled setup wire parse checks target parameters created query).run (memory, state) =
      (fun value => (value.1.1, (value.1.2, value.2))) <$>
        (simulateQ (sourceMid setup (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)
          checks target parameters created) ((CborRawCompile.compileImpl setup wire parse query).run memory)).run state :=
  rfl

/-- Registration's exact public log strengthens the existing native middle merge equation. The target computes that log solely from its public entry state and the actual registration reply. -/
theorem registration_step (query : Spec.Domain) (onlyRegistration : CborSplitCompiler.recordCommand query = false)
    (memory : CborAdmissionCompiler.Local) (state : Mid KemSK)
    (good : CborRawMiddleInvariant.Good setup wire parse target memory state) :
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
      (PqxdhRegistrationJointSchedule.source state.joint) good.1.nativeGood)
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
    (good : CborRawMiddleInvariant.Good setup wire parse target memory state) :
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
    record memory state good.1
  have wrapped := congrArg (fun work => (fun value => (value.1,
    (ofMemory memory, withBase (mergeX memory.copies state) value.2))) <$> work) native
  simpa only [Functor.map_map, source, records, StateT.run, merge, mergeX, CborAdmissionCompiler.merge] using wrapped

theorem step_merge (query : Spec.Domain) (memory : CborAdmissionCompiler.Local) (state : Mid KemSK)
    (good : CborRawMiddleInvariant.Good setup wire parse target memory state) :
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

/-- Every adaptive continuation after an active cut has the exact native ideal execution with only public compiler bookkeeping retained. No distributional handoff premise is assumed. -/
theorem compile_simulation
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (work : OracleComp Spec X) (memory : CborAdmissionCompiler.Local) (state : Mid KemSK)
    (good : CborRawMiddleInvariant.Good setup wire parse target memory state) :
    (fun value => (value.1.1, merge value.1.2 value.2)) <$>
        (simulateQ (sourceMid setup (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)
          checks target parameters created) ((simulateQ (CborRawCompile.compileImpl setup wire parse) work).run
            memory)).run state =
      (simulateQ (handler setup wire parse checks target parameters created) work).run (merge memory state) := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  have simulated := OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (compiled setup wire parse checks target parameters created) (handler setup wire parse checks target parameters created)
    (fun value => CborRawMiddleInvariant.Good setup wire parse target value.1 value.2)
    (fun value => merge value.1 value.2)
    (fun query initial valid result supported => by
      rw [compiled_run, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      exact CborRawMiddleInvariant.good_step setup wire parse checks target parameters created phase1 phase2 query
        initial.1 initial.2 valid inner reached)
    (fun query initial valid => by
      rw [compiled_run, Functor.map_map]
      exact step_merge setup wire parse checks target parameters created query initial.1 initial.2 valid)
    work (memory, state) good
  rw [← simulated]
  rfl

end Handler
end BeaconcryptCore.Computational.CborRawMiddleSimulation

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleSimulation.compile_simulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleSimulation.compile_simulation

-- Exact dependency observations for all public helper theorems.

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleSimulation.request_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleSimulation.request_record

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleSimulation.request_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleSimulation.request_public

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleSimulation.reply_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleSimulation.reply_public

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleSimulation.assignment_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleSimulation.assignment_public

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleSimulation.registration_public_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleSimulation.registration_public_run

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleSimulation.compiled_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleSimulation.compiled_run

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleSimulation.registration_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleSimulation.registration_step

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleSimulation.record_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleSimulation.record_step

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleSimulation.step_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleSimulation.step_merge
