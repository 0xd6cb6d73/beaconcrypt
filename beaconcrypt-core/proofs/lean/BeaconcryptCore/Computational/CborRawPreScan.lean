-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawScanProjection
import BeaconcryptCore.Computational.CborRawWorldHandoff

/-! The initialized source prefix and native raw middle prefix are projections of the same concrete compiler execution. Every reached source state retains the complete reconstruction invariant, private pool and seed state; its pending accept counter is the original raw-attempt ordinal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawPreScan
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentIdealCut (CutCE scanCE bump withAccepts)
open PqxdhDeploymentCompileBudget (commandKind)
open PqxdhDeploymentIdealPostSource (Mid)
open PqxdhDeploymentIdealParams (Target Params)
variable {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}

abbrev Source (KemSK : Type) := CborAdmissionCompiler.Local × Mid KemSK

def counter (state : Source KemSK) : Nat := state.2.backend.2.2.accepts

def native (state : Source KemSK) := CborRawMiddleSimulation.merge state.1 state.2

def pool (state : Source KemSK) := (state.1, state.2.joint)

structure Inv (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (initial : Mid KemSK) (state : Source KemSK) : Prop where
  good : CborAdmissionCompiler.Good setup (CborRawCompile.sourceCodec wire parse) state.1
    (PqxdhRegistrationJointSchedule.source state.2.joint)
  pre : CborRawPreSource.Pre state.2
  backend : state.2.backend = withAccepts initial.backend (counter state)
  seeds : state.2.seeds = initial.seeds

private theorem bump_counter (query : Spec.Domain)
    (backend : PqxdhDeploymentIdealSteps.IdealBk PqxdhDeploymentIdealSteps.TableState) :
    (bump query backend).2.2.accepts = backend.2.2.accepts + if commandKind query = 3 then 1 else 0 := by
  rcases query with coin | command
  · rfl
  · cases command <;> rfl

private theorem bump_counted (query : Spec.Domain)
    (backend : PqxdhDeploymentIdealSteps.IdealBk PqxdhDeploymentIdealSteps.TableState) (count : Nat) :
    bump query (withAccepts backend count) =
      withAccepts backend (count + if commandKind query = 3 then 1 else 0) := by
  rcases query with coin | command
  · rfl
  · cases command <;> rfl

section Scan
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)

noncomputable def poolCompiler :
    QueryImpl Spec (StateT (CborAdmissionCompiler.Local × PqxdhRegistrationJointSchedule.State KemSK) ProbComp) :=
  ((PqxdhDeploymentIdealPoolSource.sourcePool setup (CborRawCompile.sourceCodec wire parse) checks created.seed
    created.server.server.metadata.identityIndex (parameters.pool target)).mapStateTBase
      (CborRawCompile.compileImpl setup wire parse)).flattenStateT

/-- Every supported pre-cut compiled step retains the actual private backend frame and advances the raw counter exactly once on accepts. -/
theorem query_keeps
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (initial : Mid KemSK) (query : Spec.Domain) (state : Source KemSK) (valid : Inv setup wire parse initial state)
    (other : ∀ raw, query = .inr (.accept raw) → counter state ≠ target.accept)
    (value : Spec.Range query × Source KemSK)
    (supported : value ∈ support
      ((CborRawMiddleSimulation.compiled setup wire parse checks target parameters created query).run state)) :
    Inv setup wire parse initial value.2 ∧
      counter value.2 = counter state + if commandKind query = 3 then 1 else 0 := by
  rw [CborRawMiddleSimulation.compiled_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  have good := CborRawPreSource.good_step setup wire parse checks target parameters created phase1 phase2 query state.1
    state.2 valid.pre other valid.good inner reached
  rw [CborRawPreSource.shape setup wire parse checks target parameters created query state.1 state.2 valid.pre other,
    support_map] at reached
  obtain ⟨pooled, _, rfl⟩ := reached
  refine ⟨⟨good.1, good.2, ?_, valid.seeds⟩, bump_counter query state.2.backend⟩
  change bump query state.2.backend = withAccepts initial.backend (bump query state.2.backend).2.2.accepts
  rw [valid.backend, bump_counted]
  rfl

/-- The complete single-step compiler projection holds before the cut without a past-accept premise. -/
theorem query_native (initial : Mid KemSK) (query : Spec.Domain) (state : Source KemSK)
    (valid : Inv setup wire parse initial state) :
    Prod.map id native <$>
        (CborRawMiddleSimulation.compiled setup wire parse checks target parameters created query).run state =
      (CborRawMiddleSimulation.handler setup wire parse checks target parameters created query).run (native state) := by
  rw [CborRawMiddleSimulation.compiled_run, Functor.map_map]
  simpa only [Prod.map_apply, Prod.map_fst, Prod.map_snd, id_eq, native] using
    CborRawMiddleMerge.step_merge setup wire parse checks target parameters created query state.1 state.2 valid.good

/-- Erasing only the backend annotations yields the same full raw memory and actual private source pool prefix. -/
theorem query_pool (initial : Mid KemSK) (query : Spec.Domain) (state : Source KemSK)
    (valid : Inv setup wire parse initial state)
    (other : ∀ raw, query = .inr (.accept raw) → counter state ≠ target.accept) :
    Prod.map id pool <$>
        (CborRawMiddleSimulation.compiled setup wire parse checks target parameters created query).run state =
      (poolCompiler setup wire parse checks target parameters created query).run (pool state) := by
  rw [CborRawMiddleSimulation.compiled_run,
    CborRawPreSource.shape setup wire parse checks target parameters created query state.1 state.2 valid.pre other,
    Functor.map_map, Functor.map_map]
  rfl

/-- Native raw execution of a complete adaptive accept prefix is the exact merged image of the invariant-carrying source execution. -/
theorem scan_native
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (initial : Mid KemSK) (work : OracleComp Spec Result) (index : Nat) (state : Source KemSK)
    (valid : Inv setup wire parse initial state) (room : counter state + index ≤ target.accept) :
    Prod.map id native <$>
        (simulateQ (CborRawMiddleSimulation.compiled setup wire parse checks target parameters created)
          (scanCE work index)).run state =
      (simulateQ (CborRawMiddleSimulation.handler setup wire parse checks target parameters created)
        (scanCE work index)).run (native state) ∧
      ∀ value ∈ support ((simulateQ (CborRawMiddleSimulation.compiled setup wire parse checks target parameters created)
          (scanCE work index)).run state), Inv setup wire parse initial value.2 ∧
        counter value.2 ≤ counter state + index ∧
        ∀ raw next, value.1 = .pending raw next → counter value.2 = counter state + index :=
  CborRawScanProjection.scan _ _ native (Inv setup wire parse initial) counter target.accept
    (fun query current holds _ => query_native setup wire parse checks target parameters created initial query current holds)
    (query_keeps setup wire parse checks target parameters created phase1 phase2 initial) work index state valid room

/-- The same invariant-carrying execution projects to the actual raw common-prefix source pool. -/
theorem scan_pool
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (initial : Mid KemSK) (work : OracleComp Spec Result) (index : Nat) (state : Source KemSK)
    (valid : Inv setup wire parse initial state) (room : counter state + index ≤ target.accept) :
    Prod.map id pool <$>
        (simulateQ (CborRawMiddleSimulation.compiled setup wire parse checks target parameters created)
          (scanCE work index)).run state =
      (simulateQ (poolCompiler setup wire parse checks target parameters created) (scanCE work index)).run (pool state) ∧
      ∀ value ∈ support ((simulateQ (CborRawMiddleSimulation.compiled setup wire parse checks target parameters created)
          (scanCE work index)).run state), Inv setup wire parse initial value.2 ∧
        counter value.2 ≤ counter state + index ∧
        ∀ raw next, value.1 = .pending raw next → counter value.2 = counter state + index :=
  CborRawScanProjection.scan _ _ pool (Inv setup wire parse initial) counter target.accept
    (query_pool setup wire parse checks target parameters created initial)
    (query_keeps setup wire parse checks target parameters created phase1 phase2 initial) work index state valid room

end Scan
end BeaconcryptCore.Computational.CborRawPreScan

/-- info: 'BeaconcryptCore.Computational.CborRawPreScan.query_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPreScan.query_keeps
/-- info: 'BeaconcryptCore.Computational.CborRawPreScan.query_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPreScan.query_native
/-- info: 'BeaconcryptCore.Computational.CborRawPreScan.query_pool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPreScan.query_pool
/-- info: 'BeaconcryptCore.Computational.CborRawPreScan.scan_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPreScan.scan_native
/-- info: 'BeaconcryptCore.Computational.CborRawPreScan.scan_pool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPreScan.scan_pool
