-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawCompileCut
import BeaconcryptCore.Computational.CborRawMiddleCounter

/-! The public raw compiler before the selected accept, with both actual creates reading the challenger's fixed KEM pool. All other commands keep the genuine raw handler. This supplies the native pool side of the cut without replacing registration with a fixed-codec experiment. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawPoolCompiler
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentRecordCache (SourceSpec)
open PqxdhRegistrationJointRevealCosts (sourceKind)
open PqxdhDeploymentCompileBudget (commandKind)
variable {ι KemSK Reader Response X S : Type} {baseSpec : OracleSpec ι}

section Pool
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (pairs : List (PqxdhLiveKemReservation.Pair KemSK))

noncomputable def source :=
  PqxdhDeploymentIdealPool.revealPool setup (CborRawCompile.sourceCodec wire parse) checks seed pairs

noncomputable def native : QueryImpl Spec (StateT (PqxdhDeploymentNative.State KemSK) ProbComp)
  | .inr (.create pin keyId) => PqxdhDeploymentIdealPool.deploymentPool setup
      (CborRawCompile.sourceCodec wire parse) checks (CborRawCompile.route parse) seed pairs (.inr (.create pin keyId))
  | query => CborProductionBoundary.handler setup wire parse checks seed query

noncomputable def compiled : QueryImpl Spec
    (StateT (CborAdmissionCompiler.Local × PqxdhRegistrationSchedule.State KemSK) ProbComp) :=
  ((source setup wire parse checks seed pairs).mapStateTBase (CborRawCompile.compileImpl setup wire parse)).flattenStateT

theorem compiled_run (query : Spec.Domain) (memory : CborAdmissionCompiler.Local)
    (state : PqxdhRegistrationSchedule.State KemSK) :
    (compiled setup wire parse checks seed pairs query).run (memory, state) =
      (fun value => (value.1.1, (value.1.2, value.2))) <$>
        (simulateQ (source setup wire parse checks seed pairs)
          ((CborRawCompile.compileImpl setup wire parse query).run memory)).run state := rfl

theorem no_create (query : Spec.Domain) (memory : CborAdmissionCompiler.Local) (other : commandKind query ≠ 1) :
    ((CborRawCompile.compileImpl setup wire parse query).run memory).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = .inl 1) 0 := by
  have bound := CborRawCompile.step_bound setup wire parse (.inl 1) query memory
  have zero : PqxdhDeploymentCompileBudget.cost (.inl 1) (commandKind query) = 0 := by
    rcases query with coin | command
    · rfl
    · cases command <;> first | rfl | exact absurd rfl other
  simpa only [zero] using bound

theorem source_other (query : Spec.Domain) (memory : CborAdmissionCompiler.Local) (other : commandKind query ≠ 1) :
    simulateQ (source setup wire parse checks seed pairs)
        ((CborRawCompile.compileImpl setup wire parse query).run memory) =
      simulateQ (PqxdhRegistrationJointRevealSchedule.native setup (CborRawCompile.sourceCodec wire parse) checks seed)
        ((CborRawCompile.compileImpl setup wire parse query).run memory) :=
  PqxdhDeploymentIdealPool.simulateQ_congr_none _ _ _
    (PqxdhDeploymentIdealPool.revealPool_agree setup (CborRawCompile.sourceCodec wire parse) checks seed pairs)
    _ (no_create setup wire parse query memory other)

theorem create_source_run (pin : Pqxdh.Bytes) (keyId : Std.U64) (memory : CborAdmissionCompiler.Local)
    (state : PqxdhRegistrationSchedule.State KemSK) :
    (simulateQ (source setup wire parse checks seed pairs)
      ((CborRawCompile.compileImpl setup wire parse (.inr (.create pin keyId))).run memory)).run state =
      (fun value => ((value.1.1, { memory with copies := value.1.2 }), value.2)) <$>
        (simulateQ (source setup wire parse checks seed pairs)
          ((PqxdhDeploymentCompile.compileImpl setup (CborRawCompile.sourceCodec wire parse)
            (CborRawCompile.route parse) (.inr (.create pin keyId))).run memory.copies)).run state := by
  change (simulateQ (source setup wire parse checks seed pairs)
    ((fun value => (value.1, { memory with copies := value.2 })) <$>
      (PqxdhDeploymentCompile.compileImpl setup (CborRawCompile.sourceCodec wire parse)
        (CborRawCompile.route parse) (.inr (.create pin keyId))).run memory.copies)).run state = _
  rw [simulateQ_map, StateT.run_map]

theorem pool_noBuild {Y : Type} (work : OracleComp (SourceSpec KemSK) Y)
    (quiet : work.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = .inl 4) 0)
    (state : PqxdhRegistrationSchedule.State KemSK) (result : Y × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((simulateQ (source setup wire parse checks seed pairs) work).run state)) :
    result.2.shared.2.server.control.last_key_id = state.shared.2.server.control.last_key_id := by
  induction work using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at quiet
      have other : sourceKind (KemSK := KemSK) query ≠ .inl 4 := by
        rcases quiet.1 with absent | impossible
        · exact absent
        · omega
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, supported⟩ := supported
      have kept := CborRawMiddleCounter.pool_assignment setup (CborRawCompile.sourceCodec wire parse) checks seed
        pairs query state middle reached
      rw [CborRawMiddleCounter.assignedAfter_other query other] at kept
      have tail := quiet.2 middle.1
      simp only [other, ite_false] at tail
      exact (ih middle.1 tail middle.2 result supported).trans kept.symm

/-- Pool creation changes only its original generated owner and public pin log. Every other raw command keeps the established exact compiler equation. -/
theorem step_merge (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (CborTaggedSimulation.boundaryWire wire parse))
    (query : Spec.Domain) (memory : CborAdmissionCompiler.Local) (state : PqxdhRegistrationSchedule.State KemSK)
    (good : CborAdmissionCompiler.Good setup (CborRawCompile.sourceCodec wire parse) memory state) :
    (fun value => (value.1.1, CborAdmissionCompiler.merge value.1.2 value.2)) <$>
        (simulateQ (source setup wire parse checks seed pairs)
          ((CborRawCompile.compileImpl setup wire parse query).run memory)).run state =
      (native setup wire parse checks seed pairs query).run (CborAdmissionCompiler.merge memory state) := by
  by_cases create : commandKind query = 1
  · rcases query with coin | command
    · exact absurd create (by simp [commandKind])
    · cases command with
      | create pin keyId =>
          rw [create_source_run, Functor.map_map]
          have old := PqxdhDeploymentIdealPool.step_merge_pool setup (CborRawCompile.sourceCodec wire parse) checks
            (CborRawCompile.route parse) seed pairs (.inr (.create pin keyId)) memory.copies state
            (PqxdhDeploymentCompileInvariant.good_inv setup (CborRawCompile.sourceCodec wire parse)
              memory.copies state good.nativeGood)
          simpa only [PqxdhDeploymentIdealPool.compiledPool, QueryImpl.flattenStateT_mapStateTBase_apply_run,
            Functor.map_map, Prod.map_apply, id_eq, CborAdmissionCompiler.merge, native, source] using old
      | _ => exact absurd create (by simp [commandKind])
  · rw [source_other setup wire parse checks seed pairs query memory create]
    have nativeStep := CborRawCompile.public_step_merge setup wire parse checks lengths parser seed query memory state good
    rcases query with coin | command
    · exact nativeStep
    · cases command
      all_goals first | exact absurd rfl create | exact nativeStep

theorem good_step
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (query : Spec.Domain) (memory : CborAdmissionCompiler.Local) (state : PqxdhRegistrationSchedule.State KemSK)
    (good : CborAdmissionCompiler.Good setup (CborRawCompile.sourceCodec wire parse) memory state)
    (value : (Spec.Range query × CborAdmissionCompiler.Local) × PqxdhRegistrationSchedule.State KemSK)
    (supported : value ∈ support ((simulateQ (source setup wire parse checks seed pairs)
      ((CborRawCompile.compileImpl setup wire parse query).run memory)).run state)) :
    CborAdmissionCompiler.Good setup (CborRawCompile.sourceCodec wire parse) value.1.2 value.2 := by
  by_cases create : commandKind query = 1
  · rcases query with coin | command
    · exact absurd create (by simp [commandKind])
    · cases command with
      | create pin keyId =>
          rw [create_source_run, support_map] at supported
          obtain ⟨inner, reached, rfl⟩ := supported
          have oldSupported : (inner.1.1, (inner.1.2, inner.2)) ∈ support
              ((PqxdhDeploymentIdealPool.compiledPool setup (CborRawCompile.sourceCodec wire parse) checks
                (CborRawCompile.route parse) seed pairs (.inr (.create pin keyId))).run (memory.copies, state)) := by
            change _ ∈ support ((fun result :
              (Option Nat × PqxdhDeploymentCompile.Local) × PqxdhRegistrationSchedule.State KemSK =>
                (result.1.1, (result.1.2, result.2))) <$> _)
            rw [support_map]
            exact ⟨inner, reached, rfl⟩
          refine ⟨PqxdhDeploymentIdealPool.good_step_pool setup (CborRawCompile.sourceCodec wire parse) checks
            (CborRawCompile.route parse) seed pairs phase1 phase2 (.inr (.create pin keyId)) memory.copies state
            good.nativeGood _ oldSupported, ?_⟩
          have clock := pool_noBuild setup wire parse checks seed pairs _
            (CborAdmissionInvariant.existing_no_build_bound setup (CborRawCompile.sourceCodec wire parse)
              (CborRawCompile.route parse) (.inr (.create pin keyId))
              (by simp [commandKind]) memory.copies) state inner reached
          exact good.lastId.trans clock.symm
      | _ => exact absurd create (by simp [commandKind])
  · rw [source_other setup wire parse checks seed pairs query memory create] at supported
    apply CborRawCompile.good_step setup wire parse checks seed phase1 phase2 query memory state good
      (value.1.1, (value.1.2, value.2))
    rw [CborRawCompile.compiled_run, support_map]
    exact ⟨value, supported, rfl⟩

/-- Every adaptive prefix, including the secrecy wrapper's hidden draws and failed registration writes, has the exact pooled raw native execution. -/
theorem compile_simulation (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (CborTaggedSimulation.boundaryWire wire parse))
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (work : OracleComp Spec X) (memory : CborAdmissionCompiler.Local)
    (state : PqxdhRegistrationSchedule.State KemSK)
    (good : CborAdmissionCompiler.Good setup (CborRawCompile.sourceCodec wire parse) memory state) :
    (fun value => (value.1.1, CborAdmissionCompiler.merge value.1.2 value.2)) <$>
        (simulateQ (source setup wire parse checks seed pairs)
          ((simulateQ (CborRawCompile.compileImpl setup wire parse) work).run memory)).run state =
      (simulateQ (native setup wire parse checks seed pairs) work).run (CborAdmissionCompiler.merge memory state) := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  have simulated := OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (compiled setup wire parse checks seed pairs) (native setup wire parse checks seed pairs)
    (fun initial => CborAdmissionCompiler.Good setup (CborRawCompile.sourceCodec wire parse) initial.1 initial.2)
    (fun initial => CborAdmissionCompiler.merge initial.1 initial.2)
    (fun query initial valid result supported => by
      rw [compiled_run, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      exact good_step setup wire parse checks seed pairs phase1 phase2 query initial.1 initial.2 valid inner reached)
    (fun query initial valid => by
      rw [compiled_run, Functor.map_map]
      exact step_merge setup wire parse checks seed pairs lengths parser query initial.1 initial.2 valid)
    work (memory, state) good
  rw [← simulated]
  rfl

end Pool
end BeaconcryptCore.Computational.CborRawPoolCompiler

/-- info: 'BeaconcryptCore.Computational.CborRawPoolCompiler.step_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPoolCompiler.step_merge

/-- info: 'BeaconcryptCore.Computational.CborRawPoolCompiler.good_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPoolCompiler.good_step

/-- info: 'BeaconcryptCore.Computational.CborRawPoolCompiler.compile_simulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPoolCompiler.compile_simulation

-- Exact dependency observations for all public helper theorems.

/-- info: 'BeaconcryptCore.Computational.CborRawPoolCompiler.compiled_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPoolCompiler.compiled_run

/-- info: 'BeaconcryptCore.Computational.CborRawPoolCompiler.no_create' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPoolCompiler.no_create

/-- info: 'BeaconcryptCore.Computational.CborRawPoolCompiler.source_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPoolCompiler.source_other

/-- info: 'BeaconcryptCore.Computational.CborRawPoolCompiler.create_source_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPoolCompiler.create_source_run

/-- info: 'BeaconcryptCore.Computational.CborRawPoolCompiler.pool_noBuild' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPoolCompiler.pool_noBuild
