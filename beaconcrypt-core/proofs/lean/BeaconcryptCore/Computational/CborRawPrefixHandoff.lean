-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawPreScan

/-! One initialized source execution supplies both sides of the raw selected-accept prefix. At a pending cut its full native state is reconstructed from the actual common-prefix outcome, with the exact selected ordinal and original continuation. Completed runs return the explicit no-selected-accept result. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawPrefixHandoff
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentIdealCut (CutCE scanCE sourceInit withAccepts)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealPostSource (Mid)
open CborRawPublicState (Public ofMemory)
open CborRawMiddleSimulation (Native)
variable {ι KemSK Reader Response A Result : Type} {baseSpec : OracleSpec ι}
section Prefix
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)

noncomputable def initial (privatePool : PqxdhRegistrationJointPreparation.Pool KemSK) : Mid KemSK :=
  ⟨sourceInit created privatePool, PqxdhDeploymentIdealSteps.idealInit created, ∅⟩

noncomputable def start (privatePool : PqxdhRegistrationJointPreparation.Pool KemSK) : CborRawPreScan.Source KemSK :=
  (CborAdmissionCompiler.Local.empty setup.serverKeyId, initial created privatePool)

/-- The exact native state at a reached pending cut; source-owned private pools remain in the source outcome. -/
def atCut (value : (CutCE Result × CborAdmissionCompiler.Local) × PqxdhRegistrationJointSchedule.State KemSK) :
    Public × Native KemSK :=
  CborRawMiddleSimulation.merge value.1.2
    ⟨value.2, withAccepts (PqxdhDeploymentIdealSteps.idealInit created) target.accept, ∅⟩

def resume (next : (raw : Pqxdh.Bytes) → (Option Nat → OracleComp Spec Result) → (Public × Native KemSK) → ProbComp Bool) :
    CutCE Result → (Public × Native KemSK) → ProbComp Bool
  | .complete _, _ => pure false
  | .pending raw rest, state => next raw rest state

/-- The source prefix invariant starts at the actual generated/imported Server constructor outcome. -/
theorem initial_inv (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (before after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (born : (some created, after) ∈ support
      ((PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId supplied).run before)) :
    CborRawPreScan.Inv setup wire parse (initial created after.1) (start setup created after.1) := by
  refine ⟨?_, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact CborRawInitializedCut.initial_good setup wire parse created ensureInit supplied before after born

/-- The initial full source reconstruction is the actual native initial state. -/
theorem native_start (privatePool : PqxdhRegistrationJointPreparation.Pool KemSK) :
    CborRawPreScan.native (start setup created privatePool) =
      (ofMemory (CborAdmissionCompiler.Local.empty setup.serverKeyId),
        PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created)) := by
  simp only [CborRawPreScan.native, start, initial, CborRawMiddleSimulation.merge,
    PqxdhDeploymentIdealPostSource.mergeX, CborAdmissionCompiler.Local.empty, PqxdhDeploymentCompile.merge_empty]
  rfl

/-- Flattening the actual pool compiler gives precisely the initialized raw common prefix. -/
theorem pool_run (privatePool : PqxdhRegistrationJointPreparation.Pool KemSK) (work : OracleComp Spec Result) :
    (fun value => ((value.1, value.2.1), value.2.2)) <$>
        (simulateQ (CborRawPreScan.poolCompiler setup wire parse checks target parameters created)
          (scanCE work target.accept)).run
            (CborAdmissionCompiler.Local.empty setup.serverKeyId, sourceInit created privatePool) =
      CborRawInitializedCut.commonPrefix setup wire parse checks target parameters created privatePool work := by
  have flattened := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (PqxdhDeploymentIdealPoolSource.sourcePool setup (CborRawCompile.sourceCodec wire parse) checks created.seed
      created.server.server.metadata.identityIndex (parameters.pool target)) (CborRawCompile.compileImpl setup wire parse)
    (scanCE work target.accept) (CborAdmissionCompiler.Local.empty setup.serverKeyId) (sourceInit created privatePool)
  simpa only [CborRawPreScan.poolCompiler, CborRawInitializedCut.commonPrefix, CborRawCutPrefix.source,
    CborRawCompile.compile] using flattened.symm

/-- Native and item-2 prefixes feed exactly the same pending native continuation, including actual raw replies and complete reconstructed state. No prefix-simulation premise is supplied. -/
theorem common_prefix
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (before after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (born : (some created, after) ∈ support
      ((PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId supplied).run before))
    (work : OracleComp Spec Result)
    (next : (raw : Pqxdh.Bytes) → (Option Nat → OracleComp Spec Result) → (Public × Native KemSK) → ProbComp Bool) :
    ((simulateQ (CborRawMiddleSimulation.handler setup wire parse checks target parameters created)
        (scanCE work target.accept)).run
          (ofMemory (CborAdmissionCompiler.Local.empty setup.serverKeyId),
            PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created)) >>= fun value =>
        resume next value.1 value.2) =
      (CborRawInitializedCut.commonPrefix setup wire parse checks target parameters created after.1 work >>= fun value =>
        resume next value.1.1 (atCut target created value)) := by
  have valid := initial_inv setup wire parse created ensureInit supplied before after born
  have room : CborRawPreScan.counter (start setup created after.1) + target.accept ≤ target.accept := by
    simp only [CborRawPreScan.counter, start, initial, PqxdhDeploymentIdealSteps.idealInit,
      PqxdhDeploymentIdealSteps.IdealCore.initial, Nat.zero_add]
    exact Nat.le_refl _
  have merged := CborRawPreScan.scan_native setup wire parse checks target parameters created phase1 phase2
    (initial created after.1) work target.accept (start setup created after.1) valid room
  have pooled := CborRawPreScan.scan_pool setup wire parse checks target parameters created phase1 phase2
    (initial created after.1) work target.accept (start setup created after.1) valid room
  have nativeRun := merged.1
  rw [native_start] at nativeRun
  have poolRun := congrArg (fun program => (fun value => ((value.1, value.2.1), value.2.2)) <$> program) pooled.1
  rw [Functor.map_map] at poolRun
  change _ = (fun value => ((value.1, value.2.1), value.2.2)) <$>
    (simulateQ (CborRawPreScan.poolCompiler setup wire parse checks target parameters created)
      (scanCE work target.accept)).run
      (CborAdmissionCompiler.Local.empty setup.serverKeyId, sourceInit created after.1) at poolRun
  rw [pool_run] at poolRun
  rw [← nativeRun, bind_map_left, ← poolRun, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun value supported => ?_
  cases pending : value.1 with
  | complete result =>
      simp only [Prod.map_fst, id_eq, pending, resume]
  | pending raw continuation =>
      obtain ⟨kept, _, clock⟩ := merged.2 value supported
      have current : CborRawPreScan.counter value.2 = target.accept := by
        simpa only [CborRawPreScan.counter, start, initial, PqxdhDeploymentIdealSteps.idealInit,
          PqxdhDeploymentIdealSteps.IdealCore.initial, Nat.zero_add] using clock raw continuation pending
      have backend : value.2.2.backend = withAccepts (PqxdhDeploymentIdealSteps.idealInit created) target.accept := by
        rw [kept.backend, current]
        rfl
      have seeds : value.2.2.seeds = ∅ := kept.seeds
      have nativeState : CborRawPreScan.native value.2 = atCut target created
          ((value.1, value.2.1), value.2.2.joint) := by
        simp only [CborRawPreScan.native, atCut, CborRawMiddleSimulation.merge,
          PqxdhDeploymentIdealPostSource.mergeX, backend, seeds]
      simp only [resume, pending, Prod.map_fst, Prod.map_snd, id_eq, CborRawPreScan.pool]
      rw [nativeState, pending]

end Prefix
end BeaconcryptCore.Computational.CborRawPrefixHandoff

/-- info: 'BeaconcryptCore.Computational.CborRawPrefixHandoff.initial_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPrefixHandoff.initial_inv
/-- info: 'BeaconcryptCore.Computational.CborRawPrefixHandoff.native_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPrefixHandoff.native_start
/-- info: 'BeaconcryptCore.Computational.CborRawPrefixHandoff.pool_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPrefixHandoff.pool_run
/-- info: 'BeaconcryptCore.Computational.CborRawPrefixHandoff.common_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPrefixHandoff.common_prefix
