-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawMiddleMarks
import BeaconcryptCore.Computational.CborRawPostActive

/-! Cutting an initialized native raw ideal execution preserves its selected-session decision. A completed prefix is unmarked, and a pending prefix resumes the actual raw accept on the complete state reconstructed from the shared source execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawMarkedPrefix
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealCut (CutCE scanCE finishCE)
open CborRawPublicState (Public ofMemory)
open CborRawMiddleSimulation (Native)
open CborRawPrefixHandoff (initial start atCut)
variable {ι KemSK Reader Response A Result : Type} {baseSpec : OracleSpec ι}
section Prefix
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)

noncomputable def run (work : OracleComp Spec Result) (event : Result × CborRawPostActive.Produced → Bool)
    (state : Public × Native KemSK) : ProbComp Bool :=
  (fun value => event (value.1, value.2.2.base.produced) && (CborRawMiddleMarks.marks value.2).isSome) <$>
    (simulateQ (CborRawMiddleSimulation.handler setup wire parse checks target parameters created) work).run state

noncomputable def resume (event : Result × CborRawPostActive.Produced → Bool) (cut : CutCE Result)
    (state : Public × Native KemSK) : ProbComp Bool :=
  CborRawPrefixHandoff.resume (fun raw next current =>
    run setup wire parse checks target parameters created (finishCE (.pending raw next)) event current) cut state

/-- The complete initialized marked native execution is the actual source common prefix followed by its original pending continuation. -/
theorem common_prefix
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (before after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (born : (some created, after) ∈ support
      ((PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId supplied).run before))
    (work : OracleComp Spec Result) (event : Result × CborRawPostActive.Produced → Bool) :
    run setup wire parse checks target parameters created work event
      (ofMemory (CborAdmissionCompiler.Local.empty setup.serverKeyId),
        PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created)) =
      (CborRawInitializedCut.commonPrefix setup wire parse checks target parameters created after.1 work >>= fun value =>
        resume setup wire parse checks target parameters created event value.1.1 (atCut target created value)) := by
  have valid := CborRawPrefixHandoff.initial_inv setup wire parse created ensureInit supplied before after born
  have room : CborRawPreScan.counter (start setup created after.1) + target.accept ≤ target.accept := by
    simp only [CborRawPreScan.counter, start, initial, PqxdhDeploymentIdealSteps.idealInit,
      PqxdhDeploymentIdealSteps.IdealCore.initial, Nat.zero_add]
    exact Nat.le_refl _
  have merged := CborRawPreScan.scan_native setup wire parse checks target parameters created phase1 phase2
    (initial created after.1) work target.accept (start setup created after.1) valid room
  have nativeRun := merged.1
  rw [CborRawPrefixHandoff.native_start] at nativeRun
  have first : run setup wire parse checks target parameters created work event
      (ofMemory (CborAdmissionCompiler.Local.empty setup.serverKeyId),
        PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created)) =
      ((simulateQ (CborRawMiddleSimulation.handler setup wire parse checks target parameters created)
        (scanCE work target.accept)).run
          (ofMemory (CborAdmissionCompiler.Local.empty setup.serverKeyId),
            PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created)) >>= fun value =>
        resume setup wire parse checks target parameters created event value.1 value.2) := by
    rw [run, PqxdhDeploymentIdealCut.run_scanCE, map_bind, ← nativeRun, bind_map_left]
    rw [bind_map_left]
    refine bind_congr_of_forall_mem_support _ fun value supported => ?_
    cases pending : value.1 with
    | pending raw next =>
        simp only [Prod.map_fst, Prod.map_snd, id_eq, pending, resume, CborRawPrefixHandoff.resume, run]
    | complete result =>
        have kept := (merged.2 value supported).1
        have empty : CborRawMiddleMarks.marks (CborRawPreScan.native value.2) = none := by
          change value.2.2.backend.2.2.marks = none
          rw [kept.backend]
          rfl
        simp only [Prod.map_fst, Prod.map_snd, id_eq, pending, finishCE, simulateQ_pure, StateT.run_pure,
          map_pure, resume, CborRawPrefixHandoff.resume, empty, Option.isSome_none, Bool.and_false]
  rw [first]
  exact CborRawPrefixHandoff.common_prefix setup wire parse checks target parameters created phase1 phase2 ensureInit
    supplied before after born work (fun raw next current =>
      run setup wire parse checks target parameters created (finishCE (.pending raw next)) event current)

end Prefix
end BeaconcryptCore.Computational.CborRawMarkedPrefix

/-- info: 'BeaconcryptCore.Computational.CborRawMarkedPrefix.common_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMarkedPrefix.common_prefix
