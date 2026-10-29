-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawCompile
import BeaconcryptCore.Computational.PqxdhDeploymentIdealCut

/-! Cutting the public raw compiler counts original accept attempts, including rejections. The generic theorem depends only on an exact forwarded accept and the proved absence of accepts from every other command. It makes no assumption about an ideal-game or event simulation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawCompileCut
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentRecordCache (SourceSpec)
open PqxdhRegistrationJointRevealCosts (sourceKind)
open PqxdhRegistrationJointAcceptCut (Cut scan)
open PqxdhDeploymentIdealCut (CutCE scanCE)
open PqxdhDeploymentCompileBudget (commandKind)
variable {ι KemSK Reader Response S X : Type} {baseSpec : OracleSpec ι}

section Generic
variable (compiler : QueryImpl Spec (StateT S (OracleComp (SourceSpec KemSK))))
  (afterAccept : S → Pqxdh.Bytes → Option Nat → S)

/-- Resume a public cut only after logging the eventual answer of its suspended original accept. -/
noncomputable def cut : CutCE X × S → Cut KemSK (X × S)
  | (.complete value, memory) => .complete (value, memory)
  | (.pending raw next, memory) => .pending raw fun answer =>
      (simulateQ compiler (next answer)).run (afterAccept memory raw answer)

/-- Any exact stateful compiler that forwards accepts once and emits no hidden accepts commutes with the raw-attempt scan. -/
theorem compile_scan
    (accept : ∀ raw memory, (compiler (.inr (.accept raw))).run memory =
      ((SourceSpec KemSK).query (.inl (.inr (.accept raw))) : OracleComp (SourceSpec KemSK) (Option Nat)) >>= fun answer =>
        pure (answer, afterAccept memory raw answer))
    (noAccept : ∀ query memory, commandKind query ≠ 3 →
      ((compiler query).run memory).IsQueryBoundP
        (fun request => sourceKind (KemSK := KemSK) request = .inl 3) 0)
    (work : OracleComp Spec X) (index : Nat) (memory : S) :
    scan ((simulateQ compiler work).run memory) index =
      cut compiler afterAccept <$> (simulateQ compiler (scanCE work index)).run memory := by
  induction work using OracleComp.inductionOn generalizing index memory with
  | pure value => rfl
  | query_bind query next ih =>
    by_cases selected : commandKind query = 3
    · rcases query with coin | command
      · exact absurd selected (by simp [commandKind])
      · cases command with
        | accept raw =>
          cases index with
          | zero =>
            simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, accept, bind_assoc,
              pure_bind, PqxdhDeploymentIdealCut.scanCE_accept_zero, simulateQ_pure,
              StateT.run_pure, map_pure, cut]
            rfl
          | succ index =>
            rw [PqxdhDeploymentIdealCut.scanCE_accept_succ, simulateQ_bind, simulateQ_bind,
              simulateQ_spec_query, StateT.run_bind, StateT.run_bind, map_bind]
            simp only [accept, bind_assoc, pure_bind]
            change ((SourceSpec KemSK).query (.inl (.inr (.accept raw))) >>= fun answer =>
              scan ((simulateQ compiler (next answer)).run (afterAccept memory raw answer)) index :
                OracleComp (SourceSpec KemSK) _) = _
            exact bind_congr fun answer => ih answer index _
        | _ => exact absurd selected (by simp [commandKind])
    · have shape : (simulateQ compiler ((Spec.query query : OracleComp Spec _) >>= next)).run memory =
          (compiler query).run memory >>= fun result =>
            (simulateQ compiler (next result.1)).run result.2 := by
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [shape, PqxdhDeploymentIdealCut.scan_bind_noAccept _ (noAccept query memory selected),
        PqxdhDeploymentIdealCut.scanCE_other query selected, simulateQ_bind, simulateQ_spec_query,
        StateT.run_bind, map_bind]
      exact bind_congr fun result => ih result.1 index result.2

end Generic

def logAccept (memory : CborAdmissionCompiler.Local) (raw : Pqxdh.Bytes) (answer : Option Nat) :
    CborAdmissionCompiler.Local :=
  { memory with copies := { memory.copies with
    log := PqxdhDeploymentCompile.logReply memory.copies.log (.accept raw) answer } }

/-- The raw registration adapter does not rewrite accept bytes or introduce a second attempt. -/
theorem accept_run (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (raw : Pqxdh.Bytes)
    (memory : CborAdmissionCompiler.Local) :
    (CborRawCompile.compileImpl setup wire parse (.inr (.accept raw))).run memory =
      ((SourceSpec KemSK).query (.inl (.inr (.accept raw))) : OracleComp (SourceSpec KemSK) (Option Nat)) >>= fun answer =>
        pure (answer, logAccept memory raw answer) := by
  simp only [CborRawCompile.compileImpl, CborSplitCompiler.compileImpl,
    CborAdmissionCompiler.compileImpl, CborAdmissionCompiler.liftExisting,
    PqxdhDeploymentCompile.compileImpl, PqxdhDeploymentCompile.forwardLogged,
    PqxdhDeploymentCompile.forward, StateT.run, map_bind, map_pure, id_eq, logAccept]
  rfl

/-- The existing fourteen-coordinate cost certificate excludes accept from every other command. -/
theorem no_accept (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (query : Spec.Domain) (memory : CborAdmissionCompiler.Local) (other : commandKind query ≠ 3) :
    ((CborRawCompile.compileImpl setup wire parse query).run memory).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = .inl 3) 0 := by
  have bound := CborRawCompile.step_bound setup wire parse (.inl 3) query memory
  have zero : PqxdhDeploymentCompileBudget.cost (.inl 3) (commandKind query) = 0 := by
    rcases query with coin | command
    · rfl
    · cases command <;> first | rfl | exact absurd rfl other
  simpa only [zero] using bound

/-- The complete public raw compiler and its local pin/assignment state commute with the same cut used by the KEM reduction. All original reply continuations and rejection attempts are retained. -/
theorem raw_compile_scan (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (work : OracleComp Spec X) (index : Nat) (memory : CborAdmissionCompiler.Local) :
    scan ((simulateQ (CborRawCompile.compileImpl setup wire parse) work).run memory) index =
      cut (CborRawCompile.compileImpl setup wire parse) logAccept <$>
        (simulateQ (CborRawCompile.compileImpl setup wire parse) (scanCE work index)).run memory :=
  compile_scan (CborRawCompile.compileImpl setup wire parse) logAccept
    (accept_run setup wire parse) (no_accept setup wire parse) work index memory

end BeaconcryptCore.Computational.CborRawCompileCut

/-- info: 'BeaconcryptCore.Computational.CborRawCompileCut.raw_compile_scan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompileCut.raw_compile_scan

-- Exact dependency observations for all public helper theorems.

/-- info: 'BeaconcryptCore.Computational.CborRawCompileCut.compile_scan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompileCut.compile_scan

/-- info: 'BeaconcryptCore.Computational.CborRawCompileCut.accept_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompileCut.accept_run

/-- info: 'BeaconcryptCore.Computational.CborRawCompileCut.no_accept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompileCut.no_accept
