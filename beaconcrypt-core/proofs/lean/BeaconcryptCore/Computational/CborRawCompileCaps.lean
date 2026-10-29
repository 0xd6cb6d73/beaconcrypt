-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawCompileSecrecy
import BeaconcryptCore.Computational.PqxdhDeploymentCompileCaps
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills

/-! The actual raw compiler meets the existing closed source14 caps and the certified KEM reduction's concrete bills. Admission checks and public representation changes introduce no extra primitive or kernel queries. This resource result makes no event-security claim. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawCompileCaps
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Budget FreshBounds Mode ModeSpec)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
open PqxdhDeploymentCompileCaps (transported)
open CborRawCompileSecrecy (compileFull)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

/-- All fourteen closed source caps follow from the raw compiler's complete secrecy-layer certificate. -/
theorem certified (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (kind : SourceKind) :
    (compileFull setup wire parse bounds mode adversary).IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = kind) (transported bounds budget kind) := by
  rw [← PqxdhDeploymentCompileCaps.transported_eq]
  exact CborRawCompileSecrecy.compile_full_bound setup wire parse bounds mode adversary budget respects kind

/-- Tagging any original accept ordinal preserves the same source bills, including rejected attempts. -/
theorem tag_certified (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (index : Nat) (kind : SourceKind) :
    (PqxdhRegistrationJointAcceptCutTag.tag (compileFull setup wire parse bounds mode adversary) index).IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = kind) (transported bounds budget kind) :=
  PqxdhRegistrationJointAcceptCutTag.tag_bound _ index _ _
    (certified setup wire parse bounds mode adversary budget respects kind)

/-- The proof-carrying one-key KEM adversary for the actual raw compiled work has the original concrete prechallenge and postchallenge allowances. Every decision here reads the actual raw compiler result; no event-correspondence premise is supplied. -/
theorem kem_bills (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget) (respects : budget.Respects adversary)
    (decision : ((X × PqxdhDeploymentSecrecy.Ledger) × CborAdmissionCompiler.Local) → Bool)
    (runtime : A) (selected : Fin budget.capacity) (index : Nat) :
    (PqxdhRegistrationJointKemRawCertified.adversary setup (CborRawCompile.sourceCodec wire parse) checks
      ensureInit none decision (compileFull setup wire parse bounds mode adversary) runtime budget.create
      selected index).MakesAtMostQueries
      ((qInit + 32) + (caps.keygenCost * budget.create + PqxdhRegistrationJointKemPostBills.uniformCap caps
        budget.create budget.finish (PqxdhRegistrationJointOpenUniform.total caps (transported bounds budget))
        budget.accept))
      (caps.decapsBase * budget.finish) budget.finish
      (PqxdhRegistrationJointKemPostBills.uniformCap caps budget.create budget.finish
        (PqxdhRegistrationJointOpenUniform.total caps (transported bounds budget)) budget.accept)
      (caps.decapsBase * budget.finish) budget.finish :=
  PqxdhRegistrationJointKemRawBills.adversary_bound setup (CborRawCompile.sourceCodec wire parse) checks
    caps bounded ensureInit qInit initBound none decision (compileFull setup wire parse bounds mode adversary)
    (transported bounds budget) (certified setup wire parse bounds mode adversary budget respects)
    runtime budget.create selected index

end BeaconcryptCore.Computational.CborRawCompileCaps

/-- info: 'BeaconcryptCore.Computational.CborRawCompileCaps.certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompileCaps.certified

/-- info: 'BeaconcryptCore.Computational.CborRawCompileCaps.kem_bills' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompileCaps.kem_bills

-- Exact dependency observations for all public helper theorems.

/-- info: 'BeaconcryptCore.Computational.CborRawCompileCaps.tag_certified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompileCaps.tag_certified
