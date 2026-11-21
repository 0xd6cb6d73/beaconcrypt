-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeFullCompiler
import BeaconcryptCore.Computational.FinitePartitionTotal

/-! The unchanged raw native resource contract gives an explicit total typed-query allowance. Every typed request belongs to one of the twelve literal native classes. Summing the existing per-class compiler bounds counts every possible request once, retaining every reply path and the original test/fresh-message compilation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCoinCompilerBounds
attribute [local irreducible] RegistrationNativeFullCompiler.compile
open PqxdhDeploymentInterface (FreshBounds Budget Mode)
variable {Value : Type}

def caps (bounds : FreshBounds) (budget : Budget) (kind : Fin 12) : Nat :=
  ∑ full : Fin 14, PqxdhDeploymentCompileSecrecy.wrapCost bounds kind full * budget.cap full

def total (bounds : FreshBounds) (budget : Budget) : Nat :=
  ∑ kind : Fin 12, caps bounds budget kind

/-- The actual complete raw compiler supplies a finite total typed-query cap directly from the original adversary budget. -/
theorem compile (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKid : U64)
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (bounded : RegistrationNativeInterface.Respects budget work) :
    (RegistrationNativeFullCompiler.compile crypto wire serverKid bounds mode work).IsTotalQueryBound (total bounds budget) := by
  simpa only [FinitePartitionQueryBounds.bill, Nat.one_mul, total] using
    FinitePartitionTotal.bound RegistrationNativeRawAdapter.kind
      (RegistrationNativeFullCompiler.compile crypto wire serverKid bounds mode work) (caps bounds budget)
      (fun kind => RegistrationNativeFullCompiler.compile_bound crypto wire serverKid bounds mode work budget bounded kind)
end BeaconcryptCore.Computational.RegistrationNativeMldsaCoinCompilerBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinCompilerBounds.compile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinCompilerBounds.compile
