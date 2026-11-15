-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterServerConstructorInitialized
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterServerConstructorRetained
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperState
open BeaconcryptCore.Computational
variable {n : Nat} {I KemSK R : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable [PublicWrapperPlatform.Material] [PublicWrapperPlatform.Platform]
variable [AdapterInitEdPrimitive.Operations]
variable [LocalOperations (RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp))]
variable [CryptoOperations (RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp))]
variable [ChildOperations (RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp))]

omit [ChildOperations (RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp))] in
theorem returned (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (view : MaterialView mlSource KemSK) (identityIndex : Nat) (identifier : U64)
    (self : beaconcrypt_public_wrapper.server.Server) (rng : R)
    (before after : PqxdhRecordLiftWorld.State n)
    (ready : AdapterServerConstructorInitialized.Ready n KemSK R mlSource)
    (supported : (some ready,after)∈support ((AdapterServerConstructorInitialized.finish setup view identityIndex identifier self rng).run before)) :
    ready.stored=self ∧ ready.rng=rng := by
  simp only [AdapterServerConstructorInitialized.finish,StateT.run,mem_support_bind_iff] at supported
  obtain ⟨installed,_installed,pinned,_pinned,supported⟩:=supported
  split at supported
  · simp only [mem_support_pure_iff,Prod.mk.injEq,Option.some.injEq] at supported
    obtain ⟨equal,_after⟩:=supported
    subst ready
    exact ⟨rfl,rfl⟩
  · simp only [mem_support_pure_iff,Prod.mk.injEq,reduceCtorEq,false_and] at supported
end BeaconcryptCore.Refinement.AdapterServerConstructorRetained

/-- info: 'BeaconcryptCore.Refinement.AdapterServerConstructorRetained.returned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterServerConstructorRetained.returned
