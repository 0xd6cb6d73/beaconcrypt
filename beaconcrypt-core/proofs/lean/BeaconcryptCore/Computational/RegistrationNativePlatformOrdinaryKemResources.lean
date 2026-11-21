-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemProfile
/-! The actual ordinary runtime profile retains the original private KEM budgets even when record writers fail. All four dynamic record routes lift ordinary computations and cost zero private births, encapsulations and decapsulations. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept.authenticate
  BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.pin
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemResources
open BeaconcryptCore.Refinement
open RegistrationNativeKemResourceFootprint (Kind)
open RegistrationNativeKemResourceCaps (Counted)
open RegistrationNativePlatformKemHandlerResources (Bounded apiClass allowance lift_free ordinary_free wrap_sum)
variable {I KemSK Platform A : Type} {n : Nat} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [primitive : AdapterSealPrimitive.Operations]
variable {E : Type}
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

theorem handler (kind : Kind) (query : RegistrationNativeRawAdapter.TypedSpec.Domain) :
    Bounded kind (if RegistrationNativeRawAdapter.kind query = apiClass kind then 1 else 0)
      (RegistrationNativePlatformOrdinaryKemHandler.handler (n := n) setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query) := by
  cases query with
  | inl coin =>
      exact RegistrationNativePlatformKemHandlerResources.handler setup checks
        (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer kind (.inl coin)
  | inr command =>
      cases command <;> first
        | cases kind <;> exact lift_free _ _
        | exact RegistrationNativePlatformKemHandlerResources.handler setup checks
            (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created credential view failure allocation
            reserveRegistration reservePeer erased helper writer kind _

theorem typed (kind : Kind) (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A) (cap : Nat)
    (bounded : work.IsQueryBoundP (fun query => RegistrationNativeRawAdapter.kind query = apiClass kind) cap) :
    Bounded kind cap (simulateQ
      (RegistrationNativePlatformOrdinaryKemHandler.handler (n := n) setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer) work) :=
  RegistrationNativePlatformQueryBounds.simulate_bound _ (Counted kind) _
    (handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer kind)
    work cap bounded

theorem compiled (kind : Kind) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) :
    Bounded kind (allowance kind budget) (simulateQ
      (RegistrationNativePlatformOrdinaryKemHandler.handler (n := n) setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer)
      (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) created.server.server.metadata.sender bounds mode work)) := by
  apply typed setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
  simpa only [wrap_sum] using RegistrationNativeFullCompiler.compile_bound setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
    created.server.server.metadata.sender bounds mode work budget bounded (apiClass kind)

theorem initialized (kind : Kind) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput)) (previous : Platform) :
    ((RegistrationNativePlatformOrdinaryKemProfile.program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary).run previous).IsQueryBoundP (Counted kind) (allowance kind budget) := by
  unfold RegistrationNativePlatformOrdinaryKemProfile.program
  rw [StateT.run_bind, StateT.run_lift]
  rw [← Nat.zero_add (allowance kind budget)]
  apply isQueryBoundP_bind (n := 0) (m := allowance kind budget)
  · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using ordinary_free (KemSK := KemSK) kind
      (RegistrationNativePlatformKemCountedProfile.start (n := n) setup source ensureInit identityIndex serverKeyId)
  · intro initialized _
    cases initialized.1 with
    | none => exact isQueryBoundP_pure _ _ _
    | some initial =>
        simp only [bind_pure_comp, StateT.run_map, isQueryBoundP_map_iff]
        exact compiled setup checks wire route representation initial.created initial.credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer kind bounds mode (adversary initial.public) budget
          (bounded initial.public) initial.state initialized.2

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemResources

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemResources.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemResources.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemResources.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemResources.typed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemResources.compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemResources.compiled

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemResources.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemResources.initialized
