-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedAcceptCut
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxIndependentCreateBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFamily
/-! Every fixed public accept prefix retains the original raw create and signing bills; reification therefore obtains one exact reserved-family marginal without a source-capacity premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixBounds
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxEdCompilerBounds (Target)
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable {E : Type}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "callback" => RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer


variable (accept : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform)
local notation "compiled" => RegistrationNativeFullCompiler.compile setup.source.crypto
  (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds mode work
local notation "prefixWork" => RegistrationNativeIdentityUnissuedPacketClient.visit accept callback compiled before 0

include bounded in
/-- Every actually generated row before the chosen parsed accept is charged to the original public create allowance. -/
theorem creates : (prefixWork).IsQueryBoundP (Target .create) budget.create := by
  rw [RegistrationNativeIdentityUnissuedAcceptCut.packet_source,isQueryBoundP_map_iff]
  have bill := RegistrationNativeFullCompiler.compile_bound setup.source.crypto
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds mode work budget bounded 1
  simp [Fin.sum_univ_succ,PqxdhDeploymentCompileSecrecy.wrapCost] at bill
  exact RegistrationNativePlatformIdentityCtxTypedEdBounds.program_create_bound setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer _ (budget.cap 1)
    (RegistrationNativeIdentityUnissuedAcceptCut.query_bound accept 0 _ (budget.cap 1) compiled bill) before

include bounded in
/-- Repeated and failed earlier bundle signatures retain their complete three-per-attempt bill in this same actual prefix. -/
theorem signs : (prefixWork).IsQueryBoundP (Target .sign) (3*budget.bundle) := by
  rw [RegistrationNativeIdentityUnissuedAcceptCut.packet_source,isQueryBoundP_map_iff]
  have bill := RegistrationNativeFullCompiler.compile_bound setup.source.crypto
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds mode work budget bounded 2
  simp [Fin.sum_univ_succ,PqxdhDeploymentCompileSecrecy.wrapCost] at bill
  exact RegistrationNativePlatformIdentityCtxTypedEdBounds.program_sign_bound setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer _ (budget.cap 2)
    (RegistrationNativeIdentityUnissuedAcceptCut.query_bound accept 0 _ (budget.cap 2) compiled bill) before

include bounded in
/-- The actual stopped source prefix has one reserved qCreate+1 family marginal, retaining its same pool, physical cache/journal and returned packet. Capacity is derived from the original command budget. -/
theorem source_marginal (physical : RegistrationNativePlatformCtxBackend.State) :
    EvalDistEq ((simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation setup.joint) prefixWork).run
      (PqxdhDynamicIdentityPool.initialState,physical))
      (RegistrationNativePlatformIdentityCtxFamily.project <$>
        RegistrationNativePlatformIdentityCtxFamily.run setup.joint (budget.create+1) prefixWork physical) := by
  have cap := RegistrationNativePlatformIdentityCtxIndependentCreateBounds.program_bound prefixWork budget.create
    (creates setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      accept serverKeyId bounds mode work budget bounded before) physical
  exact RegistrationNativePlatformIdentityCtxFamily.source_marginal setup.joint (budget.create+1) prefixWork physical
    (cap.mono (Nat.le_succ _))

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixBounds.creates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixBounds.creates

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixBounds.signs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixBounds.signs

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixBounds.source_marginal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixBounds.source_marginal
