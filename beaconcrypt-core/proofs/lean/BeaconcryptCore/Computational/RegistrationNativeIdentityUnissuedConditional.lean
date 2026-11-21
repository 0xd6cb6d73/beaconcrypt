-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamilySecurity
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedInitialized
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedStartup
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixBounds
/-! Original raw Respects derives the literal native fixed-prefix ordinary weak-EUF bound, without a caller source-history or capacity conclusion. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedConditional
open RegistrationNativeIdentityTemplateProtocol (PublicSpec)
variable {Value : Type}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I}
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (CoreModels.core.result.Result Unit E)) (erased : beaconcrypt_core.commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

variable (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (previous : Platform)


/-- For any genuine initialized state, the unchanged original same-family field event is bounded by the literal ordinary client with all original source-create bills discharged from Respects. -/
theorem bound (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget (adversary initial.public))
    (target : Fin (budget.create+1)) (accept : Nat) (tag : Fin 3) (fallback : PqxdhJointIdentity.Forgery) :
    Pr{let result ← (RegistrationNativePlatformIdentityCtxFamily.run setup.joint (budget.create+1)
      (RegistrationNativeIdentityUnissuedInitialized.tree setup checks wire route representation view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer source bounds mode adversary previous initial)
      (RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey]))}[
        RegistrationNativeIdentityUnissuedEvents.At setup.joint (PqxdhJointIdentityFamily.familyPublic setup.joint result.1) target accept tag result.2.1.1] ≤
      Pr{let result ← (RegistrationNativeIdentityUnissuedChosenGame.familyGame setup.joint target
        (fun _keys => RegistrationNativeIdentityUnissuedStartup.fieldPrefix setup checks wire route representation view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer source bounds mode adversary previous initial accept tag) fallback)}[result=true] := by
  let callback := RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation initial.created initial.credential
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
  let compiled := RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
    initial.created.server.server.metadata.sender bounds mode (adversary initial.public)
  let before := (RegistrationNativeIdentityMainProfile.fromInitial initial,previous)
  let physical : RegistrationNativePlatformCtxBackend.State :=
    (RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey])
  have bill := RegistrationNativeFullCompiler.compile_bound setup.source.crypto
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) initial.created.server.server.metadata.sender bounds mode (adversary initial.public) budget bounded 1
  simp [Fin.sum_univ_succ,PqxdhDeploymentCompileSecrecy.wrapCost] at bill
  have cutBill := RegistrationNativeIdentityUnissuedAcceptCut.query_bound accept 0 _ (budget.cap 1) compiled bill
  have free := RegistrationNativePlatformIdentityCtxTypedEdBounds.program_create_bound setup checks wire route representation initial.created initial.credential
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ (budget.cap 1) cutBill before
  have logged : ((simulateQ (RegistrationNativePlatformIdentityCtxSigningTrace.wrap callback)
      (RegistrationNativeIdentityUnissuedAcceptCut.stop accept compiled 0)).run (before,{})).IsQueryBoundP
      (RegistrationNativePlatformIdentityCtxEdCompilerBounds.Target .create) budget.create := by
    have mapped : (Prod.map id Prod.fst <$> (simulateQ (RegistrationNativePlatformIdentityCtxSigningTrace.wrap callback)
        (RegistrationNativeIdentityUnissuedAcceptCut.stop accept compiled 0)).run (before,{})).IsQueryBoundP
        (RegistrationNativePlatformIdentityCtxEdCompilerBounds.Target .create) budget.create := by
      rw [RegistrationNativePlatformIdentityCtxSigningTrace.program_erasure]
      exact free
    exact (isQueryBoundP_map_iff _ _ _).mp mapped
  have independent := RegistrationNativePlatformIdentityCtxIndependentCreateBounds.program_bound _ budget.create logged physical
  exact RegistrationNativeIdentityUnissuedFamilySecurity.bound setup.joint target callback compiled before physical accept tag fallback
    (independent.mono (Nat.le_succ _))

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedConditional

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedConditional.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedConditional.bound
