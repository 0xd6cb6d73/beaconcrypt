-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalCore
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFamilyActual
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedProjection
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedObserved
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedNativeClient
import BeaconcryptCore.Computational.RegistrationNativeIdentityFreeStageTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFamily
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedAcceptCut
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedChosenGame
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxInitial
/-! The original complete journal and its final generated seed pool have one exact observed eager-family marginal under the original raw command allowance. The same-run unissued event is included in that family event without reconstructing private historical snapshots. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalMarginal
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



open RegistrationNativeIdentityUnissuedOriginalCore (Original Observation original project PoolEvent)
variable (initial : RegistrationNativeExperiment.Initial n KemSK source)
local notation "frontend" => RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation initial.created initial.credential
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "compiled" => RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
  initial.created.server.server.metadata.sender bounds mode (adversary initial.public)
local notation "observedTree" => RegistrationNativeIdentityUnissuedInitialized.tree setup checks wire route representation view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer source bounds mode adversary previous initial

/-- Original Respects bounds every actual generated row in the observed source journal; both signing and callback journals are derived erasures. -/
theorem tree_bound     (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget (adversary initial.public)) :
    (observedTree).IsQueryBoundP (RegistrationNativePlatformIdentityCtxEdCompilerBounds.Target .create) budget.create := by
  have bill := RegistrationNativeFullCompiler.compile_bound setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
    initial.created.server.server.metadata.sender bounds mode (adversary initial.public) budget bounded 1
  simp [Fin.sum_univ_succ,PqxdhDeploymentCompileSecrecy.wrapCost] at bill
  have plain := RegistrationNativePlatformIdentityCtxTypedEdBounds.program_create_bound setup checks wire route representation initial.created initial.credential
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (compiled) (budget.cap 1) bill
    (RegistrationNativeIdentityMainProfile.fromInitial initial,previous)
  have logged := RegistrationNativePlatformIdentityCtxSigningTrace.program_erasure (frontend) (compiled)
    ((RegistrationNativeIdentityMainProfile.fromInitial initial,previous),{})
  have observed := RegistrationNativeObservedStageTrace.erase id (RegistrationNativePlatformIdentityCtxSigningTrace.wrap (frontend))
    (compiled) (((RegistrationNativeIdentityMainProfile.fromInitial initial,previous),{}),[])
  have final := congrArg (fun distribution => Prod.map id Prod.fst <$> distribution) observed
  rw [Functor.map_map,logged] at final
  simp only [Prod.map_def,id_eq] at final
  have receipt : ((fun result => (result.1,result.2.1.1)) <$> observedTree).IsQueryBoundP
      (RegistrationNativePlatformIdentityCtxEdCompilerBounds.Target .create) budget.create := by
    rw [RegistrationNativeIdentityUnissuedInitialized.tree,final]
    exact plain
  exact (isQueryBoundP_map_iff _ _ _).mp receipt

/-- The complete reached source pool and the unchanged original observed journal are the marginal of one genuine reserved family. -/
theorem marginal     (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget (adversary initial.public)) :
    project source <$> original setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source bounds mode adversary previous initial =ᵈ
    RegistrationNativePlatformIdentityCtxFamily.project <$>
      RegistrationNativePlatformIdentityCtxFamily.run setup.joint (budget.create+1) (observedTree)
        (RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey]) := by
  rw [RegistrationNativeIdentityUnissuedOriginalCore.source_run]
  have cap := RegistrationNativePlatformIdentityCtxIndependentCreateBounds.program_bound (observedTree) budget.create
    (tree_bound setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source bounds mode adversary previous initial budget bounded)
    (RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey])
  exact RegistrationNativePlatformIdentityCtxFamily.source_marginal setup.joint (budget.create+1) _ _ (cap.mono (Nat.le_succ _))

def Unissued (budget : PqxdhDeploymentInterface.Budget) (result : Original n KemSK Platform Value source) : Prop :=
  ∃ attempt : RegistrationNativePlatformIdentityCtxCausalAttempt.Attempt setup.joint
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) budget result.2.2.2 result.2.2.1,
    RegistrationNativePlatformIdentityCtxFiniteCover.Unissued attempt

/-- The actual original causal Unissued event is bounded by the same eager-family field event, with source ownership and chronological log evidence derived internally. -/
theorem fixed_bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget (adversary initial.public)) :
    Pr{let result ← (original setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source bounds mode adversary previous initial)}[Unissued setup wire source budget result] ≤
    Pr{let result ← (RegistrationNativePlatformIdentityCtxFamily.run setup.joint (budget.create+1) observedTree
      (RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey]))}[
        RegistrationNativeIdentityUnissuedInitialized.Any setup source budget (some result)] := by
  have covered : Pr{let result ← (original setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source bounds mode adversary previous initial)}[Unissued setup wire source budget result] ≤
      Pr{let result ← (original setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        source bounds mode adversary previous initial)}[PoolEvent source setup.joint budget (project source result)] := by
    apply prEvent_mono_of_support
    rintro result supported ⟨attempt,unissued⟩
    exact RegistrationNativeIdentityUnissuedOriginalCore.covered setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source bounds mode adversary previous initial budget result supported attempt unissued
  have equality := (marginal setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source bounds mode adversary previous initial budget bounded).prEvent_eq (PoolEvent source setup.joint budget)
  simp only [prEvent_map] at equality
  refine covered.trans (equality.le.trans ?_)
  apply prEvent_mono_of_support
  intro result supported event
  exact RegistrationNativeIdentityUnissuedOriginalCore.family_covered setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source bounds mode adversary previous budget initial result supported event

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalMarginal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalMarginal.tree_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalMarginal.tree_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalMarginal.marginal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalMarginal.marginal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalMarginal.fixed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalMarginal.fixed_bound
