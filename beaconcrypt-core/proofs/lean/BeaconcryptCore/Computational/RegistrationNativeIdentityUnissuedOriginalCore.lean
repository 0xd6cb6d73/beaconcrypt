-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedInitialized
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedProjection
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedObserved
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedNativeClient
import BeaconcryptCore.Computational.RegistrationNativeIdentityFreeStageTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFamily
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedAcceptCut
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedChosenGame
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxInitial
/-! The original same-run Unissued field is covered by a seed actually owned by a final owner and its own earlier signing log. Only private call snapshots are projected; the complete live source/platform state remains. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalCore
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


open RegistrationNativePlatformIdentityCtxKeyJournal (Whole owners drop Good)
open RegistrationNativeRawAdapter (TypedSpec)
abbrev Original (n : Nat) (KemSK Platform Value : Type) (source : RegistrationNativeMldsa.Source) :=
  Value × (RegistrationNativeLedger.State × (Whole n KemSK Platform source ×
    List (RegistrationNativeStageTrace.Call TypedSpec (Whole n KemSK Platform source))))
abbrev Observation (n : Nat) (KemSK Platform Value : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativeIdentityUnissuedInitialized.Observed n KemSK Platform Value source × RegistrationNativePlatformIdentityCtxSource.State

def project (result : Original n KemSK Platform Value source) : Observation n KemSK Platform Value source :=
  (((result.1,result.2.1),(result.2.2.1.1,result.2.2.2.map (RegistrationNativeObservedStageTrace.mapCall Prod.fst))),result.2.2.1.2)

def PoolEvent (joint : PqxdhJointIdentity.Primitives) (budget : PqxdhDeploymentInterface.Budget)
    (result : Observation n KemSK Platform Value source) : Prop :=
  ∃ handle seed, result.2.1.seeds[handle]?=some seed ∧ ∃ accept : Fin budget.accept, ∃ tag : Fin 3,
    RegistrationNativeIdentityUnissuedEvents.At joint (fun _ : Fin (handle+1) => joint.publicKeys seed)
      ⟨handle,Nat.lt_succ_self handle⟩ accept.val tag result.1

noncomputable def original (initial : RegistrationNativeExperiment.Initial n KemSK source) :
    ProbComp (Original n KemSK Platform Value source) :=
  RegistrationNativeFullCompiler.run setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
    initial.created.server.server.metadata.sender bounds
    (RegistrationNativeStageTrace.handler (RegistrationNativePlatformIdentityCtxSigningSource.typedHandler setup.joint
      (RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation initial.created initial.credential
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer))) mode (adversary initial.public)
    ((((RegistrationNativeIdentityMainProfile.fromInitial initial,previous),{}),
      (PqxdhDynamicIdentityPool.initialState,(RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey]))),[])

/-- Final generated ownership and actual chronological prefix coherence derive the original Unissued field's stored seed and exact before-log event. -/
theorem covered (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (budget : PqxdhDeploymentInterface.Budget) (result : Original n KemSK Platform Value source)
    (supported : result ∈ support (original setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source bounds mode adversary previous initial))
    (attempt : RegistrationNativePlatformIdentityCtxCausalAttempt.Attempt setup.joint (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) budget result.2.2.2 result.2.2.1)
    (unissued : RegistrationNativePlatformIdentityCtxFiniteCover.Unissued attempt) :
    PoolEvent source setup.joint budget (project source result) := by
  let frontend := RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation initial.created initial.credential
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
  let actual := RegistrationNativePlatformIdentityCtxSigningSource.typedHandler setup.joint frontend
  have path := RegistrationNativeFullRegistrationJournal.path setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
    initial.created.server.server.metadata.sender bounds actual mode (adversary initial.public) _ result supported
  have good : Good setup.joint result.2.2.1 :=
    RegistrationNativePlatformIdentityCtxKeyJournal.path_good setup checks wire route representation initial.created initial.credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer path ⟨RegistrationNativePlatformIdentityCtxInitial.initial_owned setup.joint initial previous _,by exact List.nodup_nil⟩
  obtain ⟨seed,found,publicKey⟩ := good.1 attempt.finalOwner (List.mem_of_getElem? attempt.finalFound)
  have member : attempt.call ∈ result.2.2.2 := by
    exact (congrArg (fun calls => attempt.call ∈ calls) attempt.split).mpr (by simp only [List.mem_append,List.mem_cons,true_or,or_true])
  obtain ⟨_leading,_trailing,_same,beforePath,_called,_following⟩ := path.member attempt.call member
  have coherent := RegistrationNativeIdentityUnissuedObserved.coherent_path setup.joint frontend beforePath rfl
  obtain ⟨tag,captured⟩ := RegistrationNativeIdentityUnissuedProjection.attempt setup.joint _ budget _ _ attempt unissued
    (fun _ : Fin (attempt.finalOwner.identity.handle+1) => setup.joint.publicKeys seed)
    ⟨attempt.finalOwner.identity.handle,Nat.lt_succ_self _⟩ rfl (congrArg PqxdhJointIdentity.PublicIdentity.ed25519 publicKey.symm) coherent
  exact ⟨attempt.finalOwner.identity.handle,seed,found,RegistrationNativePlatformIdentityCtxFiniteCover.acceptanceOrdinal attempt,tag,captured⟩

/-- Projecting only private call snapshots gives the exact free observed source journal while retaining its complete live backend. -/
theorem source_run (initial : RegistrationNativeExperiment.Initial n KemSK source) :
    project source <$> original setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source bounds mode adversary previous initial =
    (simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation setup.joint)
      (RegistrationNativeIdentityUnissuedInitialized.tree setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        source bounds mode adversary previous initial)).run
      (PqxdhDynamicIdentityPool.initialState,(RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey])) := by
  unfold original
  rw [RegistrationNativeFullCompiler.compile_run,Functor.map_map]
  have law := RegistrationNativeIdentityFreeStageTrace.full_program
    (RegistrationNativePlatformIdentityCtxSigningTrace.wrap
      (RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation initial.created initial.credential
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer))
    (RegistrationNativePlatformIdentityCtxSource.implementation setup.joint)
    (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      initial.created.server.server.metadata.sender bounds mode (adversary initial.public))
    ((((RegistrationNativeIdentityMainProfile.fromInitial initial,previous),{}),
      (PqxdhDynamicIdentityPool.initialState,(RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey]))),[])
  rw [QueryImpl.Stateful.simulateQ_link_run] at law
  have mapped := congrArg (fun distribution => (fun result => ((result.1,result.2.1),result.2.2)) <$> distribution) law
  simpa only [RegistrationNativePlatformIdentityCtxSigningSource.typedHandler,
    RegistrationNativeIdentityUnissuedInitialized.tree,project,Functor.map_map,RegistrationNativeIdentityFreeStageTrace.projectFull,
    List.map_nil,Prod.map_def,id_eq,Prod.mk.eta,id_map',QueryImpl.Stateful.Frame.prod,PFunctor.Lens.State.fst_put,PFunctor.Lens.State.snd_put] using mapped

/-- A seed actually present in the final created pool is exactly its same reserved family index, even when it was created after the accepted attempt. -/
theorem family_covered (budget : PqxdhDeploymentInterface.Budget)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (result : RegistrationNativeIdentityUnissuedInitialized.Result (budget.create+1) n KemSK Platform Value source)
    (supported : result ∈ support (RegistrationNativePlatformIdentityCtxFamily.run setup.joint (budget.create+1)
      (RegistrationNativeIdentityUnissuedInitialized.tree setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        source bounds mode adversary previous initial)
      (RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey])))
    (covered : PoolEvent source setup.joint budget (RegistrationNativePlatformIdentityCtxFamily.project result)) :
    RegistrationNativeIdentityUnissuedInitialized.Any setup source budget (some result) := by
  obtain ⟨handle,seed,found,accept,tag,event⟩ := covered
  have capacity := RegistrationNativePlatformIdentityCtxFamily.capacity setup.joint (budget.create+1) _ _ result supported
  have within := (List.getElem?_eq_some_iff.mp found).1
  have created : handle < result.2.2.1.created := by
    simpa only [RegistrationNativePlatformIdentityCtxFamily.project,PqxdhDynamicIdentityRouting.sourceState_length _ _ capacity] using within
  have valid : handle < budget.create+1 := lt_of_lt_of_le created capacity
  have lookup := PqxdhDynamicIdentityRouting.sourceState_lookup result.1 result.2.2.1 handle created valid
  change (PqxdhDynamicIdentityRouting.sourceState result.1 result.2.2.1).seeds[handle]?=some seed at found
  rw [lookup] at found
  have seedEq := Option.some.inj found
  refine ⟨⟨handle,valid⟩,accept,tag,?_⟩
  simpa only [RegistrationNativeIdentityUnissuedInitialized.At,Option.elim_some,
    RegistrationNativeIdentityUnissuedEvents.At,RegistrationNativeIdentityUnissuedCutEvent.At,RegistrationNativeIdentityUnissuedEvents.Field,
    PqxdhJointIdentityFamily.familyPublic,seedEq,RegistrationNativePlatformIdentityCtxFamily.project] using event

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalCore

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalCore.covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalCore.covered

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalCore.source_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalCore.source_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalCore.family_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalCore.family_covered
