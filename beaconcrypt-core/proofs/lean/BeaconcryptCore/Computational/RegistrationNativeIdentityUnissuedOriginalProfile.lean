-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalInitialized
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxProfile
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalMarginal
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedStartup
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedConditional
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedAcceptCut
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedChosenGame
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxInitial
/-! Erasing only analysis journals restores the literal initialized ordinary native profile, with complete ledger, native state and persistent platform observation retained. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalProfile
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




open RegistrationNativeIdentityUnissuedOriginalCore (Original original)
open RegistrationNativePlatformIdentityCtxKeyJournal (drop)
open RegistrationNativePlatformIdentityCtxLifecycle (native)

def observe (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool)
    (result : Option (Original n KemSK Platform Value source)) : Bool × Platform :=
  match result with
  | none => (false,previous)
  | some result =>
      (event (result.1,(result.2.1,(native (drop result.2.2.1)).1)),(native (drop result.2.2.1)).2)

/-- Removing only callback and signing journals retains the exact complete source/native/platform body. -/
theorem body_source (initial : RegistrationNativeExperiment.Initial n KemSK source) :
    (fun result => ((result.1,result.2.1),drop result.2.2.1)) <$>
      original setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        source bounds mode adversary previous initial =
    (RegistrationNativePlatformIdentityCtxMain.interpret setup.joint
      (RegistrationNativePlatformIdentityCtxFull.run setup checks wire route representation initial.created initial.credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode (adversary initial.public))).run
      (RegistrationNativePlatformIdentityCtxInitial.fromInitial initial previous PqxdhDynamicIdentityPool.initialState) := by
  let frontend := RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation initial.created initial.credential
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
  let compiled := RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
    initial.created.server.server.metadata.sender bounds mode (adversary initial.public)
  let before := (RegistrationNativeIdentityMainProfile.fromInitial initial,previous)
  let physical : RegistrationNativePlatformIdentityCtxSource.State :=
    (PqxdhDynamicIdentityPool.initialState,(RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey]))
  have observed := RegistrationNativeObservedStageTrace.erase id (RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend) compiled ((before,{}),[])
  have logged := RegistrationNativePlatformIdentityCtxSigningTrace.program_erasure frontend compiled (before,{})
  have forgotten := congrArg (fun distribution => Prod.map id Prod.fst <$> distribution) observed
  rw [Functor.map_map,logged] at forgotten
  have closed := congrArg (fun tree => (simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation setup.joint) tree).run physical) forgotten
  have mapped := congrArg (fun distribution => (fun result => (result.1.1,(result.1.2,result.2))) <$> distribution) closed
  have actual := congrArg (fun distribution => (fun result => (result.1.1,(result.1.2.1.1,result.2))) <$> distribution)
    (RegistrationNativeIdentityUnissuedOriginalCore.source_run setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source bounds mode adversary previous initial)
  simp only [simulateQ_map,StateT.run_map,Functor.map_map,Prod.map_def,id_eq] at mapped
  have combined := actual.trans (by simpa only [RegistrationNativeIdentityUnissuedOriginalCore.project,RegistrationNativeIdentityUnissuedInitialized.tree,
    RegistrationNativePlatformIdentityCtxMain.interpret,RegistrationNativePlatformIdentityCtxFull.run,RegistrationNativePlatformIdentityCtxInitial.fromInitial,
    drop,frontend,compiled,before,physical,Functor.map_map,Prod.map_def,id_eq] using mapped)
  simpa only [RegistrationNativeIdentityUnissuedOriginalCore.project,drop,Functor.map_map,
    RegistrationNativePlatformIdentityCtxMain.interpret,RegistrationNativePlatformIdentityCtxFull.run,
    RegistrationNativePlatformIdentityCtxInitial.fromInitial,StateT.run,frontend,compiled,before,physical] using combined

/-- The unchanged actual initialized ordinary profile is obtained by erasing only analysis journals, retaining any original native-state event jointly with its reached platform state. -/
theorem profile_source (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool) :
    observe source previous event <$>
      RegistrationNativeIdentityUnissuedOriginalInitialized.game (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        source ensureInit identityIndex serverKeyId bounds mode adversary previous =
    (RegistrationNativePlatformOrdinaryExperiment.profile setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary event).run previous := by
  rw [←RegistrationNativePlatformIdentityCtxProfile.profile_source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds mode adversary event PqxdhDynamicIdentityPool.initialState previous]
  unfold RegistrationNativeIdentityUnissuedOriginalInitialized.game RegistrationNativePlatformIdentityCtxProfile.profile
  simp only [map_bind,StateT.run]
  apply bind_congr
  intro initialized
  cases initialized with
  | none => simp only [map_pure,observe]
  | some initial =>
      have law := congrArg (fun distribution => (fun result => (event (result.1.1,(result.1.2,(native result.2).1)),(native result.2).2)) <$> distribution)
        (body_source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
          source bounds mode adversary previous initial)
      simpa only [Functor.map_map,observe,StateT.run] using law

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalProfile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalProfile.body_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalProfile.body_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalProfile.profile_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalProfile.profile_source
