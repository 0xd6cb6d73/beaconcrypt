-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildLoggedPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuild
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceEvents
/-! The independent source Builder retains actual operation observations and its original one-use token move. Missing, consumed and conversion-refused calls execute the same source store transitions. Removing only the source log yields the original complete physical source operation on every outcome. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildLoggedActualSource
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformPublicAdapterSourceEvents (Event State Outcome outcome store)
open RegistrationNativePlatformPublicAdapterStore (Store)
open RegistrationNativePlatformSdkReification (Backend)
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [primitive :AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {n :Nat} {I KemSK P E R Reader Response :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
local notation "Base"=>StateT P ProbComp
local notation "Reply"=>Option PqxdhServerRegistrationPublication.Response

local notation "SourceM"=>StateT (RegistrationNativePlatformCutJournal.State (Backend n KemSK×List (Event n KemSK R P))) Base

private def assemble {A :Type} (log :List (Event n KemSK R P))
    (result :RegistrationNativePlatformPublicAdapterPhysicalOrdinary.Raw (n:=n) (KemSK:=KemSK) (R:=R) (Platform:=P) A) :Outcome n KemSK R P A :=
  (Prod.map id RegistrationNativePlatformPublicAdapterSourceRuntime.objects <$>result.1,(result.2.1,(result.2.2,log)))

noncomputable def active
    (coins :QueryImpl unifSpec Base) (setup :PqxdhServerAuthExperiment.Setup base KemSK)
    (codec :PqxdhServerAuthExperiment.Codec Reader Response) (keyView :RegistrationNativePlatformSourceSeal.KeyView)
    (failure :primitive.Error) (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (view :AdapterPublicWrapperState.MaterialView source KemSK) (views :AdapterPublicWrapperStorage.Views)
    (originalLocal :LocalOperations (RustT Base))
    (previousCrypto :CryptoOperations (RustT SourceM)) (previous :ChildOperations (RustT SourceM))
    (original :ContainerOperations (RustT Base))
    (token :beaconcrypt_public_wrapper.server.RegistrationOutput) (data :core.option.Option (Slice U8))
    (before :State n KemSK R P) :ProbComp (Outcome n KemSK R P Reply) :=
  (fun result=>assemble result.1.2.1.2
    (RegistrationNativePlatformPublicAdapterBuildPhysical.finish view views (store before)
      (result.1.1,(result.1.2.1.1,result.2)))) <$>
    ((RegistrationNativePlatformPublicAdapterBuildObservedProgram.program Event.stage coins setup codec keyView failure allocation helper erased
      (RegistrationNativeMldsa.owned source (view.mldsa (platform.arcView before.server.identity).mldsa_identity))
      (fun _=>pure .None) view originalLocal previousCrypto previous writer original before.server token data).run
      ((before.backend.1,before.backend.2.2),none)).run before.backend.2.1

noncomputable def run
    (coins :QueryImpl unifSpec Base) (setup :PqxdhServerAuthExperiment.Setup base KemSK)
    (codec :PqxdhServerAuthExperiment.Codec Reader Response) (keyView :RegistrationNativePlatformSourceSeal.KeyView)
    (failure :primitive.Error) (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (view :AdapterPublicWrapperState.MaterialView source KemSK) (views :AdapterPublicWrapperStorage.Views)
    (originalLocal :LocalOperations (RustT Base))
    (previousCrypto :CryptoOperations (RustT SourceM)) (previous :ChildOperations (RustT SourceM))
    (original :ContainerOperations (RustT Base)) (handle :Nat) (payload :Option Pqxdh.Bytes)
    (before :State n KemSK R P) :ProbComp (Outcome n KemSK R P Reply) :=
  match before.tokens handle with
  | none=>pure (.ok (none,RegistrationNativePlatformPublicAdapterSourceRuntime.objects before),before.backend)
  | some token=>
    let moved:=RegistrationNativePlatformPublicAdapterStore.move before handle
    match RegistrationNativeRawAdapter.application payload with
    | none=>pure (.ok (none,RegistrationNativePlatformPublicAdapterSourceRuntime.objects moved),moved.backend)
    | some app=>active coins setup codec keyView failure allocation helper erased writer view views originalLocal previousCrypto previous original token (.Some app) moved

theorem active_source
    (coins :QueryImpl unifSpec Base) (setup :PqxdhServerAuthExperiment.Setup base KemSK)
    (codec :PqxdhServerAuthExperiment.Codec Reader Response) (keyView :RegistrationNativePlatformSourceSeal.KeyView)
    (failure :primitive.Error) (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (view :AdapterPublicWrapperState.MaterialView source KemSK) (views :AdapterPublicWrapperStorage.Views)
    (originalLocal :LocalOperations (RustT Base))
    (previousCrypto :CryptoOperations (RustT SourceM)) (previous :ChildOperations (RustT SourceM))
    (original :ContainerOperations (RustT Base))
    (token :beaconcrypt_public_wrapper.server.RegistrationOutput) (data :core.option.Option (Slice U8))
    (before :State n KemSK R P) :RegistrationNativePlatformPublicAdapterBuildLoggedPhysical.active coins setup codec keyView failure allocation helper erased writer view views original token data before=
      active coins setup codec keyView failure allocation helper erased writer view views originalLocal previousCrypto previous original token data before :=by
  let actualSign:=RegistrationNativeMldsa.owned source (view.mldsa (platform.arcView before.server.identity).mldsa_identity)
  have same:=congrArg (fun computation=>computation.run before.backend.2.1)
    (RegistrationNativePlatformPublicAdapterBuildObservedProgram.program_source Event.stage coins setup codec keyView failure allocation helper erased
      actualSign (fun _=>pure .None) view originalLocal previousCrypto previous writer original
      before.server token data ((before.backend.1,before.backend.2.2),none))
  let observe (result :((RustM AdapterPublicServerBuildBody.Reply×(Backend n KemSK×List (Event n KemSK R P)))×P)) :=
    assemble result.1.2.2 (RegistrationNativePlatformPublicAdapterBuildPhysical.finish view views (store before)
      (result.1.1,(result.1.2.1,result.2)))
  have mapped:=congrArg (fun computation=>observe <$>computation) same
  simp only [StateT.run_map,Functor.map_map,Prod.map,id_eq,observe,actualSign] at mapped
  convert mapped.symm using 1 <;> rfl

theorem run_source
    (coins :QueryImpl unifSpec Base) (setup :PqxdhServerAuthExperiment.Setup base KemSK)
    (codec :PqxdhServerAuthExperiment.Codec Reader Response) (keyView :RegistrationNativePlatformSourceSeal.KeyView)
    (failure :primitive.Error) (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (view :AdapterPublicWrapperState.MaterialView source KemSK) (views :AdapterPublicWrapperStorage.Views)
    (originalLocal :LocalOperations (RustT Base))
    (previousCrypto :CryptoOperations (RustT SourceM)) (previous :ChildOperations (RustT SourceM))
    (original :ContainerOperations (RustT Base))
    (handle :Nat) (payload :Option Pqxdh.Bytes) (before :State n KemSK R P) :
    RegistrationNativePlatformPublicAdapterBuildLoggedPhysical.run coins setup codec keyView failure allocation helper erased writer view views original handle payload before=
      run coins setup codec keyView failure allocation helper erased writer view views originalLocal previousCrypto previous original handle payload before :=by
  cases selected:before.tokens handle with
  | none=>simp only [run,RegistrationNativePlatformPublicAdapterBuildLoggedPhysical.run,selected]
  | some token=>
    simp only [run,RegistrationNativePlatformPublicAdapterBuildLoggedPhysical.run,selected]
    cases converted:RegistrationNativeRawAdapter.application payload with
    | none=>rfl
    | some app=>
      simpa only [converted] using active_source coins setup codec keyView failure allocation helper erased writer view views originalLocal previousCrypto previous original token (.Some app)
        (RegistrationNativePlatformPublicAdapterStore.move before handle)

section Configured
variable {Error :Type}
variable [AdapterPublicOrdinaryPlatform.LookupOperations]
variable [originalGenerators :AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto :CryptoOperations (RustT ProbComp)]
variable [originalLocal :LocalOperations (RustT (StateT P ProbComp))]
variable [originalContainers :ContainerOperations (RustT (StateT P ProbComp))]
variable {setup :PqxdhServerAuthExperiment.Setup base KemSK} {checks :PqxdhServerAuthExperiment.Checks}
variable (configuration :RegistrationNativePlatformPublicAdapterConfiguration.Configuration
  (P:=P) (E:=E) (R:=R) (Error:=Error) (source:=source) setup checks)

noncomputable def operation {setup :PqxdhServerAuthExperiment.Setup base KemSK} {checks :PqxdhServerAuthExperiment.Checks}
    (configuration :RegistrationNativePlatformPublicAdapterConfiguration.Configuration
      (P:=P) (E:=E) (R:=R) (Error:=Error) (source:=source) setup checks)
    (before :State n KemSK R P) (handle :Nat) (payload :Option (Slice U8)) :
    ProbComp (Outcome n KemSK R P Reply) :=
  let previousCrypto:=RegistrationNativePlatformPublicAdapterUniformObserver.operations
    (fun query=>StateT.lift (RegistrationNativePlatformMldsaProgram.coins query) :QueryImpl unifSpec SourceM) originalCrypto
  run RegistrationNativePlatformMldsaProgram.coins setup
    (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire))
    configuration.keyView configuration.sealFailure
    (RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin)
    (RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame) configuration.erased
    (RegistrationNativePlatformConcreteSource.writer configuration.reservePackets) configuration.view configuration.views
    originalLocal previousCrypto RegistrationNativePlatformPublicAdapterDispatcherCore.children originalContainers
    handle (payload.map TranscriptAuthParts.absSlice) before

theorem operation_source {setup :PqxdhServerAuthExperiment.Setup base KemSK} {checks :PqxdhServerAuthExperiment.Checks}
    (configuration :RegistrationNativePlatformPublicAdapterConfiguration.Configuration
      (P:=P) (E:=E) (R:=R) (Error:=Error) (source:=source) setup checks)
    (before :State n KemSK R P) (handle :Nat) (payload :Option (Slice U8)) :
    RegistrationNativePlatformPublicAdapterBuildLoggedPhysical.operation configuration before handle payload=
      operation configuration before handle payload :=by
  unfold RegistrationNativePlatformPublicAdapterBuildLoggedPhysical.operation operation
  exact run_source _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ handle (payload.map TranscriptAuthParts.absSlice) before
end Configured

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildLoggedActualSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildLoggedActualSource.active_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildLoggedActualSource.active_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildLoggedActualSource.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildLoggedActualSource.run_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildLoggedActualSource.operation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildLoggedActualSource.operation_source
