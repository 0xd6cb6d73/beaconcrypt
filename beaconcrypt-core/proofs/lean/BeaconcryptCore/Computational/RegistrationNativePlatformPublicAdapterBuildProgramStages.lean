-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStageCut
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildNormalization
/-! The actual Builder prefix and source installer enclose the jointly observed first-record/signing suffix. Readonly lookup and all allocator refusals execute unchanged. Observations survive the actual returned source Server, even when the response writer or subsequent source map installation fails. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicServerBuildTrace (Publication Word)
open RegistrationNativePlatformSdkReification (Backend backend)
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [primitive : AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
abbrev Spec := RegistrationNativePlatformPublicAdapterBuildProgram.Spec
variable {Log : Type}
variable {n : Nat} {I KemSK E P : Type} {base : OracleSpec I} {Reader Response : Type}
variable {mlSource : RegistrationNativeMldsa.Source}
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
variable (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
variable (erased : commitment.CommitmentTranscript)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
variable (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
local notation "Cut" => RegistrationNativePlatformCutJournal.State Native
local notation "Base" => StateT P ProbComp
local notation "SourceM" => StateT Cut Base
variable (originalLocal : LocalOperations (RustT Base)) (original : ContainerOperations (RustT Base))
variable (previousCrypto : CryptoOperations (RustT SourceM)) (previousChildren : ChildOperations (RustT SourceM))
variable (fallback : registration.MldsaSigningRequest → StateT Native Base RegistrationSigningShared.SignReply)
attribute [local irreducible] RegistrationNativePlatformPublicAdapterBuildSource.nativeHandler
  RegistrationNativePlatformPublicAdapterBuildSource.handler

private def lift {S A : Type} (work : StateT S Base A) : StateT (S × List Log) Base A := fun before =>
  (fun result => (result.1,(result.2,before.2))) <$> work.run before.1

noncomputable def physicalComplete (note : Stage → Log) (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (original : ContainerOperations (RustT (StateT P ProbComp))) (self : beaconcrypt_public_wrapper.server.Server) (initial : registration.ServerInitialKdf) :
    StateT (Backend n KemSK × List Log) Base (Publication × RustM AdapterPublicServerBuildBody.Reply) :=
  letI : ContainerOperations (RustT Base) := original
  fun before => do
    let published ← (RegistrationNativePlatformPublicAdapterBuildStageLog.physical coins setup codec keyView failure allocation helper erased sign writer note initial).run before
    let word ← AdapterPublicServerPublication.afterPublication (m:=Base) self published.1
    pure ((published.1,word),published.2)

noncomputable def physical (note : Stage → Log) (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (original : ContainerOperations (RustT (StateT P ProbComp))) : QueryImpl Spec (StateT (Backend n KemSK × List Log) Base)
  | .inr (.inr (.inr (self,initial))) => physicalComplete note coins setup codec keyView failure allocation helper erased sign writer original self initial
  | query => lift (RegistrationNativePlatformPublicAdapterBuildSource.handler coins setup codec keyView failure allocation helper erased sign writer view original query)

noncomputable def nativeComplete (note : Stage → Log) (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (original : ContainerOperations (RustT (StateT P ProbComp))) (self : beaconcrypt_public_wrapper.server.Server) (initial : registration.ServerInitialKdf) :
    StateT (Cut × List Log) Base (Publication × RustM AdapterPublicServerBuildBody.Reply) :=
  letI : ContainerOperations (RustT Base) := original
  fun before => do
    let published ← (simulateQ
      (RegistrationNativePlatformPublicAdapterSourceTrace.recorded
        (RegistrationNativePlatformPublicAdapterBuildStageCut.lifted
          (RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer))
        (fun query reply => (RegistrationNativePlatformPublicAdapterBuildStages.observation query reply).map note))
      (RegistrationNativePlatformPublicAdapterBuildStages.code initial)).run before
    let word ← AdapterPublicServerPublication.afterPublication (m:=Base) self published.1
    pure ((published.1,word),published.2)

noncomputable def native (note : Stage → Log) (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (originalLocal : LocalOperations (RustT Base)) (original : ContainerOperations (RustT Base))
    (previousCrypto : CryptoOperations (RustT SourceM)) (previousChildren : ChildOperations (RustT SourceM))
    (fallback : registration.MldsaSigningRequest → StateT Native Base RegistrationSigningShared.SignReply) : QueryImpl Spec (StateT (Cut × List Log) Base)
  | .inr (.inr (.inr (self,initial))) => nativeComplete note coins setup codec keyView failure allocation helper erased sign writer original self initial
  | query => lift (RegistrationNativePlatformPublicAdapterBuildSource.nativeHandler coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback query)

theorem complete_source (note : Stage → Log) (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (original : ContainerOperations (RustT (StateT P ProbComp))) (self : beaconcrypt_public_wrapper.server.Server) (initial : registration.ServerInitialKdf)
    (before : Cut × List Log) :
    Prod.map id (fun current => (backend current.1.1,current.2)) <$>
      (nativeComplete note coins setup codec keyView failure allocation helper erased sign writer original self initial).run before =
      (physicalComplete note coins setup codec keyView failure allocation helper erased sign writer original self initial).run (backend before.1.1,before.2) := by
  let : ContainerOperations (RustT Base) := original
  unfold nativeComplete physicalComplete
  simp only [StateT.run,map_bind,map_pure]
  have same : Prod.map id (Prod.map (fun current : Cut => backend current.1) id) <$>
      (simulateQ (RegistrationNativePlatformPublicAdapterSourceTrace.recorded
        (RegistrationNativePlatformPublicAdapterBuildStageCut.lifted
          (RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer))
        (fun query reply => (RegistrationNativePlatformPublicAdapterBuildStages.observation query reply).map note))
        (RegistrationNativePlatformPublicAdapterBuildStages.code initial)).run before =
      (RegistrationNativePlatformPublicAdapterBuildStageLog.physical coins setup codec keyView failure allocation helper erased sign writer note initial).run (backend before.1.1,before.2) := by
    apply RegistrationNativePlatformPublicAdapterSourceTrace.source
    intro query current
    exact RegistrationNativePlatformPublicAdapterBuildStageCut.query_source _ _ backend
      (RegistrationNativePlatformPublicAdapterBuildPublication.query_source coins setup codec keyView failure allocation helper erased sign writer) query current
  simp only [StateT.run] at same
  rw [←same,bind_map_left]
  apply bind_congr
  rintro ⟨published,current⟩
  simp only [bind_pure_comp,Prod.map,id_eq]

theorem query_source (note : Stage → Log) (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (originalLocal : LocalOperations (RustT Base)) (original : ContainerOperations (RustT Base))
    (previousCrypto : CryptoOperations (RustT SourceM)) (previousChildren : ChildOperations (RustT SourceM))
    (fallback : registration.MldsaSigningRequest → StateT Native Base RegistrationSigningShared.SignReply)
    (query : Spec.Domain) (before : Cut × List Log) :
    Prod.map id (fun current => (backend current.1.1,current.2)) <$>
      (native note coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback query).run before =
      (physical note coins setup codec keyView failure allocation helper erased sign writer view original query).run (backend before.1.1,before.2) := by
  have unlogged := RegistrationNativePlatformPublicAdapterBuildSource.query_source coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback query before.1
  cases query with
  | inl self =>
    simpa only [native,physical,lift,StateT.run,Functor.map_map,Prod.map,id_eq] using
      congrArg (fun computation => (fun result => (result.1,(result.2,before.2))) <$> computation) unlogged
  | inr query => cases query with
    | inl pair =>
      simpa only [native,physical,lift,StateT.run,Functor.map_map,Prod.map,id_eq] using
        congrArg (fun computation => (fun result => (result.1,(result.2,before.2))) <$> computation) unlogged
    | inr query => cases query with
      | inl known =>
        simpa only [native,physical,lift,StateT.run,Functor.map_map,Prod.map,id_eq] using
          congrArg (fun computation => (fun result => (result.1,(result.2,before.2))) <$> computation) unlogged
      | inr pair => exact complete_source note coins setup codec keyView failure allocation helper erased sign writer original pair.1 pair.2 before

theorem source (note : Stage → Log) (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (originalLocal : LocalOperations (RustT Base)) (original : ContainerOperations (RustT Base))
    (previousCrypto : CryptoOperations (RustT SourceM)) (previousChildren : ChildOperations (RustT SourceM))
    (fallback : registration.MldsaSigningRequest → StateT Native Base RegistrationSigningShared.SignReply)
    (self : beaconcrypt_public_wrapper.server.Server)
    (token : beaconcrypt_public_wrapper.server.RegistrationOutput) (data : core.option.Option (Slice U8))
    (before : Cut × List Log) :
    Prod.map id (fun current => (backend current.1.1,current.2)) <$>
      (simulateQ (native note coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback)
        (RegistrationNativePlatformPublicAdapterBuildProgram.program self token data)).run before =
      (simulateQ (physical note coins setup codec keyView failure allocation helper erased sign writer view original)
        (RegistrationNativePlatformPublicAdapterBuildProgram.program self token data)).run (backend before.1.1,before.2) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ _
    (query_source note coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback) _ before


theorem complete_erase (note : Stage → Log) (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (original : ContainerOperations (RustT (StateT P ProbComp))) (self : beaconcrypt_public_wrapper.server.Server) (initial : registration.ServerInitialKdf)
    (before : Backend n KemSK × List Log) :
    Prod.map id Prod.fst <$> (physicalComplete note coins setup codec keyView failure allocation helper erased sign writer original self initial).run before =
      (RegistrationNativePlatformPublicAdapterBuildComplete.complete coins setup codec keyView failure allocation helper erased sign writer original self initial).run before.1 := by
  let : ContainerOperations (RustT Base) := original
  unfold physicalComplete RegistrationNativePlatformPublicAdapterBuildComplete.complete
  simp only [StateT.run_bind,StateT.run_lift,StateT.run_pure]
  dsimp only [StateT.run]
  simp only [map_bind,map_pure,bind_assoc,pure_bind]
  have same := RegistrationNativePlatformPublicAdapterBuildStageLog.erase coins setup codec keyView failure allocation helper erased sign writer note initial before
  simp only [StateT.run] at same
  rw [←same,bind_map_left]
  apply bind_congr
  rintro ⟨published,current⟩
  simp only [bind_pure_comp,Prod.map,id_eq]


omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem lift_erase {S A : Type} (work : StateT S Base A) (before : S × List Log) :
    Prod.map id Prod.fst <$> (lift work).run before = work.run before.1 := by
  simp only [lift,StateT.run,Functor.map_map,Prod.map,id_eq]
  exact id_map _

theorem query_erase (note : Stage → Log) (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (original : ContainerOperations (RustT (StateT P ProbComp)))
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (query : Spec.Domain) (before : Backend n KemSK × List Log) :
    Prod.map id Prod.fst <$> (physical note coins setup codec keyView failure allocation helper erased sign writer view original query).run before =
      (RegistrationNativePlatformPublicAdapterBuildSource.handler coins setup codec keyView failure allocation helper erased sign writer view original query).run before.1 := by
  cases query with
  | inl self => exact lift_erase _ before
  | inr query => cases query with
    | inl pair => exact lift_erase _ before
    | inr query => cases query with
      | inl known => exact lift_erase _ before
      | inr pair =>
        unfold physical RegistrationNativePlatformPublicAdapterBuildSource.handler
        exact complete_erase note coins setup codec keyView failure allocation helper erased sign writer original pair.1 pair.2 before

theorem erase (note : Stage → Log) (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (original : ContainerOperations (RustT (StateT P ProbComp)))
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (self : beaconcrypt_public_wrapper.server.Server)
    (token : beaconcrypt_public_wrapper.server.RegistrationOutput) (data : core.option.Option (Slice U8))
    (before : Backend n KemSK × List Log) :
    Prod.map id Prod.fst <$>
      (simulateQ (physical note coins setup codec keyView failure allocation helper erased sign writer view original)
        (RegistrationNativePlatformPublicAdapterBuildProgram.program self token data)).run before =
      (RegistrationNativePlatformPublicAdapterBuildSource.program coins setup codec keyView failure allocation helper erased sign writer view original self token data).run before.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (query_erase note coins setup codec keyView failure allocation helper erased sign writer original view) _ before


theorem sdk_erasure (note : Stage → Log) (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (originalLocal : LocalOperations (RustT Base)) (original : ContainerOperations (RustT Base))
    (previousCrypto : CryptoOperations (RustT SourceM)) (previousChildren : ChildOperations (RustT SourceM))
    (fallback : registration.MldsaSigningRequest → StateT Native Base RegistrationSigningShared.SignReply)

    (self : beaconcrypt_public_wrapper.server.Server) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data : core.option.Option (Slice U8)) (before : Cut) (log : List Log) :
    Prod.map id (fun current => backend current.1) <$>
      (RegistrationNativePlatformPublicAdapterBuildSource.nativeSdk coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback self token data).run before =
      (fun result => (result.1.2,result.2.1)) <$>
        (simulateQ (physical note coins setup codec keyView failure allocation helper erased sign writer view original)
          (RegistrationNativePlatformPublicAdapterBuildProgram.program self token data)).run (backend before.1,log) := by
  rw [RegistrationNativePlatformPublicAdapterBuildSource.sdk_source coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback self token data before]
  have same := congrArg (fun computation => (fun result => (result.1.2,result.2)) <$> computation)
    (erase note coins setup codec keyView failure allocation helper erased sign writer original view self token data (backend before.1,log))
  simpa only [StateT.run_map,Functor.map_map,Prod.map,id_eq] using same.symm


theorem complete_native_erasure (note : Stage → Log) (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (original : ContainerOperations (RustT (StateT P ProbComp)))
    (fallback : registration.MldsaSigningRequest → StateT Native Base RegistrationSigningShared.SignReply)
    (self : beaconcrypt_public_wrapper.server.Server) (initial : registration.ServerInitialKdf)
    (before : Cut × List Log) :
    let : ContainerOperations (RustT SourceM) := RegistrationNativePlatformPublicAdapterBuildDictionaries.containers (n:=n) (source:=mlSource) original
    Prod.map id Prod.fst <$> (nativeComplete note coins setup codec keyView failure allocation helper erased sign writer original self initial).run before =
      (AdapterPublicServerBuildTrace.complete coins setup codec keyView failure allocation helper erased sign writer fallback self initial).run before.1 := by
  let : ContainerOperations (RustT Base) := original
  let : ContainerOperations (RustT SourceM) := RegistrationNativePlatformPublicAdapterBuildDictionaries.containers (n:=n) (source:=mlSource) original
  have observed := RegistrationNativePlatformPublicAdapterSourceTrace.erase
    (RegistrationNativePlatformPublicAdapterBuildStageCut.lifted
      (RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer))
    (fun query reply => (RegistrationNativePlatformPublicAdapterBuildStages.observation query reply).map note)
    (RegistrationNativePlatformPublicAdapterBuildStages.code initial) before
  rw [RegistrationNativePlatformPublicAdapterBuildStageCut.actual _ fallback] at observed
  have installer (published : Publication) : AdapterPublicServerPublication.afterPublication (m:=SourceM) self published =
      StateT.lift (AdapterPublicServerPublication.afterPublication (m:=Base) self published) :=
    RegistrationNativePlatformPublicAdapterBuildInstall.after_publication original self published
  dsimp only
  unfold nativeComplete AdapterPublicServerBuildTrace.complete AdapterPublicServerCompletionSource.receipt
  simp_rw [installer]
  simp only [StateT.run_bind,StateT.run_lift,StateT.run_pure]
  dsimp only [StateT.run]
  simp only [map_bind,map_pure,bind_assoc,pure_bind]
  simp only [StateT.run] at observed
  change (Prod.map id Prod.fst <$>
    simulateQ (RegistrationNativePlatformPublicAdapterSourceTrace.recorded
      (RegistrationNativePlatformPublicAdapterBuildStageCut.lifted
        (RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer))
      (fun query reply => (RegistrationNativePlatformPublicAdapterBuildStages.observation query reply).map note))
      (RegistrationNativePlatformPublicAdapterBuildStages.code initial) before) =
    AdapterPublicServerCompletionSource.beforeInstall
      (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
      (AdapterPublicServerCompletionNative.outgoing coins sign) fallback coins setup codec keyView failure allocation helper erased
      (AdapterPublicServerCompletionNative.writer writer) initial before.1 at observed
  rw [←observed,bind_map_left]
  apply bind_congr
  rintro ⟨published,current⟩
  simp only [bind_pure_comp,Prod.map,id_eq]


theorem query_native_erasure (note : Stage → Log) (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (originalLocal : LocalOperations (RustT Base)) (original : ContainerOperations (RustT Base))
    (previousCrypto : CryptoOperations (RustT SourceM)) (previousChildren : ChildOperations (RustT SourceM))
    (fallback : registration.MldsaSigningRequest → StateT Native Base RegistrationSigningShared.SignReply)

    (query : Spec.Domain) (before : Cut × List Log) :
    Prod.map id Prod.fst <$> (native note coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback query).run before =
      (RegistrationNativePlatformPublicAdapterBuildSource.nativeHandler coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback query).run before.1 := by
  cases query with
  | inl self => exact lift_erase _ before
  | inr query => cases query with
    | inl pair => exact lift_erase _ before
    | inr query => cases query with
      | inl known => exact lift_erase _ before
      | inr pair =>
        unfold native RegistrationNativePlatformPublicAdapterBuildSource.nativeHandler RegistrationNativePlatformPublicAdapterBuildProgram.handler
        exact complete_native_erasure note coins setup codec keyView failure allocation helper erased sign writer original fallback pair.1 pair.2 before

theorem native_erasure (note : Stage → Log) (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (originalLocal : LocalOperations (RustT Base)) (original : ContainerOperations (RustT Base))
    (previousCrypto : CryptoOperations (RustT SourceM)) (previousChildren : ChildOperations (RustT SourceM))
    (fallback : registration.MldsaSigningRequest → StateT Native Base RegistrationSigningShared.SignReply)

    (self : beaconcrypt_public_wrapper.server.Server) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data : core.option.Option (Slice U8)) (before : Cut × List Log) :
    Prod.map id Prod.fst <$>
      (simulateQ (native note coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback)
        (RegistrationNativePlatformPublicAdapterBuildProgram.program self token data)).run before =
      (simulateQ (RegistrationNativePlatformPublicAdapterBuildSource.nativeHandler coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback)
        (RegistrationNativePlatformPublicAdapterBuildProgram.program self token data)).run before.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (query_native_erasure note coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback) _ before

noncomputable def sample (note : Stage → Log) (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (originalLocal : LocalOperations (RustT Base)) (original : ContainerOperations (RustT Base))
    (previousCrypto : CryptoOperations (RustT SourceM)) (previousChildren : ChildOperations (RustT SourceM))
    (fallback : registration.MldsaSigningRequest → StateT Native Base RegistrationSigningShared.SignReply)

    (self : beaconcrypt_public_wrapper.server.Server) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data : core.option.Option (Slice U8)) (before : Cut) (previous : P) (log : List Log) :
    ProbComp (((Word × Cut) × P) × List Log) :=
  (fun result => (((result.1.1,result.1.2.1),result.2),result.1.2.2)) <$>
    ((simulateQ (native note coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback)
      (RegistrationNativePlatformPublicAdapterBuildProgram.program self token data)).run (before,log)).run previous

theorem sample_erase (note : Stage → Log) (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (originalLocal : LocalOperations (RustT Base)) (original : ContainerOperations (RustT Base))
    (previousCrypto : CryptoOperations (RustT SourceM)) (previousChildren : ChildOperations (RustT SourceM))
    (fallback : registration.MldsaSigningRequest → StateT Native Base RegistrationSigningShared.SignReply)

    (self : beaconcrypt_public_wrapper.server.Server) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data : core.option.Option (Slice U8)) (before : Cut) (previous : P) (log : List Log) :
    Prod.fst <$> sample note coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback self token data before previous log =
      ((simulateQ (RegistrationNativePlatformPublicAdapterBuildSource.nativeHandler coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback)
        (RegistrationNativePlatformPublicAdapterBuildProgram.program self token data)).run before).run previous := by
  have same := congrArg (fun computation => computation.run previous)
    (native_erasure note coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback self token data (before,log))
  simpa only [sample,StateT.run_map,Functor.map_map,Prod.map,id_eq] using same


noncomputable def sdkRunner (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (originalLocal : LocalOperations (RustT Base)) (original : ContainerOperations (RustT Base))
    (previousCrypto : CryptoOperations (RustT SourceM)) (previousChildren : ChildOperations (RustT SourceM))
    (fallback : registration.MldsaSigningRequest → StateT Native Base RegistrationSigningShared.SignReply)

    (self : beaconcrypt_public_wrapper.server.Server) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data : core.option.Option (Slice U8)) : SourceM Word :=
  let previousLocal := RegistrationNativePlatformPublicAdapterBuildDictionaries.locals (n:=n) view originalLocal
  letI : ContainerOperations (RustT SourceM) := RegistrationNativePlatformPublicAdapterBuildDictionaries.containers (n:=n) (source:=mlSource) original
  letI : CryptoOperations (RustT SourceM) := RegistrationNativePlatformPublicAdapterBuildDictionaries.crypto view previousCrypto
  letI : LocalOperations (RustT SourceM) := AdapterPublicServerCompletionSource.localOperations
    (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) fallback previousLocal coins setup codec keyView failure allocation helper
  letI : ChildOperations (RustT SourceM) := AdapterPublicServerCompletionSource.children
    (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
    (AdapterPublicServerCompletionNative.writer writer)
  RegistrationNativePlatformExtractedSdkServer.Build.run coins setup codec keyView failure allocation helper erased sign writer fallback self token data

theorem sdk_code (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (originalLocal : LocalOperations (RustT Base)) (original : ContainerOperations (RustT Base))
    (previousCrypto : CryptoOperations (RustT SourceM)) (previousChildren : ChildOperations (RustT SourceM))
    (fallback : registration.MldsaSigningRequest → StateT Native Base RegistrationSigningShared.SignReply)

    (self : beaconcrypt_public_wrapper.server.Server) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data : core.option.Option (Slice U8)) :
    simulateQ (RegistrationNativePlatformPublicAdapterBuildSource.nativeHandler coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback)
      (RegistrationNativePlatformPublicAdapterBuildProgram.program self token data) =
      sdkRunner coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback self token data := by
  let previousLocal := RegistrationNativePlatformPublicAdapterBuildDictionaries.locals (n:=n) view originalLocal
  let : ContainerOperations (RustT SourceM) := RegistrationNativePlatformPublicAdapterBuildDictionaries.containers (n:=n) (source:=mlSource) original
  let : CryptoOperations (RustT SourceM) := RegistrationNativePlatformPublicAdapterBuildDictionaries.crypto view previousCrypto
  let : LocalOperations (RustT SourceM) := AdapterPublicServerCompletionSource.localOperations
    (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) fallback previousLocal coins setup codec keyView failure allocation helper
  let : ChildOperations (RustT SourceM) := AdapterPublicServerCompletionSource.children
    (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
    (AdapterPublicServerCompletionNative.writer writer)
  unfold sdkRunner RegistrationNativePlatformPublicAdapterBuildSource.nativeHandler
  rw [RegistrationNativePlatformPublicAdapterBuildProgram.source]
  rfl

theorem sample_sdk (note : Stage → Log) (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (originalLocal : LocalOperations (RustT Base)) (original : ContainerOperations (RustT Base))
    (previousCrypto : CryptoOperations (RustT SourceM)) (previousChildren : ChildOperations (RustT SourceM))
    (fallback : registration.MldsaSigningRequest → StateT Native Base RegistrationSigningShared.SignReply)

    (self : beaconcrypt_public_wrapper.server.Server) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data : core.option.Option (Slice U8)) (before : Cut) (previous : P) (log : List Log) :
    Prod.fst <$> sample note coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback self token data before previous log =
      ((sdkRunner coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback self token data).run before).run previous := by
  rw [sample_erase,sdk_code]


theorem sample_source (note : Stage → Log) (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (originalLocal : LocalOperations (RustT Base)) (original : ContainerOperations (RustT Base))
    (previousCrypto : CryptoOperations (RustT SourceM)) (previousChildren : ChildOperations (RustT SourceM))
    (fallback : registration.MldsaSigningRequest → StateT Native Base RegistrationSigningShared.SignReply)


    (self : beaconcrypt_public_wrapper.server.Server) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data : core.option.Option (Slice U8)) (before : Cut) (previous : P) (log : List Log) :
    (fun result => (((result.1.1.1,backend result.1.1.2.1),result.1.2),result.2)) <$>
      sample note coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback self token data before previous log =
    (fun result => (((result.1.1,result.1.2.1),result.2),result.1.2.2)) <$>
      ((simulateQ (physical note coins setup codec keyView failure allocation helper erased sign writer view original)
        (RegistrationNativePlatformPublicAdapterBuildProgram.program self token data)).run (backend before.1,log)).run previous := by
  have same := congrArg (fun computation => computation.run previous)
    (source note coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback self token data (before,log))
  have arranged := congrArg (fun computation =>
    (fun result => (((result.1.1,result.1.2.1),result.2),result.1.2.2)) <$> computation) same
  simpa only [sample,StateT.run_map,Functor.map_map,Prod.map,id_eq] using arranged


omit material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem stage_frame (note : Stage → Log) (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))

    (initial : registration.ServerInitialKdf) (before : Backend n KemSK × List Log) :
    Prod.map id (Prod.map RegistrationNativePlatformPublicAdapterPhysicalBackend.erase id) <$>
      (RegistrationNativePlatformPublicAdapterBuildStageLog.physical coins setup codec keyView failure allocation helper erased sign writer note initial).run before =
      (RegistrationNativePlatformPublicAdapterBuildStageLog.physical coins setup codec keyView failure allocation helper erased sign writer note initial).run
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.erase before.1,before.2) :=by
  apply RegistrationNativePlatformPublicAdapterSourceTrace.source
  intro query current
  exact RegistrationNativePlatformPublicAdapterBuildNormalization.publication_query coins setup codec keyView failure allocation helper erased sign writer query current

theorem complete_frame (note : Stage → Log) (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (original : ContainerOperations (RustT (StateT P ProbComp)))
    (self :beaconcrypt_public_wrapper.server.Server) (initial :registration.ServerInitialKdf)
    (before : Backend n KemSK × List Log) :
    Prod.map id (Prod.map RegistrationNativePlatformPublicAdapterPhysicalBackend.erase id) <$>
      (physicalComplete note coins setup codec keyView failure allocation helper erased sign writer original self initial).run before =
      (physicalComplete note coins setup codec keyView failure allocation helper erased sign writer original self initial).run
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.erase before.1,before.2) :=by
  let :ContainerOperations (RustT Base):=original
  unfold physicalComplete
  simp only [StateT.run,map_bind,map_pure]
  have same:=stage_frame note coins setup codec keyView failure allocation helper erased sign writer initial before
  simp only [StateT.run] at same
  rw [←same,bind_map_left]
  apply bind_congr
  rintro ⟨published,current⟩
  rfl

theorem query_frame (note : Stage → Log) (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (original : ContainerOperations (RustT (StateT P ProbComp)))
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)

    (query : Spec.Domain) (before : Backend n KemSK × List Log) :
    Prod.map id (Prod.map RegistrationNativePlatformPublicAdapterPhysicalBackend.erase id) <$>
      (physical note coins setup codec keyView failure allocation helper erased sign writer view original query).run before =
      (physical note coins setup codec keyView failure allocation helper erased sign writer view original query).run
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.erase before.1,before.2) :=by
  have law:=RegistrationNativePlatformPublicAdapterBuildNormalization.query coins setup codec keyView failure allocation helper erased sign writer view original query before.1
  cases query with
  | inl self=>
    simpa only [physical,lift,StateT.run,Functor.map_map,Prod.map,id_eq] using
      congrArg (fun computation=>(fun result=>(result.1,(result.2,before.2))) <$>computation) law
  | inr query=>cases query with
    | inl pair=>
      simpa only [physical,lift,StateT.run,Functor.map_map,Prod.map,id_eq] using
        congrArg (fun computation=>(fun result=>(result.1,(result.2,before.2))) <$>computation) law
    | inr query=>cases query with
      | inl known=>
        simpa only [physical,lift,StateT.run,Functor.map_map,Prod.map,id_eq] using
          congrArg (fun computation=>(fun result=>(result.1,(result.2,before.2))) <$>computation) law
      | inr pair=>exact complete_frame note coins setup codec keyView failure allocation helper erased sign writer original pair.1 pair.2 before

theorem program_frame (note : Stage → Log) (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (original : ContainerOperations (RustT (StateT P ProbComp)))
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)

    (self :beaconcrypt_public_wrapper.server.Server) (token :beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data :core.option.Option (Slice U8)) (before : Backend n KemSK × List Log) :
    Prod.map id (Prod.map RegistrationNativePlatformPublicAdapterPhysicalBackend.erase id) <$>
      (simulateQ (physical note coins setup codec keyView failure allocation helper erased sign writer view original)
        (RegistrationNativePlatformPublicAdapterBuildProgram.program self token data)).run before =
      (simulateQ (physical note coins setup codec keyView failure allocation helper erased sign writer view original)
        (RegistrationNativePlatformPublicAdapterBuildProgram.program self token data)).run
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.erase before.1,before.2) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ _
    (query_frame note coins setup codec keyView failure allocation helper erased sign writer original view) _ before


theorem sample_normalized_source (note : Stage → Log) (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (originalLocal : LocalOperations (RustT Base)) (original : ContainerOperations (RustT Base))
    (previousCrypto : CryptoOperations (RustT SourceM)) (previousChildren : ChildOperations (RustT SourceM))
    (fallback : registration.MldsaSigningRequest → StateT Native Base RegistrationSigningShared.SignReply)



    (self : beaconcrypt_public_wrapper.server.Server) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data : core.option.Option (Slice U8)) (before : Cut) (previous : P) (log : List Log) :
    (fun result => (((result.1.1.1,RegistrationNativePlatformPublicAdapterPhysicalBackend.erase (backend result.1.1.2.1)),result.1.2),result.2)) <$>
      sample note coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback self token data before previous log =
    (fun result => (((result.1.1,result.1.2.1),result.2),result.1.2.2)) <$>
      ((simulateQ (physical note coins setup codec keyView failure allocation helper erased sign writer view original)
        (RegistrationNativePlatformPublicAdapterBuildProgram.program self token data)).run
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.erase (backend before.1),log)).run previous :=by
  have projected:=congrArg (fun computation=>(fun result=>
    (((result.1.1.1,RegistrationNativePlatformPublicAdapterPhysicalBackend.erase result.1.1.2),result.1.2),result.2)) <$>computation)
    (sample_source note coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback self token data before previous log)
  have frame:=congrArg (fun computation=>computation.run previous)
    (program_frame note coins setup codec keyView failure allocation helper erased sign writer original view self token data (backend before.1,log))
  have normalized:=congrArg (fun computation=>(fun result=>(((result.1.1,result.1.2.1),result.2),result.1.2.2)) <$>computation) frame
  simp only [StateT.run_map,Functor.map_map,Prod.map,id_eq] at projected normalized
  exact projected.trans normalized

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.complete_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.complete_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.complete_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.complete_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.query_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.query_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.sdk_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.sdk_erasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.complete_native_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.complete_native_erasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.query_native_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.query_native_erasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.native_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.native_erasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.sample_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.sample_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.sdk_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.sdk_code

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.sample_sdk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.sample_sdk

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.sample_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.sample_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.stage_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.stage_frame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.complete_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.complete_frame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.query_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.query_frame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.program_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.program_frame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.sample_normalized_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages.sample_normalized_source
