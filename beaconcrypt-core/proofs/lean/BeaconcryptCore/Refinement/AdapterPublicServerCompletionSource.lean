-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerRecordNative
import BeaconcryptCore.Refinement.AdapterPublicServerSigningNative
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The complete actual SDK first-record, response signing and response writer suffix is one same-run source program. Its selected leaves are the literal prefixed seal/raw writer request programs, functional native HKDF, actual native hash/sign callbacks with a checked private hash cut, and the checked mutable registration writer. The final mutable-map installer remains the exact source continuation. No success, codec, normality or complete controller equality is supplied as an assumption. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerCompletionSource
open BeaconcryptCore.Computational
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformCutJournal (State)
open RegistrationNativePlatformCutErasure (liftWorld)
variable {n : Nat} {S E KemSK I Reader Response : Type} {base : OracleSpec I}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
local notation "SourceM" => StateT (State S) m
variable (F : ∀ {A : Type}, StateT (RegistrationServerRootCompiler.Local n) m A → StateT (State S) m A)
variable (impl : QueryImpl RegistrationSigningShared.Spec (StateT S m))
variable (fallback : registration.MldsaSigningRequest → StateT S m RegistrationSigningShared.SignReply)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [sealingPrimitive : AdapterSealPrimitive.Operations]

@[instance_reducible] noncomputable def localOperations (previous : LocalOperations (RustT SourceM))
    (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : sealingPrimitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m) : LocalOperations (RustT SourceM) :=
  AdapterPublicServerSigningNative.localOperations impl fallback
    (AdapterPublicServerRecordNative.localOperations F previous coins setup codec view failure allocation helper)

@[instance_reducible] noncomputable def children (previous : ChildOperations (RustT SourceM))
    (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (erased : commitment.CommitmentTranscript)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT S m)) : ChildOperations (RustT SourceM) :=
  AdapterPublicServerSigningNative.children impl
    (AdapterPublicServerRecordNative.children F previous coins setup codec erased) writer

variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [containers : ContainerOperations (RustT (StateT (State S) m))]

noncomputable def beforeInstall
    (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : sealingPrimitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (erased : commitment.CommitmentTranscript)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT S m))
    (initial : registration.ServerInitialKdf) :
    SourceM (RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))) := do
  let recorded ← F (RegistrationNativePlatformSourceRecord.fromInitialWithHash
    (RegistrationNativePlatformServerCompletion.records coins setup codec)
    (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
    (RegistrationNativePlatformSourceSeal.hash coins setup codec erased)
    (RegistrationNativePlatformSourceBuild.write helper) initial)
  RegistrationNativePlatformServerPublication.continueResult recorded
    (RegistrationNativePlatformServerPublication.program
      (RegistrationNativePlatformCutJournal.source impl fallback)
      (fun view => liftWorld (AdapterPublicServerSigningNative.encoder writer view)))

noncomputable def program
    (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : sealingPrimitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (erased : commitment.CommitmentTranscript)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT S m))
    (self : beaconcrypt_public_wrapper.server.Server) (initial : registration.ServerInitialKdf) :
    SourceM (RustM AdapterPublicServerBuildBody.Reply) := do
  let published ← beforeInstall F impl fallback coins setup codec view failure allocation helper erased writer initial
  AdapterPublicServerPublication.afterPublication self published

noncomputable def receipt
    (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : sealingPrimitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (erased : commitment.CommitmentTranscript)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT S m))
    (self : beaconcrypt_public_wrapper.server.Server) (initial : registration.ServerInitialKdf) :
    SourceM (RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)) × RustM AdapterPublicServerBuildBody.Reply) := do
  let published ← beforeInstall F impl fallback coins setup codec view failure allocation helper erased writer initial
  let word ← AdapterPublicServerPublication.afterPublication self published
  pure (published, word)

theorem source (hom : Cslib.IsMonadHom (StateT (RegistrationServerRootCompiler.Local n) m) SourceM F)
    (previousLocal : LocalOperations (RustT SourceM)) (previousChildren : ChildOperations (RustT SourceM))
    (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : sealingPrimitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (erased : commitment.CommitmentTranscript)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT S m))
    (self : beaconcrypt_public_wrapper.server.Server) (initial : registration.ServerInitialKdf) :
    letI : LocalOperations (RustT SourceM) := localOperations F impl fallback previousLocal coins setup codec view failure allocation helper
    letI : ChildOperations (RustT SourceM) := children F impl previousChildren coins setup codec erased writer
    (AdapterPublicServerBuildBody.record (m := SourceM) self initial).run =
      program F impl fallback coins setup codec view failure allocation helper erased writer self initial := by
  let : LocalOperations (RustT SourceM) := localOperations F impl fallback previousLocal coins setup codec view failure allocation helper
  let : ChildOperations (RustT SourceM) := children F impl previousChildren coins setup codec erased writer
  rw [AdapterPublicServerRecordNative.source F hom
    (AdapterPublicServerSigningNative.localOperations impl fallback previousLocal)
    (AdapterPublicServerSigningNative.children impl previousChildren writer)
    coins setup codec view failure allocation helper erased self initial]
  unfold program beforeInstall
  rw [bind_assoc]
  apply bind_congr
  intro recorded
  cases recorded with
  | fail error | div => simp only [AdapterPublicServerRecord.afterRecord,
      RegistrationNativePlatformServerPublication.continueResult, pure_bind, AdapterPublicServerPublication.afterPublication]
  | ok result => cases result with
    | Err rejected => simp only [AdapterPublicServerRecord.afterRecord,
        RegistrationNativePlatformServerPublication.continueResult, pure_bind, AdapterPublicServerPublication.afterPublication]
    | Ok pending =>
      exact AdapterPublicServerSigningNative.source impl fallback
        (AdapterPublicServerRecordNative.localOperations F previousLocal coins setup codec view failure allocation helper)
        (AdapterPublicServerRecordNative.children F previousChildren coins setup codec erased) writer self pending
theorem receipt_erasure
    (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : sealingPrimitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (erased : commitment.CommitmentTranscript)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT S m))
    (self : beaconcrypt_public_wrapper.server.Server) (initial : registration.ServerInitialKdf) :
    Prod.snd <$> receipt F impl fallback coins setup codec view failure allocation helper erased writer self initial =
      program F impl fallback coins setup codec view failure allocation helper erased writer self initial := by
  simp only [receipt, program, map_bind, map_pure, bind_pure]

end BeaconcryptCore.Refinement.AdapterPublicServerCompletionSource
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionSource.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionSource.source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionSource.receipt_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionSource.receipt_erasure
