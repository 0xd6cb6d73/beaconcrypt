-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerPublicationNative
import BeaconcryptCore.Refinement.AdapterPublicWrapperChildren
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The literal SDK response hash/sign/writer body uses the checked same-run hash-cut interpretation. Its source dictionary changes only individual hash/sign leaves and the actual writer child. The complete actual mutable-map installer remains its original continuation, including every earlier failure. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerSigningNative
open BeaconcryptCore.Computational
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformCutJournal (State)
open RegistrationNativePlatformCutErasure (liftWorld)
variable {S E : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
local notation "SourceM" => StateT (State S) m
variable (impl : QueryImpl RegistrationSigningShared.Spec (StateT S m))
variable (fallback : registration.MldsaSigningRequest → StateT S m RegistrationSigningShared.SignReply)

@[instance_reducible] noncomputable def localOperations (previous : LocalOperations (RustT SourceM)) :
    LocalOperations (RustT SourceM) :=
  {previous with auth_MldsaIdentity_sign_requested := fun _ request =>
    ⟨RustM.ok <$> AdapterPublicBundleNative.sign impl fallback request⟩}

@[instance_reducible] noncomputable def children (previous : ChildOperations (RustT SourceM))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT S m)) :
    ChildOperations (RustT SourceM) :=
  {previous with
    executeHash := fun request => ⟨(fun digest => RustM.ok (core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest))) <$>
      RegistrationNativePlatformCutJournal.hash impl request⟩
    encodeResponse := fun packet => ⟨liftWorld (simulateQ writer
      (AdapterRegistrationWriterRequestExtraction.encodeResponse (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E) packet).run)⟩}

noncomputable def encoder (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT S m))
    (view : registration.SignedResponseView) : StateT S m (RustM (core.option.Option (alloc.vec.Vec U8))) :=
  simulateQ writer (AdapterRegistrationWriterRequestExtraction.encodeResponse (E := E)
    (m := AdapterRegistrationWriterRequestMonad.Program E) (RegistrationNativeSourceEncoders.responseSyntax view)).run

variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [containers : ContainerOperations (RustT (StateT (State S) m))]

theorem source (previousLocal : LocalOperations (RustT SourceM)) (previousChildren : ChildOperations (RustT SourceM))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT S m))
    (self : beaconcrypt_public_wrapper.server.Server) (pending : registration.ServerResponseHash) :
    letI : LocalOperations (RustT SourceM) := localOperations impl fallback previousLocal
    letI : ChildOperations (RustT SourceM) := children impl previousChildren writer
    (AdapterPublicServerBuildBody.sign (m := SourceM) self pending).run = (do
      let published ← RegistrationNativePlatformServerPublication.program
        (RegistrationNativePlatformCutJournal.source impl fallback)
        (fun view => liftWorld (encoder writer view)) pending
      AdapterPublicServerPublication.afterPublication self published) := by
  let : LocalOperations (RustT SourceM) := localOperations impl fallback previousLocal
  let : ChildOperations (RustT SourceM) := children impl previousChildren writer
  rw [AdapterPublicServerPublication.sign (AdapterPublicServerPublicationNative.primitives impl fallback)
    self ⟨fun _ => rfl, fun _ => rfl⟩]
  rw [AdapterPublicServerPublicationNative.outgoing_source]
  rfl

omit material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] containers in
theorem publication (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT S m))
    (pending : registration.ServerResponseHash) (before : State S) :
    Prod.map id Prod.fst <$>
      (RegistrationNativePlatformServerPublication.program
        (RegistrationNativePlatformCutJournal.source impl fallback)
        (fun view => liftWorld (encoder writer view)) pending).run before =
      (RegistrationNativePlatformServerPublication.program impl (encoder writer) pending).run before.1 :=
  RegistrationNativePlatformCutWorld.server impl fallback (encoder writer) pending before

end BeaconcryptCore.Refinement.AdapterPublicServerSigningNative
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerSigningNative.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerSigningNative.source
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerSigningNative.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerSigningNative.publication
