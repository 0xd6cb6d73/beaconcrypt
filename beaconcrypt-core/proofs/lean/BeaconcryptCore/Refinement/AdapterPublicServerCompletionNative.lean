-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerCompletionCut
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The whole source completion dictionary instantiates the existing full Native Local lens and checked private signing-cut lift. Both dynamic writers still execute their actual request programs in the same external state. Erasing only the private cut recovers the actual native first-record/publication callbacks and full native state. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerCompletionNative
open BeaconcryptCore.Computational
open RegistrationNativePlatformCutJournal (State)
open RegistrationNativePlatformCutErasure (liftWorld)
variable {n : Nat} {E KemSK I Reader Response A B : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
local notation "LocalM" => StateT (RegistrationServerRootCompiler.Local n) m
local notation "NativeM" => RegistrationNativePlatformExperiment.M n KemSK mlSource m
local notation "SourceM" => StateT (State (RegistrationNativeExperiment.State n KemSK mlSource)) m

def inCut (work : LocalM A) : SourceM A := liftWorld (AdapterPublicServerLocalLens.localState work)

theorem inCut_pure (value : A) : inCut (n := n) (KemSK := KemSK) (mlSource := mlSource) (pure value : LocalM A) = pure value := by
  rw [inCut, AdapterPublicServerLocalLens.local_pure, RegistrationNativePlatformCutLift.pure_lifted]

theorem inCut_bind (work : LocalM A) (next : A → LocalM B) :
    inCut (KemSK := KemSK) (mlSource := mlSource) (work >>= next) = (inCut work >>= fun value => inCut (next value)) := by
  rw [inCut, AdapterPublicServerLocalLens.local_bind, RegistrationNativePlatformCutLift.bind_lifted]
  rfl

theorem hom : Cslib.IsMonadHom LocalM SourceM (fun {A} (work : LocalM A) => inCut work) :=
  .mk' inCut_pure inCut_bind

noncomputable def outgoing (coins : QueryImpl unifSpec m)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl RegistrationSigningShared.Spec NativeM := fun query =>
  AdapterPublicServerLocalLens.localState (RegistrationNativePlatformServerCompletion.outgoing coins sign query)

def writer (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m) :
    QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) NativeM := fun query => StateT.lift (implementation query)

theorem encoder_source (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (view : registration.SignedResponseView) :
    AdapterPublicServerSigningNative.encoder (writer (n := n) (KemSK := KemSK) (mlSource := mlSource) implementation) view =
      AdapterPublicServerLocalLens.localState (RegistrationNativePlatformSourceBuild.encode implementation view) := by
  unfold AdapterPublicServerSigningNative.encoder writer
  change simulateQ (implementation.liftTarget NativeM)
      (AdapterRegistrationWriterRequestExtraction.encodeResponse (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E)
        (RegistrationNativeSourceEncoders.responseSyntax view)).run = _
  rw [simulateQ_liftTarget]
  unfold RegistrationNativePlatformSourceBuild.encode
  rw [AdapterPublicServerLocalLens.local_lift]
  rfl

variable [primitive : AdapterSealPrimitive.Operations]

noncomputable def beforeInstall
    (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (initial : registration.ServerInitialKdf) : NativeM (RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))) :=
  AdapterPublicServerCompletionCut.native
    (AdapterPublicServerLocalLens.localState (RegistrationNativePlatformSourceRecord.fromInitialWithHash
      (RegistrationNativePlatformServerCompletion.records coins setup codec)
      (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
      (RegistrationNativePlatformSourceSeal.hash coins setup codec erased)
      (RegistrationNativePlatformSourceBuild.write helper) initial))
    (outgoing coins sign) (AdapterPublicServerSigningNative.encoder (writer implementation))

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [containers : AdapterPublicWrapperRequestMonad.ContainerOperations
  (AdapterPublicWrapperRustT.RustT (StateT (State (RegistrationNativeExperiment.State n KemSK mlSource)) m))]

omit material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] containers in
theorem erasure
    (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (fallback : registration.MldsaSigningRequest → NativeM RegistrationSigningShared.SignReply)
    (initial : registration.ServerInitialKdf) (before : State (RegistrationNativeExperiment.State n KemSK mlSource)) :
    Prod.map id Prod.fst <$>
      (AdapterPublicServerCompletionSource.beforeInstall (fun {A} (work : LocalM A) => inCut work)
        (outgoing coins sign) fallback coins setup codec view failure allocation helper erased
        (writer implementation) initial).run before =
      (beforeInstall coins setup codec view failure allocation helper erased sign implementation initial).run before.1 := by
  exact AdapterPublicServerCompletionCut.erasure _ (outgoing coins sign) fallback
    (AdapterPublicServerSigningNative.encoder (writer implementation)) before
end BeaconcryptCore.Refinement.AdapterPublicServerCompletionNative
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionNative.inCut_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionNative.inCut_pure
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionNative.inCut_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionNative.inCut_bind
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionNative.encoder_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionNative.encoder_source
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionNative.erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionNative.erasure

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionNative.hom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionNative.hom
