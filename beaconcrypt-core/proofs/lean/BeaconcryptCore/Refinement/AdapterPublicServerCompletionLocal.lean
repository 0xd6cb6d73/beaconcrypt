-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerCompletionNative
import BeaconcryptCore.Refinement.AdapterPublicServerPublicationInstall
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The full native source first-record and response-publication prefix is the same literal Local controller lifted through the existing complete Native field. Factoring the actual corrected completion separates only its deterministic final installation/commit cut, preserving all preceding stateful allocation, crypto and writer failures. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerCompletionLocal
open BeaconcryptCore.Computational
variable {n : Nat} {E KemSK I Reader Response : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [primitive : AdapterSealPrimitive.Operations]
local notation "LocalM" => StateT (RegistrationServerRootCompiler.Local n) m
local notation "NativeM" => RegistrationNativePlatformExperiment.M n KemSK mlSource m

noncomputable def beforeInstall
    (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (initial : registration.ServerInitialKdf) : LocalM (RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))) := do
  let recorded ← RegistrationNativePlatformSourceRecord.fromInitialWithHash
    (RegistrationNativePlatformServerCompletion.records coins setup codec)
    (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
    (RegistrationNativePlatformSourceSeal.hash coins setup codec erased)
    (RegistrationNativePlatformSourceBuild.write helper) initial
  RegistrationNativePlatformServerPublication.continueResult recorded
    (RegistrationNativePlatformServerPublication.program
      (RegistrationNativePlatformServerCompletion.outgoing coins sign)
      (RegistrationNativePlatformSourceBuild.encode writer))

theorem native_local
    (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (initial : registration.ServerInitialKdf) :
    AdapterPublicServerCompletionNative.beforeInstall (n := n) (mlSource := mlSource)
      coins setup codec view failure allocation helper erased sign writer initial =
      AdapterPublicServerLocalLens.localState (beforeInstall coins setup codec view failure allocation helper erased sign writer initial) := by
  unfold AdapterPublicServerCompletionNative.beforeInstall AdapterPublicServerCompletionCut.native beforeInstall
  rw [AdapterPublicServerLocalLens.local_bind]
  apply bind_congr
  intro recorded
  cases recorded with
  | fail error | div => exact (AdapterPublicServerLocalLens.local_pure _).symm
  | ok result => cases result with
    | Err rejected => exact (AdapterPublicServerLocalLens.local_pure _).symm
    | Ok pending =>
      simp only [RegistrationNativePlatformServerPublication.continueResult]
      have hom : Cslib.IsMonadHom LocalM NativeM (fun {A} (work : LocalM A) => AdapterPublicServerLocalLens.localState work) :=
        .mk' AdapterPublicServerLocalLens.local_pure AdapterPublicServerLocalLens.local_bind
      rw [RegistrationNativePlatformBuildInterpret.Publication.program hom]
      simp only [← AdapterPublicServerCompletionNative.encoder_source]
      rfl

theorem finish_factor
    (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf) :
    RegistrationNativePlatformSourceBuild.finishSource (n := n) coins setup codec
      (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
      (RegistrationNativePlatformSourceSeal.hash coins setup codec erased) sign helper writer control initial = (do
        let published ← beforeInstall coins setup codec view failure allocation helper erased sign writer initial
        RegistrationNativePlatformServerCompletion.continueResult published
          (RegistrationNativePlatformServerCompletion.installWith
            (RegistrationNativePlatformServerCompletion.capability coins) control)) := by
  unfold RegistrationNativePlatformSourceBuild.finishSource RegistrationNativePlatformSourceCompletion.fromInitialSource beforeInstall
  rw [bind_assoc]
  apply bind_congr
  intro recorded
  cases recorded with
  | fail error | div => simp only [RegistrationNativePlatformServerCompletion.continueResult,
      RegistrationNativePlatformServerPublication.continueResult, pure_bind]
  | ok result => cases result <;> simp only [RegistrationNativePlatformServerCompletion.continueResult,
      RegistrationNativePlatformServerPublication.continueResult, pure_bind]
theorem fromInitial_factor
    (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf) :
    RegistrationNativePlatformExperiment.server (n := n) (source := mlSource)
      (RegistrationNativePlatformCompletionSdk.fromInitial
        (RegistrationNativePlatformSourceBuild.finishSource coins setup codec
          (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
          (RegistrationNativePlatformSourceSeal.hash coins setup codec erased) sign helper writer) control initial) = (do
        let published ← AdapterPublicServerLocalLens.localState
          (beforeInstall coins setup codec view failure allocation helper erased sign writer initial)
        RegistrationNativePlatformExperiment.server
          (AdapterPublicServerPublicationInstall.native coins control published) : NativeM _) := by
  unfold RegistrationNativePlatformCompletionSdk.fromInitial
  rw [AdapterPublicServerSourceLens.server_bind]
  change (do let completed ← AdapterPublicServerLocalLens.localState
               (RegistrationNativePlatformSourceBuild.finishSource coins setup codec
                 (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
                 (RegistrationNativePlatformSourceSeal.hash coins setup codec erased) sign helper writer control initial)
             RegistrationNativePlatformExperiment.server (RegistrationNativePlatformServerSdk.commit completed)) = _
  rw [finish_factor, AdapterPublicServerLocalLens.local_bind, bind_assoc]
  apply bind_congr
  intro published
  unfold AdapterPublicServerPublicationInstall.native
  rw [AdapterPublicServerSourceLens.server_bind]
  rfl

end BeaconcryptCore.Refinement.AdapterPublicServerCompletionLocal
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionLocal.native_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionLocal.native_local
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionLocal.finish_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionLocal.finish_factor

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionLocal.fromInitial_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionLocal.fromInitial_factor
