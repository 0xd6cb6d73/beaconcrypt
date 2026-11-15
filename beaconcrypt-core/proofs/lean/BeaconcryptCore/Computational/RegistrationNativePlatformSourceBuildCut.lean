-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkBuildCut

/-! The actual source completion is cut at its reached first-record result before response signing or serialization. Successful completion derives this result from the supported source run; it is never supplied as an authentication, installation or security premise. All native and external intermediate states remain explicit. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildCut
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerRootCompiler (Local)
open RegistrationSigningShared (SignReply)
variable {n : Nat} {E Platform ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable [primitive : AdapterSealPrimitive.Operations]

noncomputable def afterRecord (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (hashed : registration.ServerResponseHash) :
    StateT (Local n) (StateT Platform ProbComp)
      (RustM (RegistrationWorldServerCompletion.Result (alloc.vec.Vec U8))) := do
  let published ← RegistrationNativePlatformServerPublication.program
    (RegistrationNativePlatformServerCompletion.outgoing coins sign)
    (RegistrationNativePlatformSourceBuild.encode writer) hashed
  RegistrationNativePlatformServerCompletion.continueResult published
    (RegistrationNativePlatformServerCompletion.installWith
      (RegistrationNativePlatformServerCompletion.capability coins) control)

/-- Any supported complete source result retains its actual first-record call and actual continuation. -/
theorem cut (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf)
    (before after : Local n) (previous next : Platform)
    (result : RustM (RegistrationWorldServerCompletion.Result (alloc.vec.Vec U8)))
    (supported : ((result, after), next) ∈ support
      (((RegistrationNativePlatformSourceBuild.finishSource coins setup codec
        (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash coins setup codec erased) sign helper writer control initial).run before).run previous)) :
    ∃ recorded current platform,
      ((recorded, current), platform) ∈ support
        (((RegistrationNativePlatformSourceSealTrace.record coins setup codec view failure allocation erased helper initial).run before).run previous) ∧
      ((result, after), next) ∈ support
        (((RegistrationNativePlatformServerCompletion.continueResult recorded
          (afterRecord coins sign writer control)).run current).run platform) := by
  change ((result, after), next) ∈ support (((do
    let recorded ← RegistrationNativePlatformSourceSealTrace.record coins setup codec view failure allocation erased helper initial
    RegistrationNativePlatformServerCompletion.continueResult recorded (afterRecord coins sign writer control)).run before).run previous) at supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨recorded, current⟩, platform⟩, called, continued⟩ := supported
  exact ⟨recorded, current, platform, called, continued⟩

/-- Successful actual source completion supplies its complete first-record trace at the same reached cut, before publication and installation. -/
theorem successful (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf)
    (published : peer.PublishedPeer (alloc.vec.Vec U8))
    (before after : Local n) (previous next : Platform)
    (supported : ((.ok (.Ok published), after), next) ∈ support
      (((RegistrationNativePlatformSourceBuild.finishSource coins setup codec
        (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash coins setup codec erased) sign helper writer control initial).run before).run previous)) :
    ∃ hashed current platform,
      ((.ok (.Ok hashed), current), platform) ∈ support
        (((RegistrationNativePlatformSourceSealTrace.record coins setup codec view failure allocation erased helper initial).run before).run previous) ∧
      Nonempty (RegistrationNativePlatformRecordTrace.Trace
        (fun query => RegistrationNativePlatformSourceSealTrace.joint (RegistrationNativePlatformServerCompletion.records coins setup codec query))
        (fun request => RegistrationNativePlatformSourceSealTrace.joint (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation request))
        (fun transcript => RegistrationNativePlatformSourceSealTrace.joint (RegistrationNativePlatformSourceSeal.hash coins setup codec erased transcript))
        (fun request => RegistrationNativePlatformSourceSealTrace.joint (RegistrationNativePlatformSourceBuild.write helper request))
        initial hashed (before, previous) (current, platform)) ∧
      ((.ok (.Ok published), after), next) ∈ support
        (((afterRecord coins sign writer control hashed).run current).run platform) := by
  obtain ⟨recorded, current, platform, called, continued⟩ := cut coins setup codec view failure allocation erased
    sign helper writer control initial before after previous next _ supported
  cases recorded with
  | fail error | div => simp [RegistrationNativePlatformServerCompletion.continueResult, StateT.run_pure] at continued
  | ok result => cases result with
    | Err prior => simp [RegistrationNativePlatformServerCompletion.continueResult, StateT.run_pure] at continued
    | Ok hashed =>
        have jointSupported : (.ok (.Ok hashed), (current, platform)) ∈ support
            ((RegistrationNativePlatformSourceSealTrace.joint
              (RegistrationNativePlatformSourceSealTrace.record coins setup codec view failure allocation erased helper initial)).run (before, previous)) := by
          change (.ok (.Ok hashed), (current, platform)) ∈ support
            ((fun result => (result.1.1, (result.1.2, result.2))) <$>
              ((RegistrationNativePlatformSourceSealTrace.record coins setup codec view failure allocation erased helper initial).run before).run previous)
          rw [support_map]
          exact ⟨((.ok (.Ok hashed), current), platform), called, rfl⟩
        exact ⟨hashed, current, platform, called,
          RegistrationNativePlatformSourceSealTrace.run coins setup codec view failure allocation erased helper initial hashed
            (before, previous) (current, platform) jointSupported, continued⟩

/-- Literal successful SourceSeal.build derives the moved-token SDK prefix and actual first-record trace on its same shared execution. -/
theorem source (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript) (reservePeer : StateT Platform ProbComp Bool)
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (handle : Nat) (application : Option (Slice U8)) (assigned : U64) (encoded : alloc.vec.Vec U8)
    (before after : RegistrationServerFrontendCompiler.State n) (previous next : Platform)
    (supported : ((.ok (some (assigned, encoded)), after), next) ∈ support
      (((RegistrationNativePlatformSourceSeal.build coins setup codec view failure allocation erased reservePeer sign helper writer
        handle application).run before).run previous)) :
    ∃ cut : RegistrationNativePlatformSdkBuildCut.Cut
      (RegistrationNativePlatformCompletionSdk.nativeAdHash coins)
      (RegistrationNativePlatformSourceBuild.pin coins) (StateT.lift reservePeer)
      (RegistrationNativePlatformCompletionSdk.nativePresent coins)
      (RegistrationNativePlatformSourceBuild.finishSource coins setup codec
        (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash coins setup codec erased) sign helper writer)
      handle application assigned encoded before after previous next,
    ∃ hashed current platform,
      ((.ok (.Ok hashed), current), platform) ∈ support
        (((RegistrationNativePlatformSourceSealTrace.record coins setup codec view failure allocation erased helper cut.initial).run cut.reserved.world).run cut.reservePlatform) ∧
      Nonempty (RegistrationNativePlatformRecordTrace.Trace
        (fun query => RegistrationNativePlatformSourceSealTrace.joint (RegistrationNativePlatformServerCompletion.records coins setup codec query))
        (fun request => RegistrationNativePlatformSourceSealTrace.joint (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation request))
        (fun transcript => RegistrationNativePlatformSourceSealTrace.joint (RegistrationNativePlatformSourceSeal.hash coins setup codec erased transcript))
        (fun request => RegistrationNativePlatformSourceSealTrace.joint (RegistrationNativePlatformSourceBuild.write helper request))
        cut.initial hashed (cut.reserved.world, cut.reservePlatform) (current, platform)) ∧
      ((.ok (.Ok cut.published), cut.completed), next) ∈ support
        (((afterRecord coins sign writer cut.current.control hashed).run current).run platform) := by
  obtain ⟨cut⟩ := RegistrationNativePlatformSdkBuildCut.build
    (RegistrationNativePlatformCompletionSdk.nativeAdHash coins)
    (RegistrationNativePlatformSourceBuild.pin coins) (StateT.lift reservePeer)
    (RegistrationNativePlatformCompletionSdk.nativePresent coins)
    (RegistrationNativePlatformSourceBuild.finishSource coins setup codec
      (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
      (RegistrationNativePlatformSourceSeal.hash coins setup codec erased) sign helper writer)
    handle application assigned encoded before after previous next supported
  obtain ⟨hashed, current, platform, called, trace, continued⟩ := successful coins setup codec view failure allocation erased
    sign helper writer cut.current.control cut.initial cut.published cut.reserved.world cut.completed cut.reservePlatform next cut.finishCalled
  exact ⟨cut, hashed, current, platform, called, trace, continued⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildCut.cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildCut.cut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildCut.successful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildCut.successful

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildCut.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildCut.source
