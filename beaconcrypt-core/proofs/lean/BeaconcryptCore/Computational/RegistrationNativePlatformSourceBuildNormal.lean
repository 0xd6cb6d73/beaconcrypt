-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal
import BeaconcryptCore.PanicFreedom.RegistrationPublication
import BeaconcryptCore.PanicFreedom.RegistrationTrivial
import BeaconcryptCore.PanicFreedom.PeerOwnership
/-! Normality of the actual first-record and response publication controller is derived from the extracted Core getter/resume totality and individual source leaf contracts. All optional crypto, allocation, serialization and installation rejection replies remain ordinary outcomes with their full shared poststate. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildNormal
variable {S P A B Encoded : Type}
def Normal (work : (StateT S (StateT P ProbComp)) (RustM A)) : Prop :=
  ∀before previous result,result∈support ((work.run before).run previous) →∃value,result.1.1=.ok value
private theorem pure_normal (value : A) : Normal (S:=S) (P:=P) (pure (.ok value)) := by
  intro before previous result reached
  simp only [StateT.run_pure,support_pure,Set.mem_singleton_iff] at reached
  subst result
  exact ⟨value,rfl⟩
private theorem bind_normal (work : (StateT S (StateT P ProbComp)) A) (next : A→(StateT S (StateT P ProbComp)) (RustM B))
    (safe : ∀value,Normal (next value)) : Normal (work >>= next) := by
  intro before previous result reached
  simp only [StateT.run_bind,mem_support_bind_iff] at reached
  obtain ⟨middle,called,continued⟩ := reached
  exact safe middle.1.1 middle.1.2 middle.2 result continued
private theorem bind_ok (work : (StateT S (StateT P ProbComp)) (RustM A)) (safe : Normal work) (next : RustM A→(StateT S (StateT P ProbComp)) (RustM B))
    (continued : ∀value,Normal (next (.ok value))) : Normal (work >>= next) := by
  intro before previous result reached
  simp only [StateT.run_bind,mem_support_bind_iff] at reached
  obtain ⟨middle,called,finished⟩ := reached
  obtain ⟨value,normal⟩ := safe before previous middle called
  rw [normal] at finished
  exact continued value middle.1.2 middle.2 result finished
namespace Publication
open RegistrationNativePlatformServerPublication
variable (impl : QueryImpl RegistrationSigningShared.Spec (StateT S (StateT P ProbComp)))
variable (encode : registration.SignedResponseView→(StateT S (StateT P ProbComp)) (RustM (core.option.Option Encoded)))
variable (encoded : ∀view,Normal (encode view))
include encoded in
private theorem ready (pending : registration.ServerResponseReady) : Normal (RegistrationNativePlatformServerPublication.ready encode pending) := by
  obtain ⟨view,message⟩ := BeaconcryptCore.PanicFreedom.RegistrationTrivial.ServerResponseReady_message_total pending
  unfold RegistrationNativePlatformServerPublication.ready
  rw [message]
  dsimp only [continueWith]
  apply bind_ok _ (encoded view)
  intro optional
  obtain ⟨result,published⟩ := BeaconcryptCore.PanicFreedom.RegistrationTrivial.ServerResponseReady_publish_total pending optional
  simpa only [bind_tc_ok,published] using pure_normal result
include encoded in
private theorem signing (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.ServerResponseSigning) : Normal (RegistrationNativePlatformServerPublication.signing impl encode payload digest pending) := by
  obtain ⟨request,requested⟩ := BeaconcryptCore.PanicFreedom.RegistrationTrivial.ServerResponseSigning_request_total pending
  unfold RegistrationNativePlatformServerPublication.signing
  rw [requested]
  dsimp only [continueWith]
  apply bind_normal
  intro signature
  obtain ⟨next,resumed⟩ := BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerResponseSigning_resume_total pending signature
  rw [resumed]
  cases next with
  | Err previous => exact pure_normal _
  | Ok selected => exact ready encode encoded selected
include encoded in
theorem program (pending : registration.ServerResponseHash) : Normal (RegistrationNativePlatformServerPublication.program impl encode pending) := by
  obtain ⟨request,requested⟩ := BeaconcryptCore.PanicFreedom.RegistrationTrivial.ServerResponseHash_request_total pending
  unfold RegistrationNativePlatformServerPublication.program
  rw [requested]
  dsimp only [continueWith]
  apply bind_normal
  intro digest
  obtain ⟨next,resumed⟩ := BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerResponseHash_resume_total pending (.Some (RegistrationAuthenticationShared.digestArray digest))
  rw [resumed]
  cases next with
  | Err previous => exact pure_normal _
  | Ok selected => exact signing impl encode encoded _ _ selected
end Publication
namespace Record
open RegistrationNativePlatformServerRecord
variable (record : QueryImpl RegistrationRecordPrimitives.Spec (StateT S (StateT P ProbComp)))
variable (sealing : record_effects.AeadSealRequest→(StateT S (StateT P ProbComp)) (RustM (core.option.Option (Slice U8×Std.Array U8 16#usize))))
variable (write : record_effects.RecordWriteRequest→(StateT S (StateT P ProbComp)) (RustM (core.option.Option (Slice U8))))
variable (sealed : ∀request,Normal (sealing request)) (written : ∀request,Normal (write request))
include written in
private theorem fromWrite (pending : registration.ServerRecordWrite) : Normal (RegistrationNativePlatformServerRecord.fromWrite write pending) := by
  obtain ⟨request,requested⟩ := BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerRecordWrite_request_total pending
  unfold RegistrationNativePlatformServerRecord.fromWrite
  rw [requested]
  dsimp only [continueWith]
  apply bind_ok _ (written request)
  intro optional
  obtain ⟨result,resumed⟩ := BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerRecordWrite_resume_total pending optional
  simpa only [bind_tc_ok,resumed] using pure_normal result
include written in
private theorem fromCommitment (pending : registration.ServerRecordCommitment) : Normal (RegistrationNativePlatformServerRecord.fromCommitment record write pending) := by
  obtain ⟨transcript,requested⟩ := BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerRecordCommitment_transcript_total pending
  unfold RegistrationNativePlatformServerRecord.fromCommitment
  rw [requested]
  dsimp only [continueWith]
  apply bind_normal
  intro digest
  obtain ⟨next,resumed⟩ := BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerRecordCommitment_resume_total pending digest
  rw [resumed]
  cases next with
  | Err previous => exact pure_normal _
  | Ok selected => exact fromWrite write written selected
include sealed written in
private theorem fromAead (pending : registration.ServerRecordAead) : Normal (RegistrationNativePlatformSourceRecord.fromAead record sealing write pending) := by
  obtain ⟨request,requested⟩ := BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerRecordAead_request_total pending
  unfold RegistrationNativePlatformSourceRecord.fromAead
  rw [requested]
  dsimp only [continueWith]
  apply bind_ok _ (sealed request)
  intro optional
  obtain ⟨next,resumed⟩ := BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerRecordAead_resume_total pending optional
  simp only [bind_tc_ok,resumed]
  cases next with
  | Err previous => exact pure_normal _
  | Ok selected => exact fromCommitment record write written selected
include sealed written in
private theorem fromRatchet (pending : registration.ServerInitialSeal) : Normal (RegistrationNativePlatformSourceRecord.fromRatchet record sealing write pending) := by
  obtain ⟨request,requested⟩ := BeaconcryptCore.PanicFreedom.RegistrationTrivial.ServerInitialSeal_request_total pending
  unfold RegistrationNativePlatformSourceRecord.fromRatchet
  rw [requested]
  dsimp only [continueWith]
  apply bind_normal
  intro reply
  obtain ⟨next,resumed⟩ := BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerInitialSeal_resume_total pending reply
  rw [resumed]
  cases next with
  | Err previous => exact pure_normal _
  | Ok selected => exact fromAead record sealing write sealed written selected
include sealed written in
theorem fromInitial (pending : registration.ServerInitialKdf) : Normal (RegistrationNativePlatformSourceRecord.fromInitial record sealing write pending) := by
  obtain ⟨request,requested⟩ := BeaconcryptCore.PanicFreedom.RegistrationTrivial.ServerInitialKdf_request_total pending
  unfold RegistrationNativePlatformSourceRecord.fromInitial
  rw [requested]
  dsimp only [continueWith]
  apply bind_normal
  intro reply
  obtain ⟨next,resumed⟩ := BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerInitialKdf_resume_total pending reply
  rw [resumed]
  cases next with
  | Err previous => exact pure_normal _
  | Ok selected => exact fromRatchet record sealing write sealed written selected
end Record
namespace Completion
variable {n : Nat}
variable (record : QueryImpl RegistrationRecordPrimitives.Spec (StateT S (StateT P ProbComp)))
variable (sealing : record_effects.AeadSealRequest→StateT S (StateT P ProbComp) (RustM (core.option.Option (Slice U8×Std.Array U8 16#usize))))
variable (write : record_effects.RecordWriteRequest→StateT S (StateT P ProbComp) (RustM (core.option.Option (Slice U8))))
variable (sign : QueryImpl RegistrationSigningShared.Spec (StateT S (StateT P ProbComp)))
variable (capability : QueryImpl (PqxdhRecordLiftInterface.CapabilitySpec n) (StateT S (StateT P ProbComp)))
variable (encode : registration.SignedResponseView→StateT S (StateT P ProbComp) (RustM (core.option.Option Encoded)))
variable (sealed : ∀request,Normal (sealing request)) (written : ∀request,Normal (write request))
variable (encoded : ∀view,Normal (encode view))
private theorem install (control : pqxdh.ServerState) (published : registration.PublishedServerResponse Encoded) :
    Normal (RegistrationNativePlatformServerCompletion.installWith capability control published) := by
  obtain ⟨result,began⟩ := BeaconcryptCore.PanicFreedom.PeerOwnership.begin_peer_insert_total control published
  unfold RegistrationNativePlatformServerCompletion.installWith
  rw [began]
  cases result with
  | Err previous => exact pure_normal _
  | Ok pending =>
    obtain ⟨keyId,requested⟩ := BeaconcryptCore.PanicFreedom.PeerOwnership.PeerInsert_request_total pending
    obtain ⟨parts,partsEq⟩ := BeaconcryptCore.PanicFreedom.PeerOwnership.PeerInsert_into_parts_total pending
    dsimp only [RegistrationNativePlatformServerCompletion.continueResult]
    rw [requested]
    dsimp only [RegistrationNativePlatformServerCompletion.continueWith]
    rw [partsEq]
    dsimp only [RegistrationNativePlatformServerCompletion.continueWith]
    apply bind_normal
    intro inserted
    obtain ⟨result,finished⟩ := BeaconcryptCore.PanicFreedom.PeerOwnership.PublicationFinish_finish_total parts.2 inserted
    simpa only [finished] using pure_normal result
include sealed written encoded in
theorem fromInitial (erased : commitment.CommitmentTranscript) (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    Normal (RegistrationNativePlatformSourceCompletion.fromInitialSource record sealing
      (fun transcript=>(fun digest=>RustM.ok (digest,erased)) <$>record (.hash transcript))
      write sign capability encode control pending) := by
  unfold RegistrationNativePlatformSourceCompletion.fromInitialSource
  rw [RegistrationNativePlatformSourceRecord.fromInitialWithHash_native]
  apply bind_ok _ (Record.fromInitial record sealing write sealed written pending)
  intro result
  cases result with
  | Err previous => exact pure_normal _
  | Ok response =>
    dsimp only [RegistrationNativePlatformServerCompletion.continueResult]
    apply bind_ok _ (Publication.program sign encode encoded response)
    intro result
    cases result with
    | Err previous => exact pure_normal _
    | Ok published => exact install capability control published
end Completion
namespace Sdk
variable {n : Nat}
variable (finish : RegistrationNativePlatformCompletionSdk.Completion n (StateT P ProbComp) Encoded)
variable (finished : ∀control pending,Normal (finish control pending))
include finished in
private theorem initial (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    Normal (RegistrationNativePlatformCompletionSdk.fromInitial finish control pending) := by
  intro before previous result reached
  unfold RegistrationNativePlatformCompletionSdk.fromInitial at reached
  simp only [StateT.run_bind,mem_support_bind_iff] at reached
  obtain ⟨middle,called,continued⟩ := reached
  change middle∈support (((fun localResult=>(localResult.1,{before with world:=localResult.2})) <$>
    (finish control pending).run before.world).run previous) at called
  rw [StateT.run_map,support_map] at called
  obtain ⟨localResult,localCalled,same⟩ := called
  obtain ⟨value,normal⟩ := finished control pending before.world previous localResult localCalled
  subst middle
  rw [normal] at continued
  cases value <;>
    simp only [RegistrationNativePlatformServerSdk.commit,StateT.run] at continued <;>
    exact ⟨_,congrArg (fun output=>output.1.1) continued⟩
variable (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT P ProbComp) Bool)
variable (present : U64→StateT (RegistrationServerFrontendCompiler.State n) (StateT P ProbComp) Bool)
include finished in
private theorem afterOccupancy (control : pqxdh.ServerState) (pending : peer.CompletionLookup) (occupied : Bool) :
    Normal (RegistrationNativePlatformCompletionSdk.afterOccupancy reserve finish control pending occupied) := by
  obtain ⟨result,resumed⟩ := BeaconcryptCore.PanicFreedom.PeerOwnership.CompletionLookup_resume_total pending occupied
  unfold RegistrationNativePlatformCompletionSdk.afterOccupancy
  rw [resumed]
  cases result with
  | Err previous => exact pure_normal _
  | Ok selected =>
    apply bind_normal
    intro admitted
    cases admitted with
    | false => exact pure_normal _
    | true => exact initial finish finished control selected
include finished in
private theorem afterPin (control : pqxdh.ServerState) (token : peer.ConsumedRegistration) (application : Slice U8)
    (pin : core.option.Option session.ServerAuthenticationPin) :
    Normal (RegistrationNativePlatformCompletionSdk.afterPin reserve present finish control token application (.ok pin)) := by
  unfold RegistrationNativePlatformCompletionSdk.afterPin
  cases pin with
  | none => exact pure_normal _
  | some pin =>
    dsimp only
    obtain ⟨result,began⟩ := BeaconcryptCore.PanicFreedom.PeerOwnership.begin_completion_lookup_total control pin token application
    rw [began]
    cases result with
    | Err previous => exact pure_normal _
    | Ok pending =>
      dsimp only
      obtain ⟨keyId,requested⟩ := BeaconcryptCore.PanicFreedom.PeerOwnership.CompletionLookup_request_total pending
      rw [requested]
      dsimp only
      split
      · apply bind_normal
        intro occupied
        exact afterOccupancy finish finished reserve control pending occupied
      · exact pure_normal _
include finished in
theorem complete
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (StateT P ProbComp) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (pinned : Normal pin) (token : peer.ConsumedRegistration) (application : Slice U8) :
    Normal (RegistrationNativePlatformCompletionSdk.complete pin reserve present finish token application) := by
  unfold RegistrationNativePlatformCompletionSdk.complete
  apply bind_normal
  intro before
  apply bind_ok _ pinned
  intro value
  exact afterPin finish finished reserve present before.control token application value
end Sdk
variable {n : Nat} {I KemSK Reader Response E : Type} {base : OracleSpec I}
theorem pin (coins : QueryImpl unifSpec (StateT P ProbComp)) :
    Normal (RegistrationNativePlatformSourceBuild.pin (n:=n) coins) := by
  intro before previous result reached
  change result∈support (((fun localResult : RegistrationNativeServerPinRecompute.PinReply×PqxdhRecordLiftWorld.State n =>
    (localResult.1,{before with world:={before.world with world:=(localResult.2,before.world.world.2)}})) <$>
    simulateQ coins ((RegistrationNativeServerPinRecompute.native before.pin.binding before.pin.public_key).run before.world.world.1)).run previous) at reached
  rw [RegistrationNativeServerPinRecompute.native_run] at reached
  simp only [bind_pure_comp,simulateQ_map,Functor.map_map] at reached
  change result∈support (((fun hashed=>
    (.ok (.Some (⟨before.pin.binding,before.pin.public_key,RegistrationAuthenticationShared.digestArray hashed.1⟩ : session.ServerAuthenticationPin)),
    {before with world:={before.world with world:=(hashed.2,before.world.world.2)}})) <$>
    simulateQ coins ((PqxdhRecordLiftWorld.effects (.inr (.hash (PqxdhRefinement.absBytes before.pin.public_key)))).run before.world.world.1)).run previous) at reached
  rw [StateT.run_map,support_map] at reached
  obtain ⟨hashed,called,same⟩ := reached
  subst result
  exact ⟨_,rfl⟩
theorem finishSource
    (coins : QueryImpl unifSpec (StateT P ProbComp)) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (sealing : record_effects.AeadSealRequest→StateT (RegistrationServerRootCompiler.Local n) (StateT P ProbComp) (RustM (core.option.Option (Slice U8×Std.Array U8 16#usize))))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (sealed : ∀request,Normal (sealing request))
    (written : ∀request,Normal (RegistrationNativePlatformSourceBuild.write (n:=n) helper request))
    (encoded : ∀view,Normal (RegistrationNativePlatformSourceBuild.encode (n:=n) writer view))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    Normal (RegistrationNativePlatformSourceBuild.finishSource coins setup codec sealing
      (RegistrationNativePlatformSourceSeal.hash coins setup codec erased) sign helper writer control pending) := by
  have hashEq : RegistrationNativePlatformSourceSeal.hash (n:=n) (Auxiliary:=RegistrationServerRoleBackend.State) coins setup codec erased=
      fun transcript=>(fun digest=>RustM.ok (digest,erased)) <$>
        RegistrationNativePlatformServerCompletion.records coins setup codec (.hash transcript) := by
    funext transcript
    exact bind_pure_comp _ _
  unfold RegistrationNativePlatformSourceBuild.finishSource
  rw [hashEq]
  exact Completion.fromInitial _ sealing _ _ _ _ sealed written encoded erased control pending

theorem completeSource
    (coins : QueryImpl unifSpec (StateT P ProbComp)) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (sealing : record_effects.AeadSealRequest→StateT (RegistrationServerRootCompiler.Local n) (StateT P ProbComp) (RustM (core.option.Option (Slice U8×Std.Array U8 16#usize))))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (sealed : ∀request,Normal (sealing request))
    (written : ∀request,Normal (RegistrationNativePlatformSourceBuild.write (n:=n) helper request))
    (encoded : ∀view,Normal (RegistrationNativePlatformSourceBuild.encode (n:=n) writer view))
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT P ProbComp) Bool)
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    Normal (RegistrationNativePlatformCompletionSdk.complete (RegistrationNativePlatformSourceBuild.pin coins)
      reserve (RegistrationNativePlatformCompletionSdk.nativePresent coins)
      (RegistrationNativePlatformSourceBuild.finishSource coins setup codec sealing
        (RegistrationNativePlatformSourceSeal.hash coins setup codec erased) sign helper writer) token application) := by
  exact Sdk.complete _ (fun control pending=>finishSource coins setup codec sealing erased sign helper writer sealed written encoded control pending)
    reserve _ _ (pin coins) token application
end BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildNormal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildNormal.Publication.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildNormal.Publication.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildNormal.Record.fromInitial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildNormal.Record.fromInitial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildNormal.Completion.fromInitial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildNormal.Completion.fromInitial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildNormal.Sdk.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildNormal.Sdk.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildNormal.pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildNormal.pin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildNormal.finishSource' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildNormal.finishSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildNormal.completeSource' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildNormal.completeSource
