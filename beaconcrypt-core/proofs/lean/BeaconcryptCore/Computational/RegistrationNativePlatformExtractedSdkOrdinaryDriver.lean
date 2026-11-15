-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicOrdinaryBeacon
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceLoggedWorld
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryDriver
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open PqxdhServerAuthExperiment (Setup Codec)
variable {Platform E I KemSK Reader Response : Type} {base : OracleSpec I}
abbrev State := RegistrationNativePlatformOrdinarySourceJournal.State
abbrev M (Platform : Type) := StateT State (StateT Platform ProbComp)

noncomputable def callbacks [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) :
    QueryImpl AdapterRecordSendRequestMonad.Spec (M Platform) :=
  RegistrationNativePlatformOrdinarySourceReceipt.callbacks view failure
    (RegistrationNativePlatformOrdinarySourceJournal.kdf setup codec reserve)
    (RegistrationNativePlatformOrdinarySourceJournal.aead setup codec reserve)
    (RegistrationNativePlatformOrdinarySourceJournal.hash setup codec reserve)
    (RegistrationNativePlatformOrdinarySourceJournal.reserveNative reserve) erased
    RegistrationNativePlatformOrdinarySourceJournal.receipt

noncomputable def send [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (context : record_effects.SealFrameContext) : M Platform (RustM AdapterRecordStatefulSend.Result) :=
  AdapterRecordStatefulSend.execute (callbacks setup codec reserve view failure erased) kernel context

def sendReply (reply : core.option.Option beaconcrypt_record_send.shared.Encrypted) :
    Option RawCtxSourceSend.Encrypted :=
  _root_.Option.map (fun record => ⟨TranscriptAuthParts.absSlice record.ciphertext,record.key_id,record.seq⟩) reply

theorem send_projection {Metadata : Type} (owner : RawCtxWholeOwner.OwnerState Metadata)
    (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (reply : core.option.Option beaconcrypt_record_send.shared.Encrypted) :
    RegistrationNativePlatformOrdinarySourceReceiptOwner.ownerResult owner
      (RegistrationNativePlatformOrdinarySourceReceipt.abstractOutput (.ok (kernel,reply))) =
        .ok (sendReply reply,{owner with owner := {owner.owner with kernel := kernel}}) := by
  cases reply <;> rfl

theorem send_native [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (view : RegistrationNativePlatformSourceSeal.KeyView)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    {Metadata : Type} (owner : RawCtxWholeOwner.OwnerState Metadata)
    (plaintext : Slice U8) (sender : U64) (associated : Array U8 151#usize)
    (sameAD : owner.owner.associatedData = PqxdhRefinement.absBytes associated) :
    (RegistrationNativePlatformOrdinarySourceReceiptOwner.ownerResult owner ∘
      RegistrationNativePlatformOrdinarySourceReceipt.abstractOutput) <$>
      send setup codec reserve view failure erased owner.owner.kernel
        ⟨plaintext,.None,associated,owner.owner.expectedSender,sender,.Frame⟩ =
    .ok <$> simulateQ (RegistrationNativePlatformOrdinarySourceJournal.native setup codec reserve)
      (simulateQ RawCtxMixedOwner.sendAdapter
        ((RawCtxSourceSend.sendOwner sender (TranscriptAuthParts.absSlice plaintext)).run owner)) := by
  unfold send
  rw [← AdapterRecordStatefulSend.interpreted]
  exact RegistrationNativePlatformOrdinarySourceLoggedWorld.source_owner setup codec reserve length view converted
    failure erased owner plaintext sender associated sameAD


theorem send_normal [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (view : RegistrationNativePlatformSourceSeal.KeyView)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    {Metadata : Type} (owner : RawCtxWholeOwner.OwnerState Metadata)
    (plaintext : Slice U8) (sender : U64) (associated : Array U8 151#usize)
    (sameAD : owner.owner.associatedData = PqxdhRefinement.absBytes associated)
    (before after : State) (previous next : Platform) (reply : RustM AdapterRecordStatefulSend.Result)
    (supported : ((reply,after),next) ∈ support
      (((send setup codec reserve view failure erased owner.owner.kernel
        ⟨plaintext,.None,associated,owner.owner.expectedSender,sender,.Frame⟩).run before).run previous)) :
    ∃ value, reply = .ok value := by
  let project := RegistrationNativePlatformOrdinarySourceReceiptOwner.ownerResult owner ∘
    RegistrationNativePlatformOrdinarySourceReceipt.abstractOutput
  let native := simulateQ (RegistrationNativePlatformOrdinarySourceJournal.native setup codec reserve)
    (simulateQ RawCtxMixedOwner.sendAdapter
      ((RawCtxSourceSend.sendOwner sender (TranscriptAuthParts.absSlice plaintext)).run owner))
  have equality := congrArg (fun work => (work.run before).run previous)
    (send_native setup codec reserve length view converted failure erased owner plaintext sender associated sameAD)
  have closed :
      (fun result : (RustM AdapterRecordStatefulSend.Result ×State) ×Platform =>
        ((project result.1.1,result.1.2),result.2)) <$>
        (((send setup codec reserve view failure erased owner.owner.kernel
          ⟨plaintext,.None,associated,owner.owner.expectedSender,sender,.Frame⟩).run before).run previous) =
      (fun result => ((.ok result.1.1,result.1.2),result.2)) <$> (native.run before).run previous := by
    simpa only [StateT.run_map,Functor.map_map] using equality
  have possible : ((project reply,after),next) ∈ support
      ((fun result => ((.ok result.1.1,result.1.2),result.2)) <$> (native.run before).run previous) := by
    rw [← closed,support_map]
    exact ⟨((reply,after),next),supported,rfl⟩
  rw [support_map] at possible
  obtain ⟨reached,_supported,same⟩ := possible
  have normal := (congrArg (fun result => result.1.1) same).symm
  cases reply with
  | ok value => exact ⟨value,rfl⟩
  | fail error =>
      change RustM.fail error = .ok reached.1.1 at normal
      cases normal
  | div =>
      change RustM.div = .ok reached.1.1 at normal
      cases normal

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryDriver

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryDriver.send_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryDriver.send_projection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryDriver.send_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryDriver.send_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryDriver.send_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryDriver.send_normal
