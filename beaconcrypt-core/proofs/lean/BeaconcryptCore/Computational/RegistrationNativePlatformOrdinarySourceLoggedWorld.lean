-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceReceiptOwner
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceJournal
/-! The literal extracted outer send and all native children retain every reached writer frame, primitive poststate and platform poststate. Source Rust outcomes are proved normal before taking the native optional reply. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceLoggedWorld
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorld (Primitive)
open RegistrationNativePlatformOrdinarySourceWorld (AeadLength)
open RegistrationNativePlatformOrdinarySourceJournal
  (State native implementation kdf aead hash reserveNative receipt functional writer_source)
open RegistrationNativePlatformOrdinarySourceRepresentation (typed)
variable {Platform E I KemSK Reader Response : Type} {base : OracleSpec I}
/-- The typed native four-child service has the exact dynamic source writer and one reached-writer analysis receipt, even when capacity refuses before reservation. -/
theorem typed_queries (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) :
    RegistrationNativePlatformOrdinarySourceReceipt.native (aead setup codec reserve) (hash setup codec reserve)
      (reserveNative reserve) receipt = typed (implementation setup codec reserve) := by
  funext query
  rcases query with input | (bytes | frame)
  · rfl
  · rfl
  · exact writer_source setup codec reserve frame

private theorem raw_queries (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) :
    RegistrationNativePlatformOrdinarySourceRepresentation.model (kdf setup codec reserve) (implementation setup codec reserve) =
      native setup codec reserve ∘ₛ RawCtxMixedOwner.sendAdapter := by
  funext query
  rcases query with request | input
  · simp only [RegistrationNativePlatformOrdinarySourceRepresentation.model, kdf, QueryImpl.apply_compose,
      RawCtxMixedOwner.sendAdapter, RawCtxSourceSeal.nativeAdapter, RawCtxMixedOwner.sendLift, simulateQ_spec_query]
  · simp only [RegistrationNativePlatformOrdinarySourceRepresentation.model, QueryImpl.apply_compose,
      RawCtxMixedOwner.sendAdapter, RawCtxSourceSeal.nativeAdapter]
    have inclusion : RawCtxMixedOwner.sendLift ∘ₛ RawCtxSourceSeal.sealLift = RegistrationNativePlatformOrdinaryWorldSeal.inject := by
      funext request
      rcases request with request | (bytes | frame)
      all_goals simp only [QueryImpl.apply_compose, RawCtxMixedOwner.sendLift, RawCtxSourceSeal.sealLift,
        RegistrationNativePlatformOrdinaryWorldSeal.inject, simulateQ_spec_query]
    rw [← QueryImpl.simulateQ_compose RawCtxMixedOwner.sendLift RawCtxSourceSeal.sealLift, inclusion]
    simp only [implementation, QueryImpl.simulateQ_compose]

private theorem typed_model (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) :
    RegistrationNativePlatformOrdinarySourceReceiptOwner.model (kdf setup codec reserve) (aead setup codec reserve) (hash setup codec reserve)
      (reserveNative reserve) receipt = RegistrationNativePlatformOrdinarySourceRepresentation.typedModel
        (kdf setup codec reserve) (implementation setup codec reserve) := by
  funext query
  cases query with
  | inl request => rfl
  | inr input =>
      unfold RegistrationNativePlatformOrdinarySourceReceiptOwner.model RegistrationNativePlatformOrdinarySourceRepresentation.typedModel
      dsimp only
      rw [typed_queries, QueryImpl.simulateQ_compose]

/-- Actual outer send, detached sealing, commitment writeback and source Frame3 writing share the concrete private World and one public platform state. Ciphertext representability follows only from the narrow primitive length law and the source Slice bound. -/
theorem source_owner [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (length : AeadLength setup.source.crypto)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    {Metadata : Type} (owner : RawCtxWholeOwner.OwnerState Metadata)
    (plaintext : Slice U8) (sender : U64) (associated : Std.Array U8 281#usize)
    (sameAD : owner.owner.associatedData = PqxdhRefinement.absBytes associated) :
    (RegistrationNativePlatformOrdinarySourceReceiptOwner.ownerResult owner ∘ RegistrationNativePlatformOrdinarySourceReceipt.abstractOutput) <$>
      simulateQ (RegistrationNativePlatformOrdinarySourceReceipt.callbacks view failure (kdf setup codec reserve)
        (aead setup codec reserve) (hash setup codec reserve) (reserveNative reserve) erased receipt)
        (AdapterRecordStatefulSend.program owner.owner.kernel
          ⟨plaintext, .None, associated, owner.owner.expectedSender, sender, .Frame⟩) =
      .ok <$> simulateQ (native setup codec reserve)
        (simulateQ RawCtxMixedOwner.sendAdapter
          ((RawCtxSourceSend.sendOwner sender (TranscriptAuthParts.absSlice plaintext)).run owner)) := by
  rw [RegistrationNativePlatformOrdinarySourceReceiptOwner.source_owner view converted failure
    (kdf setup codec reserve) (aead setup codec reserve) (hash setup codec reserve) (reserveNative reserve) erased
    owner plaintext sender associated sameAD receipt, typed_model,
    RegistrationNativePlatformOrdinarySourceRepresentation.owner_native (kdf setup codec reserve)
      (implementation setup codec reserve) (functional setup codec reserve length), raw_queries,
    QueryImpl.simulateQ_compose]


def total {Metadata : Type} (before : RawCtxWholeOwner.OwnerState Metadata) :
    RustM (Option RawCtxSourceSend.Encrypted × RawCtxWholeOwner.OwnerState Metadata) →
      Option RawCtxSourceSend.Encrypted × RawCtxWholeOwner.OwnerState Metadata
  | .ok value => value
  | .fail _ | .div => (none,before)
noncomputable def owner [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript)
    {Metadata : Type} (before : RawCtxWholeOwner.OwnerState Metadata)
    (plaintext : Slice U8) (sender : U64) (associated : Array U8 281#usize) :
    StateT State (StateT Platform ProbComp) (Option RawCtxSourceSend.Encrypted × RawCtxWholeOwner.OwnerState Metadata) :=
  (total before ∘ RegistrationNativePlatformOrdinarySourceReceiptOwner.ownerResult before ∘
    RegistrationNativePlatformOrdinarySourceReceipt.abstractOutput) <$>
      simulateQ (RegistrationNativePlatformOrdinarySourceReceipt.callbacks view failure (kdf setup codec reserve)
        (aead setup codec reserve) (hash setup codec reserve) (reserveNative reserve) erased receipt)
        (AdapterRecordStatefulSend.program before.owner.kernel
          ⟨plaintext,.None,associated,before.owner.expectedSender,sender,.Frame⟩)
/-- The source totalization consumes only outcomes already proved normal by the actual controller and narrow primitive contracts. -/
theorem owner_source [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (length : AeadLength setup.source.crypto)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    {Metadata : Type} (before : RawCtxWholeOwner.OwnerState Metadata)
    (plaintext : Slice U8) (sender : U64) (associated : Array U8 281#usize)
    (sameAD : before.owner.associatedData=PqxdhRefinement.absBytes associated) :
    owner setup codec reserve view failure erased before plaintext sender associated =
      simulateQ (native setup codec reserve)
        (simulateQ RawCtxMixedOwner.sendAdapter
          ((RawCtxSourceSend.sendOwner sender (TranscriptAuthParts.absSlice plaintext)).run before)) := by
  have same := congrArg (fun work => total before <$> work)
    (source_owner setup codec reserve length view converted failure erased before plaintext sender associated sameAD)
  simpa only [owner,Functor.map_map,Function.comp_def,total,id_map'] using same
/-- Source execution retains the exact original writer journal even when publication is refused. -/
theorem owner_logged [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (length : AeadLength setup.source.crypto)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    {Metadata : Type} (before : RawCtxWholeOwner.OwnerState Metadata)
    (plaintext : Slice U8) (sender : U64) (associated : Array U8 281#usize)
    (sameAD : before.owner.associatedData=PqxdhRefinement.absBytes associated)
    (primitive : Primitive) (frames : PqxdhRecordLiftLoggedAdapters.Frames) :
    (owner setup codec reserve view failure erased before plaintext sender associated).run (primitive,frames) =
      PqxdhRecordLiftLoggedAdapters.swapResult <$>
        (simulateQ (RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve)
          ((simulateQ PqxdhDeploymentNative.frameLog
            (simulateQ RawCtxMixedOwner.sendAdapter
              ((RawCtxSourceSend.sendOwner sender (TranscriptAuthParts.absSlice plaintext)).run before))).run frames)).run primitive := by
  rw [owner_source setup codec reserve length view converted failure erased before plaintext sender associated sameAD]
  exact RegistrationNativePlatformOrdinaryLogged.program_source _ _ _ _
end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceLoggedWorld

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceLoggedWorld.typed_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceLoggedWorld.typed_queries

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceLoggedWorld.source_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceLoggedWorld.source_owner

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceLoggedWorld.owner_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceLoggedWorld.owner_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceLoggedWorld.owner_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceLoggedWorld.owner_logged
