-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationGlobal

/-! Accepted-frame evidence tied to the actual transcript before that receive. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationTemporal
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal PqxdhRecordLiftInterface PqxdhRecordLiftFlat
open PqxdhRecordFactsOriginReplay
open PqxdhRecordFactsOriginHandles PqxdhRecordFactsOriginControl
open PqxdhRecordFactsOriginAccepted PqxdhRecordFactsOriginMonotone
open PqxdhRecordFactsOriginPublicationHistory PqxdhRecordFactsOriginPublicationNative
open PqxdhRecordLiftProtocolHistory (Safe Step)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Handle Receiver Entry Spec FullSpec FreshBounds)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- The actual accepted plaintext has an owned seal whose writer failed or whose frame appeared before this receive. -/
def AcceptedBefore (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n)
    (transcript : List Entry) (handle : Handle) (raw : Pqxdh.Bytes) (opened : RawCtxWholeOwner.Decrypted) : Prop :=
  KnownAt control handle ∨
    ∃ label, handleSlot control handle = some label.slot ∧ label.direction = !handleDirection handle ∧
      ∃ frame, codec.frameRead raw = some frame ∧
      ∃ entry ∈ (secret.keys label).1.successfulSeals, Matches frame entry ∧ entry.input.plaintext = opened.plaintext ∧
      ∃ sender, OwnsLabel control label sender ∧
        (codec.frameWrite frame = none ∨ PublishedBefore codec transcript sender frame)

/-- Exact before-receive dictionary evidence and current history supply the temporal accepted witness. -/
theorem accepted_history (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n) (transcript : List Entry)
    (history : History codec control secret transcript) (handle : Handle) (raw : Pqxdh.Bytes)
    (opened : RawCtxWholeOwner.Decrypted) (accepted : Accepted codec control secret handle raw opened) :
    AcceptedBefore codec control secret transcript handle raw opened := by
  rcases accepted with known | ⟨label, slot, direction, frame, decoded, entry, member, matched, plaintext⟩
  · exact Or.inl known
  · obtain ⟨sender, generated, owned, generatedMatch, outcome⟩ := history label entry member
    have same := matches_unique generated frame entry generatedMatch matched
    subst generated
    exact Or.inr ⟨label, slot, direction, frame, decoded, entry, member, matched, plaintext, sender, owned, outcome⟩

/-- Later source steps preserve the earlier receive prefix without extending it or replacing its witnesses. -/
theorem acceptedBefore_mono (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control next : PqxdhRecordLiftProtocol.Control n) (before after : CtxPrivate n)
    (progress : Step control next) (known : ∀ handle, KnownAt control handle → KnownAt next handle)
    (seals : ∀ label entry, entry ∈ (before.keys label).1.successfulSeals → entry ∈ (after.keys label).1.successfulSeals)
    (transcript : List Entry) (handle : Handle) (raw : Pqxdh.Bytes) (opened : RawCtxWholeOwner.Decrypted)
    (good : AcceptedBefore codec control before transcript handle raw opened) :
    AcceptedBefore codec next after transcript handle raw opened := by
  rcases good with good | ⟨label, slot, direction, frame, decoded, entry, member, matched, plaintext, sender, owned, outcome⟩
  · exact Or.inl (known handle good)
  · exact Or.inr ⟨label, handleSlot_step control next progress handle label.slot slot, direction,
      frame, decoded, entry, seals label entry member, matched, plaintext, sender,
      ownsLabel_step control next progress label sender owned, outcome⟩

/-- Every literal successful receive in this event carries its exact pre-event transcript witness. -/
def ReceivedBefore (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (control : PqxdhRecordLiftProtocol.Control n)
    (secret : CtxPrivate n) (transcript : List Entry) (event : Entry) : Prop :=
  ∀ receiver raw opened, event.received = some (receiver, raw, .Some opened) →
    ∃ handle, receivingHandle route receiver raw = some handle ∧
      AcceptedBefore codec control secret transcript handle raw opened

/-- Previously recorded receive evidence survives future state changes with its original prefix unchanged. -/
theorem receivedBefore_mono (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (control next : PqxdhRecordLiftProtocol.Control n)
    (before after : CtxPrivate n) (progress : Step control next)
    (known : ∀ handle, KnownAt control handle → KnownAt next handle)
    (seals : ∀ label entry, entry ∈ (before.keys label).1.successfulSeals → entry ∈ (after.keys label).1.successfulSeals)
    (transcript : List Entry) (event : Entry) (good : ReceivedBefore codec route control before transcript event) :
    ReceivedBefore codec route next after transcript event := by
  intro receiver raw opened received
  obtain ⟨handle, routed, accepted⟩ := good receiver raw opened received
  exact ⟨handle, routed, acceptedBefore_mono codec control next before after progress known seals
    transcript handle raw opened accepted⟩

/-- Actual native acceptance consults the before-receive dictionary and current transcript, then retains that witness in the poststate. -/
theorem native_receivedBefore (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (query : Spec.Domain) (before : NativeState n E) (safe : Safe before.1.2)
    (transcript : List Entry) (history : History codec before.1.2 before.2 transcript)
    (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env query).run before)) :
    ReceivedBefore codec route result.2.1.2 result.2.2 transcript ⟨.inl query, result.1⟩ := by
  intro receiver raw opened received
  obtain ⟨handle, routed, accepted⟩ := native_received_before modes ideal replace setup codec route
    readback env query before safe result supported receiver raw opened received
  refine ⟨handle, routed, acceptedBefore_mono codec before.1.2 result.2.1.2 before.2 result.2.2
    (native_step modes replace setup codec route env query before safe result supported) ?_
    (native_grows modes ideal replace setup codec route env query before result supported).seals
    transcript handle raw opened (accepted_history codec before.1.2 before.2 transcript history handle raw opened accepted)⟩
  exact fun other known => nativeImpl_known modes replace setup codec route env other query before known result supported

/-- A complete ledger command's received record refers to its literal pre-command transcript. -/
theorem full_receivedBefore (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E) (safe : Safe before.2.1.2)
    (history : History codec before.2.1.2 before.2.2 before.1.transcript)
    (result : FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((fullImpl modes replace setup codec route env serverKid bounds query).run before)) :
    ReceivedBefore codec route result.2.2.1.2 result.2.2.2 before.1.transcript ⟨query, result.1⟩ := by
  rcases query with forwarded | secrecy
  · rw [fullImpl_run, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query,
      StateT.run_map, support_map] at reached
    obtain ⟨nativeResult, nativeReached, rfl⟩ := reached
    exact native_receivedBefore modes ideal replace setup codec route readback env forwarded before.2 safe
      before.1.transcript history nativeResult nativeReached
  · cases secrecy <;> simp [ReceivedBefore, Entry.received]

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationTemporal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationTemporal.accepted_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationTemporal.accepted_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationTemporal.acceptedBefore_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationTemporal.acceptedBefore_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationTemporal.receivedBefore_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationTemporal.receivedBefore_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationTemporal.native_receivedBefore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationTemporal.native_receivedBefore

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationTemporal.full_receivedBefore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationTemporal.full_receivedBefore
