-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationNative

/-! Dictionary evidence relative to the actual current transcript transcript. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationHistory
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal PqxdhRecordLiftInterface PqxdhRecordLiftFlat
open PqxdhRecordFactsOriginReplay PqxdhRecordFactsOriginHandles PqxdhRecordFactsOriginPublicationNative
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Handle Entry Spec)
open PqxdhRecordLiftProtocolHistory (Step)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- Every current dictionary entry has either failed its literal writer or been published in this actual transcript. -/
def History (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n) (transcript : List Entry) : Prop :=
  ∀ label entry, entry ∈ (secret.keys label).1.successfulSeals →
    ∃ handle frame, OwnsLabel control label handle ∧ Matches frame entry ∧
      (codec.frameWrite frame = none ∨ PublishedBefore codec transcript handle frame)

/-- A previously returned ciphertext remains in every appended transcript transcript. -/
theorem published_append (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (transcript suffix : List Entry) (handle : Handle) (frame : PqxdhDeploymentNative.Frame)
    (published : PublishedBefore codec transcript handle frame) :
    PublishedBefore codec (transcript ++ suffix) handle frame := by
  obtain ⟨encrypted, member, decoded⟩ := published
  exact ⟨encrypted, by rw [List.filterMap_append]; exact List.mem_append_left _ member, decoded⟩

/-- Exact dictionaries and source control progress preserve all earlier transcript witnesses. -/
theorem history_transport (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control next : PqxdhRecordLiftProtocol.Control n) (before after : CtxPrivate n)
    (transcript suffix : List Entry) (progress : Step control next)
    (same : ∀ label, (after.keys label).1.successfulSeals = (before.keys label).1.successfulSeals)
    (history : History codec control before transcript) : History codec next after (transcript ++ suffix) := by
  intro label entry member
  obtain ⟨handle, frame, owned, matched, outcome⟩ := history label entry (same label ▸ member)
  exact ⟨handle, frame, ownsLabel_step control next progress label handle owned, matched,
    outcome.imp_right (published_append codec transcript suffix handle frame)⟩

/-- A literal record return is a publication in the newly appended transcript entry. -/
theorem current_published (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (transcript : List Entry) (event : Entry) (handle : Handle) (encrypted : RawCtxSourceSend.Encrypted)
    (frame : PqxdhDeploymentNative.Frame) (published : event.published = some (handle, encrypted))
    (decoded : codec.frameRead encrypted.ciphertext = some frame) :
    PublishedBefore codec (transcript ++ [event]) handle frame := by
  refine ⟨encrypted, ?_, decoded⟩
  rw [List.filterMap_append]
  exact List.mem_append_right _ (List.mem_filterMap.mpr ⟨event, List.mem_singleton_self _, published⟩)

/-- The exact old-or-created entry split advances the actual current-transcript invariant. -/
theorem history_extend (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control next : PqxdhRecordLiftProtocol.Control n) (before after : CtxPrivate n)
    (transcript : List Entry) (event : Entry) (progress : Step control next)
    (history : History codec control before transcript)
    (entries : ∀ label entry, entry ∈ (after.keys label).1.successfulSeals →
      entry ∈ (before.keys label).1.successfulSeals ∨ CreatedAt codec control event label entry) :
    History codec next after (transcript ++ [event]) := by
  intro label entry member
  rcases entries label entry member with prior | created
  · obtain ⟨handle, frame, owned, matched, outcome⟩ := history label entry prior
    exact ⟨handle, frame, ownsLabel_step control next progress label handle owned, matched,
      outcome.imp_right (published_append codec transcript [event] handle frame)⟩
  · obtain ⟨handle, frame, owned, matched, outcome⟩ := created
    refine ⟨handle, frame, ownsLabel_step control next progress label handle owned, matched, ?_⟩
    rcases outcome with failed | ⟨encrypted, published, decoded⟩
    · exact Or.inl failed
    · exact Or.inr (current_published codec transcript event handle encrypted frame published decoded)

/-- Every complete native call advances publication evidence relative to its actual transcript entry. -/
theorem native_history (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (query : Spec.Domain) (before : NativeState n E)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2) (transcript : List Entry)
    (history : History codec before.1.2 before.2 transcript)
    (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env query).run before)) :
    History codec result.2.1.2 result.2.2 (transcript ++ [⟨.inl query, result.1⟩]) :=
  history_extend codec before.1.2 result.2.1.2 before.2 result.2.2 transcript _
    (PqxdhRecordFactsOriginControl.native_step modes replace setup codec route env query before safe result supported)
    history (native_entry modes ideal replace setup codec route readback env query before safe result supported)

/-- Re-expressing a literal transcript with identical publication observations preserves the history predicate. -/
theorem history_publications_eq (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n) (first second : List Entry)
    (publications : first.filterMap Entry.published = second.filterMap Entry.published)
    (history : History codec control secret first) : History codec control secret second := by
  simpa only [History, PublishedBefore, publications] using history

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationHistory

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationHistory.published_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationHistory.published_append

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationHistory.history_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationHistory.history_transport

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationHistory.current_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationHistory.current_published

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationHistory.history_extend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationHistory.history_extend

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationHistory.native_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationHistory.native_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationHistory.history_publications_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationHistory.history_publications_eq
