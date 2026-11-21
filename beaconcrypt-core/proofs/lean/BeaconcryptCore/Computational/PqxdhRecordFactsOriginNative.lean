-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginDispatch
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginControl
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMonotone

/-! Actual native record replies and persistent transcript facts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftFlat
open PqxdhRecordFactsOriginHandles PqxdhRecordFactsOriginControl
open PqxdhRecordFactsOriginPublished PqxdhRecordFactsOriginAccepted
open PqxdhRecordFactsOriginDispatch PqxdhRecordFactsOriginMonotone
open PqxdhRecordLiftProtocolHistory (Safe Step)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Handle Receiver Spec Entry)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- Local accepted-frame evidence survives actual control and seal-dictionary growth. -/
theorem accepted_mono (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control next : PqxdhRecordLiftProtocol.Control n) (before after : CtxPrivate n)
    (progress : Step control next) (known : ∀ handle, KnownAt control handle → KnownAt next handle)
    (seals : ∀ label entry, entry ∈ (before.keys label).1.successfulSeals → entry ∈ (after.keys label).1.successfulSeals)
    (handle : Handle) (raw : Pqxdh.Bytes) (opened : RawCtxWholeOwner.Decrypted)
    (good : Accepted codec control before handle raw opened) :
    Accepted codec next after handle raw opened := by
  rcases good with good | ⟨label, slot, direction, frame, decoded, entry, member, matched, plaintext⟩
  · exact Or.inl (known handle good)
  · exact Or.inr ⟨label, handleSlot_step control next progress handle label.slot slot, direction, frame, decoded,
      entry, seals label entry member, matched, plaintext⟩

/-- Successful-send evidence survives actual control and seal-dictionary growth. -/
theorem published_mono (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control next : PqxdhRecordLiftProtocol.Control n) (before after : CtxPrivate n)
    (progress : Step control next) (known : ∀ handle, KnownAt control handle → KnownAt next handle)
    (seals : ∀ label entry, entry ∈ (before.keys label).1.successfulSeals → entry ∈ (after.keys label).1.successfulSeals)
    (handle : Handle) (encrypted : RawCtxSourceSend.Encrypted)
    (good : Published codec control before handle encrypted) :
    Published codec next after handle encrypted := by
  rcases good with good | ⟨label, owned, frame, decoded, entry, member, matched⟩
  · exact Or.inl (known handle good)
  · exact Or.inr ⟨label, ownsLabel_step control next progress label handle owned, frame, decoded,
      entry, seals label entry member, matched⟩

/-- Native Server raw delivery invokes the exact routed source dispatcher and retains environment state. -/
theorem native_serverRaw_run (env : Environment n E) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (raw : Pqxdh.Bytes) (e : E)
    (control : PqxdhRecordLiftProtocol.Control n) :
    (simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
      ((native env (.inr (.serverRaw raw))).run e)).run control =
      (fun p => ((p.1, e), p.2)) <$>
        (PqxdhRecordLiftProtocol.serverStep codec.frameRead route (.inr raw)).run control := by
  simp only [native, StateT.lift, StateT.run]
  erw [simulateQ_bind, simulateQ_spec_query]
  simp only [simulateQ_pure, PqxdhRecordLiftProtocol.handler, map_eq_bind_pure_comp]
  rfl

/-- Native Beacon raw delivery invokes the exact owner dispatcher and retains environment state. -/
theorem native_beaconRaw_run (env : Environment n E) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (owner : Nat) (raw : Pqxdh.Bytes) (e : E)
    (control : PqxdhRecordLiftProtocol.Control n) :
    (simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
      ((native env (.inr (.beaconRaw owner raw))).run e)).run control =
      (fun p => ((p.1, e), p.2)) <$>
        (PqxdhRecordLiftProtocol.beaconStep codec.frameRead owner (.inr raw)).run control := by
  simp only [native, StateT.lift, StateT.run]
  erw [simulateQ_bind, simulateQ_spec_query]
  simp only [simulateQ_pure, PqxdhRecordLiftProtocol.handler, map_eq_bind_pure_comp]
  rfl

/-- A successful native Server receive keeps its routed physical handle and actual accepted-frame evidence. -/
theorem native_serverRaw_accepted (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (raw : Pqxdh.Bytes) (before : NativeState n E) (safe : Safe before.1.2)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env (.inr (.serverRaw raw))).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1 = .Some opened) :
    ∃ handle, receivingHandle route .server raw = some handle ∧
      Accepted codec before.1.2 result.2.2 handle raw opened := by
  simp only [nativeImpl_run, native_serverRaw_run, simulateQ_map, StateT.run_map,
    Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact serverReceive_accepted modes ideal replace setup codec route before.1.2 safe raw
    before.2 inner reached opened returned

/-- A successful native Beacon receive retains the requested owner and actual accepted-frame evidence. -/
theorem native_beaconRaw_accepted (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (owner : Nat) (raw : Pqxdh.Bytes) (before : NativeState n E) (safe : Safe before.1.2)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env (.inr (.beaconRaw owner raw))).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1 = .Some opened) :
    Accepted codec before.1.2 result.2.2 (.owner owner) raw opened := by
  simp only [nativeImpl_run, native_beaconRaw_run, simulateQ_map, StateT.run_map,
    Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact beaconReceive_accepted modes ideal replace setup codec before.1.2 safe owner raw
    before.2 inner reached opened returned

/-- A successful native Server send retains its actual peer and post-execution dictionary witness. -/
theorem native_serverSend_published (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (keyId : Std.U64) (plaintext : Pqxdh.Bytes)
    (before : NativeState n E) (safe : Safe before.1.2)
    (result : Option RawCtxSourceSend.Encrypted × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env (.inr (.serverSend keyId plaintext))).run before))
    (encrypted : RawCtxSourceSend.Encrypted) (returned : result.1 = some encrypted) :
    Published codec before.1.2 result.2.2 (.peer keyId) encrypted := by
  simp only [nativeImpl_run, native_serverSend_run, simulateQ_map, StateT.run_map,
    Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact serverSend_published modes ideal replace setup codec route readback before.1.2 safe
    keyId plaintext before.2 inner reached encrypted returned

/-- A successful native Beacon send retains its actual owner and post-execution dictionary witness. -/
theorem native_beaconSend_published (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (owner : Nat) (plaintext : Pqxdh.Bytes)
    (before : NativeState n E) (safe : Safe before.1.2)
    (result : Option RawCtxSourceSend.Encrypted × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env (.inr (.beaconSend owner plaintext))).run before))
    (encrypted : RawCtxSourceSend.Encrypted) (returned : result.1 = some encrypted) :
    Published codec before.1.2 result.2.2 (.owner owner) encrypted := by
  simp only [nativeImpl_run, native_beaconSend_run, simulateQ_map, StateT.run_map,
    Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact beaconSend_published modes ideal replace setup codec readback before.1.2 safe
    owner plaintext before.2 inner reached encrypted returned

/-- Exact structural witnesses for the actual successful record observations in one ledger entry. -/
def EntryFacts (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (control : PqxdhRecordLiftProtocol.Control n)
    (secret : CtxPrivate n) (entry : Entry) : Prop :=
  (∀ handle encrypted, entry.published = some (handle, encrypted) → Published codec control secret handle encrypted) ∧
  (∀ receiver raw opened, entry.received = some (receiver, raw, .Some opened) →
    ∃ handle, receivingHandle route receiver raw = some handle ∧ Accepted codec control secret handle raw opened)

/-- Both actual record observations persist through source control and dictionary growth. -/
theorem entryFacts_mono (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (control next : PqxdhRecordLiftProtocol.Control n)
    (before after : CtxPrivate n) (progress : Step control next)
    (known : ∀ handle, KnownAt control handle → KnownAt next handle)
    (seals : ∀ label entry, entry ∈ (before.keys label).1.successfulSeals → entry ∈ (after.keys label).1.successfulSeals)
    (entry : Entry) (good : EntryFacts codec route control before entry) :
    EntryFacts codec route next after entry := by
  refine ⟨fun handle encrypted returned => published_mono codec control next before after progress known seals
    handle encrypted (good.1 handle encrypted returned), ?_⟩
  intro receiver raw opened returned
  obtain ⟨handle, routed, accepted⟩ := good.2 receiver raw opened returned
  exact ⟨handle, routed, accepted_mono codec control next before after progress known seals handle raw opened accepted⟩

/-- Every actual native reply supplies exact record observations for the literal forwarded ledger entry. -/
theorem native_entryFacts_before (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (query : Spec.Domain) (before : NativeState n E) (safe : Safe before.1.2)
    (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env query).run before)) :
    EntryFacts codec route before.1.2 result.2.2 ⟨.inl query, result.1⟩ := by
  rcases query with coin | command
  · simp [EntryFacts, Entry.published, Entry.received]
  · cases command <;> simp only [EntryFacts, Entry.published, Entry.received, reduceCtorEq, false_implies, implies_true, and_self, and_true, true_and]
    case serverSend keyId plaintext =>
      rcases returned : result.1 with _ | encrypted
      · simp
      · simpa using native_serverSend_published modes ideal replace setup codec route readback env
          keyId plaintext before safe result supported encrypted returned
    case serverRaw raw =>
      simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
      rintro _ _ opened rfl rfl returned
      exact native_serverRaw_accepted modes ideal replace setup codec route env raw before safe result supported opened returned
    case beaconSend owner plaintext =>
      rcases returned : result.1 with _ | encrypted
      · simp
      · simpa using native_beaconSend_published modes ideal replace setup codec route readback env
          owner plaintext before safe result supported encrypted returned
    case beaconRaw owner raw =>
      simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
      rintro _ _ opened rfl rfl returned
      exact ⟨.owner owner, rfl, native_beaconRaw_accepted modes ideal replace setup codec route env
        owner raw before safe result supported opened returned⟩

/-- Native replies satisfy record-entry facts at their complete final control and private state. -/
theorem native_entryFacts (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (query : Spec.Domain) (before : NativeState n E) (safe : Safe before.1.2)
    (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env query).run before)) :
    EntryFacts codec route result.2.1.2 result.2.2 ⟨.inl query, result.1⟩ :=
  entryFacts_mono codec route before.1.2 result.2.1.2 result.2.2 result.2.2
    (native_step modes replace setup codec route env query before safe result supported)
    (fun handle known => nativeImpl_known modes replace setup codec route env handle query before known result supported)
    (fun _ _ member => member) _
    (native_entryFacts_before modes ideal replace setup codec route readback env query before safe result supported)

/-- An experiment-generated native send satisfies the same final-state publication witness. -/
theorem native_send_published (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (handle : Handle) (plaintext : Pqxdh.Bytes)
    (before : NativeState n E) (safe : Safe before.1.2)
    (result : Option RawCtxSourceSend.Encrypted × NativeState n E)
    (supported : result ∈ support ((simulateQ (nativeImpl modes replace setup codec route env)
      (PqxdhDeploymentSecrecy.send handle plaintext)).run before))
    (encrypted : RawCtxSourceSend.Encrypted) (returned : result.1 = some encrypted) :
    Published codec result.2.1.2 result.2.2 handle encrypted := by
  cases handle with
  | peer keyId =>
    simp only [PqxdhDeploymentSecrecy.send, simulateQ_spec_query] at supported
    apply (native_entryFacts modes ideal replace setup codec route readback env (.inr (.serverSend keyId plaintext))
      before safe result supported).1 (.peer keyId) encrypted
    simp only [Entry.published, returned]
  | owner owner =>
    simp only [PqxdhDeploymentSecrecy.send, simulateQ_spec_query] at supported
    apply (native_entryFacts modes ideal replace setup codec route readback env (.inr (.beaconSend owner plaintext))
      before safe result supported).1 (.owner owner) encrypted
    simp only [Entry.published, returned]

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative.accepted_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative.accepted_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative.published_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative.published_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative.native_serverRaw_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative.native_serverRaw_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative.native_beaconRaw_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative.native_beaconRaw_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative.native_serverRaw_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative.native_serverRaw_accepted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative.native_beaconRaw_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative.native_beaconRaw_accepted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative.native_serverSend_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative.native_serverSend_published

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative.native_beaconSend_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative.native_beaconSend_published

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative.entryFacts_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative.entryFacts_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative.native_entryFacts_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative.native_entryFacts_before

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative.native_entryFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative.native_entryFacts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative.native_send_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative.native_send_published

