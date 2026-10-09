-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnown
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative

/-! Shared-ROM witnesses for caller-known native records and their exact transcript transport. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsBindingNative
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftFlat
open PqxdhRecordFactsBindingKnown PqxdhRecordFactsBindingEvidence
open PqxdhRecordFactsOriginHandles PqxdhRecordFactsOriginNative
open PqxdhRecordFactsOriginPublished PqxdhRecordFactsOriginAccepted
open PqxdhRecordLiftProtocolHistory (Safe Step)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Handle Receiver Spec Entry)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- The exact known-handle shared-ROM obligations of one transcript entry. -/
def KnownEntryFacts (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (control : PqxdhRecordLiftProtocol.Control n)
    (secret : CtxPrivate n) (entry : Entry) : Prop :=
  (∀ handle encrypted, entry.published = some (handle, encrypted) →
    KnownAt control handle → SharedRecord codec secret encrypted.ciphertext) ∧
  (∀ receiver raw opened handle, entry.received = some (receiver, raw, .Some opened) →
    receivingHandle route receiver raw = some handle →
    KnownAt control handle → SharedRecord codec secret raw)

/-- A final caller-known publisher cannot have been hidden earlier; its original shared-cache witness persists. -/
theorem published_known_mono (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control next : PqxdhRecordLiftProtocol.Control n) (before after : CtxPrivate n)
    (progress : Step control next) (cache : before.base.primitive.2 ≤ after.base.primitive.2)
    (handle : Handle) (encrypted : RawCtxSourceSend.Encrypted)
    (published : Published codec control before handle encrypted)
    (knownShared : KnownAt control handle → SharedRecord codec before encrypted.ciphertext)
    (known : KnownAt next handle) : SharedRecord codec after encrypted.ciphertext := by
  rcases published with earlier | ⟨label, owned, _⟩
  · exact SharedRecord.grows codec before after encrypted.ciphertext cache (knownShared earlier)
  · exact False.elim (by simpa only [known_no_slot next handle known, reduceCtorEq] using
      (handleSlot_step control next progress handle label.slot owned.1))

/-- A final caller-known receiver cannot have been hidden earlier; its actual raw-record cache witness persists. -/
theorem accepted_known_mono (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control next : PqxdhRecordLiftProtocol.Control n) (before after : CtxPrivate n)
    (progress : Step control next) (cache : before.base.primitive.2 ≤ after.base.primitive.2)
    (handle : Handle) (raw : Pqxdh.Bytes) (opened : RawCtxWholeOwner.Decrypted)
    (accepted : Accepted codec control before handle raw opened)
    (knownShared : KnownAt control handle → SharedRecord codec before raw)
    (known : KnownAt next handle) : SharedRecord codec after raw := by
  exact accepted.elim (fun earlier => SharedRecord.grows codec before after raw cache (knownShared earlier))
    (fun hidden => hidden.elim fun label hidden => False.elim (by
      simpa only [known_no_slot next handle known, reduceCtorEq] using
        (handleSlot_step control next progress handle label.slot hidden.1)))

/-- Conditional caller-known transcript evidence survives actual forward control and shared-cache growth. -/
theorem knownEntryFacts_mono (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (control next : PqxdhRecordLiftProtocol.Control n)
    (before after : CtxPrivate n) (progress : Step control next)
    (cache : before.base.primitive.2 ≤ after.base.primitive.2) (entry : Entry)
    (facts : EntryFacts codec route control before entry)
    (shared : KnownEntryFacts codec route control before entry) :
    KnownEntryFacts codec route next after entry := by
  refine ⟨fun handle encrypted returned known => published_known_mono codec control next before after
    progress cache handle encrypted (facts.1 handle encrypted returned) (shared.1 handle encrypted returned) known, ?_⟩
  intro receiver raw opened handle returned routed known
  obtain ⟨actualHandle, actualRoute, accepted⟩ := facts.2 receiver raw opened returned
  exact accepted_known_mono codec control next before after progress cache handle raw opened
    ((Option.some.inj (actualRoute.symm.trans routed)) ▸ accepted)
    (shared.2 receiver raw opened handle returned routed) known

/-- An actual caller-known Server raw receive leaves its decoded commitment in the shared cache. -/
theorem native_serverRaw_shared (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (raw : Pqxdh.Bytes) (handle : Handle) (before : NativeState n E)
    (routed : receivingHandle route .server raw = some handle) (known : KnownAt before.1.2 handle)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env (.inr (.serverRaw raw))).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1 = .Some opened) :
    SharedRecord codec result.2.2 raw := by
  simp only [nativeImpl_run, native_serverRaw_run, simulateQ_map, StateT.run_map,
    Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact serverReceive_shared modes replace setup codec route before.1.2 raw handle routed known before.2 inner reached opened returned

/-- An actual caller-known Beacon raw receive leaves its decoded commitment in the shared cache. -/
theorem native_beaconRaw_shared (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (owner : Nat) (raw : Pqxdh.Bytes) (before : NativeState n E)
    (known : KnownAt before.1.2 (.owner owner))
    (result : core.option.Option RawCtxWholeOwner.Decrypted × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env (.inr (.beaconRaw owner raw))).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1 = .Some opened) :
    SharedRecord codec result.2.2 raw := by
  simp only [nativeImpl_run, native_beaconRaw_run, simulateQ_map, StateT.run_map,
    Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact beaconReceive_shared modes replace setup codec before.1.2 owner known raw before.2 inner reached opened returned

/-- An actual caller-known Server send leaves its returned record commitment in the shared cache. -/
theorem native_serverSend_shared (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (keyId : Std.U64) (plaintext : Pqxdh.Bytes) (before : NativeState n E)
    (known : KnownAt before.1.2 (.peer keyId))
    (result : Option RawCtxSourceSend.Encrypted × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env (.inr (.serverSend keyId plaintext))).run before))
    (encrypted : RawCtxSourceSend.Encrypted) (returned : result.1 = some encrypted) :
    SharedRecord codec result.2.2 encrypted.ciphertext := by
  simp only [nativeImpl_run, native_serverSend_run, simulateQ_map, StateT.run_map,
    Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact serverSend_shared modes replace setup codec route readback before.1.2 keyId known plaintext before.2 inner reached encrypted returned

/-- An actual caller-known Beacon send leaves its returned record commitment in the shared cache. -/
theorem native_beaconSend_shared (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (owner : Nat) (plaintext : Pqxdh.Bytes) (before : NativeState n E)
    (known : KnownAt before.1.2 (.owner owner))
    (result : Option RawCtxSourceSend.Encrypted × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env (.inr (.beaconSend owner plaintext))).run before))
    (encrypted : RawCtxSourceSend.Encrypted) (returned : result.1 = some encrypted) :
    SharedRecord codec result.2.2 encrypted.ciphertext := by
  simp only [nativeImpl_run, native_beaconSend_run, simulateQ_map, StateT.run_map,
    Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact beaconSend_shared modes replace setup codec readback before.1.2 owner known plaintext before.2 inner reached encrypted returned

/-- Every literal native reply supplies the caller-known shared-cache obligations of its exact forwarded entry. -/
theorem native_knownEntryFacts_before (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (query : Spec.Domain) (before : NativeState n E)
    (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env query).run before)) :
    KnownEntryFacts codec route before.1.2 result.2.2 ⟨.inl query, result.1⟩ := by
  rcases query with coin | command
  · simp [KnownEntryFacts, Entry.published, Entry.received]
  · cases command <;> simp only [KnownEntryFacts, Entry.published, Entry.received,
      reduceCtorEq, false_implies, implies_true, and_self, and_true, true_and]
    case serverSend keyId plaintext =>
      rcases returned : result.1 with _ | encrypted
      · simp
      · simpa using (fun known => native_serverSend_shared modes replace setup codec route readback env
          keyId plaintext before known result supported encrypted returned)
    case serverRaw raw =>
      simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
      rintro _ _ opened handle rfl rfl returned routed known
      exact native_serverRaw_shared modes replace setup codec route env raw handle before routed known result supported opened returned
    case beaconSend owner plaintext =>
      rcases returned : result.1 with _ | encrypted
      · simp
      · simpa using (fun known => native_beaconSend_shared modes replace setup codec route readback env
          owner plaintext before known result supported encrypted returned)
    case beaconRaw owner raw =>
      simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
      rintro _ _ opened handle rfl rfl returned routed known
      exact native_beaconRaw_shared modes replace setup codec route env owner raw before
        ((Option.some.inj routed).symm ▸ known) result supported opened returned

/-- Native replies retain caller-known commitment evidence at their actual final control and private state. -/
theorem native_knownEntryFacts (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (query : Spec.Domain) (before : NativeState n E) (safe : Safe before.1.2)
    (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env query).run before)) :
    KnownEntryFacts codec route result.2.1.2 result.2.2 ⟨.inl query, result.1⟩ :=
  knownEntryFacts_mono codec route before.1.2 result.2.1.2 result.2.2 result.2.2
    (PqxdhRecordFactsOriginControl.native_step modes replace setup codec route env query before safe result supported)
    le_rfl _
    (native_entryFacts_before modes ideal replace setup codec route readback env query before safe result supported)
    (native_knownEntryFacts_before modes replace setup codec route readback env query before result supported)

/-- An experiment-generated successful send on a final caller-known handle has a shared-ROM commitment witness. -/
theorem native_send_shared (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (handle : Handle) (plaintext : Pqxdh.Bytes)
    (before : NativeState n E) (safe : Safe before.1.2)
    (result : Option RawCtxSourceSend.Encrypted × NativeState n E)
    (supported : result ∈ support ((simulateQ (nativeImpl modes replace setup codec route env)
      (PqxdhDeploymentSecrecy.send handle plaintext)).run before))
    (encrypted : RawCtxSourceSend.Encrypted) (returned : result.1 = some encrypted)
    (known : KnownAt result.2.1.2 handle) : SharedRecord codec result.2.2 encrypted.ciphertext := by
  cases handle with
  | peer keyId =>
    simp only [PqxdhDeploymentSecrecy.send, simulateQ_spec_query] at supported
    apply (native_knownEntryFacts modes ideal replace setup codec route readback env (.inr (.serverSend keyId plaintext))
      before safe result supported).1 (.peer keyId) encrypted ?_ known
    simp only [Entry.published, returned]
  | owner owner =>
    simp only [PqxdhDeploymentSecrecy.send, simulateQ_spec_query] at supported
    apply (native_knownEntryFacts modes ideal replace setup codec route readback env (.inr (.beaconSend owner plaintext))
      before safe result supported).1 (.owner owner) encrypted ?_ known
    simp only [Entry.published, returned]

end BeaconcryptCore.Computational.PqxdhRecordFactsBindingNative

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingNative.published_known_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingNative.published_known_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingNative.accepted_known_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingNative.accepted_known_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingNative.knownEntryFacts_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingNative.knownEntryFacts_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingNative.native_serverRaw_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingNative.native_serverRaw_shared

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingNative.native_beaconRaw_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingNative.native_beaconRaw_shared

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingNative.native_serverSend_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingNative.native_serverSend_shared

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingNative.native_beaconSend_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingNative.native_beaconSend_shared

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingNative.native_knownEntryFacts_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingNative.native_knownEntryFacts_before

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingNative.native_knownEntryFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingNative.native_knownEntryFacts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingNative.native_send_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingNative.native_send_shared
