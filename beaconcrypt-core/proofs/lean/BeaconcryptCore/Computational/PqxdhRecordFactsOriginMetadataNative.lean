-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerGlobal
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceiveMetadata

/-! Exact returned receive metadata through the actual marked native compiler. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataNative
open PqxdhRecordLiftIdeal
open PqxdhRecordLiftFlat (KnownAt support_run_fst)
open PqxdhRecordLiftInterface (Environment)
open PqxdhRecordLiftWorldCompiler (Label Owner)
open PqxdhDeploymentInterface (Handle Entry Spec)
open PqxdhRecordFactsOriginHandles PqxdhRecordFactsOriginMarkerNative
variable {n : Nat} {ι KemSK Reader Response E : Type} {baseSpec : OracleSpec ι}

/-- The actual returned record metadata equals the decoded raw frame metadata. -/
def Metadata (read : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (opened : RawCtxWholeOwner.Decrypted) : Prop :=
  ∃ frame, read raw = some frame ∧ opened.sequence = frame.sequence ∧ opened.keyId = frame.sender

/-- The actual looked-up owner either was caller-known or returns the exact decoded metadata, with only the analysis flag erased. -/
theorem owner_metadata (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (handle : Handle) (owner : Owner n)
    (stored : handleKernel control handle = some owner.kernel)
    (tag : PqxdhDeploymentInterface.FrameTag) (sender : Std.U64) (raw : Pqxdh.Bytes)
    (before : CtxPrivate n × Bool)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × Owner n) × (CtxPrivate n × Bool))
    (supported : result ∈ support ((simulateQ (service target modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerRun tag sender codec.frameRead (.inr raw) owner)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1.1 = .Some opened) :
    KnownAt control handle ∨ Metadata codec.frameRead raw opened := by
  cases kind : owner.kernel with
  | known kernel => exact Or.inl (PqxdhRecordFactsOriginPublished.known_of_handleKernel control handle kernel (by simpa only [kind] using stored))
  | hidden slot entry =>
      have actual : (result.1, result.2.1) ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
        (PqxdhRecordLiftProtocol.ownerRun tag sender codec.frameRead (.inr raw) owner)).run before.1) := by
        rw [← PqxdhRecordFactsOriginMuteAdaptive.complete_erase target (RawCtxUniversalDecoder.decoder codec.frameRead)
          (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) _ before, support_map]
        exact ⟨result, supported, rfl⟩
      exact Or.inr (PqxdhRecordFactsOriginReceiveMetadata.owner_run_metadata modes replace setup codec tag sender codec.frameRead
        raw owner slot entry kind before.1 (result.1, result.2.1) actual opened returned)

/-- Server routing retains exact decoded metadata unless the stored peer was caller-known. -/
theorem server_metadata (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (control : PqxdhRecordLiftProtocol.Control n)
    (raw : Pqxdh.Bytes) (keyId : Std.U64) (routed : route raw = some keyId)
    (before : CtxPrivate n × Bool)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftProtocol.Control n) × (CtxPrivate n × Bool))
    (supported : result ∈ support ((simulateQ (service target modes replace setup codec)
      (PqxdhRecordLiftProtocol.serverStep codec.frameRead route (.inr raw) control)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1.1 = .Some opened) :
    KnownAt control (.peer keyId) ∨ Metadata codec.frameRead raw opened := by
  cases existing : control.server with
  | none =>
    simp only [PqxdhRecordLiftProtocol.serverStep, existing, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    simp only [supported, reduceCtorEq] at returned
  | some server =>
    cases found : server.peers keyId with
    | none =>
      simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, found, simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      simp only [supported, reduceCtorEq] at returned
    | some peer =>
      simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, found, bind_pure_comp,
        simulateQ_map, StateT.run_map, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      apply owner_metadata target modes replace setup codec control (.peer keyId)
        (PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer) _ _ server.sender raw
        before inner reached opened returned
      simp only [handleKernel, existing, Option.bind_some, found, Option.map_some,
        PqxdhRecordLiftWorldCompiler.serverOwner]

/-- Beacon dispatch retains decoded metadata unless the actual established owner was caller-known. -/
theorem beacon_metadata (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (index : Nat) (raw : Pqxdh.Bytes)
    (before : CtxPrivate n × Bool)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftProtocol.Control n) × (CtxPrivate n × Bool))
    (supported : result ∈ support ((simulateQ (service target modes replace setup codec)
      (PqxdhRecordLiftProtocol.beaconStep codec.frameRead index (.inr raw) control)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1.1 = .Some opened) :
    KnownAt control (.owner index) ∨ Metadata codec.frameRead raw opened := by
  rcases found : control.owners[index]? with _ | (phase | ⟨shell, kernel⟩)
  · simp only [PqxdhRecordLiftProtocol.beaconStep, found, PqxdhDeploymentNative.absent,
      simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    simp only [supported, reduceCtorEq] at returned
  · simp only [PqxdhRecordLiftProtocol.beaconStep, found, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    simp only [supported, reduceCtorEq] at returned
  · simp only [PqxdhRecordLiftProtocol.beaconStep, found, bind_pure_comp,
      simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    apply owner_metadata target modes replace setup codec control (.owner index)
      (PqxdhRecordLiftWorldCompiler.beaconOwner shell kernel (control.ownerRaw index))
      _ _ shell.identityKeyId raw before inner reached opened returned
    simp only [handleKernel, found, Option.bind_some, PqxdhRecordLiftWorldCompiler.beaconOwner]

/-- The exact native Server delivery retains the before-state known classification or decoded metadata. -/
theorem serverRaw_metadata (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (raw : Pqxdh.Bytes) (keyId : Std.U64) (routed : route raw = some keyId)
    (before : State n E) (result : core.option.Option RawCtxWholeOwner.Decrypted × State n E)
    (supported : result ∈ support ((nativeImpl target modes replace setup codec route env (.inr (.serverRaw raw))).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1 = .Some opened) :
    KnownAt before.1.2 (.peer keyId) ∨ Metadata codec.frameRead raw opened := by
  simp only [native_run, PqxdhRecordFactsOriginNative.native_serverRaw_run, simulateQ_map, StateT.run_map,
    Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact server_metadata target modes replace setup codec route before.1.2 raw keyId routed before.2 inner reached opened returned

/-- The exact native Beacon delivery retains the before-state known classification or decoded metadata. -/
theorem beaconRaw_metadata (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (index : Nat) (raw : Pqxdh.Bytes) (before : State n E)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × State n E)
    (supported : result ∈ support ((nativeImpl target modes replace setup codec route env (.inr (.beaconRaw index raw))).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1 = .Some opened) :
    KnownAt before.1.2 (.owner index) ∨ Metadata codec.frameRead raw opened := by
  simp only [native_run, PqxdhRecordFactsOriginNative.native_beaconRaw_run, simulateQ_map, StateT.run_map,
    Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact beacon_metadata target modes replace setup codec before.1.2 index raw before.2 inner reached opened returned

/-- Each actual successful received transcript entry either belongs to a caller-known owner or returns decoded metadata. -/
def EntryFact (read : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (control : PqxdhRecordLiftProtocol.Control n) (entry : Entry) : Prop :=
  ∀ receiver raw opened handle, entry.received = some (receiver, raw, .Some opened) →
    receivingHandle route receiver raw = some handle → KnownAt control handle ∨ Metadata read raw opened

/-- Forward persistence of known kernels is sufficient to transport old metadata entries. -/
theorem entry_mono (read : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (before after : PqxdhRecordLiftProtocol.Control n)
    (known : ∀ handle, KnownAt before handle → KnownAt after handle)
    (entry : Entry) (good : EntryFact read route before entry) : EntryFact read route after entry := by
  intro receiver raw opened handle received routed
  exact (good receiver raw opened handle received routed).imp (known handle) id

/-- Every literal native reply supplies the exact metadata classification at its before-command control. -/
theorem native_before (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (query : Spec.Domain) (before : State n E)
    (result : Spec.Range query × State n E)
    (supported : result ∈ support ((nativeImpl target modes replace setup codec route env query).run before)) :
    EntryFact codec.frameRead route before.1.2 ⟨.inl query, result.1⟩ := by
  rcases query with coin | command
  · simp [EntryFact, Entry.received]
  · cases command <;> simp only [EntryFact, Entry.received, reduceCtorEq, false_implies, implies_true]
    case serverRaw raw =>
      simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
      rintro _ _ opened handle rfl rfl returned routed
      rcases routeValue : route raw with _ | keyId
      · simp only [receivingHandle, routeValue, Option.map_none, reduceCtorEq] at routed
      · simp only [receivingHandle, routeValue, Option.map_some, Option.some.injEq] at routed
        subst handle
        exact serverRaw_metadata target modes replace setup codec route env raw keyId routeValue before result supported opened returned
    case beaconRaw index raw =>
      simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
      rintro _ _ opened handle rfl rfl returned routed
      simp only [receivingHandle, Option.some.injEq] at routed
      subst handle
      exact beaconRaw_metadata target modes replace setup codec route env index raw before result supported opened returned

/-- Exact native completion retains metadata in the final control using only forward known-kernel persistence. -/
theorem native_final (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (query : Spec.Domain) (before : State n E)
    (result : Spec.Range query × State n E)
    (supported : result ∈ support ((nativeImpl target modes replace setup codec route env query).run before)) :
    EntryFact codec.frameRead route result.2.1.2 ⟨.inl query, result.1⟩ :=
  entry_mono codec.frameRead route before.1.2 result.2.1.2
    (fun handle known => native_known target modes replace setup codec route env handle query before known result supported)
    _ (native_before target modes replace setup codec route env query before result supported)

/-- Experiment-generated send entries contain no receive reply. -/
theorem secrecy_entry (read : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (control : PqxdhRecordLiftProtocol.Control n)
    (query : PqxdhDeploymentInterface.Secrecy) (reply : Option RawCtxSourceSend.Encrypted) :
    EntryFact read route control ⟨.inr query, reply⟩ := by
  cases query <;> simp [EntryFact, Entry.received]

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataNative

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataNative.owner_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataNative.owner_metadata

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataNative.server_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataNative.server_metadata

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataNative.beacon_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataNative.beacon_metadata

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataNative.serverRaw_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataNative.serverRaw_metadata

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataNative.beaconRaw_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataNative.beaconRaw_metadata

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataNative.entry_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataNative.entry_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataNative.native_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataNative.native_before

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataNative.native_final' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataNative.native_final

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataNative.secrecy_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataNative.secrecy_entry
