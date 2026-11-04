-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateReply
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendAcquisition
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealFacts

/-! Newly retained erased-service seals retain their actual source sender, frame and public send outcome at arbitrary reached state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedAttribution
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal PqxdhRecordFactsOriginReplay PqxdhRecordFactsOriginServices
open PqxdhRecordFactsOriginHandles PqxdhRecordFactsOriginReceive
open PqxdhRecordFactsOriginPublicationStep (WriterOutcome)
open PqxdhRecordLiftWorldCompiler (Label StoredKernel LabeledKernel)
open PqxdhDeploymentInterface (Handle Entry Spec)
variable {n : Nat} {ι KemSK Reader Response E Failure A : Type} {baseSpec : OracleSpec ι}

/-- Every post-seal dictionary entry is old or has the exact current writer outcome. -/
private theorem sealing_entry (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (before : CtxPrivate n)
    (result : Option RawCtxSourceSend.Encrypted × CtxPrivate n)
    (supported : result ∈ support ((PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.sealing pending)).run before))
    (label : Label n) (entry : CtxSuccessfulSeal) (member : entry ∈ (result.2.keys label).1.successfulSeals) :
    entry ∈ (before.keys label).1.successfulSeals ∨
      label = pending.material ∧ ∃ frame, Matches frame entry ∧ WriterOutcome codec result.1 frame := by
  obtain ⟨produced, unchanged | ⟨width, record, inserted, logged, reply⟩⟩ :=
    PqxdhRecordFactsOriginSealFacts.erased_sealing_trace modes ideal replace setup codec pending before result supported
  · exact Or.inl (unchanged.2.2 label ▸ member)
  · by_cases same : label = pending.material
    · subst label
      rw [inserted, List.mem_cons] at member
      rcases member with rfl | prior
      · refine Or.inr ⟨rfl, ⟨pending.sequence, pending.context.senderId, record.encode⟩, ⟨rfl, rfl, rfl⟩, ?_⟩
        cases written : codec.frameWrite ⟨pending.sequence, pending.context.senderId, record.encode⟩ with
        | none => exact Or.inl written
        | some bytes =>
          refine Or.inr ⟨⟨bytes, pending.context.targetId, pending.sequence⟩, ?_, (readback _ _ written).2⟩
          simpa only [written, Option.map_some] using reply
      · exact Or.inl prior
    · exact Or.inl ((congrArg (fun key : KeyEntry => key.1.successfulSeals)
        (RegistrationNativePlatformOriginErasedFields.sealing_other modes replace setup codec pending before result supported label same)) ▸ member)

/-- A hidden kernel send attributes every new seal to its actual current coordinate and writer reply. -/
private theorem kernelSend_entry (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (slot : PqxdhRecordLiftInterface.Slot n) (kernel : LabeledKernel n)
    (context : RawCtxSourceSend.SealContext) (before : CtxPrivate n)
    (result : (StoredKernel n × Option RawCtxSourceSend.Encrypted) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.kernelSend (.hidden slot kernel) context)).run before))
    (label : Label n) (entry : CtxSuccessfulSeal) (member : entry ∈ (result.2.keys label).1.successfulSeals) :
    entry ∈ (before.keys label).1.successfulSeals ∨
      label = kernel.send_chain ∧ ∃ frame, Matches frame entry ∧ WriterOutcome codec result.1.2 frame := by
  have tracked := PqxdhRecordLiftChainState.send_begin_tracked kernel context
  cases admitted : RawCtxChainSend.normalBegin kernel context with
  | exhausted original prior =>
    simp only [PqxdhRecordLiftProtocol.kernelSend, PqxdhRecordLiftOpaqueDrivers.admittedSend,
      admitted, PqxdhRecordLiftOpaqueDrivers.sendProgram, simulateQ_pure,
      StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact Or.inl member
  | requested pending =>
    rw [admitted] at tracked
    simp only [PqxdhRecordLiftProtocol.kernelSend, PqxdhRecordLiftOpaqueDrivers.admittedSend,
      admitted, PqxdhRecordLiftOpaqueDrivers.sendProgram, simulateQ_bind, simulateQ_spec_query,
      simulateQ_pure, PqxdhRecordLiftProtocol.localLift, StateT.run_bind, StateT.run_pure,
      bind_assoc, pure_bind] at supported
    rw [mem_support_bind_iff] at supported
    obtain ⟨looked, lookupSupported, continued⟩ := supported
    rw [mem_support_bind_iff] at continued
    obtain ⟨sealed, sealSupported, finished⟩ := continued
    simp only [support_pure, Set.mem_singleton_iff] at finished
    subst result
    rcases sealing_entry modes ideal replace setup codec readback _ looked.2 sealed sealSupported
      label entry member with prior | current
    · have kept := RegistrationNativePlatformOriginErasedFields.base_call modes replace setup codec (.lookup pending.request) (by trivial) before looked lookupSupported
      exact Or.inl ((congrArg (fun keys => (keys label).1.successfulSeals) kept) ▸ prior)
    · right
      simpa only [RawCtxChainSend.ready, tracked.2.2.1] using current

/-- Every newly generated owner-send seal retains its actual installed sender and writer outcome. -/
private theorem ownerSend_entry (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (handle : Handle) (owner : PqxdhRecordLiftWorldCompiler.Owner n)
    (stored : handleKernel control handle = some owner.kernel) (sender : Std.U64) (plaintext : Pqxdh.Bytes)
    (before : CtxPrivate n)
    (result : (Option RawCtxSourceSend.Encrypted × PqxdhRecordLiftWorldCompiler.Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerSend sender plaintext owner)).run before))
    (label : Label n) (entry : CtxSuccessfulSeal) (member : entry ∈ (result.2.keys label).1.successfulSeals) :
    entry ∈ (before.keys label).1.successfulSeals ∨
      OwnsLabel control label handle ∧ ∃ frame, Matches frame entry ∧ WriterOutcome codec result.1.1 frame := by
  unfold PqxdhRecordLiftProtocol.ownerSend at supported
  split at supported
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact Or.inl member
  · simp only [bind_pure_comp, simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    cases kind : owner.kernel with
    | hidden slot kernel =>
      rw [kind] at stored reached
      rcases kernelSend_entry modes ideal replace setup codec readback slot kernel _ before inner
        reached label entry member with prior | ⟨same, frame, matched, outcome⟩
      · exact Or.inl prior
      · right
        have claimed := PqxdhRecordFactsOriginSend.sending_claim control safe handle slot kernel stored
        obtain ⟨other, tagged, owned⟩ := claimed
        cases Option.some.inj tagged.symm
        exact ⟨same ▸ owned, frame, matched, outcome⟩
    | known kernel =>
      rw [kind] at reached
      simp only [PqxdhRecordLiftProtocol.kernelSend, bind_pure_comp, simulateQ_map,
        simulateQ_spec_query, StateT.run_map, support_map] at reached
      obtain ⟨native, nativeReached, rfl⟩ := reached
      have kept := RegistrationNativePlatformOriginErasedFields.base_call modes replace setup codec
        (.knownSend kernel _) (by trivial) before native nativeReached
      exact Or.inl ((congrArg (fun keys => (keys label).1.successfulSeals) kept) ▸ member)


/-- The actual tagged owner-send publication retains the new seal's literal writer outcome. -/
private theorem ownerRun_entry (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (handle : Handle) (owner : PqxdhRecordLiftWorldCompiler.Owner n)
    (stored : handleKernel control handle = some owner.kernel) (sender : Std.U64) (plaintext : Pqxdh.Bytes)
    (before : CtxPrivate n)
    (result : (Option RawCtxSourceSend.Encrypted × PqxdhRecordLiftWorldCompiler.Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerRun (some handle) sender codec.frameRead (.inl plaintext) owner)).run before))
    (label : Label n) (entry : CtxSuccessfulSeal) (member : entry ∈ (result.2.keys label).1.successfulSeals) :
    entry ∈ (before.keys label).1.successfulSeals ∨
      OwnsLabel control label handle ∧ ∃ frame, Matches frame entry ∧ WriterOutcome codec result.1.1 frame := by
  simp only [PqxdhRecordLiftProtocol.ownerRun, PqxdhRecordLiftProtocol.ownerStep,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff] at supported
  obtain ⟨sent, sendSupported, published, publishSupported, finished⟩ := supported
  obtain rfl := (mem_support_pure_iff _ _).mp finished
  have kept := RegistrationNativePlatformOriginErasedFields.base_call modes replace setup codec
    (.publish _) (by trivial) sent.2 published publishSupported
  apply ownerSend_entry modes ideal replace setup codec readback control safe handle owner stored sender
    plaintext before sent sendSupported label entry
  exact (congrArg (fun keys => (keys label).1.successfulSeals) kept) ▸ member


/-- Every new Server-send seal names its actual requested peer and literal writer outcome. -/
private theorem serverSend_entry (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (keyId : Std.U64) (plaintext : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (Option RawCtxSourceSend.Encrypted × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.serverStep codec.frameRead route (.inl (plaintext, keyId)) control)).run before))
    (label : Label n) (entry : CtxSuccessfulSeal) (member : entry ∈ (result.2.keys label).1.successfulSeals) :
    entry ∈ (before.keys label).1.successfulSeals ∨
      OwnsLabel control label (.peer keyId) ∧ ∃ frame, Matches frame entry ∧ WriterOutcome codec result.1.1 frame := by
  rcases existing : control.server with _ | server
  · simp only [PqxdhRecordLiftProtocol.serverStep, existing, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact Or.inl member
  · rcases found : server.peers keyId with _ | peer
    · simp only [PqxdhRecordLiftProtocol.serverStep, existing, found, simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact Or.inl member
    · simp only [PqxdhRecordLiftProtocol.serverStep, existing, found, bind_pure_comp,
        simulateQ_map, StateT.run_map, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      apply ownerRun_entry modes ideal replace setup codec readback control safe (.peer keyId)
        (PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer) _ server.sender plaintext
        before inner reached label entry member
      simp only [handleKernel, existing, Option.bind_some, found, Option.map_some,
        PqxdhRecordLiftWorldCompiler.serverOwner]

/-- Every new Beacon-send seal names its actual requested owner and literal writer outcome. -/
private theorem beaconSend_entry (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (owner : Nat) (plaintext : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (Option RawCtxSourceSend.Encrypted × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.beaconStep codec.frameRead owner (.inl plaintext) control)).run before))
    (label : Label n) (entry : CtxSuccessfulSeal) (member : entry ∈ (result.2.keys label).1.successfulSeals) :
    entry ∈ (before.keys label).1.successfulSeals ∨
      OwnsLabel control label (.owner owner) ∧ ∃ frame, Matches frame entry ∧ WriterOutcome codec result.1.1 frame := by
  rcases found : control.owners[owner]? with _ | (phase | ⟨shell, kernel⟩)
  · simp only [PqxdhRecordLiftProtocol.beaconStep, PqxdhDeploymentNative.absent, found,
      simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact Or.inl member
  · simp only [PqxdhRecordLiftProtocol.beaconStep, found, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact Or.inl member
  · simp only [PqxdhRecordLiftProtocol.beaconStep, found, bind_pure_comp,
      simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    apply ownerRun_entry modes ideal replace setup codec readback control safe (.owner owner)
      (PqxdhRecordLiftWorldCompiler.beaconOwner shell kernel (control.ownerRaw owner))
      _ shell.identityKeyId plaintext before inner reached label entry member
    simp only [handleKernel, found, Option.bind_some, PqxdhRecordLiftWorldCompiler.beaconOwner]


private theorem nonseal_program (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (work : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) A)
    (quiet : work.AllQueriesSatisfy (fun query => ∀pending,query≠.sealing pending))
    (before : CtxPrivate n) (result : A × CtxPrivate n)
    (supported : result∈support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) work).run before)) :
    ∀label,(result.2.keys label).1.successfulSeals=(before.keys label).1.successfulSeals := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    exact fun _ => rfl
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at quiet
    rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,continued⟩ := supported
    have kept := PqxdhRecordFactsOriginOrdinalServices.service_nonSeal modes
      (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
      (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace
      query quiet.1 before middle called
    intro label
    exact (ih middle.1 (quiet.2 middle.1) middle.2 result continued label).trans (kept label)

private theorem original_run (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : PqxdhRecordLiftInterface.Environment n E)
    (query : Spec.Domain) (before : (E × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n) :
    (CborRawRecordOriginService.original (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      env codec route query).run before =
    (fun z => (z.1.1.1, ((z.1.1.2,z.1.2),z.2))) <$>
      (simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
        ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
          ((PqxdhRecordLiftInterface.native env query).run before.1.1)).run before.1.2)).run before.2 := by
  simp only [CborRawRecordOriginService.original,PqxdhRecordLiftFlat.clientImpl,
    QueryImpl.flattenStateT,QueryImpl.mapStateTBase,StateT.run_mk,simulateQ_map,StateT.run_map,Functor.map_map]

private theorem send_entry (modes : Label n → KeyMode) (ideal : ∀label,modes label≠.real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : PqxdhRecordLiftInterface.Environment n E) (handle : Handle) (plaintext : Pqxdh.Bytes)
    (before : CborRawRecordFlat.NativeState n E) (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2)
    (result : Option RawCtxSourceSend.Encrypted × CborRawRecordFlat.NativeState n E)
    (supported : result∈support ((simulateQ (CborRawRecordOriginService.native
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) env codec route)
      (PqxdhDeploymentSecrecy.send handle plaintext)).run before))
    (label : Label n) (entry : CtxSuccessfulSeal) (member : entry∈(result.2.2.keys label).1.successfulSeals) :
    entry∈(before.2.keys label).1.successfulSeals ∨
      PqxdhRecordFactsOriginPublicationNative.CreatedAt codec before.1.2
        (RegistrationNativePlatformOriginGateEntry.sendEntry handle plaintext result.1) label entry := by
  have projected : (result.1,CborRawRecordOriginService.project result.2)∈support
      (Prod.map id CborRawRecordOriginService.project <$>
        (simulateQ (CborRawRecordOriginService.native (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
          env codec route) (PqxdhDeploymentSecrecy.send handle plaintext)).run before) := by
    rw [support_map]
    exact ⟨result,supported,rfl⟩
  rw [CborRawRecordOriginService.send_project] at projected
  cases refused : CborRawRecordFlat.sendRefusal (n:=n) handle plaintext before.1.1.2 with
  | some reply =>
    rw [refused,mem_support_pure_iff] at projected
    have privateSame := congrArg (fun result => result.2.2) projected
    exact Or.inl (privateSame ▸ member)
  | none =>
    rw [refused] at projected
    cases handle with
    | peer keyId =>
      simp only [PqxdhDeploymentSecrecy.send,simulateQ_spec_query] at projected
      rw [original_run modes replace setup codec route env _ (CborRawRecordOriginService.project before)] at projected
      simp only [CborRawRecordOriginService.project,CborRawRecordFlat.clientProject,
        PqxdhRecordLiftFlat.native_serverSend_run,simulateQ_map,StateT.run_map,Functor.map_map,support_map] at projected
      obtain ⟨inner,reached,same⟩ := projected
      have valueSame : inner.1.1=result.1 := congrArg Prod.fst same
      have privateSame : inner.2=result.2.2 := congrArg (fun value => value.2.2) same
      have innerMember : entry∈(inner.2.keys label).1.successfulSeals := by rw [privateSame];exact member
      rcases serverSend_entry modes ideal replace setup codec route readback before.1.2 safe keyId plaintext
        before.2 inner reached label entry innerMember with prior | ⟨owned,frame,matched,outcome⟩
      · exact Or.inl prior
      · refine Or.inr ⟨.peer keyId,frame,owned,matched,?_⟩
        rcases outcome with failed | ⟨encrypted,returned,decoded⟩
        · exact Or.inl failed
        · exact Or.inr ⟨encrypted,by simp only [RegistrationNativePlatformOriginGateEntry.sendEntry,Entry.published,←valueSame,returned],decoded⟩
    | owner owner =>
      simp only [PqxdhDeploymentSecrecy.send,simulateQ_spec_query] at projected
      rw [original_run modes replace setup codec route env _ (CborRawRecordOriginService.project before)] at projected
      simp only [CborRawRecordOriginService.project,CborRawRecordFlat.clientProject,
        PqxdhRecordLiftFlat.native_beaconSend_run,simulateQ_map,StateT.run_map,Functor.map_map,support_map] at projected
      obtain ⟨inner,reached,same⟩ := projected
      have valueSame : inner.1.1=result.1 := congrArg Prod.fst same
      have privateSame : inner.2=result.2.2 := congrArg (fun value => value.2.2) same
      have innerMember : entry∈(inner.2.keys label).1.successfulSeals := by rw [privateSame];exact member
      rcases beaconSend_entry modes ideal replace setup codec readback before.1.2 safe owner plaintext
        before.2 inner reached label entry innerMember with prior | ⟨owned,frame,matched,outcome⟩
      · exact Or.inl prior
      · refine Or.inr ⟨.owner owner,frame,owned,matched,?_⟩
        rcases outcome with failed | ⟨encrypted,returned,decoded⟩
        · exact Or.inl failed
        · exact Or.inr ⟨encrypted,by simp only [RegistrationNativePlatformOriginGateEntry.sendEntry,Entry.published,←valueSame,returned],decoded⟩

private theorem source_run (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : PqxdhRecordLiftInterface.Environment n E)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (query : Spec.Domain)
    (before : CborRawRecordFlat.NativeState n E) :
    (RegistrationNativePlatformGatedRecordFlat.native (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      env reserve codec route query).run before =
    RegistrationNativePlatformGatedRecordFlat.join <$>
      (simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
        (RegistrationNativePlatformOriginNativeTails.source env reserve codec route (Spec.query query)
          before.1.1.1 before.1.1.2 before.1.2)).run before.2 := by
  simpa only [simulateQ_spec_query,RegistrationNativePlatformOriginNativeTails.source,
    CborRawRecordOriginFlatten.interpret] using RegistrationNativePlatformGatedRecordFlat.native_program
    (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) env reserve codec route (Spec.query query)
    before.1.1.1 before.1.1.2 before.1.2 before.2

/-- A newly retained seal under the named erased service comes from one of the actual two native send constructors, at the original reached state. -/
theorem query_sending (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : PqxdhRecordLiftInterface.Environment n E)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (query : Spec.Domain)
    (before : CborRawRecordFlat.NativeState n E) (result : Spec.Range query × CborRawRecordFlat.NativeState n E)
    (supported : result∈support ((RegistrationNativePlatformGatedRecordFlat.native
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) env reserve codec route query).run before))
    (label : Label n) (entry : CtxSuccessfulSeal) (absent : entry∉(before.2.keys label).1.successfulSeals)
    (present : entry∈(result.2.2.keys label).1.successfulSeals) :
    (∃keyId plaintext,query=.inr (.serverSend keyId plaintext)) ∨
      (∃owner plaintext,query=.inr (.beaconSend owner plaintext)) := by
  by_cases nonsend : ¬PqxdhRecordLiftBudget.NativeRecord .send query
  · rw [source_run,support_map] at supported
    obtain ⟨inner,called,rfl⟩ := supported
    have kept := nonseal_program modes replace setup codec _
      (RegistrationNativePlatformOriginNativeTails.non_send env reserve codec route query nonsend
        before.1.1.1 before.1.1.2 before.1.2) before.2 inner (by simpa only [RegistrationNativePlatformOriginNativeTails.source,simulateQ_spec_query] using called) label
    exact (absent (kept ▸ present)).elim
  · rcases query with coin | command
    · exact (nonsend (by simp [PqxdhRecordLiftBudget.NativeRecord,PqxdhDeploymentCompileBudget.commandKind])).elim
    · cases command
      case serverSend keyId plaintext => exact Or.inl ⟨keyId,plaintext,rfl⟩
      case beaconSend owner plaintext => exact Or.inr ⟨owner,plaintext,rfl⟩
      all_goals exact (nonsend (by simp [PqxdhRecordLiftBudget.NativeRecord,PqxdhDeploymentCompileBudget.commandKind])).elim


private theorem coins_base {X : Type} (work : ProbComp X) :
    (simulateQ (RegistrationNativePlatformOriginGateSource.coins (n:=n)) work).AllQueriesSatisfy
      RegistrationNativePlatformOriginErasedFields.BaseOnly := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,RegistrationNativePlatformOriginGateSource.coins,bind_assoc,
      allQueriesSatisfy_query_bind_iff]
    exact ⟨by trivial,fun _ => ⟨by trivial,fun reply => ih reply⟩⟩

private theorem closed_keys (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : StateT E ProbComp A)
    (before : CborRawRecordFlat.NativeState n E) (result : A × CborRawRecordFlat.NativeState n E)
    (supported : result∈support ((RegistrationNativePlatformGatedRecordFlat.fold
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) codec route
      (RegistrationNativePlatformGatedRecordInterface.closed work)).run before)) :
    result.2.2.keys=before.2.keys := by
  rw [RegistrationNativePlatformOriginGateSource.closed_source,support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  exact RegistrationNativePlatformOriginErasedFields.program modes replace setup codec _ (coins_base _)
    before.2 inner called

private theorem post_keys (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (query : Spec.Domain) (reply : Spec.Range query)
    (before : CborRawRecordFlat.NativeState n E) (result : Spec.Range query × CborRawRecordFlat.NativeState n E)
    (supported : result∈support ((RegistrationNativePlatformGatedRecordFlat.fold
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) codec route
      (RegistrationNativePlatformGatedRecordInterface.post reserve query reply)).run before)) :
    result.2.2.keys=before.2.keys := by
  rcases query with coin | command
  · exact closed_keys modes replace setup codec route (pure reply) before result supported
  · cases command
    case serverSend keyId plaintext =>
      exact closed_keys modes replace setup codec route
        (RegistrationNativePlatformOrdinaryGate.gate reserve (fun value : RawCtxSourceSend.Encrypted => value.ciphertext.length) reply)
        before result supported
    case beaconSend owner plaintext =>
      exact closed_keys modes replace setup codec route
        (RegistrationNativePlatformOrdinaryGate.gate reserve (fun value : RawCtxSourceSend.Encrypted => value.ciphertext.length) reply)
        before result supported
    all_goals exact closed_keys modes replace setup codec route (pure reply) before result supported

/-- A newly acquired hidden seal in the actual erased native callback retains its installed sender and exact generated frame. The source encoder refusal, actual public-send refusal and same ciphertext publication are kept distinct. -/
theorem query (modes : Label n → KeyMode) (ideal : ∀label,modes label≠.real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : PqxdhRecordLiftInterface.Environment n E)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (nativeQuery : Spec.Domain)
    (before : CborRawRecordFlat.NativeState n E) (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2)
    (result : Spec.Range nativeQuery × CborRawRecordFlat.NativeState n E)
    (supported : result∈support ((RegistrationNativePlatformGatedRecordFlat.native
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) env reserve codec route nativeQuery).run before))
    (label : Label n) (entry : CtxSuccessfulSeal) (absent : entry∉(before.2.keys label).1.successfulSeals)
    (present : entry∈(result.2.2.keys label).1.successfulSeals) :
    ((∃keyId plaintext,nativeQuery=.inr (.serverSend keyId plaintext)) ∨
      (∃owner plaintext,nativeQuery=.inr (.beaconSend owner plaintext))) ∧
    ∃sender frame,PqxdhRecordFactsOriginHandles.OwnsLabel before.1.2 label sender ∧
      PqxdhRecordFactsOriginReplay.Matches frame entry ∧
      (codec.frameWrite frame=none ∨ (⟨.inl nativeQuery,result.1⟩ : Entry).published=none ∨
        ∃encrypted,(⟨.inl nativeQuery,result.1⟩ : Entry).published=some (sender,encrypted) ∧
          codec.frameRead encrypted.ciphertext=some frame) := by
  have sending := query_sending modes replace setup codec route env reserve nativeQuery before result supported label entry absent present
  refine ⟨sending,?_⟩
  rw [RegistrationNativePlatformGatedRecordFlat.native_split,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨original,called,gated⟩ := supported
  have keys := post_keys modes replace setup codec route reserve nativeQuery original.1 original.2 result gated
  have originalMember : entry∈(original.2.2.keys label).1.successfulSeals := by rw [←keys];exact present
  have created : PqxdhRecordFactsOriginPublicationNative.CreatedAt codec before.1.2 ⟨.inl nativeQuery,original.1⟩ label entry := by
    rcases sending with ⟨keyId,plaintext,rfl⟩ | ⟨owner,plaintext,rfl⟩
    · exact (send_entry modes ideal replace setup codec route readback env (.peer keyId) plaintext before safe original
        (by simpa only [PqxdhDeploymentSecrecy.send,simulateQ_spec_query] using called) label entry originalMember).resolve_left absent
    · exact (send_entry modes ideal replace setup codec route readback env (.owner owner) plaintext before safe original
        (by simpa only [PqxdhDeploymentSecrecy.send,simulateQ_spec_query] using called) label entry originalMember).resolve_left absent
  obtain ⟨sender,frame,owned,matched,outcome⟩ := created
  refine ⟨sender,frame,owned,matched,?_⟩
  rcases outcome with refused | ⟨encrypted,published,decoded⟩
  · exact Or.inl refused
  · have gate := RegistrationNativePlatformOriginGateReply.post_subset
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) codec route reserve
      nativeQuery original.1 original.2 result gated
    rcases gate with refused | same
    · exact Or.inr (Or.inl refused)
    · exact Or.inr (Or.inr ⟨encrypted,same.trans published,decoded⟩)

end BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedAttribution

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedAttribution.query_sending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedAttribution.query_sending
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedAttribution.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedAttribution.query
