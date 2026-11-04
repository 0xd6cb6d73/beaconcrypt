-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedAttribution
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginAccepted
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataNative
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedReceive
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal PqxdhRecordLiftWorldCompiler PqxdhRecordLiftWorldProvenance
open PqxdhRecordFactsOriginReplay PqxdhRecordFactsOriginDictionary PqxdhRecordFactsOriginHandles
open PqxdhRecordFactsOriginReceive (ReceiveOrigin finish_reply)
open PqxdhRecordFactsOriginAccepted (Accepted)
open PqxdhRecordFactsOriginPublished (known_of_handleKernel)
open PqxdhRecordLiftCtxLink PqxdhRecordLiftCtxAvailability
open PqxdhDeploymentInterface (Handle Entry Spec FullSpec)
variable {n : Nat} {ι KemSK Reader Response E Failure : Type} {baseSpec : OracleSpec ι}

private theorem keyed_frame (modes : Label n →KeyMode) (read : RawCtxReceive.FrameDecoder) (crypto : Pqxdh.Crypto)
    (label : Label n) (envelope : RawCtxUniversalDecoder.Envelope) (before after : CtxPrivate n) (plaintext : Pqxdh.Bytes)
    (supported : (some plaintext,after)∈support ((PqxdhRecordFactsPrivateCacheFamily.erasedKeyed modes
      (RawCtxUniversalDecoder.decoder read) crypto (label,.inr (RawCtxUniversalDecoder.pack envelope))).run before)) :
    ∃frame,read envelope.raw=some frame ∧∃entry∈(before.keys label).1.successfulSeals,
      Matches frame entry ∧entry.input.plaintext=plaintext := by
  rw [PqxdhRecordFactsHashLocal.keyedRaw_exact,mem_support_pure_iff] at supported
  have returned := congrArg Prod.fst supported.symm
  change (PqxdhRecordFactsHashLocal.rawResult (RawCtxUniversalDecoder.decoder read)
    (RawCtxUniversalDecoder.pack envelope) (before.keys label,before.base.primitive.2)).1=some plaintext at returned
  unfold PqxdhRecordFactsHashLocal.rawResult at returned
  cases decoded : RawCtxUniversalDecoder.decoder read (RawCtxUniversalDecoder.pack envelope) with
  | none => simp only [decoded] at returned;cases returned
  | some target =>
    simp only [decoded] at returned
    obtain ⟨entry,member,nonce,context,record,value⟩ := replay_witness (AdaptiveCtxSharedReplay.install (before.keys label) ∅).ctx target plaintext returned
    obtain ⟨frame,readFrame,slices,parsed,rfl⟩ := decoder_frame read envelope target decoded
    exact ⟨frame,readFrame,entry,member,target_matches envelope.nonce frame envelope.ad.toList slices parsed envelope.ad.2 entry
      ⟨nonce,context,record⟩,value⟩
/-- Every accepted hidden opening in an ideal mode refers to a pre-existing coordinate dictionary entry with the actual returned plaintext. -/
private theorem opening_frame (modes : PqxdhRecordLiftWorldCompiler.Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (pending : PqxdhRecordLiftProtocol.Opening n) (before after : CtxPrivate n)
    (opened : RawCtxWholeOwner.Decrypted)
    (supported : (.Some opened, after) ∈ support
      ((PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.opening pending)).run before)) :
    ∃ label, RawCtxInterpretedOpening.material pending = .ok (.Some label) ∧
      ∃ frame, codec.frameRead pending.context.raw = some frame ∧
      ∃ entry ∈ (before.keys label).1.successfulSeals,
        Matches frame entry ∧ entry.input.plaintext = opened.plaintext := by
  change (.Some opened,after)∈support ((simulateQ (PqxdhRecordFactsPrivateCacheServices.erased modes
    (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
    (PqxdhRecordFactsPrivateCacheCompiler.base (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec)))
    (PqxdhRecordFactsPrivateCacheCompiler.compile codec.frameWrite replace (.opening pending))).run before) at supported
  rw [PqxdhRecordFactsPrivateCacheSource.erased_opening] at supported
  unfold hiddenOpening at supported
  split at supported
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    cases congrArg Prod.fst supported
  · split at supported
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases congrArg Prod.fst supported
    · rename_i input arguments
      split at supported
      · rename_i width
        simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at supported
        obtain ⟨⟨reply, secret⟩, reached, equal⟩ := supported
        cases reply with
        | none => cases congrArg Prod.fst equal
        | some plaintext =>
          have replyEq : RawCtxSharedOpeningConsumer.apiReply input.sequence input.context (some plaintext) = .Some opened := congrArg Prod.fst equal
          cases replyEq
          have contextEq : input.context = pending.context :=
            (PqxdhRecordLiftCtxHybrid.openArguments_facts _ input arguments).2
          obtain ⟨frame, readFrame, entry, member, matched, message⟩ :=
            keyed_frame modes codec.frameRead setup.source.crypto input.material
              (RawCtxUniversalDecoder.envelope (materialAt before.base.chain input.material).2 input.context width)
              before secret plaintext reached
          refine ⟨input.material, ?_, frame, by simpa only [RawCtxUniversalDecoder.envelope, contextEq] using readFrame,
            entry, member, matched, message⟩
          simpa only [RawCtxChainInterpretation.opening_material_chains] using
            PqxdhRecordLiftCtxAvailability.openArguments_material _ input arguments
      · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        cases congrArg Prod.fst supported


private noncomputable def receiveRun (modes : Label n →KeyMode) (replace : Pqxdh.Bytes →Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (effect : RawCtxChainReceive.Effect (Label n) (Label n) (Label n) RawCtxWholeOwner.OpenContext) (state : CtxPrivate n) :=
  (simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
    (simulateQ PqxdhRecordLiftProtocol.localLift (PqxdhRecordLiftOpaqueDrivers.receiveProgram effect))).run state
/-- Successful recursive source receive preserves getter attribution through every skipped-key callback and returns an earlier exact seal witness. -/
private theorem receive_origin (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (entry : LabeledKernel n)
    (context : RawCtxWholeOwner.OpenContext) (target : Std.U64)
    (aligned : PqxdhRecordLiftChainState.Aligned entry)
    (effect : RawCtxChainReceive.Effect (Label n) (Label n) (Label n) RawCtxWholeOwner.OpenContext)
    (tracked : PqxdhRecordLiftChainState.Tracked entry context effect)
    (admitted : PqxdhFirstRecordReplay.Admitted entry target effect)
    (attributed : PqxdhRecordLiftMaterialTable.EffectAttributed entry.receive_chain effect)
    (before : CtxPrivate n)
    (result : (LabeledKernel n × core.option.Option RawCtxWholeOwner.Decrypted) × CtxPrivate n)
    (supported : result ∈ support (receiveRun modes replace setup codec effect before))
    (opened : RawCtxWholeOwner.Decrypted) (accepted : result.1.2 = .Some opened) :
    ReceiveOrigin codec entry.receive_chain context before opened := by
  generalize hdepth : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect before result with
  | h depth ih =>
      cases effect with
      | rejected original prior =>
          simp only [receiveRun, PqxdhRecordLiftOpaqueDrivers.receiveProgram, simulateQ_pure,
            StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          simp only [supported, reduceCtorEq] at accepted
      | openRequested pending =>
          simp only [receiveRun, PqxdhRecordLiftOpaqueDrivers.receiveProgram, bind_pure_comp,
            simulateQ_map, simulateQ_spec_query, PqxdhRecordLiftProtocol.localLift,
            StateT.run_map, support_map] at supported
          obtain ⟨reply, reached, rfl⟩ := supported
          have serviceAccepted : reply.1 = .Some opened := (finish_reply pending reply.1).symm.trans accepted
          obtain ⟨label, material, frame, decoded, sealedEntry, member, matched, plaintext⟩ :=
            opening_frame modes replace setup codec pending before reply.2 opened
              (by simpa only [← serviceAccepted, Prod.mk.eta] using reached)
          obtain ⟨sequence, _, origin⟩ := PqxdhRecordLiftMaterialTable.opening_attributed
            entry.receive_chain pending attributed label material
          exact ⟨label, origin.1, origin.2.1, frame, by simpa only [tracked.2.1] using decoded,
            sealedEntry, member, matched, plaintext⟩
      | kdfRequested pending =>
          simp only [receiveRun, PqxdhRecordLiftOpaqueDrivers.receiveProgram, simulateQ_bind,
            simulateQ_spec_query, PqxdhRecordLiftProtocol.localLift, StateT.run_bind,
            mem_support_bind_iff] at supported
          obtain ⟨looked, reached, continued⟩ := supported
          have nextOrigin := ih _ (hdepth ▸ RawCtxChainReceive.normalResume_rank pending
            (PqxdhRecordLiftChainState.advance pending.request 1, pending.request)) _
            (PqxdhRecordLiftChainState.resume_tracked entry context pending pending.request tracked)
            (PqxdhFirstRecordReplay.resume_admitted entry target pending
              (PqxdhRecordLiftChainState.advance pending.request 1, pending.request) admitted)
            (PqxdhRecordLiftMaterialTable.resume_source_attributed entry context target pending aligned tracked admitted
              attributed.1 attributed.2) looked.2 result continued accepted rfl
          simpa only [ReceiveOrigin, RegistrationNativePlatformOriginErasedFields.base_call modes replace setup codec (.lookup pending.request) (by trivial) before looked reached]
            using nextOrigin

/-- The source admission operation supplies every callback provenance premise from the existing kernel certificate. -/
private theorem admitted_origin (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (entry : LabeledKernel n)
    (context : RawCtxWholeOwner.OpenContext) (target : Std.U64)
    (certified : PqxdhRecordLiftChainCoordinates.Certified entry) (before : CtxPrivate n)
    (result : (LabeledKernel n × core.option.Option RawCtxWholeOwner.Decrypted) × CtxPrivate n)
    (supported : result ∈ support (receiveRun modes replace setup codec
      (RawCtxChainReceive.normalBegin entry target context) before))
    (opened : RawCtxWholeOwner.Decrypted) (accepted : result.1.2 = .Some opened) :
    ReceiveOrigin codec entry.receive_chain context before opened := by
  exact receive_origin modes replace setup codec entry context target certified.2.1 _
    (PqxdhRecordLiftChainState.begin_tracked entry context target)
    (PqxdhFirstRecordReplay.begin_admitted entry target context certified.1.capacity)
    (PqxdhRecordLiftMaterialTable.begin_attributed entry.receive_chain entry certified.2.2 target context)
    before result supported opened accepted

/-- A successful actual hidden kernel receive returns a matching pre-existing CTX seal at the installed slot and opposite physical direction, retaining all seal histories and writer logs. -/
private theorem kernel_receive_origin (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (role : PqxdhRecordLiftInterface.Role)
    (slot : PqxdhRecordLiftInterface.Slot n) (entry : LabeledKernel n)
    (oriented : Oriented role (.hidden slot entry)) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (before : CtxPrivate n)
    (result : (StoredKernel n × core.option.Option RawCtxWholeOwner.Decrypted) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.kernelReceive (.hidden slot entry) target context)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (accepted : result.1.2 = .Some opened) :
    ∃ label, label.slot = slot ∧ label.direction = !sendDirection role ∧
      ∃ frame, codec.frameRead context.raw = some frame ∧
        ∃ old ∈ (before.keys label).1.successfulSeals, Matches frame old ∧ old.input.plaintext = opened.plaintext := by
  simp only [PqxdhRecordLiftProtocol.kernelReceive, bind_pure_comp, simulateQ_map,
    StateT.run_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  obtain ⟨label, origin, direction, rest⟩ := admitted_origin modes replace setup codec entry context target
    oriented.1 before inner reached opened accepted
  exact ⟨label, origin.trans oriented.2.1.2, direction.trans oriented.2.2.2, rest⟩

/-- Every successful actual owner receive is classified from its selected source storage without assuming that selection hidden or honest. -/
private theorem ownerReceive_accepted (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (handle : Handle) (owner : PqxdhRecordLiftWorldCompiler.Owner n)
    (stored : handleKernel control handle = some owner.kernel) (raw : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftWorldCompiler.Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerReceive codec.frameRead raw owner)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1.1 = .Some opened) :
    Accepted codec control before handle raw opened := by
  cases storedKind : owner.kernel with
  | known kernel =>
    exact Or.inl (known_of_handleKernel control handle kernel (by simpa only [storedKind] using stored))
  | hidden slot entry =>
    simp only [PqxdhRecordLiftProtocol.ownerReceive] at supported
    repeat' split at supported
    case h_2.isTrue =>
      simp only [storedKind, bind_pure_comp, simulateQ_map, StateT.run_map, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      obtain ⟨label, labelSlot, direction, decoded, parsed, old, member, matched, plaintext⟩ :=
        kernel_receive_origin modes replace setup codec (handleRole handle) slot entry
          (handleKernel_oriented control safe handle _ (by simpa only [storedKind] using stored))
          _ _ before inner reached opened returned
      refine Or.inr ⟨label, ?_, ?_, decoded, parsed, old, ?_, matched, plaintext⟩
      · simpa only [labelSlot] using handleKernel_slot control handle slot entry (by simpa only [storedKind] using stored)
      · simpa only [handleRole_direction] using direction
      · exact member
    all_goals simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    all_goals simp only [supported, reduceCtorEq] at returned

/-- The receive witness survives the actual publication tag, which may be absent on a routed Server receive. -/
private theorem ownerRun_accepted_tag (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (handle : Handle) (owner : PqxdhRecordLiftWorldCompiler.Owner n)
    (stored : handleKernel control handle = some owner.kernel) (tag : PqxdhDeploymentInterface.FrameTag)
    (sender : Std.U64) (raw : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftWorldCompiler.Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerRun tag sender codec.frameRead (.inr raw) owner)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1.1 = .Some opened) :
    Accepted codec control before handle raw opened := by
  simp only [PqxdhRecordLiftProtocol.ownerRun, PqxdhRecordLiftProtocol.ownerStep,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff] at supported
  obtain ⟨received, receiveSupported, published, _publishSupported, finished⟩ := supported
  obtain rfl := (mem_support_pure_iff _ _).mp finished
  exact ownerReceive_accepted modes replace setup codec control safe handle owner stored
    raw before received receiveSupported opened returned

/-- Every successful routed Server receive identifies its actual selected peer and exact source receive witness. -/
private theorem serverReceive_accepted (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (raw : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.serverStep codec.frameRead route (.inr raw) control)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1.1 = .Some opened) :
    ∃ handle, receivingHandle route .server raw = some handle ∧ Accepted codec control before handle raw opened := by
  cases existing : control.server with
  | none =>
    simp only [PqxdhRecordLiftProtocol.serverStep, existing, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    simp only [supported, reduceCtorEq] at returned
  | some server =>
    cases routed : route raw with
    | none =>
      simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      simp only [supported, reduceCtorEq] at returned
    | some keyId =>
      cases found : server.peers keyId with
      | none =>
        simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, found, simulateQ_pure,
          StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        simp only [supported, reduceCtorEq] at returned
      | some peer =>
        simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, found, bind_pure_comp,
          simulateQ_map, StateT.run_map, support_map] at supported
        obtain ⟨inner, reached, rfl⟩ := supported
        refine ⟨.peer keyId, by simp only [receivingHandle, routed, Option.map_some], ?_⟩
        apply ownerRun_accepted_tag modes replace setup codec control safe (.peer keyId)
          (PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer) _ _ server.sender raw
          before inner reached opened returned
        simp only [handleKernel, existing, Option.bind_some, found, Option.map_some,
          PqxdhRecordLiftWorldCompiler.serverOwner]


/-- Every successful Beacon receive retains its actual owner handle and source receive witness. -/
private theorem beaconReceive_accepted (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (owner : Nat) (raw : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.beaconStep codec.frameRead owner (.inr raw) control)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1.1 = .Some opened) :
    Accepted codec control before (.owner owner) raw opened := by
  rcases found : control.owners[owner]? with _ | (phase | ⟨shell, kernel⟩)
  · simp only [PqxdhRecordLiftProtocol.beaconStep, found, PqxdhDeploymentNative.absent,
      simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    simp only [supported, reduceCtorEq] at returned
  · simp only [PqxdhRecordLiftProtocol.beaconStep, found, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at supported
    simp only [supported, reduceCtorEq] at returned
  · simp only [PqxdhRecordLiftProtocol.beaconStep, found, bind_pure_comp,
      simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    apply ownerRun_accepted_tag modes replace setup codec control safe (.owner owner)
      (PqxdhRecordLiftWorldCompiler.beaconOwner shell kernel (control.ownerRaw owner))
      _ _ shell.identityKeyId raw before inner reached opened returned
    simp only [handleKernel, found, Option.bind_some, PqxdhRecordLiftWorldCompiler.beaconOwner]

open PqxdhRecordFactsOriginMetadataNative (Metadata)
open PqxdhRecordLiftFlat (KnownAt)
private theorem erased_owner_metadata (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (handle : Handle) (owner : Owner n)
    (stored : handleKernel control handle = some owner.kernel)
    (tag : PqxdhDeploymentInterface.FrameTag) (sender : Std.U64) (raw : Pqxdh.Bytes)
    (before : CtxPrivate n)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerRun tag sender codec.frameRead (.inr raw) owner)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1.1 = .Some opened) :
    KnownAt control handle ∨ Metadata codec.frameRead raw opened := by
  cases kind : owner.kernel with
  | known kernel => exact Or.inl (PqxdhRecordFactsOriginPublished.known_of_handleKernel control handle kernel (by simpa only [kind] using stored))
  | hidden slot entry =>
      exact Or.inr (PqxdhRecordFactsOriginReceiveMetadata.owner_run_metadata modes replace setup codec tag sender codec.frameRead
        raw owner slot entry kind before result supported opened returned)


/-- Server routing retains exact decoded metadata unless the stored peer was caller-known. -/
private theorem erased_server_metadata (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (control : PqxdhRecordLiftProtocol.Control n)
    (raw : Pqxdh.Bytes) (keyId : Std.U64) (routed : route raw = some keyId)
    (before : CtxPrivate n)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
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
      apply erased_owner_metadata modes replace setup codec control (.peer keyId)
        (PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer) _ _ server.sender raw
        before inner reached opened returned
      simp only [handleKernel, existing, Option.bind_some, found, Option.map_some,
        PqxdhRecordLiftWorldCompiler.serverOwner]

/-- Beacon dispatch retains decoded metadata unless the actual established owner was caller-known. -/
private theorem erased_beacon_metadata (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (index : Nat) (raw : Pqxdh.Bytes)
    (before : CtxPrivate n)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
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
    apply erased_owner_metadata modes replace setup codec control (.owner index)
      (PqxdhRecordLiftWorldCompiler.beaconOwner shell kernel (control.ownerRaw index))
      _ _ shell.identityKeyId raw before inner reached opened returned
    simp only [handleKernel, found, Option.bind_some, PqxdhRecordLiftWorldCompiler.beaconOwner]


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


private theorem original_received (modes : Label n →KeyMode) (replace : Pqxdh.Bytes →Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : PqxdhRecordLiftInterface.Environment n E)
    (query : Spec.Domain) (before : (E ×PqxdhRecordLiftProtocol.Control n) ×CtxPrivate n)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2)
    (result : Spec.Range query ×((E ×PqxdhRecordLiftProtocol.Control n) ×CtxPrivate n))
    (supported : result∈support ((CborRawRecordOriginService.original
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) env codec route query).run before))
    (receiver : PqxdhDeploymentInterface.Receiver) (raw : Pqxdh.Bytes) (opened : RawCtxWholeOwner.Decrypted)
    (received : (⟨.inl query,result.1⟩ : Entry).received=some (receiver,raw,.Some opened)) :
    ∃handle,receivingHandle route receiver raw=some handle ∧Accepted codec before.1.2 before.2 handle raw opened := by
  rcases query with coin | command
  · cases received
  · cases command <;> try cases received
    case serverRaw submitted =>
      simp only [Entry.received,Option.some.injEq,Prod.mk.injEq] at received
      obtain ⟨rfl,rfl,returned⟩ := received
      simp only [original_run,PqxdhRecordFactsOriginNative.native_serverRaw_run,simulateQ_map,StateT.run_map,
        Functor.map_map,support_map] at supported
      obtain ⟨inner,called,rfl⟩ := supported
      exact serverReceive_accepted modes replace setup codec route before.1.2 safe submitted before.2 inner called opened returned
    case beaconRaw owner submitted =>
      simp only [Entry.received,Option.some.injEq,Prod.mk.injEq] at received
      obtain ⟨rfl,rfl,returned⟩ := received
      simp only [original_run,PqxdhRecordFactsOriginNative.native_beaconRaw_run,simulateQ_map,StateT.run_map,
        Functor.map_map,support_map] at supported
      obtain ⟨inner,called,rfl⟩ := supported
      exact ⟨.owner owner,rfl,beaconReceive_accepted modes replace setup codec before.1.2 safe owner submitted before.2 inner called opened returned⟩

private theorem pure_apply {S X : Type} (value : X) (state : S) :
    (pure value : StateT S ProbComp X) state=pure (value,state) :=rfl

private theorem original_metadata (modes : Label n →KeyMode) (replace : Pqxdh.Bytes →Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : PqxdhRecordLiftInterface.Environment n E)
    (query : Spec.Domain) (before : (E ×PqxdhRecordLiftProtocol.Control n) ×CtxPrivate n)
    (result : Spec.Range query ×((E ×PqxdhRecordLiftProtocol.Control n) ×CtxPrivate n))
    (supported : result∈support ((CborRawRecordOriginService.original
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) env codec route query).run before))
    (receiver : PqxdhDeploymentInterface.Receiver) (raw : Pqxdh.Bytes) (opened : RawCtxWholeOwner.Decrypted)
    (received : (⟨.inl query,result.1⟩ : Entry).received=some (receiver,raw,.Some opened)) :
    ∃handle,receivingHandle route receiver raw=some handle ∧(KnownAt before.1.2 handle ∨Metadata codec.frameRead raw opened) := by
  rcases query with coin | command
  · cases received
  · cases command <;> try cases received
    case serverRaw submitted =>
      simp only [Entry.received,Option.some.injEq,Prod.mk.injEq] at received
      obtain ⟨rfl,rfl,returned⟩ := received
      simp only [original_run,PqxdhRecordFactsOriginNative.native_serverRaw_run,simulateQ_map,StateT.run_map,
        Functor.map_map,support_map] at supported
      obtain ⟨inner,called,rfl⟩ := supported
      cases routed : route submitted with
      | none=>
        cases existing : before.1.2.server <;>
          simp only [StateT.run,PqxdhRecordLiftProtocol.serverStep,existing,routed,simulateQ_pure,
            pure_apply,mem_support_pure_iff] at called <;>
          simp only [called,reduceCtorEq] at returned
      | some keyId=>
        exact ⟨.peer keyId,by simp only [receivingHandle,routed,Option.map_some],
          erased_server_metadata modes replace setup codec route before.1.2 submitted keyId routed before.2 inner called opened returned⟩
    case beaconRaw owner submitted =>
      simp only [Entry.received,Option.some.injEq,Prod.mk.injEq] at received
      obtain ⟨rfl,rfl,returned⟩ := received
      simp only [original_run,PqxdhRecordFactsOriginNative.native_beaconRaw_run,simulateQ_map,StateT.run_map,
        Functor.map_map,support_map] at supported
      obtain ⟨inner,called,rfl⟩ := supported
      exact ⟨.owner owner,rfl,erased_beacon_metadata modes replace setup codec before.1.2 owner submitted before.2 inner called opened returned⟩


/-- An actual erased native receive classifies its own routed handle and exact matching seal at the same pre-call private state. All warm caches, counters and refused raw attempts remain part of the original call. -/
theorem received_before (modes : Label n →KeyMode) (replace : Pqxdh.Bytes →Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : PqxdhRecordLiftInterface.Environment n E)
    (reserve : Nat →StateT E ProbComp (core.result.Result Unit Failure)) (query : Spec.Domain)
    (before : CborRawRecordFlat.NativeState n E) (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2)
    (result : Spec.Range query ×CborRawRecordFlat.NativeState n E)
    (supported : result∈support ((RegistrationNativePlatformGatedRecordFlat.native
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) env reserve codec route query).run before))
    (receiver : PqxdhDeploymentInterface.Receiver) (raw : Pqxdh.Bytes) (opened : RawCtxWholeOwner.Decrypted)
    (received : (⟨.inl query,result.1⟩ : Entry).received=some (receiver,raw,.Some opened)) :
    ∃handle,receivingHandle route receiver raw=some handle ∧Accepted codec before.1.2 before.2 handle raw opened := by
  have nonsending : PqxdhRecordFactsOriginPublicationNative.NonSending query := by
    rcases query with coin | command
    · trivial
    · cases command <;> simp_all only [PqxdhRecordFactsOriginPublicationNative.NonSending,Entry.received,reduceCtorEq]
  rw [RegistrationNativePlatformGatedRecordOriginStage.native_nonSend _ codec route env reserve query nonsending] at supported
  have projected : (result.1,CborRawRecordOriginService.project result.2)∈support
      ((CborRawRecordOriginService.original (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
        env codec route query).run (CborRawRecordOriginService.project before)) := by
    rw [←CborRawRecordOriginService.nonrecord_project _ env codec route query before ?_,support_map]
    · exact ⟨result,supported,rfl⟩
    · rcases query with coin | command
      · simp [PqxdhRecordLiftBudget.NativeRecord,PqxdhDeploymentCompileBudget.commandKind]
      · cases command <;> simp_all [PqxdhRecordFactsOriginPublicationNative.NonSending,PqxdhRecordLiftBudget.NativeRecord,PqxdhDeploymentCompileBudget.commandKind]
  exact original_received modes replace setup codec route env query (CborRawRecordOriginService.project before) safe
    (result.1,CborRawRecordOriginService.project result.2) projected receiver raw opened received

/-- The same erased full-ledger callback retains the original accepted raw entry and its own pre-call seal witness. Tests and fresh-message callbacks cannot synthesize a receive entry. -/
theorem full_received_before (modes : Label n →KeyMode) (replace : Pqxdh.Bytes →Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : PqxdhRecordLiftInterface.Environment n E)
    (reserve : Nat →StateT E ProbComp (core.result.Result Unit Failure))
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (query : FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger ×CborRawRecordFlat.NativeState n E)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before.2.1.2)
    (result : FullSpec.Range query ×(PqxdhDeploymentSecrecy.Ledger ×CborRawRecordFlat.NativeState n E))
    (supported : result∈support ((RegistrationNativePlatformGatedRecordFlat.full
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) env reserve setup.source.crypto codec route serverKeyId bounds query).run before))
    (receiver : PqxdhDeploymentInterface.Receiver) (raw : Pqxdh.Bytes) (opened : RawCtxWholeOwner.Decrypted)
    (received : (⟨query,result.1⟩ : Entry).received=some (receiver,raw,.Some opened)) :
    ∃handle,receivingHandle route receiver raw=some handle ∧Accepted codec before.2.1.2 before.2.2 handle raw opened := by
  rcases query with forwarded | secrecy
  · change result∈support ((fun inner => (inner.1.1,(inner.1.2,inner.2))) <$>
      (simulateQ (RegistrationNativePlatformGatedRecordFlat.native (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) env reserve codec route)
        ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKeyId bounds (.inl forwarded)).run before.1)).run before.2) at supported
    rw [support_map] at supported
    obtain ⟨inner,called,rfl⟩ := supported
    rw [PqxdhDeploymentSecrecy.ledgerImpl_forward,simulateQ_map,simulateQ_spec_query,StateT.run_map,support_map] at called
    obtain ⟨actual,reached,rfl⟩ := called
    exact received_before modes replace setup codec route env reserve forwarded before.2 safe actual reached receiver raw opened received
  · cases secrecy <;> simp [Entry.received] at received

/-- Actual erased raw metadata retains the known-owner classification or exact decoded sequence at the original prefix. -/
theorem received_sequence (modes : Label n →KeyMode) (replace : Pqxdh.Bytes →Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : PqxdhRecordLiftInterface.Environment n E)
    (reserve : Nat →StateT E ProbComp (core.result.Result Unit Failure)) (query : Spec.Domain)
    (before : CborRawRecordFlat.NativeState n E)
    (result : Spec.Range query ×CborRawRecordFlat.NativeState n E)
    (supported : result∈support ((RegistrationNativePlatformGatedRecordFlat.native
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) env reserve codec route query).run before))
    (receiver : PqxdhDeploymentInterface.Receiver) (raw : Pqxdh.Bytes) (opened : RawCtxWholeOwner.Decrypted)
    (received : (⟨.inl query,result.1⟩ : Entry).received=some (receiver,raw,.Some opened))
    (frame : RawCtxReceive.DecodedFrame) (decoded : codec.frameRead raw=some frame) :
    ∃handle,receivingHandle route receiver raw=some handle ∧(KnownAt before.1.2 handle ∨opened.sequence=frame.sequence) := by
  have nonsending : PqxdhRecordFactsOriginPublicationNative.NonSending query := by
    rcases query with coin | command
    · trivial
    · cases command <;> simp_all only [PqxdhRecordFactsOriginPublicationNative.NonSending,Entry.received,reduceCtorEq]
  rw [RegistrationNativePlatformGatedRecordOriginStage.native_nonSend _ codec route env reserve query nonsending] at supported
  have projected : (result.1,CborRawRecordOriginService.project result.2)∈support
      ((CborRawRecordOriginService.original (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
        env codec route query).run (CborRawRecordOriginService.project before)) := by
    rw [←CborRawRecordOriginService.nonrecord_project _ env codec route query before ?_,support_map]
    · exact ⟨result,supported,rfl⟩
    · rcases query with coin | command
      · simp [PqxdhRecordLiftBudget.NativeRecord,PqxdhDeploymentCompileBudget.commandKind]
      · cases command <;> simp_all [PqxdhRecordFactsOriginPublicationNative.NonSending,PqxdhRecordLiftBudget.NativeRecord,PqxdhDeploymentCompileBudget.commandKind]
  obtain ⟨handle,routed,known|⟨actualFrame,parsed,sequence,_sender⟩⟩ :=
    original_metadata modes replace setup codec route env query (CborRawRecordOriginService.project before)
      (result.1,CborRawRecordOriginService.project result.2) projected receiver raw opened received
  · exact ⟨handle,routed,Or.inl known⟩
  · have same := Option.some.inj (parsed.symm.trans decoded)
    exact ⟨handle,routed,Or.inr (same ▸sequence)⟩


/-- Full ledger forwarding preserves the same erased receive sequence classification without changing its original callback. -/
theorem full_received_sequence (modes : Label n →KeyMode) (replace : Pqxdh.Bytes →Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : PqxdhRecordLiftInterface.Environment n E)
    (reserve : Nat →StateT E ProbComp (core.result.Result Unit Failure))
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (query : FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger ×CborRawRecordFlat.NativeState n E)
    (result : FullSpec.Range query ×(PqxdhDeploymentSecrecy.Ledger ×CborRawRecordFlat.NativeState n E))
    (supported : result∈support ((RegistrationNativePlatformGatedRecordFlat.full
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) env reserve setup.source.crypto codec route serverKeyId bounds query).run before))
    (receiver : PqxdhDeploymentInterface.Receiver) (raw : Pqxdh.Bytes) (opened : RawCtxWholeOwner.Decrypted)
    (received : (⟨query,result.1⟩ : Entry).received=some (receiver,raw,.Some opened))
    (frame : RawCtxReceive.DecodedFrame) (decoded : codec.frameRead raw=some frame) :
    ∃handle,receivingHandle route receiver raw=some handle ∧(KnownAt before.2.1.2 handle ∨opened.sequence=frame.sequence) := by
  rcases query with forwarded | secrecy
  · change result∈support ((fun inner => (inner.1.1,(inner.1.2,inner.2))) <$>
      (simulateQ (RegistrationNativePlatformGatedRecordFlat.native (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) env reserve codec route)
        ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKeyId bounds (.inl forwarded)).run before.1)).run before.2) at supported
    rw [support_map] at supported
    obtain ⟨inner,called,rfl⟩ := supported
    rw [PqxdhDeploymentSecrecy.ledgerImpl_forward,simulateQ_map,simulateQ_spec_query,StateT.run_map,support_map] at called
    obtain ⟨actual,reached,rfl⟩ := called
    exact received_sequence modes replace setup codec route env reserve forwarded before.2 actual reached receiver raw opened received frame decoded
  · cases secrecy <;> simp [Entry.received] at received


end BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedReceive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedReceive.received_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedReceive.received_before

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedReceive.full_received_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedReceive.full_received_before

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedReceive.received_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedReceive.received_sequence

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedReceive.full_received_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedReceive.full_received_sequence
