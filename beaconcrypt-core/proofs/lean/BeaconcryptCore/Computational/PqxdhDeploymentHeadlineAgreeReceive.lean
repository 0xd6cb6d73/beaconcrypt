-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal

/-!
# AG, receive side: accepted hidden receives keep the receiving handle's associated data (CE-12 P2b, design-v2 section 7.7)

The second ingredient of AG: in every ideal CTX world (`PqxdhRecordLiftIdeal.ctxRun` in any assignment of the replay and random modes, in particular `idealAuth`), every accepted raw receive recorded in the ledger's transcript on a hidden handle matches a pre-existing replay-dictionary seal at the handle's slot and opposite physical direction whose plaintext is the returned plaintext and whose record AD bytes are the receiving handle's AD (`PqxdhDeploymentHeadlineAgreeSeal.handleAd`).

The replay acceptance of the ideal worlds (`AdaptiveCtxReplayDictionary.replayPlaintext`, `AdaptiveCtxReplayDictionary.lean:12-14`) matches the complete tuple of nonce, record context and encoded record; the record context's AD (`Pqxdh.RecordAD`) carries the 153 AD bytes, the sequence and the sender. The frozen origin facts keep the sequence, sender and payload (`PqxdhRecordFactsOriginReplay.Matches`) and the plaintext, but drop the AD bytes. This module keeps them along the same proof route:

- `keyRaw_frame_ad`, `keyed_frame_ad`: an accepted keyed raw request has a matching seal whose record AD bytes are the universal envelope's AD (the decoder target is `RawCtxKeyFreeDecoder.target`, whose record AD bytes are the envelope's).
- `opening_frame_ad`: the hidden opening service's envelope carries the pending opening context's AD (`PqxdhRecordLiftCtxHybrid.openArguments_facts`).
- `receive_origin_ad`, `admitted_origin_ad`, `kernel_receive_origin_ad`: the recursive source receive opens with its own context (`PqxdhRecordLiftChainState.Tracked`), through every skipped-key callback.
- `AcceptedAd` (the frozen `PqxdhRecordFactsOriginAccepted.Accepted` with the AD conjunct `handleAd control handle = some entry.input.context.ad.bytes`), `ownerReceive_acceptedAd` (the owner receive opens with `owner.associatedData`), `ownerRun_acceptedAd`, `serverReceive_acceptedAd`, `beaconReceive_acceptedAd` (the selected owner's AD is the handle's AD: `handleAd_peer`, `handleAd_owner`), and the native commands `native_serverRaw_acceptedAd`, `native_beaconRaw_acceptedAd`.
- `EntryAd` (every successful raw receive of a transcript entry has its receiving handle and `AcceptedAd`), persistence `acceptedAd_mono`, `entryAd_mono` (with `PqxdhDeploymentHeadlineAgreeSeal.AdKept`), `native_entryAd`, `full_record_ad` (the ledger appends exactly one entry, `PqxdhRecordLiftFlat.ledger_append`; secrecy entries record no raw receive), the ledger invariant `InvariantAd` with `full_invariant_ad` and `full_program_invariant_ad`, and `ctxRun_entryAd`: every transcript entry of every supported outcome of every ideal CTX world satisfies `EntryAd` at the final control and private state.

Unlike the frozen `ctxRun_entryFacts`, no `FrameReadBack` premise is needed, because only receives are tracked. No assumption or contract is added, and no `PqxdhBoundary*` module is imported.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftFlat
open PqxdhRecordFactsOriginHandles PqxdhRecordFactsOriginReplay
open PqxdhDeploymentHeadlineAgreeSeal (handleAd AdKept handleAd_peer handleAd_owner native_adKept full_adKept)
open PqxdhRecordLiftProtocolHistory (Safe Step)
open PqxdhRecordLiftWorldCompiler (Label StoredKernel LabeledKernel)
open PqxdhDeploymentInterface (Handle FrameTag Receiver Spec FullSpec Entry FreshBounds Mode ModeSpec asModeO)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- An accepted keyed raw request in either ideal mode has a source-frame witness, its exact dictionary plaintext and the envelope's AD as the seal's record AD bytes. -/
theorem keyRaw_frame_ad (read : RawCtxReceive.FrameDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (mode : KeyMode) (ideal : mode ≠ .real) (envelope : RawCtxUniversalDecoder.Envelope)
    (before : KeyEntry) (plaintext : Pqxdh.Bytes) (after : KeyEntry)
    (supported : (some plaintext, after) ∈ support
      ((keyImpl (RawCtxUniversalDecoder.decoder read) crypto key mode
        (.inr (RawCtxUniversalDecoder.pack envelope))).run before)) :
    ∃ frame, read envelope.raw = some frame ∧ ∃ entry ∈ before.1.successfulSeals,
      Matches frame entry ∧ entry.input.plaintext = plaintext ∧ entry.input.context.ad.bytes = envelope.ad.toList := by
  obtain ⟨target, decoded, entry, member, nonce, context, record, value⟩ :=
    keyRaw_witness (RawCtxUniversalDecoder.decoder read) crypto key mode ideal _ before plaintext after supported
  obtain ⟨frame, readFrame, slices, parsed, rfl⟩ := decoder_frame read envelope target decoded
  exact ⟨frame, readFrame, entry, member,
    target_matches envelope.nonce frame envelope.ad.toList slices parsed envelope.ad.2 entry
      ⟨nonce, context, record⟩, value, (congrArg Pqxdh.RecordAD.bytes context).symm⟩

/-- A successful global keyed receive has a matching source frame in the selected coordinate's existing dictionary, with its plaintext and the envelope's AD as record AD bytes. -/
theorem keyed_frame_ad (modes : Label n → KeyMode)
    (read : RawCtxReceive.FrameDecoder) (crypto : Pqxdh.Crypto)
    (label : Label n) (ideal : modes label ≠ .real)
    (envelope : RawCtxUniversalDecoder.Envelope) (before after : CtxPrivate n) (plaintext : Pqxdh.Bytes)
    (supported : (some plaintext, after) ∈ support
      ((keyed modes (RawCtxUniversalDecoder.decoder read) crypto
        (label, .inr (RawCtxUniversalDecoder.pack envelope))).run before)) :
    ∃ frame, read envelope.raw = some frame ∧ ∃ entry ∈ (before.keys label).1.successfulSeals,
      Matches frame entry ∧ entry.input.plaintext = plaintext ∧ entry.input.context.ad.bytes = envelope.ad.toList := by
  obtain ⟨localAfter, reached, _⟩ := PqxdhRecordFactsOriginDictionary.keyed_witness modes
    (RawCtxUniversalDecoder.decoder read) crypto (label, .inr (RawCtxUniversalDecoder.pack envelope)) before
    (some plaintext, after) supported
  exact keyRaw_frame_ad read crypto (materialAt before.base.chain label).1 (modes label) ideal
    envelope (before.keys label) plaintext localAfter reached

/-- Every accepted hidden opening in an ideal mode refers to a pre-existing coordinate dictionary entry with the returned plaintext and the pending opening context's AD as record AD bytes. -/
theorem opening_frame_ad (modes : Label n → KeyMode)
    (ideal : ∀ label, modes label ≠ .real) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (pending : PqxdhRecordLiftProtocol.Opening n) (before after : CtxPrivate n)
    (opened : RawCtxWholeOwner.Decrypted)
    (supported : (.Some opened, after) ∈ support
      ((ctxInterpreter modes replace setup codec (.opening pending)).run before)) :
    ∃ label, RawCtxInterpretedOpening.material pending = .ok (.Some label) ∧
      ∃ frame, codec.frameRead pending.context.raw = some frame ∧
      ∃ entry ∈ (before.keys label).1.successfulSeals,
        Matches frame entry ∧ entry.input.plaintext = opened.plaintext ∧
          entry.input.context.ad.bytes = pending.context.associatedData := by
  change (.Some opened, after) ∈ support ((simulateQ
    (keyed modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto)
    (hiddenOpening (PqxdhRecordLiftProtocol.cachedSeeds before.base) before.base.chain pending)).run before) at supported
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
          have replyEq : RawCtxSharedOpeningConsumer.apiReply input.sequence input.context (some plaintext) = .Some opened :=
            congrArg Prod.fst equal
          cases replyEq
          have contextEq : input.context = pending.context :=
            (PqxdhRecordLiftCtxHybrid.openArguments_facts _ input arguments).2
          obtain ⟨frame, readFrame, entry, member, matched, message, adEq⟩ :=
            keyed_frame_ad modes codec.frameRead setup.source.crypto input.material (ideal input.material)
              (RawCtxUniversalDecoder.envelope (materialAt before.base.chain input.material).2 input.context width)
              before secret plaintext reached
          refine ⟨input.material, ?_, frame, by simpa only [RawCtxUniversalDecoder.envelope, contextEq] using readFrame,
            entry, member, matched, message, ?_⟩
          · simpa only [RawCtxChainInterpretation.opening_material_chains] using
              PqxdhRecordLiftCtxAvailability.openArguments_material _ input arguments
          · rw [adEq, ← contextEq]
            rfl
      · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        cases congrArg Prod.fst supported

/-- A returned plaintext has an earlier exact seal at the receive coordinate's slot and direction, with the plaintext and the receive context's AD as record AD bytes. -/
def ReceiveOriginAd (codec : PqxdhServerAuthExperiment.Codec Reader Response) (anchor : Label n)
    (context : RawCtxWholeOwner.OpenContext) (before : CtxPrivate n) (opened : RawCtxWholeOwner.Decrypted) : Prop :=
  ∃ label, label.slot = anchor.slot ∧ label.direction = anchor.direction ∧
    ∃ frame, codec.frameRead context.raw = some frame ∧
      ∃ entry ∈ (before.keys label).1.successfulSeals, Matches frame entry ∧
        entry.input.plaintext = opened.plaintext ∧ entry.input.context.ad.bytes = context.associatedData

/-- Successful recursive source receive returns an earlier exact seal witness with the receive context's AD, through every skipped-key callback. -/
theorem receive_origin_ad (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
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
    (supported : result ∈ support (PqxdhRecordFactsOriginReceive.receiveRun modes replace setup codec effect before))
    (opened : RawCtxWholeOwner.Decrypted) (accepted : result.1.2 = .Some opened) :
    ReceiveOriginAd codec entry.receive_chain context before opened := by
  generalize hdepth : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect before result with
  | h depth ih =>
      cases effect with
      | rejected original prior =>
          simp only [PqxdhRecordFactsOriginReceive.receiveRun, PqxdhRecordLiftOpaqueDrivers.receiveProgram, simulateQ_pure,
            StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          simp only [supported, reduceCtorEq] at accepted
      | openRequested pending =>
          simp only [PqxdhRecordFactsOriginReceive.receiveRun, PqxdhRecordLiftOpaqueDrivers.receiveProgram, bind_pure_comp,
            simulateQ_map, simulateQ_spec_query, PqxdhRecordLiftProtocol.localLift,
            StateT.run_map, support_map] at supported
          obtain ⟨reply, reached, rfl⟩ := supported
          have serviceAccepted : reply.1 = .Some opened :=
            (PqxdhRecordFactsOriginReceive.finish_reply pending reply.1).symm.trans accepted
          obtain ⟨label, material, frame, decoded, sealedEntry, member, matched, plaintext, adEq⟩ :=
            opening_frame_ad modes ideal replace setup codec pending before reply.2 opened
              (by simpa only [← serviceAccepted, Prod.mk.eta] using reached)
          obtain ⟨sequence, _, origin⟩ := PqxdhRecordLiftMaterialTable.opening_attributed
            entry.receive_chain pending attributed label material
          exact ⟨label, origin.1, origin.2.1, frame, by simpa only [tracked.2.1] using decoded,
            sealedEntry, member, matched, plaintext, by simpa only [tracked.2.1] using adEq⟩
      | kdfRequested pending =>
          simp only [PqxdhRecordFactsOriginReceive.receiveRun, PqxdhRecordLiftOpaqueDrivers.receiveProgram, simulateQ_bind,
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
          simpa only [ReceiveOriginAd, (PqxdhRecordFactsOriginReceive.lookup_preserves modes replace setup codec
            pending.request before looked reached).1] using nextOrigin

/-- The source admission operation supplies the callback premises of `receive_origin_ad` from the kernel certificate. -/
theorem admitted_origin_ad (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (entry : LabeledKernel n)
    (context : RawCtxWholeOwner.OpenContext) (target : Std.U64)
    (certified : PqxdhRecordLiftChainCoordinates.Certified entry) (before : CtxPrivate n)
    (result : (LabeledKernel n × core.option.Option RawCtxWholeOwner.Decrypted) × CtxPrivate n)
    (supported : result ∈ support (PqxdhRecordFactsOriginReceive.receiveRun modes replace setup codec
      (RawCtxChainReceive.normalBegin entry target context) before))
    (opened : RawCtxWholeOwner.Decrypted) (accepted : result.1.2 = .Some opened) :
    ReceiveOriginAd codec entry.receive_chain context before opened :=
  receive_origin_ad modes ideal replace setup codec entry context target certified.2.1 _
    (PqxdhRecordLiftChainState.begin_tracked entry context target)
    (PqxdhFirstRecordReplay.begin_admitted entry target context certified.1.capacity)
    (PqxdhRecordLiftMaterialTable.begin_attributed entry.receive_chain entry certified.2.2 target context)
    before result supported opened accepted

/-- A successful hidden kernel receive returns a matching pre-existing seal at the installed slot and opposite physical direction, with the returned plaintext and the receive context's AD as record AD bytes, retaining all seal histories and writer logs. -/
theorem kernel_receive_origin_ad (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (role : Role)
    (slot : Slot n) (entry : LabeledKernel n)
    (oriented : PqxdhRecordLiftWorldProvenance.Oriented role (.hidden slot entry)) (target : Std.U64)
    (context : RawCtxWholeOwner.OpenContext) (before : CtxPrivate n)
    (result : (StoredKernel n × core.option.Option RawCtxWholeOwner.Decrypted) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.kernelReceive (.hidden slot entry) target context)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (accepted : result.1.2 = .Some opened) :
    PqxdhRecordFactsOriginReceive.Retained before result.2 ∧
      ∃ label, label.slot = slot ∧ label.direction = !PqxdhRecordLiftWorldProvenance.sendDirection role ∧
      ∃ frame, codec.frameRead context.raw = some frame ∧
        ∃ old ∈ (before.keys label).1.successfulSeals, Matches frame old ∧
          old.input.plaintext = opened.plaintext ∧ old.input.context.ad.bytes = context.associatedData := by
  simp only [PqxdhRecordLiftProtocol.kernelReceive, bind_pure_comp, simulateQ_map,
    StateT.run_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  refine ⟨PqxdhRecordFactsOriginReceive.receive_retained modes ideal replace setup codec _ before inner reached, ?_⟩
  obtain ⟨label, origin, direction, rest⟩ := admitted_origin_ad modes ideal replace setup codec entry context target
    oriented.1 before inner reached opened accepted
  exact ⟨label, origin.trans oriented.2.1.2, direction.trans oriented.2.2.2, rest⟩

/-- The frozen accepted-receive witness with the AD: the handle is caller-known, or the frame matches a seal at the handle's slot and opposite direction whose plaintext is the returned plaintext and whose record AD bytes are the handle's AD. -/
def AcceptedAd (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n)
    (handle : Handle) (raw : Pqxdh.Bytes) (opened : RawCtxWholeOwner.Decrypted) : Prop :=
  KnownAt control handle ∨
    ∃ label, handleSlot control handle = some label.slot ∧ label.direction = !handleDirection handle ∧
      ∃ frame, codec.frameRead raw = some frame ∧
      ∃ entry ∈ (secret.keys label).1.successfulSeals, Matches frame entry ∧
        entry.input.plaintext = opened.plaintext ∧ handleAd control handle = some entry.input.context.ad.bytes

/-- Every successful owner receive opens with the owner's AD, so a hidden receive has an `AcceptedAd` witness when the owner's AD is the handle's AD. -/
theorem ownerReceive_acceptedAd (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : Safe control)
    (handle : Handle) (owner : PqxdhRecordLiftWorldCompiler.Owner n)
    (stored : handleKernel control handle = some owner.kernel)
    (adStored : handleAd control handle = some owner.associatedData) (raw : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftWorldCompiler.Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerReceive codec.frameRead raw owner)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1.1 = .Some opened) :
    AcceptedAd codec control result.2 handle raw opened := by
  cases storedKind : owner.kernel with
  | known kernel =>
    exact Or.inl (PqxdhRecordFactsOriginPublished.known_of_handleKernel control handle kernel
      (by simpa only [storedKind] using stored))
  | hidden slot entry =>
    simp only [PqxdhRecordLiftProtocol.ownerReceive] at supported
    repeat' split at supported
    case h_2.isTrue =>
      simp only [storedKind, bind_pure_comp, simulateQ_map, StateT.run_map, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      obtain ⟨kept, label, labelSlot, direction, decoded, parsed, old, member, matched, plaintext, adEq⟩ :=
        kernel_receive_origin_ad modes ideal replace setup codec (handleRole handle) slot entry
          (handleKernel_oriented control safe handle _ (by simpa only [storedKind] using stored))
          _ _ before inner reached opened returned
      refine Or.inr ⟨label, ?_, ?_, decoded, parsed, old, ?_, matched, plaintext, ?_⟩
      · simpa only [labelSlot] using handleKernel_slot control handle slot entry (by simpa only [storedKind] using stored)
      · simpa only [handleRole_direction] using direction
      · simpa only [kept.seals] using member
      · rw [adEq]
        exact adStored
    all_goals simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    all_goals simp only [supported, reduceCtorEq] at returned

/-- The complete owner receive command keeps its `AcceptedAd` witness through its publication callback. -/
theorem ownerRun_acceptedAd (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : Safe control)
    (handle : Handle) (owner : PqxdhRecordLiftWorldCompiler.Owner n)
    (stored : handleKernel control handle = some owner.kernel)
    (adStored : handleAd control handle = some owner.associatedData) (tag : FrameTag)
    (sender : Std.U64) (raw : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftWorldCompiler.Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerRun tag sender codec.frameRead (.inr raw) owner)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1.1 = .Some opened) :
    AcceptedAd codec control result.2 handle raw opened := by
  simp only [PqxdhRecordLiftProtocol.ownerRun, PqxdhRecordLiftProtocol.ownerStep,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff] at supported
  obtain ⟨received, receiveSupported, published, publishSupported, finished⟩ := supported
  rw [PqxdhRecordFactsOriginBuffers.publish_callback, support_pure, Set.mem_singleton_iff] at publishSupported
  subst published
  obtain rfl := (mem_support_pure_iff _ _).mp finished
  exact ownerReceive_acceptedAd modes ideal replace setup codec control safe handle owner stored adStored
    raw before received receiveSupported opened returned

/-- Every successful routed Server receive identifies its selected peer, whose AD is the selected source owner's, with an `AcceptedAd` witness. -/
theorem serverReceive_acceptedAd (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : Safe control)
    (raw : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.serverStep codec.frameRead route (.inr raw) control)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1.1 = .Some opened) :
    ∃ handle, receivingHandle route .server raw = some handle ∧ AcceptedAd codec control result.2 handle raw opened := by
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
        apply ownerRun_acceptedAd modes ideal replace setup codec control safe (.peer keyId)
          (PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer) _
          (handleAd_peer control server existing keyId peer found) _ server.sender raw
          before inner reached opened returned
        simp only [handleKernel, existing, Option.bind_some, found, Option.map_some,
          PqxdhRecordLiftWorldCompiler.serverOwner]

/-- Every successful Beacon receive has an `AcceptedAd` witness on its established owner handle. -/
theorem beaconReceive_acceptedAd (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : Safe control)
    (owner : Nat) (raw : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.beaconStep codec.frameRead owner (.inr raw) control)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1.1 = .Some opened) :
    AcceptedAd codec control result.2 (.owner owner) raw opened := by
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
    apply ownerRun_acceptedAd modes ideal replace setup codec control safe (.owner owner)
      (PqxdhRecordLiftWorldCompiler.beaconOwner shell kernel (control.ownerRaw owner))
      _ (handleAd_owner control owner shell kernel found (control.ownerRaw owner)) _ shell.identityKeyId raw
      before inner reached opened returned
    simp only [handleKernel, found, Option.bind_some, PqxdhRecordLiftWorldCompiler.beaconOwner]

/-- A successful native Server receive keeps its routed handle and `AcceptedAd` witness. -/
theorem native_serverRaw_acceptedAd (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (raw : Pqxdh.Bytes) (before : NativeState n E) (safe : Safe before.1.2)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env (.inr (.serverRaw raw))).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1 = .Some opened) :
    ∃ handle, receivingHandle route .server raw = some handle ∧
      AcceptedAd codec before.1.2 result.2.2 handle raw opened := by
  simp only [nativeImpl_run, PqxdhRecordFactsOriginNative.native_serverRaw_run, simulateQ_map, StateT.run_map,
    Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact serverReceive_acceptedAd modes ideal replace setup codec route before.1.2 safe raw
    before.2 inner reached opened returned

/-- A successful native Beacon receive keeps its owner handle and `AcceptedAd` witness. -/
theorem native_beaconRaw_acceptedAd (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (owner : Nat) (raw : Pqxdh.Bytes) (before : NativeState n E) (safe : Safe before.1.2)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env (.inr (.beaconRaw owner raw))).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1 = .Some opened) :
    AcceptedAd codec before.1.2 result.2.2 (.owner owner) raw opened := by
  simp only [nativeImpl_run, PqxdhRecordFactsOriginNative.native_beaconRaw_run, simulateQ_map, StateT.run_map,
    Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact beaconReceive_acceptedAd modes ideal replace setup codec before.1.2 safe owner raw
    before.2 inner reached opened returned

/-- An `AcceptedAd` witness survives control steps with persisting caller-known handles and ADs and seal-dictionary growth. -/
theorem acceptedAd_mono (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control next : PqxdhRecordLiftProtocol.Control n) (before after : CtxPrivate n)
    (progress : Step control next) (known : ∀ handle, KnownAt control handle → KnownAt next handle)
    (seals : ∀ label entry, entry ∈ (before.keys label).1.successfulSeals → entry ∈ (after.keys label).1.successfulSeals)
    (kept : AdKept control next) (handle : Handle) (raw : Pqxdh.Bytes) (opened : RawCtxWholeOwner.Decrypted)
    (good : AcceptedAd codec control before handle raw opened) :
    AcceptedAd codec next after handle raw opened := by
  rcases good with good | ⟨label, slot, direction, frame, decoded, entry, member, matched, plaintext, adEq⟩
  · exact Or.inl (known handle good)
  · exact Or.inr ⟨label, handleSlot_step control next progress handle label.slot slot, direction, frame, decoded,
      entry, seals label entry member, matched, plaintext, kept handle _ adEq⟩

/-- Every successful raw receive of a transcript entry has its receiving handle and an `AcceptedAd` witness. -/
def EntryAd (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (control : PqxdhRecordLiftProtocol.Control n)
    (secret : CtxPrivate n) (entry : Entry) : Prop :=
  ∀ receiver raw opened, entry.received = some (receiver, raw, .Some opened) →
    ∃ handle, receivingHandle route receiver raw = some handle ∧ AcceptedAd codec control secret handle raw opened

/-- `EntryAd` survives control steps with persisting caller-known handles and ADs and seal-dictionary growth. -/
theorem entryAd_mono (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (control next : PqxdhRecordLiftProtocol.Control n)
    (before after : CtxPrivate n) (progress : Step control next)
    (known : ∀ handle, KnownAt control handle → KnownAt next handle)
    (seals : ∀ label entry, entry ∈ (before.keys label).1.successfulSeals → entry ∈ (after.keys label).1.successfulSeals)
    (kept : AdKept control next) (entry : Entry) (good : EntryAd codec route control before entry) :
    EntryAd codec route next after entry := by
  intro receiver raw opened returned
  obtain ⟨handle, routed, accepted⟩ := good receiver raw opened returned
  exact ⟨handle, routed, acceptedAd_mono codec control next before after progress known seals kept handle raw opened accepted⟩

/-- Every native reply gives `EntryAd` for its forwarded entry at the control before the command. -/
theorem native_entryAd_before (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (query : Spec.Domain) (before : NativeState n E) (safe : Safe before.1.2)
    (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env query).run before)) :
    EntryAd codec route before.1.2 result.2.2 ⟨.inl query, result.1⟩ := by
  rcases query with coin | command
  · simp [EntryAd, Entry.received]
  · cases command <;> simp only [EntryAd, Entry.received, reduceCtorEq, false_implies, implies_true]
    case serverRaw raw =>
      simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
      rintro _ _ opened rfl rfl returned
      exact native_serverRaw_acceptedAd modes ideal replace setup codec route env raw before safe result supported
        opened returned
    case beaconRaw owner raw =>
      simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
      rintro _ _ opened rfl rfl returned
      exact ⟨.owner owner, rfl, native_beaconRaw_acceptedAd modes ideal replace setup codec route env
        owner raw before safe result supported opened returned⟩

/-- Every native reply gives `EntryAd` for its forwarded entry at the final control and private state. -/
theorem native_entryAd (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (query : Spec.Domain) (before : NativeState n E) (safe : Safe before.1.2)
    (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env query).run before)) :
    EntryAd codec route result.2.1.2 result.2.2 ⟨.inl query, result.1⟩ :=
  entryAd_mono codec route before.1.2 result.2.1.2 result.2.2 result.2.2
    (PqxdhRecordFactsOriginControl.native_step modes replace setup codec route env query before safe result supported)
    (fun handle known => nativeImpl_known modes replace setup codec route env handle
      query before known result supported)
    (fun _ _ member => member)
    (native_adKept modes replace setup codec route env query before result supported) _
    (native_entryAd_before modes ideal replace setup codec route env query before safe result supported)

/-- One secrecy-ledger command appends exactly one entry with `EntryAd` at its final state; secrecy entries record no raw receive. -/
theorem full_record_ad (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E) (safe : Safe before.2.1.2)
    (result : FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((fullImpl modes replace setup codec route env serverKid bounds query).run before)) :
    ∃ reply, result.2.1.transcript = before.1.transcript ++ [⟨query, reply⟩] ∧
      EntryAd codec route result.2.2.1.2 result.2.2.2 ⟨query, reply⟩ := by
  rw [fullImpl_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  rcases query with forwarded | secrecy
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query,
      StateT.run_map, support_map] at reached
    obtain ⟨native, nativeReached, rfl⟩ := reached
    exact ⟨native.1, rfl, native_entryAd modes ideal replace setup codec route env forwarded before.2 safe
      native nativeReached⟩
  · obtain ⟨reply, appended⟩ := ledger_append setup.source.crypto codec serverKid bounds (.inr secrecy) before.1
      inner.1 (support_run_fst _ _ _ inner reached)
    refine ⟨reply, appended, ?_⟩
    intro receiver raw opened received
    cases secrecy <;> simp [Entry.received] at received

/-- The ledger invariant: source control safety, and `EntryAd` for every transcript entry at the current control and private state. -/
def InvariantAd (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (state : PqxdhDeploymentSecrecy.Ledger × NativeState n E) : Prop :=
  Safe state.2.1.2 ∧ ∀ entry ∈ state.1.transcript, EntryAd codec route state.2.1.2 state.2.2 entry

/-- One secrecy-ledger command keeps the ledger invariant. -/
theorem full_invariant_ad (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E) (good : InvariantAd codec route before)
    (result : FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((fullImpl modes replace setup codec route env serverKid bounds query).run before)) :
    InvariantAd codec route result.2 := by
  have progress := PqxdhRecordFactsOriginControl.full_step modes replace setup codec route env serverKid bounds query
    before good.1 result supported
  have grows := PqxdhRecordFactsOriginMonotone.full_grows modes ideal replace setup codec route env serverKid bounds
    query before result supported
  have kept := full_adKept modes replace setup codec route env serverKid bounds query before result supported
  obtain ⟨reply, appended, fresh⟩ := full_record_ad modes ideal replace setup codec route env serverKid bounds query
    before good.1 result supported
  refine ⟨progress.1, ?_⟩
  intro entry member
  rw [appended, List.mem_append, List.mem_singleton] at member
  rcases member with prior | rfl
  · exact entryAd_mono codec route before.2.1.2 result.2.2.1.2 before.2.2 result.2.2.2 progress
      (fun handle known => PqxdhRecordFactsOriginControl.full_known modes replace setup codec route env serverKid bounds
        query before handle known result supported)
      grows.seals kept entry (good.2 entry prior)
  · exact fresh

/-- Every adaptive full continuation keeps the ledger invariant. -/
theorem full_program_invariant_ad (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (client : OracleComp FullSpec X)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E) (good : InvariantAd codec route before)
    (result : X × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((simulateQ (fullImpl modes replace setup codec route env serverKid bounds) client).run before)) :
    InvariantAd codec route result.2 :=
  support_keep_oracle (fullImpl modes replace setup codec route env serverKid bounds)
    (InvariantAd codec route)
    (fun query state invariant => full_invariant_ad modes ideal replace setup codec route env serverKid bounds query
      state invariant)
    client before good result supported

/-- Every transcript entry of every supported outcome of every ideal CTX world satisfies `EntryAd` at the final control and private state. -/
theorem ctxRun_entryAd (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary)) :
    ∀ value ∈ result.1.1, ∀ entry ∈ value.2.1.2.transcript, EntryAd codec route result.1.2 result.2 entry := by
  rw [ctxRun_flat] at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨born, bornSupported, continued⟩ := supported
  have bornSafe := PqxdhRecordFactsOriginGlobal.startup_safe modes replace setup codec route env born bornSupported
  cases bornEq : born.1.1 with
  | none =>
    simp only [bornEq] at continued
    obtain rfl := (mem_support_pure_iff _ _).mp continued
    simp
  | some initial =>
    rcases initial with ⟨created, initial⟩
    simp only [bornEq] at continued
    rw [mem_support_bind_iff] at continued
    obtain ⟨installed, installSupported, continued⟩ := continued
    have installedSafe := PqxdhRecordFactsOriginGlobal.install_safe modes replace setup codec route created born.1.2
      bornSafe born.2 installed installSupported
    rw [support_map] at continued
    obtain ⟨final, finalSupported, rfl⟩ := continued
    have complete := full_program_invariant_ad modes ideal replace setup codec route env serverKid bounds
      (asModeO mode adversary) _ ⟨installedSafe, by simp [PqxdhDeploymentSecrecy.Ledger.empty]⟩ final finalSupported
    intro value member
    have equal := Option.some.inj member
    subst value
    exact complete.2

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.keyRaw_frame_ad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.keyRaw_frame_ad

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.keyed_frame_ad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.keyed_frame_ad

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.opening_frame_ad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.opening_frame_ad

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.receive_origin_ad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.receive_origin_ad

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.admitted_origin_ad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.admitted_origin_ad

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.kernel_receive_origin_ad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.kernel_receive_origin_ad

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.ownerReceive_acceptedAd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.ownerReceive_acceptedAd

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.ownerRun_acceptedAd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.ownerRun_acceptedAd

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.serverReceive_acceptedAd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.serverReceive_acceptedAd

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.beaconReceive_acceptedAd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.beaconReceive_acceptedAd

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.native_serverRaw_acceptedAd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.native_serverRaw_acceptedAd

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.native_beaconRaw_acceptedAd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.native_beaconRaw_acceptedAd

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.acceptedAd_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.acceptedAd_mono

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.entryAd_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.entryAd_mono

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.native_entryAd_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.native_entryAd_before

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.native_entryAd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.native_entryAd

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.full_record_ad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.full_record_ad

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.full_invariant_ad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.full_invariant_ad

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.full_program_invariant_ad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.full_program_invariant_ad

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.ctxRun_entryAd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive.ctxRun_entryAd
