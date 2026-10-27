-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor
import BeaconcryptCore.Computational.PqxdhDeploymentHiddenLayout
import BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence

/-!
# CE-12 D-ct: keyed commitments of the sequence-one record (receive and open level)

The commitment check of a record (`beaconcrypt/src/ratchet.rs`, `execute_open`) hashes `K ‖ N ‖ AD ‖ T ‖ LE64(seq) ‖ LE64(kid)` with BLAKE2b-512 before the AEAD, where `K` is the 32-byte message key of the opened sequence. This module identifies, on the shared native record primitives (`RawCtxSharedPrimitive.nativeImpl` on the shared BLAKE2b cache), the cache entry that a successful opening leaves: `KeyedCommit frame cache key` says that the frame's record carries a commitment digest that the cache holds at an input whose first 32 bytes are `key`.

- `open_keyed`: a successful opening of the shared native primitives (`RawCtxSharedPrimitive.openingImpl` on the open program `RawCtxSourceOpen.openInput`) caches the commitment input of the input's material key with the frame's commitment digest (`RawCtxSourceOpen.openInput_success`, `hashInput_take`, the cached BLAKE2b reply).
- The Beacon's first receive. `chainRaw_success` decomposes a successful raw receive of a chain owner. `chain_keyed`: the Beacon's local chain owner on the initial kernel of a 108-byte factor (`PqxdhServerAuthBeaconFactor.initial`, a hidden receive chain answered by the factor's ratchet response), on the actual shared receive primitives (`nativePrim`), receiving a frame at sequence one, makes exactly one derivation and one opening (`PqxdhServerAuthBeaconFirstOpening.execute_one`), and the opening's material is the decoded factor response's material; so the final cache holds the frame's commitment at an input keyed by that material's key. `factored_keyed` is the same for the factored post-root tail (`PqxdhServerAuthBeaconFactor.factored`) and `whole_keyed` for the concrete local owner on the Beacon's initial kernel of a root (`normalInitial (beaconPending (rootArray root))`), where a message of sequence one forces the frame's sequence to be one (`RawCtxOwnerProvenance.raw_success`) and the concrete receive is the factored one (`initial_source`, `RawCtxChainOwner.rawReceive_native`, `primitive_receive`). As in `beaconcrypt/src/ratchet.rs`, the Beacon opens at the frame's sequence; only the post-opening sequence-one gate (`afterOpening`) makes the hashed key the sequence-one key.
- The key. `seqKey setup prk` is the key part of the material of the real key schedule of an R1 value `prk` (root Expand, production initial HKDF, first ratchet step), split as the hidden layout splits it; `factor_key`: the material key of the factor of the root of `prk` is `seqKey setup prk` (`PqxdhServerAuthCtxMaterial.factor_source`, `RawCtxFreshChainCut.decoded_parts`). It is a fixed function of `prk`.

These are support facts about the source programs; no assumption is used.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctReceive

/-! ### Keyed commitments -/

/-- The frame's record carries a commitment digest that the cache holds at an input whose first 32 bytes are `key`. -/
def KeyedCommit (frame : RawCtxReceive.DecodedFrame) (cache : CtxRomAuth.CtxRO.QueryCache) (key : List UInt8) : Prop :=
  ∃ (record : Pqxdh.RecordCipher) (digest : CtxRomAuth.CtxDigest) (input : Pqxdh.Bytes),
    Pqxdh.decodeRecord frame.payload = some record ∧ record.commit = digest.toList ∧
      cache ((), input) = some digest ∧ input.take 32 = key

/-- A keyed commitment survives the growth of the cache. -/
theorem keyedCommit_mono (frame : RawCtxReceive.DecodedFrame) (before after : CtxRomAuth.CtxRO.QueryCache)
    (key : List UInt8) (held : KeyedCommit frame before key)
    (grows : ∀ input digest, before input = some digest → after input = some digest) : KeyedCommit frame after key := by
  obtain ⟨record, digest, input, decoded, commit, cached, prefixed⟩ := held
  exact ⟨record, digest, input, decoded, commit, grows _ _ cached, prefixed⟩

/-- The first 32 bytes of a commitment input are the material key. -/
theorem hashInput_take (input : RawCtxWholeOwner.OpenInput) (slices : RawCtxFrameDecoding.Slices) :
    (RawCtxSourceOpen.hashInput input slices).take 32 = PqxdhRefinement.absBytes input.material.key.bytes := by
  have length : (PqxdhRefinement.absBytes input.material.key.bytes).length = 32 := by
    simp [PqxdhRefinement.absBytes_length]
  simp only [RawCtxSourceOpen.hashInput, Pqxdh.ctxPreimage, BeaconcryptCore.Refinement.RepresentationBridge.absMaterial,
    List.append_assoc]
  rw [List.take_append_of_le_length (by rw [length]), List.take_of_length_le (by rw [length])]

/-- A successful opening of the shared native primitives caches the commitment input of its material key, with the frame's commitment digest. -/
theorem open_keyed (c : Pqxdh.Crypto) (input : RawCtxWholeOwner.OpenInput) (state final : RawCtxSharedPrimitive.SharedState Unit) (plaintext : Pqxdh.Bytes)
    (opened : (some plaintext, final) ∈ support
      ((simulateQ (RawCtxSharedPrimitive.openingImpl c) (RawCtxSourceOpen.openInput input)).run state)) :
    KeyedCommit input.context.frame final.2 (PqxdhRefinement.absBytes input.material.key.bytes) := by
  obtain ⟨slices, afterHash, parsed, _, hashed, aead⟩ :=
    RawCtxSourceOpen.openInput_success (RawCtxSharedPrimitive.openingImpl c) input state final plaintext opened
  simp only [RawCtxSharedPrimitive.openingImpl, StateT.run, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hashed aead
  obtain ⟨⟨digest, cache⟩, queried, same⟩ := hashed
  simp only [Prod.mk.injEq, Option.some.injEq] at same
  obtain ⟨commitEq, rfl⟩ := same
  have finalEq := congrArg Prod.snd aead
  simp only at finalEq
  subst finalEq
  obtain ⟨record, decoded, _, _, commitment, _⟩ := RawCtxFrameDecoding.fromPayload_record _ slices parsed
  refine ⟨record, digest, RawCtxSourceOpen.hashInput input slices, decoded, ?_,
    PqxdhRecordFactsBindingEvidence.hash_cached _ _ _ queried, hashInput_take input slices⟩
  rw [← commitment, commitEq]

/-! ### Raw receive of a chain owner -/

/-- A successful raw receive of a chain owner decoded a valid frame and ran the receive call at the frame's sequence. -/
theorem chainRaw_success {Kernel Metadata σ : Type} (calls : RawCtxChainOwner.Calls Kernel (StateT σ ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (owner : RawCtxChainOwner.State Kernel Metadata)
    (primitive : σ) (result : (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxChainOwner.State Kernel Metadata) × σ)
    (supported : result ∈ support (((RawCtxChainOwner.rawReceive calls decode raw).run owner).run primitive))
    (message : RawCtxWholeOwner.Decrypted) (success : result.1.1 = .Some message) :
    ∃ frame received, decode raw = some frame ∧
      RawCtxReceive.ValidFrame owner.expectedSender owner.associatedData frame ∧
      received ∈ support ((calls.receive owner.kernel frame.sequence ⟨raw, frame, owner.associatedData⟩).run primitive) ∧
      result = (RawCtxChainOwner.publish owner received.1, received.2) := by
  change result ∈ support ((if raw.isEmpty then pure (RawCtxChainOwner.publish owner (owner.kernel, .None)) else
    match decode raw with
    | none => pure (RawCtxChainOwner.publish owner (owner.kernel, .None))
    | some frame =>
      if RawCtxReceive.ValidFrame owner.expectedSender owner.associatedData frame then do
        let result ← calls.receive owner.kernel frame.sequence ⟨raw, frame, owner.associatedData⟩
        pure (RawCtxChainOwner.publish owner result)
      else pure (RawCtxChainOwner.publish owner (owner.kernel, .None)) : StateT σ ProbComp _).run primitive)
    at supported
  have rejected : ∀ (rest : σ), result ∈ support ((pure (RawCtxChainOwner.publish owner (owner.kernel, .None)) :
      StateT σ ProbComp _).run rest) → False := by
    intro rest member
    rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    rw [member] at success
    cases success
  split at supported
  · exact (rejected _ supported).elim
  · split at supported
    · exact (rejected _ supported).elim
    · rename_i frame decoded
      split at supported
      · rename_i valid
        rw [StateT.run_bind, mem_support_bind_iff] at supported
        obtain ⟨received, member, published⟩ := supported
        rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at published
        exact ⟨frame, received, decoded, valid, member, published⟩
      · exact (rejected _ supported).elim

/-! ### The Beacon's first receive in the factored tail -/

section Factored
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
open PqxdhServerAuthExperiment (Setup Codec)

/-- The native opening of the actual receive primitives is the shared opening interpreter on the open program. -/
theorem nativePrim_open (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (input : RawCtxWholeOwner.OpenInput) :
    PqxdhServerAuthBeaconFactor.nativePrim setup codec (.inr input) =
      simulateQ (RawCtxSharedPrimitive.openingImpl setup.source.crypto) (RawCtxSourceOpen.openInput input) := by
  simp only [PqxdhServerAuthBeaconFactor.nativePrim, QueryImpl.apply_compose, RawCtxSourceOpen.nativeAdapter]
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  exact RawCtxSharedPrimitive.opening_query setup.source.crypto (RawCtxSourceHkdf.kdfImpl setup.source) query

/-- The Beacon's local chain owner on the initial kernel of a factor, with the shared native receive primitives: a successful raw receive of a frame at sequence one caches the commitment input of the key of the factor's ratchet response. -/
theorem chain_keyed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (sendCall : PqxdhServerAuthSendFactor.Kernel → RawCtxSourceSend.SealContext →
      StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp
        (PqxdhServerAuthSendFactor.Kernel × Option RawCtxSourceSend.Encrypted))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (frame : RawCtxReceive.DecodedFrame)
    (decoded : decode raw = some frame) (one : frame.sequence = 1#u64)
    (candidate : pqxdh.BeaconRegistrationCandidate) (value : PqxdhServerAuthSendFactor.Factor)
    (state : RawCtxSharedPrimitive.SharedState Unit)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted ×
      RawCtxChainOwner.State PqxdhServerAuthSendFactor.Kernel Unit) × RawCtxSharedPrimitive.SharedState Unit)
    (received : result ∈ support (((RawCtxChainOwner.rawReceive (PqxdhServerAuthBeaconFactor.primCalls sendCall
      (PqxdhServerAuthBeaconFactor.nativePrim setup codec) setup.source value.1) decode raw).run
        (PqxdhServerAuthBeaconFactor.localState candidate (PqxdhServerAuthBeaconFactor.initial value.2))).run state))
    (message : RawCtxWholeOwner.Decrypted) (reply : result.1.1 = .Some message) :
    KeyedCommit frame result.2.2
      (PqxdhRefinement.absBytes (RawCtxInterpretedReceive.decodeResponse value.1).2.key.bytes) := by
  obtain ⟨frame', received', decoded', _, receivedMember, published⟩ :=
    chainRaw_success _ decode raw _ state result received message reply
  rw [decoded, Option.some.injEq] at decoded'
  subst decoded'
  rw [one] at receivedMember
  change received' ∈ support ((simulateQ (PqxdhServerAuthBeaconFactor.primLabels
    (PqxdhServerAuthBeaconFactor.nativePrim setup codec) setup.source value.1)
    (RawCtxChainReceive.execute (PqxdhServerAuthBeaconFirstOpening.initial
      (RawCtxSelectedChain.Slot.known (RawCtxFreshChainCut.concreteChain value.2)) .hidden) 1#u64 _)).run state)
    at receivedMember
  rw [PqxdhServerAuthBeaconFirstOpening.execute_one] at receivedMember
  simp only [PqxdhServerAuthBeaconFactor.primLabels, pure_bind, StateT.run_bind, mem_support_bind_iff,
    StateT.run_pure, support_pure, Set.mem_singleton_iff] at receivedMember
  obtain ⟨⟨openReply, afterOpen⟩, opened, rfl⟩ := receivedMember
  rw [published]
  have replyEq : result.1.1 = openReply := by rw [published]; rfl
  rw [reply] at replyEq
  subst replyEq
  obtain ⟨input, plaintext, arguments, _, openMember⟩ :=
    RawCtxOwnerProvenance.adapter_success _ _ state afterOpen message opened
  obtain ⟨material, _, contextEq⟩ := RawCtxWholeOwner.arguments_some _ input arguments
  have selected : ReceiveOpen.material (RawCtxInterpretedOpening.toNative
      (RawCtxChainInterpretation.mapOpeningChains (fun _ => RawCtxSelectedChain.unusedChain)
        (fun _ => RawCtxSelectedChain.unusedChain)
        (PqxdhServerAuthBeaconFirstOpening.opening
          (RawCtxSelectedChain.Slot.known (RawCtxFreshChainCut.concreteChain value.2))
          RawCtxSelectedChain.Slot.hidden
          (RawCtxSelectedChain.step setup.source value.1 RawCtxSelectedChain.Slot.hidden).1
          (RawCtxSelectedChain.step setup.source value.1 RawCtxSelectedChain.Slot.hidden).2
          (⟨raw, frame, (PqxdhServerAuthBeaconFactor.localState candidate
            (PqxdhServerAuthBeaconFactor.initial value.2)).associatedData⟩ : RawCtxWholeOwner.OpenContext)))) =
      ok (.Some (RawCtxSelectedChain.step setup.source value.1 RawCtxSelectedChain.Slot.hidden).2) := by
    rw [RawCtxInterpretedOpening.native_material]
    rfl
  rw [selected] at material
  have materialEq := (Option.some.inj (RustM.ok.inj material)).symm
  rw [nativePrim_open] at openMember
  have keyed := open_keyed setup.source.crypto input state afterOpen plaintext openMember
  rw [contextEq, materialEq] at keyed
  exact keyed

/-- In the factored Beacon tail, a successful registration with a frame at sequence one caches the commitment input of the key of the factor's ratchet response. -/
theorem factored_keyed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (sendCall : PqxdhServerAuthSendFactor.Kernel → RawCtxSourceSend.SealContext →
      StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp
        (PqxdhServerAuthSendFactor.Kernel × Option RawCtxSourceSend.Encrypted))
    (prepared : PqxdhBeaconPhase2Preparation.Prepared Response) (value : PqxdhServerAuthSendFactor.Factor)
    (state final : RawCtxSharedPrimitive.SharedState Unit) (staged : PqxdhBeaconPhase2Publication.Staged)
    (supported : (some staged, final) ∈ support ((PqxdhServerAuthBeaconFactor.factored
      (PqxdhServerAuthBeaconFactor.nativePrim setup codec) sendCall setup.source
      (fun response => pure (codec.application response)) codec.frameRead prepared value).run state))
    (raw : Pqxdh.Bytes) (frame : RawCtxReceive.DecodedFrame) (application : codec.application prepared.response = some raw)
    (decoded : codec.frameRead raw = some frame) (one : frame.sequence = 1#u64) :
    KeyedCommit frame final.2
      (PqxdhRefinement.absBytes (RawCtxInterpretedReceive.decodeResponse value.1).2.key.bytes) := by
  simp only [PqxdhServerAuthBeaconFactor.factored, application, pure_bind, StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨⟨result, middle⟩, received, finished⟩ := supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at finished
  obtain ⟨staging, rfl⟩ := finished
  obtain ⟨reply, _, _, _⟩ := PqxdhBeaconPhase2Publication.afterOpening_success _ _ _ staged staging.symm
  exact chain_keyed setup codec sendCall codec.frameRead raw frame decoded one _ value state (result, final) received
    staged.opened reply

/-- The Beacon's local owner on the initial kernel of a root, with the actual shared receive primitives: a successful raw receive whose message has sequence one decoded a frame, and the final cache holds that frame's commitment at an input keyed by the key of the root's factor. -/
theorem whole_keyed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (candidate : pqxdh.BeaconRegistrationCandidate)
    (root : PqxdhSecretInputKdf.RootOutput) (cache : RawCtxSharedPrimitive.SharedState Unit)
    (received : (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Unit) ×
      RawCtxSharedPrimitive.SharedState Unit)
    (member : received ∈ support (RawCtxWholeOwner.rawGame (RawCtxReceiveConsumption.receiveNative setup.source) decode raw
      (PqxdhBeaconPhase2Publication.localOwner candidate (PqxdhBeaconPhase2Publication.normalInitial
        (PqxdhInitialRatchetComplementarity.beaconPending (PqxdhRootTableInitialization.rootArray root))
        (RawCtxSourceHkdf.initialResponse setup.source.crypto
          (PqxdhInitialRatchetComplementarity.beaconPending (PqxdhRootTableInitialization.rootArray root)).request)))
      cache))
    (message : RawCtxWholeOwner.Decrypted) (reply : received.1.1 = .Some message) (one : message.sequence = 1#u64) :
    ∃ frame, decode raw = some frame ∧ KeyedCommit frame received.2.2
      (PqxdhRefinement.absBytes (RawCtxInterpretedReceive.decodeResponse
        (PqxdhServerAuthSendFactor.factor setup.source root).1).2.key.bytes) := by
  obtain ⟨frame, _, input, plaintext, _, decoded, _, _, _, sequence, _, messageEq, _⟩ :=
    RawCtxOwnerProvenance.raw_success _ decode raw _ cache received member message reply
  have frameOne : frame.sequence = 1#u64 := by
    rw [← sequence, ← one, messageEq]
    rfl
  refine ⟨frame, decoded, ?_⟩
  rw [PqxdhServerAuthBeaconFactor.initial_source] at member
  change received ∈ support ((simulateQ (PqxdhServerAuthBeaconFactor.nativePrim setup codec)
    ((RawCtxWholeOwner.rawReceive decode raw).run (RawCtxChainOwner.nativeState
      (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain
        (PqxdhServerAuthSendFactor.target setup.source root)))
      (PqxdhServerAuthBeaconFactor.localState candidate
        (PqxdhServerAuthBeaconFactor.initial (PqxdhServerAuthSendFactor.other setup.source root)))))).run cache) at member
  rw [RawCtxChainOwner.rawReceive_native _ (PqxdhServerAuthBeaconFactor.primCalls (fun kernel _ => pure (kernel, none))
    (PqxdhServerAuthBeaconFactor.nativePrim setup codec) setup.source (PqxdhServerAuthSendFactor.factor setup.source root).1)
    _ (PqxdhServerAuthBeaconFactor.primitive_receive _ setup.source (PqxdhServerAuthBeaconFactor.native_kdf setup codec) _)]
    at member
  rw [StateT.run_map, support_map] at member
  obtain ⟨chainResult, chainMember, rfl⟩ := member
  exact chain_keyed setup codec _ decode raw frame decoded frameOne candidate _ cache chainResult chainMember message reply

/-- The sequence-one key of an R1 value `prk`: the key part of the material of the real key schedule of `prk` (root Expand, production initial HKDF, first ratchet step), split as the hidden layout splits it. It is a fixed function of `prk`. -/
def seqKey (setup : Setup baseSpec KemSK) (prk : PqxdhSecretInputKdf.HmacBlock) : RawCtxKdfRequestTable.KeyPart :=
  (PqxdhDeploymentHiddenLayout.splitOutput (PqxdhServerAuthKeySchedule.keySchedule setup.source setup.hmac prk)).1.1

/-- The material key of the factor of the root of an R1 value is that value's sequence-one key. -/
theorem factor_key (setup : Setup baseSpec KemSK) (prk : PqxdhSecretInputKdf.HmacBlock) :
    PqxdhRefinement.absBytes (RawCtxInterpretedReceive.decodeResponse
      (PqxdhServerAuthSendFactor.factor setup.source (PqxdhSecretInputKdf.expandRoot setup.hmac prk)).1).2.key.bytes =
      (seqKey setup prk).toList := by
  rw [← PqxdhServerAuthCtxMaterial.factor_source]
  change PqxdhRefinement.absBytes (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse
    (PqxdhServerAuthKeySchedule.keySchedule setup.source setup.hmac prk).1)).2.key.bytes = _
  rw [RawCtxFreshChainCut.decoded_parts]
  simp [RawCtxFreshChainCut.concreteMaterial, PqxdhRefinement.absBytes, List.map_map, Function.comp_def,
    BeaconcryptCore.Refinement.ProtocolComposition.absByte_concreteByte, seqKey, PqxdhDeploymentHiddenLayout.splitOutput,
    PqxdhOrderedChainHybrids.material]

end Factored

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctReceive

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctReceive.keyedCommit_mono' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctReceive.keyedCommit_mono

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctReceive.hashInput_take' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctReceive.hashInput_take

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctReceive.open_keyed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctReceive.open_keyed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctReceive.chainRaw_success' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctReceive.chainRaw_success

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctReceive.nativePrim_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctReceive.nativePrim_open

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctReceive.chain_keyed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctReceive.chain_keyed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctReceive.factored_keyed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctReceive.factored_keyed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctReceive.whole_keyed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctReceive.whole_keyed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctReceive.factor_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctReceive.factor_key
