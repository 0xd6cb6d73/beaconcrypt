import BeaconcryptCore.Computational.RawCtxPositionCapability

/-!
The actual adaptive mixed send/raw source schedule embeds into a position-based operational receiver and sender. One capability state retains the same complete shared primitive state, actual send counter and private successful-receive history. Every typed original request and optional reply is retained. Sends use the existing material at the original directional chain and current counter; active failed seals advance, while empty/exhausted sends make no callback. Raw calls retain the original bytes, pure parser, pin, associated data, decoded target and actual opening reply, and preserve the send counter. The source relation derives consumed-position rejection and each admission choice before the later primitive reply.

A private monitor executes the original source schedule, constructs its typed transcript and erases exactly to the complete original client result, owner and primitive state. Every supported source execution then has a capability trace with the same transcript, final primitive state, send counter and successful-position history. The initial source invariant is maintained through sends and receives, and either actual source initializer supplies an empty-history instance. Original per-class budgets bound sends, raw attempts, total transcript length and history growth; monitoring preserves every selective underlying uniform-query bound.

The complete trace result is support inclusion, not a probability equality for arbitrary abstract admission choices or an executable source-free scheduler. The matching proof may retain source control. Fixed-functional KDF prefixes disappear only after their existing pure interpretation; no state-dependent ROM KDF is replaced by that argument. The shared source frame callback retains the existing total functional primitive/ROM and optional writer interpretation. Origin-based material reconstruction and repeated pure parsing/list work add real local computation, potentially proportional to the position. Callback or uniform-query budgets do not make this work free or prove native timing, allocation, traversal or library implementation equality. Distinct positions and origins may have identical material values, and actual finite source counter exhaustion is retained.

The scope is one uninterrupted established owner with immutable pin, associated data and metadata, supplied fixed-source relation and arbitrary adaptive send/raw calls. Public primitive services, reveals, multiple owners, registration/lifecycle transitions, restored/copied state, network/privileged API declassification and the concrete persistent ProVerif process still need their own mappings and policies. Origins, source kernels, private transcripts and spent histories are not added to public/reveal/snapshot interfaces. Actual successful API plaintext remains in the typed reply. No key-independence, authentication, primitive security loss or global computational-symbolic conclusion is introduced.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxMixedPositionCapability
open RawCtxMaterialPositions RawCtxPositionedOpening

/-- The actual fixed-response send prefix reaches the source-selected position material before any optional sealing reply. -/
theorem bare_positioned_run {AD PT CT Context Output PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (origin : RatchetChain) (entry : ConcreteRatchetKernel) (context : Context)
    (aligned : entry.refined.send_chain = Ratchet.chainAt (withInterpreter cr execute)
      origin entry.refined.control.send_sequence.val)
    (active : entry.refined.control.send_sequence ≠ core.num.U64.MAX)
    (sealing : SendSeal Context → StateT PrimitiveState (OracleComp base) (Option Output)) :
    ∃ ready : SendSeal Context,
      ready.material = Ratchet.msgKeyAt (withInterpreter cr execute) origin entry.refined.control.send_sequence.val ∧
      ready.sequence.val = entry.refined.control.send_sequence.val + 1 ∧ ready.context = context ∧
      ready.advanced.refined.control.send_sequence.val = entry.refined.control.send_sequence.val + 1 ∧
      ∀ state, (simulateQ (bareSendImpl execute sealing) (RawCtxSourceSend.send entry context)).run state = (do
        let result ← (sealing ready).run state
        pure ((ready.advanced, result.1), result.2)) := by
  obtain ⟨pending, ready, request, material, chain, advanced, sequence, ctx, complete⟩ :=
    send_positioned_run cr execute origin entry context aligned active sealing
  refine ⟨ready, material, sequence, ctx, advanced, fun state => ?_⟩
  rw [← send_complete_erase execute sealing (RawCtxSourceSend.send entry context) (state, []), complete]
  simp only [map_bind, map_pure, Prod.map_apply, id_eq]

def positionInput {AD PT CT : Type} (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (origin : RatchetChain) (position : Nat) (available : position + 1 < 2 ^ 64)
    (context : RawCtxSourceSend.SealContext) : RawCtxSourceSend.SealInput :=
  ⟨Ratchet.msgKeyAt cr origin position, Std.U64.ofNatCore (position + 1) available, context⟩

def sealingAt {PrimitiveState ι : Type} {base : OracleSpec ι}
    (sealing : RawCtxSourceSend.SealInput → StateT PrimitiveState (OracleComp base) (Option Pqxdh.Bytes))
    (pending : SendSeal RawCtxSourceSend.SealContext) :
    StateT PrimitiveState (OracleComp base) (Option RawCtxSourceSend.Encrypted) := do
  let input := RawCtxSourceSend.arguments pending
  let ciphertext ← sealing input
  pure (ciphertext.map (RawCtxSourceSend.encrypted input))

def positionSeal {AD PT CT PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (origin : RatchetChain)
    (position : Nat) (context : RawCtxSourceSend.SealContext)
    (sealing : RawCtxSourceSend.SealInput → StateT PrimitiveState (OracleComp base) (Option Pqxdh.Bytes)) :
    StateT PrimitiveState (OracleComp base) (Option RawCtxSourceSend.Encrypted × Nat) :=
  if available : position + 1 < 2 ^ 64 then do
    let input := positionInput cr origin position available context
    let ciphertext ← sealing input
    pure (ciphertext.map (RawCtxSourceSend.encrypted input), position + 1)
  else pure (none, position)

/-- The prepared source getter fields identify the same material, finite sequence and immutable sealing context. -/
theorem arguments_positioned {AD PT CT : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (origin : RatchetChain)
    (position : Nat) (context : RawCtxSourceSend.SealContext)
    (available : position + 1 < 2 ^ 64) (ready : SendSeal RawCtxSourceSend.SealContext)
    (material : ready.material = Ratchet.msgKeyAt cr origin position)
    (sequence : ready.sequence.val = position + 1) (ctx : ready.context = context) :
    RawCtxSourceSend.arguments ready = positionInput cr origin position available context := by
  have seq : ready.sequence = Std.U64.ofNatCore (position + 1) available := by
    apply UScalar.eq_of_val_eq
    simpa only [U64.ofNatCore_val_eq] using sequence
  simp only [RawCtxSourceSend.arguments, positionInput, material, seq, ctx]

/-- Projecting an active send retains its actual optional ciphertext, advanced counter and complete primitive state. -/
theorem bare_position_seal {AD PT CT PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (origin : RatchetChain) (entry : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext)
    (aligned : entry.refined.send_chain = Ratchet.chainAt (withInterpreter cr execute)
      origin entry.refined.control.send_sequence.val)
    (active : entry.refined.control.send_sequence ≠ core.num.U64.MAX)
    (sealing : RawCtxSourceSend.SealInput → StateT PrimitiveState (OracleComp base) (Option Pqxdh.Bytes))
    (state : PrimitiveState) :
    (fun result => ((result.1.2, result.1.1.refined.control.send_sequence.val), result.2)) <$>
        (simulateQ (bareSendImpl execute (sealingAt sealing)) (RawCtxSourceSend.send entry context)).run state =
      (positionSeal (withInterpreter cr execute) origin entry.refined.control.send_sequence.val context sealing).run state := by
  obtain ⟨ready, material, sequence, ctx, advanced, complete⟩ :=
    bare_positioned_run cr execute origin entry context aligned active (sealingAt sealing)
  have available : entry.refined.control.send_sequence.val + 1 < 2 ^ 64 := by
    have bound := ready.sequence.lt_succ_max
    omega
  rw [complete]
  simp only [positionSeal, available, ↓reduceDIte, sealingAt, StateT.run_bind, StateT.run_pure,
    map_bind, map_pure, bind_assoc, pure_bind, advanced,
    arguments_positioned (withInterpreter cr execute) origin _ context available ready material sequence ctx]

/-- The position sender also represents actual exhausted admission without a primitive callback. -/
theorem bare_position_seal_all {AD PT CT PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (origin : RatchetChain) (entry : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext)
    (aligned : entry.refined.send_chain = Ratchet.chainAt (withInterpreter cr execute)
      origin entry.refined.control.send_sequence.val)
    (sealing : RawCtxSourceSend.SealInput → StateT PrimitiveState (OracleComp base) (Option Pqxdh.Bytes))
    (state : PrimitiveState) :
    (fun result => ((result.1.2, result.1.1.refined.control.send_sequence.val), result.2)) <$>
        (simulateQ (bareSendImpl execute (sealingAt sealing)) (RawCtxSourceSend.send entry context)).run state =
      (positionSeal (withInterpreter cr execute) origin entry.refined.control.send_sequence.val context sealing).run state := by
  by_cases exhausted : entry.refined.control.send_sequence = core.num.U64.MAX
  · rw [RawCtxSourceSend.send_exhausted entry context exhausted]
    simp [simulateQ_pure, StateT.run_pure, positionSeal, exhausted, core.num.U64.MAX, U64.rMax]
  · exact bare_position_seal cr execute origin entry context aligned exhausted sealing state

open RawCtxReceiveConsumption

noncomputable def sendNative {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :=
  RawCtxMixedShared.sharedImpl (Auxiliary := Auxiliary) source.crypto writer (RawCtxSourceHkdf.kdfImpl source) ∘ₛ
    RawCtxMixedOwner.sendAdapter

noncomputable def sourceFrame {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxSourceSend.SealInput) :
    StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp (Option Pqxdh.Bytes) :=
  sendNative source writer (.inr input)

/-- The source sealing capability is exactly the existing common native frame callback at the prepared getters. -/
theorem source_sealingAt {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (pending : SendSeal RawCtxSourceSend.SealContext) :
    sourceSealing (Auxiliary := Auxiliary) source writer pending = sealingAt (sourceFrame source writer) pending := by
  simp only [sourceSealing, QueryImpl.compose, RawCtxSourceSend.adapter, simulateQ_bind,
    simulateQ_spec_query, simulateQ_pure, sealingAt, sourceFrame, sendNative]
  rfl

/-- The actual fixed shared source send phase has the same projected position-sealing computation. -/
theorem source_position_seal {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (origin : RatchetChain) (entry : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext)
    (aligned : entry.refined.send_chain = Ratchet.chainAt (crypto source.crypto)
      origin entry.refined.control.send_sequence.val)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (fun result => ((result.1.2, result.1.1.refined.control.send_sequence.val), result.2)) <$>
        (simulateQ (sendNative source writer)
          (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send entry context))).run state =
      (positionSeal (crypto source.crypto) origin entry.refined.control.send_sequence.val context
        (sourceFrame source writer)).run state := by
  rw [← QueryImpl.simulateQ_compose]
  change (fun result => ((result.1.2, result.1.1.refined.control.send_sequence.val), result.2)) <$>
    (simulateQ ((RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source) ∘ₛ
      RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter) (RawCtxSourceSend.send entry context)).run state = _
  rw [← source_send_handler]
  rw [funext (source_sealingAt source writer)]
  exact bare_position_seal_all (crypto source.crypto) (RawCtxSourceHkdf.response source.crypto)
    origin entry context aligned (sourceFrame source writer) state

def positionSend {AD PT CT PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (origin : RatchetChain)
    (position : Nat) (context : RawCtxSourceSend.SealContext)
    (sealing : RawCtxSourceSend.SealInput → StateT PrimitiveState (OracleComp base) (Option Pqxdh.Bytes)) :
    StateT PrimitiveState (OracleComp base) (Option RawCtxSourceSend.Encrypted × Nat) :=
  if context.plaintext.isEmpty then pure (none, position) else positionSeal cr origin position context sealing

/-- The outer send projection retains empty rejection, target/sender distinction, optional result and primitive state. -/
theorem source_position_send {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (origin : RatchetChain) (sender : Std.U64) (plaintext : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata)
    (aligned : state.owner.kernel.refined.send_chain = Ratchet.chainAt (crypto source.crypto)
      origin state.owner.kernel.refined.control.send_sequence.val)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (fun result => ((result.1.1, result.1.2.owner.kernel.refined.control.send_sequence.val), result.2)) <$>
        RawCtxSourceSend.sendGame (sendNative source writer) sender plaintext state primitive =
      (positionSend (crypto source.crypto) origin state.owner.kernel.refined.control.send_sequence.val
        ⟨plaintext, state.owner.expectedSender, sender, state.owner.associatedData⟩
        (sourceFrame source writer)).run primitive := by
  unfold RawCtxSourceSend.sendGame RawCtxSourceSend.sendOwner positionSend
  by_cases empty : plaintext.isEmpty = true
  · simp only [empty, ite_true]
    change _ <$> (pure ((none, state), primitive) : ProbComp _) = pure ((none, _), primitive)
    simp only [map_pure]
  · simp only [empty, Bool.false_eq_true, ite_false]
    dsimp only [StateT.run]
    change _ <$> (simulateQ (sendNative source writer) _).run primitive =
      (positionSeal (crypto source.crypto) origin state.owner.kernel.refined.control.send_sequence.val
        ⟨plaintext, state.owner.expectedSender, sender, state.owner.associatedData⟩
        (sourceFrame source writer)).run primitive
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, map_bind, map_pure]
    simpa only [bind_pure_comp] using source_position_seal source writer origin state.owner.kernel
      ⟨plaintext, state.owner.expectedSender, sender, state.owner.associatedData⟩ aligned primitive

/-- Every supported source receive transition preserves the actual send counter, including failed openings. -/
theorem receive_send_counter {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (origin : RatchetChain) (send : Ratchet.SendState RatchetChain)
    (receive : Ratchet.RecvState RatchetChain RatchetMaterial)
    (entry : ConcreteRatchetKernel) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (refines : KernelRefines (crypto source.crypto) origin send receive entry)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary)
    (result : (ConcreteRatchetKernel × core.option.Option RawCtxWholeOwner.Decrypted) ×
      RawCtxSharedPrimitive.SharedState Auxiliary)
    (present : result ∈ support ((simulateQ
      (RawCtxSharedPrimitive.nativeImpl source.crypto (RawCtxSourceHkdf.kdfImpl source))
      (simulateQ RawCtxSourceOpen.ownerAdapter (RawCtxOwnerOracle.receive entry target context))).run primitive)) :
    result.1.1.refined.control.send_sequence.val = entry.refined.control.send_sequence.val := by
  obtain ⟨nextReceive, preserved, transition⟩ := native_receive_transition source origin send receive entry target context refines primitive result present
  exact preserved.sendSequence.trans refines.sendSequence.symm

/-- All raw validation and receive outcomes retain the send counter under the established source relation. -/
theorem raw_send_counter {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (sendOrigin receiveOrigin : RatchetChain) (spent : List Nat)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata)
    (invariant : ConsumedRefines source.crypto sendOrigin receiveOrigin state.owner.kernel spent)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Metadata) ×
      RawCtxSharedPrimitive.SharedState Auxiliary)
    (present : result ∈ support (RawCtxWholeOwner.rawGame (receiveNative source) decode raw state primitive)) :
    result.1.2.owner.kernel.refined.control.send_sequence.val = state.owner.kernel.refined.control.send_sequence.val := by
  obtain ⟨send, receive, refines, aligned, consumed, unique⟩ := invariant
  unfold RawCtxWholeOwner.rawGame RawCtxWholeOwner.rawReceive StateT.run at present
  split at present
  · subst result
    rfl
  · split at present
    · subst result
      rfl
    · unfold StateT.run at present
      split at present
      · rw [simulateQ_bind] at present
        change result ∈ support (StateT.run _ primitive) at present
        simp only [StateT.run_bind, simulateQ_pure, StateT.run_pure, mem_support_bind_iff,
          support_pure, Set.mem_singleton_iff] at present
        obtain ⟨opened, hopen, rfl⟩ := present
        apply receive_send_counter source receiveOrigin send receive state.owner.kernel _ _ refines primitive opened
        simpa only [receiveNative, RawCtxSourceOpen.ownerAdapter, QueryImpl.simulateQ_compose] using hopen
      · simp only [simulateQ_pure] at present
        subst result
        rfl

abbrev SourceState (Metadata Auxiliary : Type) := RawCtxPositionCapability.SourceState Metadata Auxiliary
abbrev CapabilityState (Auxiliary : Type) := RawCtxSharedPrimitive.SharedState Auxiliary × (Nat × List Nat)

def project {Metadata Auxiliary : Type} (state : SourceState Metadata Auxiliary) : CapabilityState Auxiliary :=
  (state.1.2, (state.1.1.owner.kernel.refined.control.send_sequence.val, state.2))

noncomputable def capabilityImpl {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (expectedSender sender : Std.U64)
    (associatedData : Pqxdh.Bytes) (decode : RawCtxReceive.FrameDecoder) (enabled : Bool) :
    QueryImpl RawCtxMixedOwner.SourceSpec (StateT (CapabilityState Auxiliary) ProbComp) :=
  fun query state => match query with
  | .inl plaintext => do
    let result ← (positionSend (crypto source.crypto) sendOrigin state.2.1
      ⟨plaintext, expectedSender, sender, associatedData⟩ (sourceFrame source writer)).run state.1
    pure (result.1.1, (result.2, (result.1.2, state.2.2)))
  | .inr raw => do
    let result ← (RawCtxPositionCapability.capabilityStep (crypto source.crypto) receiveOrigin expectedSender
      associatedData decode raw enabled (receiveNative source)).run (state.1, state.2.2)
    pure (result.1, (result.2.1, (state.2.1, result.2.2)))

/-- Every actual mixed step has a matching capability step with the same typed reply, full primitive state, send counter and private history. -/
theorem tracked_step_capability {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : SourceState Metadata Auxiliary)
    (invariant : ConsumedRefines source.crypto sendOrigin receiveOrigin state.1.1.owner.kernel state.2)
    (result : RawCtxMixedOwner.SourceSpec.Range query × SourceState Metadata Auxiliary)
    (present : result ∈ support ((trackedImpl source writer sender decode query).run state)) :
    ∃ enabled, (result.1, project result.2) ∈ support
      ((capabilityImpl source writer sendOrigin receiveOrigin state.1.1.owner.expectedSender sender
        state.1.1.owner.associatedData decode enabled query).run (project state)) := by
  unfold trackedImpl StateT.run at present
  obtain ⟨actual, hactual, returned⟩ := mem_support_bind_peel _ _ present
  have equal := eq_of_mem_support_pure _ returned
  subst result
  cases query with
  | inl plaintext =>
    change actual ∈ support ((do
      let sent ← RawCtxSourceSend.sendGame (sendNative source writer) sender plaintext state.1.1 state.1.2
      pure (sent.1.1, (sent.1.2, sent.2))) : ProbComp _) at hactual
    obtain ⟨sent, hsent, returned⟩ := mem_support_bind_peel _ _ hactual
    have equal := eq_of_mem_support_pure _ returned
    subst actual
    obtain ⟨send, receive, refines, aligned, consumed, unique⟩ := invariant
    have sourceAligned : state.1.1.owner.kernel.refined.send_chain = Ratchet.chainAt (crypto source.crypto)
        sendOrigin state.1.1.owner.kernel.refined.control.send_sequence.val := by
      rw [refines.sendChain, refines.sendSequence]
      exact aligned
    have selected : ((sent.1.1, sent.1.2.owner.kernel.refined.control.send_sequence.val), sent.2) ∈ support
        ((positionSend (crypto source.crypto) sendOrigin state.1.1.owner.kernel.refined.control.send_sequence.val
          ⟨plaintext, state.1.1.owner.expectedSender, sender, state.1.1.owner.associatedData⟩
          (sourceFrame source writer)).run state.1.2) := by
      rw [← source_position_send source writer sendOrigin sender plaintext state.1.1 sourceAligned state.1.2,
        support_map]
      exact ⟨sent, hsent, rfl⟩
    refine ⟨false, ?_⟩
    change _ ∈ support (do
      let sealed ← (positionSend (crypto source.crypto) sendOrigin state.1.1.owner.kernel.refined.control.send_sequence.val
        ⟨plaintext, state.1.1.owner.expectedSender, sender, state.1.1.owner.associatedData⟩
        (sourceFrame source writer)).run state.1.2
      pure (sealed.1.1, (sealed.2, (sealed.1.2, state.2))))
    rw [mem_support_bind_iff]
    exact ⟨_, selected, by simp only [support_pure, Set.mem_singleton_iff]; rfl⟩
  | inr raw =>
    simp only [RawCtxMixedOwner.sourceImpl, shared_receiveNative] at hactual
    change actual ∈ support ((do
      let received ← RawCtxWholeOwner.rawGame (receiveNative source) decode raw state.1.1 state.1.2
      pure (received.1.1, (received.1.2, received.2))) : ProbComp _) at hactual
    obtain ⟨received, hreceived, returned⟩ := mem_support_bind_peel _ _ hactual
    have equal := eq_of_mem_support_pure _ returned
    subst actual
    obtain ⟨enabled, same⟩ := RawCtxPositionCapability.source_capability_step source sendOrigin receiveOrigin
      state.2 state.1.1 invariant decode raw (Auxiliary := Auxiliary)
    have selected : (received.1.1, (received.2, recordReply received.1.1 state.2)) ∈ support
        ((RawCtxPositionCapability.capabilityStep (crypto source.crypto) receiveOrigin
          state.1.1.owner.expectedSender state.1.1.owner.associatedData decode raw enabled
          (receiveNative source)).run (state.1.2, state.2)) := by
      rw [← same state.1.2]
      rw [support_map]
      exact ⟨received, hreceived, rfl⟩
    have counter := raw_send_counter source sendOrigin receiveOrigin state.2 decode raw state.1.1
      invariant state.1.2 received hreceived
    refine ⟨enabled, ?_⟩
    change _ ∈ support (do
      let opened ← (RawCtxPositionCapability.capabilityStep (crypto source.crypto) receiveOrigin
        state.1.1.owner.expectedSender state.1.1.owner.associatedData decode raw enabled
        (receiveNative source)).run (state.1.2, state.2)
      pure (opened.1, (opened.2.1, (state.1.1.owner.kernel.refined.control.send_sequence.val, opened.2.2))))
    rw [mem_support_bind_iff]
    refine ⟨_, selected, ?_⟩
    simp only [project, recordSource, counter, support_pure, Set.mem_singleton_iff]

/-- The actual mixed step retains immutable owner fields and increments the raw-attempt counter only for raw requests. -/
theorem tracked_step_metadata {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : SourceState Metadata Auxiliary)
    (result : RawCtxMixedOwner.SourceSpec.Range query × SourceState Metadata Auxiliary)
    (present : result ∈ support ((trackedImpl source writer sender decode query).run state)) :
    result.2.1.1.rawAttempts = state.1.1.rawAttempts + (if query.isRight then 1 else 0) ∧
      RawCtxMixedOwner.ownerFields result.2.1.1 = RawCtxMixedOwner.ownerFields state.1.1 := by
  unfold trackedImpl StateT.run at present
  obtain ⟨actual, hactual, returned⟩ := mem_support_bind_peel _ _ present
  have equal := eq_of_mem_support_pure _ returned
  subst result
  exact RawCtxMixedOwner.source_step _ sender decode query state.1 actual hactual

abbrev Transcript := List ((query : RawCtxMixedOwner.SourceSpec.Domain) × RawCtxMixedOwner.SourceSpec.Range query)

inductive SourceTrace {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) :
    SourceState Metadata Auxiliary → Transcript → SourceState Metadata Auxiliary → Prop
  | nil (state : SourceState Metadata Auxiliary) : SourceTrace source writer sender decode state [] state
  | step {state final : SourceState Metadata Auxiliary} (query : RawCtxMixedOwner.SourceSpec.Domain)
      {result : RawCtxMixedOwner.SourceSpec.Range query × SourceState Metadata Auxiliary} {rest : Transcript}
      (actual : result ∈ support ((trackedImpl source writer sender decode query).run state))
      (tail : SourceTrace source writer sender decode result.2 rest final) :
      SourceTrace source writer sender decode state (⟨query, result.1⟩ :: rest) final

inductive CapabilityTrace {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (expectedSender sender : Std.U64)
    (associatedData : Pqxdh.Bytes) (decode : RawCtxReceive.FrameDecoder) :
    CapabilityState Auxiliary → Transcript → CapabilityState Auxiliary → Prop
  | nil (state : CapabilityState Auxiliary) :
      CapabilityTrace source writer sendOrigin receiveOrigin expectedSender sender associatedData decode state [] state
  | step {state final : CapabilityState Auxiliary} (query : RawCtxMixedOwner.SourceSpec.Domain)
      {result : RawCtxMixedOwner.SourceSpec.Range query × CapabilityState Auxiliary} {rest : Transcript}
      (enabled : Bool)
      (actual : result ∈ support ((capabilityImpl source writer sendOrigin receiveOrigin expectedSender sender
        associatedData decode enabled query).run state))
      (tail : CapabilityTrace source writer sendOrigin receiveOrigin expectedSender sender associatedData decode result.2 rest final) :
      CapabilityTrace source writer sendOrigin receiveOrigin expectedSender sender associatedData decode state (⟨query, result.1⟩ :: rest) final

/-- Every source mixed trace embeds with its exact typed transcript and final projected state while preserving the source invariant. -/
theorem source_trace_capability {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    {initial final : SourceState Metadata Auxiliary} {transcript : Transcript}
    (trace : SourceTrace source writer sender decode initial transcript final)
    (invariant : ConsumedRefines source.crypto sendOrigin receiveOrigin initial.1.1.owner.kernel initial.2) :
    CapabilityTrace source writer sendOrigin receiveOrigin initial.1.1.owner.expectedSender sender
      initial.1.1.owner.associatedData decode (project initial) transcript (project final) ∧
      ConsumedRefines source.crypto sendOrigin receiveOrigin final.1.1.owner.kernel final.2 := by
  induction trace with
  | nil state => exact ⟨.nil _, invariant⟩
  | @step state final query result rest actual tail ih =>
    have nextInvariant := tracked_step_spent source writer sendOrigin receiveOrigin sender decode query state invariant result actual
    obtain ⟨nextTrace, finalInvariant⟩ := ih nextInvariant
    obtain ⟨enabled, supported⟩ := tracked_step_capability source writer sendOrigin receiveOrigin sender decode query state invariant result actual
    have fields := (tracked_step_metadata source writer sender decode query state result actual).2
    refine ⟨.step query enabled supported ?_, finalInvariant⟩
    have pin := congrArg Prod.fst fields
    have ad := congrArg (fun fields => fields.2.1) fields
    dsimp only [RawCtxMixedOwner.ownerFields] at pin ad
    simpa only [pin, ad] using nextTrace

noncomputable def loggedImpl {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl RawCtxMixedOwner.SourceSpec (StateT (SourceState Metadata Auxiliary × Transcript) ProbComp) :=
  fun query state => do
    let result ← (trackedImpl source writer sender decode query).run state.1
    pure (result.1, (result.2, state.2 ++ [⟨query, result.1⟩]))

/-- Erasing the private typed transcript leaves the unchanged tracked source operation. -/
theorem logged_step_erasure {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : SourceState Metadata Auxiliary × Transcript) :
    Prod.map id Prod.fst <$> (loggedImpl source writer sender decode query).run state =
      (trackedImpl source writer sender decode query).run state.1 := by
  simp [loggedImpl, StateT.run]

/-- Erasing only private transcript and history retains the entire original adaptive source computation. -/
theorem logged_run_erasure {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result) (state : SourceState Metadata Auxiliary × Transcript) :
    Prod.map id (fun state => state.1.1) <$> (simulateQ (loggedImpl source writer sender decode) client).run state =
      (simulateQ (RawCtxMixedOwner.sourceImpl
        (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source)) sender decode) client).run state.1.1 := by
  have erased := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (loggedImpl source writer sender decode) (trackedImpl source writer sender decode)
    Prod.fst (logged_step_erasure source writer sender decode) client state
  rw [← tracked_erasure source writer sender decode client state.1.1 state.1.2, ← erased]
  simp only [Functor.map_map]
  rfl

/-- Every supported monitored adaptive run constructs its mixed source trace internally from actual requests and replies. -/
theorem logged_run_trace {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result) (state : SourceState Metadata Auxiliary × Transcript)
    (result : Result × (SourceState Metadata Auxiliary × Transcript))
    (actual : result ∈ support ((simulateQ (loggedImpl source writer sender decode) client).run state)) :
    ∃ transcript, result.2.2 = state.2 ++ transcript ∧
      SourceTrace source writer sender decode state.1 transcript result.2.1 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at actual
    subst result
    exact ⟨[], by simp, .nil _⟩
  | query_bind query next ih =>
    rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, mem_support_bind_iff] at actual
    obtain ⟨step, hstep, htail⟩ := actual
    unfold loggedImpl StateT.run at hstep
    obtain ⟨received, hreceived, returned⟩ := mem_support_bind_peel _ _ hstep
    have stepEq := eq_of_mem_support_pure _ returned
    subst step
    obtain ⟨rest, history, trace⟩ := ih _ _ result htail
    refine ⟨⟨query, received.1⟩ :: rest, ?_, .step query hreceived trace⟩
    simpa only [List.append_assoc, List.singleton_append] using history

/-- Every supported original mixed client run yields a matching typed capability trace and final source relation. -/
theorem source_supported_capability {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (initial : RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) (spent : List Nat)
    (invariant : ConsumedRefines source.crypto sendOrigin receiveOrigin initial.1.owner.kernel spent)
    (result : Result × (RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary))
    (actual : result ∈ support ((simulateQ (RawCtxMixedOwner.sourceImpl
      (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source)) sender decode) client).run initial)) :
    ∃ finalSpent transcript,
      SourceTrace source writer sender decode (initial, spent) transcript (result.2, finalSpent) ∧
      CapabilityTrace source writer sendOrigin receiveOrigin initial.1.owner.expectedSender sender initial.1.owner.associatedData decode
        (project (initial, spent)) transcript (project (result.2, finalSpent)) ∧
      ConsumedRefines source.crypto sendOrigin receiveOrigin result.2.1.owner.kernel finalSpent := by
  rw [← logged_run_erasure source writer sender decode client ((initial, spent), []), support_map, Set.mem_image] at actual
  obtain ⟨logged, supported, rfl⟩ := actual
  obtain ⟨transcript, _, trace⟩ := logged_run_trace source writer sender decode client ((initial, spent), []) logged supported
  obtain ⟨capability, finalInvariant⟩ := source_trace_capability source writer sendOrigin receiveOrigin sender decode trace invariant
  exact ⟨logged.2.1.2, transcript, trace, capability, finalInvariant⟩

def queryCount (predicate : RawCtxMixedOwner.SourceSpec.Domain → Bool) (transcript : Transcript) : Nat :=
  transcript.countP (fun entry => predicate entry.1)

/-- The exact number of raw transcript entries accounts for the source attempt counter and preserves immutable fields. -/
theorem SourceTrace.metadata {Metadata Auxiliary : Type}
    {source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource} {writer : RawCtxMixedShared.Writer}
    {sender : Std.U64} {decode : RawCtxReceive.FrameDecoder}
    {initial final : SourceState Metadata Auxiliary} {transcript : Transcript}
    (trace : SourceTrace source writer sender decode initial transcript final) :
    final.1.1.rawAttempts = initial.1.1.rawAttempts + queryCount Sum.isRight transcript ∧
      RawCtxMixedOwner.ownerFields final.1.1 = RawCtxMixedOwner.ownerFields initial.1.1 := by
  induction trace with
  | nil state => exact ⟨by simp [queryCount], rfl⟩
  | @step state final query result rest actual tail ih =>
    have fields := tracked_step_metadata source writer sender decode query state result actual
    refine ⟨?_, ih.2.trans fields.2⟩
    simp only [queryCount, List.countP_cons] at *
    omega

/-- Successful-position history can grow only through actual raw replies, by at most one per raw call. -/
theorem SourceTrace.history_length {Metadata Auxiliary : Type}
    {source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource} {writer : RawCtxMixedShared.Writer}
    {sender : Std.U64} {decode : RawCtxReceive.FrameDecoder}
    {initial final : SourceState Metadata Auxiliary} {transcript : Transcript}
    (trace : SourceTrace source writer sender decode initial transcript final) :
    final.2.length ≤ initial.2.length + queryCount Sum.isRight transcript := by
  induction trace with
  | nil state => simp [queryCount]
  | @step state final query result rest actual tail ih =>
    have growth := tracked_step_length source writer sender decode query state result actual
    simp only [queryCount, List.countP_cons] at *
    omega

/-- Every original all-continuation selective query budget bounds that class of entries in the actual monitored transcript. -/
theorem logged_run_count {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (predicate : RawCtxMixedOwner.SourceSpec.Domain → Bool) (budget : Nat)
    (bounded : client.IsQueryBoundP (fun query => predicate query = true) budget)
    (state : SourceState Metadata Auxiliary × Transcript)
    (result : Result × (SourceState Metadata Auxiliary × Transcript))
    (actual : result ∈ support ((simulateQ (loggedImpl source writer sender decode) client).run state)) :
    queryCount predicate result.2.2 ≤ queryCount predicate state.2 + budget := by
  induction client using OracleComp.inductionOn generalizing budget state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at actual
    subst result
    exact Nat.le_add_right _ _
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, mem_support_bind_iff] at actual
    obtain ⟨step, hstep, htail⟩ := actual
    unfold loggedImpl StateT.run at hstep
    obtain ⟨received, hreceived, returned⟩ := mem_support_bind_peel _ _ hstep
    have stepEq := eq_of_mem_support_pure _ returned
    subst step
    have rest := ih received.1 _ (bounded.2 received.1) _ result htail
    simp only [queryCount, List.countP_append, List.countP_cons, List.countP_nil, Nat.zero_add] at rest ⊢
    by_cases counted : predicate query = true
    · simp only [counted, ite_true] at rest
      have positive := bounded.1.resolve_left (not_not.mpr counted)
      omega
    · simp only [counted, Bool.false_eq_true, ite_false] at rest
      omega

/-- Send and raw transcript entries form an exhaustive disjoint count of the original mixed calls. -/
theorem queryCount_partition (transcript : Transcript) :
    transcript.length = queryCount Sum.isLeft transcript + queryCount Sum.isRight transcript := by
  induction transcript with
  | nil => simp [queryCount]
  | cons entry rest ih =>
    rcases entry with ⟨query, reply⟩
    cases query <;>
      simp only [queryCount, List.length_cons, List.countP_cons, Sum.isLeft, Sum.isRight,
        Bool.false_eq_true, ↓reduceIte] at ih ⊢ <;>
      omega

/-- Original send/raw budgets bound the constructed transcript, per-class counts and nonrepeating successful-position history. -/
theorem source_capability_bounded {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result) (qSend qRaw : Nat)
    (hSend : client.IsQueryBoundP (fun query => query.isLeft = true) qSend)
    (hRaw : client.IsQueryBoundP (fun query => query.isRight = true) qRaw)
    (initial : RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) (spent : List Nat)
    (invariant : ConsumedRefines source.crypto sendOrigin receiveOrigin initial.1.owner.kernel spent)
    (result : Result × (RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary))
    (actual : result ∈ support ((simulateQ (RawCtxMixedOwner.sourceImpl
      (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source)) sender decode) client).run initial)) :
    ∃ finalSpent transcript,
      SourceTrace source writer sender decode (initial, spent) transcript (result.2, finalSpent) ∧
      CapabilityTrace source writer sendOrigin receiveOrigin initial.1.owner.expectedSender sender initial.1.owner.associatedData decode
        (project (initial, spent)) transcript (project (result.2, finalSpent)) ∧
      ConsumedRefines source.crypto sendOrigin receiveOrigin result.2.1.owner.kernel finalSpent ∧
      finalSpent.Nodup ∧ finalSpent.length ≤ spent.length + qRaw ∧
      queryCount Sum.isLeft transcript ≤ qSend ∧ queryCount Sum.isRight transcript ≤ qRaw ∧
      transcript.length ≤ qSend + qRaw := by
  rw [← logged_run_erasure source writer sender decode client ((initial, spent), []), support_map, Set.mem_image] at actual
  obtain ⟨logged, supported, rfl⟩ := actual
  obtain ⟨transcript, history, trace⟩ := logged_run_trace source writer sender decode client ((initial, spent), []) logged supported
  obtain ⟨capability, finalInvariant⟩ := source_trace_capability source writer sendOrigin receiveOrigin sender decode trace invariant
  have sendCount := logged_run_count source writer sender decode client Sum.isLeft qSend hSend ((initial, spent), []) logged supported
  have rawCount := logged_run_count source writer sender decode client Sum.isRight qRaw hRaw ((initial, spent), []) logged supported
  simp only [List.nil_append] at history
  simp only [history, queryCount, List.countP_nil, Nat.zero_add] at sendCount rawCount
  refine ⟨logged.2.1.2, transcript, trace, capability, finalInvariant, finalInvariant.spent_nodup,
    ?_, sendCount, rawCount, ?_⟩
  · have growth := trace.history_length
    change logged.2.1.2.length ≤ spent.length + queryCount Sum.isRight transcript at growth
    exact growth.trans (Nat.add_le_add_left rawCount _)
  · rw [queryCount_partition]
    exact Nat.add_le_add sendCount rawCount

open BeaconcryptCore.Refinement.PqxdhConcreteSession

/-- Either actual source initializer supplies the empty-history invariant for the bounded mixed trace embedding. -/
theorem initialized_capability {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (root : Std.Array Std.U8 32#usize) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result) (qSend qRaw : Nat)
    (hSend : client.IsQueryBoundP (fun query => query.isLeft = true) qSend)
    (hRaw : client.IsQueryBoundP (fun query => query.isRight = true) qRaw)
    (initial : RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary)
    (initialized : initializeBeacon root (RawCtxSourceHkdf.initialResponse source.crypto) = ok initial.1.owner.kernel ∨
      initializeServer root (RawCtxSourceHkdf.initialResponse source.crypto) = ok initial.1.owner.kernel)
    (result : Result × (RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary))
    (actual : result ∈ support ((simulateQ (RawCtxMixedOwner.sourceImpl
      (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source)) sender decode) client).run initial)) :
    ∃ finalSpent transcript,
      SourceTrace source writer sender decode (initial, []) transcript (result.2, finalSpent) ∧
      CapabilityTrace source writer initial.1.owner.kernel.refined.send_chain initial.1.owner.kernel.refined.receive_chain
        initial.1.owner.expectedSender sender initial.1.owner.associatedData decode
        (project (initial, [])) transcript (project (result.2, finalSpent)) ∧
      ConsumedRefines source.crypto initial.1.owner.kernel.refined.send_chain
        initial.1.owner.kernel.refined.receive_chain result.2.1.owner.kernel finalSpent ∧
      finalSpent.Nodup ∧ finalSpent.length ≤ qRaw ∧ queryCount Sum.isLeft transcript ≤ qSend ∧
      queryCount Sum.isRight transcript ≤ qRaw ∧ transcript.length ≤ qSend + qRaw := by
  simpa only [List.length_nil, Nat.zero_add] using source_capability_bounded source writer _ _ sender decode
    client qSend qRaw hSend hRaw initial [] (initialized_spent source.crypto root initial.1.owner.kernel initialized) result actual

/-- Private transcript monitoring preserves every selective underlying uniform-query budget of the original mixed source. -/
theorem logged_query_bounds {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result) (state : SourceState Metadata Auxiliary × Transcript)
    (predicate : unifSpec.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    ((simulateQ (loggedImpl source writer sender decode) client).run state).IsQueryBoundP predicate budget ↔
      ((simulateQ (RawCtxMixedOwner.sourceImpl
        (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source)) sender decode) client).run state.1.1).IsQueryBoundP predicate budget := by
  rw [← logged_run_erasure source writer sender decode client state, isQueryBoundP_map_iff]

end BeaconcryptCore.Computational.RawCtxMixedPositionCapability

/--
info: 'BeaconcryptCore.Computational.RawCtxMixedPositionCapability.bare_positioned_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedPositionCapability.bare_positioned_run

/--
info: 'BeaconcryptCore.Computational.RawCtxMixedPositionCapability.arguments_positioned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedPositionCapability.arguments_positioned

/--
info: 'BeaconcryptCore.Computational.RawCtxMixedPositionCapability.bare_position_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedPositionCapability.bare_position_seal

/--
info: 'BeaconcryptCore.Computational.RawCtxMixedPositionCapability.bare_position_seal_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedPositionCapability.bare_position_seal_all

/--
info: 'BeaconcryptCore.Computational.RawCtxMixedPositionCapability.source_sealingAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedPositionCapability.source_sealingAt

/--
info: 'BeaconcryptCore.Computational.RawCtxMixedPositionCapability.source_position_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedPositionCapability.source_position_seal

/--
info: 'BeaconcryptCore.Computational.RawCtxMixedPositionCapability.source_position_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedPositionCapability.source_position_send

/--
info: 'BeaconcryptCore.Computational.RawCtxMixedPositionCapability.receive_send_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedPositionCapability.receive_send_counter

/--
info: 'BeaconcryptCore.Computational.RawCtxMixedPositionCapability.raw_send_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedPositionCapability.raw_send_counter

/--
info: 'BeaconcryptCore.Computational.RawCtxMixedPositionCapability.tracked_step_capability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedPositionCapability.tracked_step_capability

/--
info: 'BeaconcryptCore.Computational.RawCtxMixedPositionCapability.tracked_step_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedPositionCapability.tracked_step_metadata

/--
info: 'BeaconcryptCore.Computational.RawCtxMixedPositionCapability.source_trace_capability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedPositionCapability.source_trace_capability

/--
info: 'BeaconcryptCore.Computational.RawCtxMixedPositionCapability.logged_step_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedPositionCapability.logged_step_erasure

/--
info: 'BeaconcryptCore.Computational.RawCtxMixedPositionCapability.logged_run_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedPositionCapability.logged_run_erasure

/--
info: 'BeaconcryptCore.Computational.RawCtxMixedPositionCapability.logged_run_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedPositionCapability.logged_run_trace

/--
info: 'BeaconcryptCore.Computational.RawCtxMixedPositionCapability.source_supported_capability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedPositionCapability.source_supported_capability

/--
info: 'BeaconcryptCore.Computational.RawCtxMixedPositionCapability.SourceTrace.metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedPositionCapability.SourceTrace.metadata

/--
info: 'BeaconcryptCore.Computational.RawCtxMixedPositionCapability.SourceTrace.history_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedPositionCapability.SourceTrace.history_length

/--
info: 'BeaconcryptCore.Computational.RawCtxMixedPositionCapability.logged_run_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedPositionCapability.logged_run_count

/--
info: 'BeaconcryptCore.Computational.RawCtxMixedPositionCapability.queryCount_partition' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedPositionCapability.queryCount_partition

/--
info: 'BeaconcryptCore.Computational.RawCtxMixedPositionCapability.source_capability_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedPositionCapability.source_capability_bounded

/--
info: 'BeaconcryptCore.Computational.RawCtxMixedPositionCapability.initialized_capability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedPositionCapability.initialized_capability

/--
info: 'BeaconcryptCore.Computational.RawCtxMixedPositionCapability.logged_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedPositionCapability.logged_query_bounds
