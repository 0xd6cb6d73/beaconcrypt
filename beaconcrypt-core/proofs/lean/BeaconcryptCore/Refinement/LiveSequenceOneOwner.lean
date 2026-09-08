import BeaconcryptCore.Refinement.LiveSequenceOne
import BeaconcryptCore.Computational.RawCtxWholeOwner

/-!
# Actual owner contexts in the live sequence-one worker

The original send/raw preludes derive every request context from the same owner: nonempty plaintext or original raw bytes, actual decoded frame, pinned sender, stored AD and fixed local sender. Exact source capability adapters retain every optional primitive reply. The worker represents the whole source kernel, immutable metadata and raw-attempt count, with the identical complete primitive state.

Every supported adaptive source client internally supplies one typed transcript and a matching worker trace. Extra pure rejection branches and mathematical counter normalization are explicit support overapproximations, not equality for arbitrary worker strategies or a probability law. Fixed functional KDF reconstruction retains its local work. Metadata equality within one owner proves no cross-owner key uniqueness, agreement binding or cryptographic origin; the actual registration relation and same-value alias/disclosure accounting remain separate. Storage persistence, snapshots and restoration are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec BeaconcryptCore.Computational
set_option autoImplicit false

namespace beaconcrypt_core.ratchet.concrete

/-- Immutable fields selected by the actual owner, never by an application frame. -/
structure LiveOwnerContext (Metadata : Type) where
  sender : Std.U64
  expected : Std.U64
  associatedData : Pqxdh.Bytes
  metadata : Metadata

def liveOwnerContext {Metadata : Type} (sender : Std.U64)
    (state : RawCtxWholeOwner.OwnerState Metadata) : LiveOwnerContext Metadata :=
  ⟨sender, state.owner.expectedSender, state.owner.associatedData, state.owner.metadata⟩

/-- The token's session fields are exactly the same source owner's immutable fields. -/
structure LiveOwnerRepresents {Metadata : Type} (sender : Std.U64)
    (state : RawCtxWholeOwner.OwnerState Metadata)
    (token : LiveToken (LiveOwnerContext Metadata)) : Prop where
  kernel : LiveRepresents state.owner.kernel token
  context : token.context = liveOwnerContext sender state

/-- Every reached raw core call retains the original buffer, actual decoder result, pinned sender and stored AD before any optional opening reply. -/
theorem live_owner_raw_prelude {Metadata PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (primitive : PrimitiveState)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Metadata) × PrimitiveState)
    (actual : result ∈ support (RawCtxWholeOwner.rawGame impl decode raw state primitive)) :
    result = (RawCtxWholeOwner.publish state (state.owner.kernel, .None), primitive) ∨
      ∃ frame received,
        raw.isEmpty = false ∧ decode raw = some frame ∧
        RawCtxReceive.ValidFrame state.owner.expectedSender state.owner.associatedData frame ∧
        received ∈ support ((simulateQ (impl ∘ₛ RawCtxWholeOwner.adapter)
          (RawCtxOwnerOracle.receive state.owner.kernel frame.sequence
            ⟨raw, frame, state.owner.associatedData⟩)).run primitive) ∧
        result = (RawCtxWholeOwner.publish state received.1, received.2) := by
  unfold RawCtxWholeOwner.rawGame RawCtxWholeOwner.rawReceive StateT.run at actual
  split at actual
  · simp only [simulateQ_pure] at actual
    exact Or.inl actual
  · split at actual
    · simp only [simulateQ_pure] at actual
      exact Or.inl actual
    · dsimp only at actual
      split at actual
      · rw [simulateQ_bind] at actual
        change result ∈ support (StateT.run _ primitive) at actual
        simp only [StateT.run_bind, simulateQ_pure, StateT.run_pure, mem_support_bind_iff,
          support_pure, Set.mem_singleton_iff] at actual
        obtain ⟨received, called, rfl⟩ := actual
        rw [← QueryImpl.simulateQ_compose] at called
        refine Or.inr ⟨_, received, ?_, ?_, ?_, called, rfl⟩
        all_goals simp_all
      · simp only [simulateQ_pure] at actual
        exact Or.inl actual

/-- Every nonempty send supplies stored AD and target plus the fixed local sender, retaining the complete source send result even on failure. -/
theorem live_owner_send_prelude {Metadata PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl RawCtxSourceSend.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (sender : Std.U64) (plaintext : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (primitive : PrimitiveState)
    (result : (Option RawCtxSourceSend.Encrypted × RawCtxWholeOwner.OwnerState Metadata) × PrimitiveState)
    (actual : result ∈ support (RawCtxSourceSend.sendGame impl sender plaintext state primitive)) :
    result = ((none, state), primitive) ∨
      ∃ sent,
        plaintext.isEmpty = false ∧
        sent ∈ support ((simulateQ (impl ∘ₛ RawCtxSourceSend.adapter)
          (RawCtxSourceSend.send state.owner.kernel
            ⟨plaintext, state.owner.expectedSender, sender, state.owner.associatedData⟩)).run primitive) ∧
        result = ((sent.1.2, { state with owner := { state.owner with kernel := sent.1.1 } }), sent.2) := by
  unfold RawCtxSourceSend.sendGame RawCtxSourceSend.sendOwner StateT.run at actual
  split at actual
  · simp only [simulateQ_pure] at actual
    exact Or.inl actual
  · rw [simulateQ_bind] at actual
    change result ∈ support (StateT.run _ primitive) at actual
    simp only [StateT.run_bind, simulateQ_pure, StateT.run_pure, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at actual
    obtain ⟨sent, called, rfl⟩ := actual
    rw [← QueryImpl.simulateQ_compose] at called
    exact Or.inr ⟨sent, by simpa using ‹¬ plaintext.isEmpty = true›, called, rfl⟩

/-- Analysis-only normalization rejects mathematical values outside the actual native word range. -/
def liveWord (sequence : Nat) : Option Std.U64 :=
  if bounded : sequence < 2 ^ 64 then some (Std.U64.ofNatCore sequence bounded) else none

/-- Every actual source word is preserved, rather than truncated or wrapped. -/
theorem live_word_source (sequence : Std.U64) :
    liveWord sequence.val = some sequence := by
  have bounded : sequence.val < 2 ^ 64 := by simpa using sequence.hBounds
  simp only [liveWord, dif_pos bounded]
  congr 1

/-- A fixed source KDF and the actual private frame callback share the same arbitrary effect monad. -/
def liveOwnerSendPrimitive {m : Type → Type} [Monad m]
    (execute : KdfInterpreter) (sealing : RawCtxSourceSend.SealInput → m (Option Pqxdh.Bytes)) :
    QueryImpl RawCtxSourceSend.PrimitiveSpec m
  | .inl request => pure (execute request)
  | .inr input => sealing input

/-- The token callback wraps the actual optional ciphertext with the original source-selected route and sequence. -/
def liveOwnerSealing {m : Type → Type} [Monad m]
    (sealing : RawCtxSourceSend.SealInput → m (Option Pqxdh.Bytes))
    (material : RatchetMaterial) (sequence : Nat) (context : RawCtxSourceSend.SealContext) :
    m (Option RawCtxSourceSend.Encrypted) :=
  match liveWord sequence with
  | none => pure none
  | some word => do
      let input : RawCtxSourceSend.SealInput := ⟨material, word, context⟩
      let reply ← sealing input
      pure (reply.map (RawCtxSourceSend.encrypted input))

/-- Native sealing arguments and optional API construction agree at every source capability, including failed sealing. -/
theorem live_owner_send_adapter {m : Type → Type} [Monad m] [LawfulMonad m]
    (execute : KdfInterpreter) (sealing : RawCtxSourceSend.SealInput → m (Option Pqxdh.Bytes)) :
    liveOwnerSendPrimitive execute sealing ∘ₛ RawCtxSourceSend.adapter =
      liveSendImpl execute (liveOwnerSealing sealing) := by
  funext request
  cases request with
  | inl request => simp [QueryImpl.compose, RawCtxSourceSend.adapter,
      liveOwnerSendPrimitive, liveSendImpl]
  | inr ready =>
      simp [QueryImpl.compose, RawCtxSourceSend.adapter, liveOwnerSendPrimitive,
        liveSendImpl, liveOwnerSealing, live_word_source,
        RawCtxSourceSend.arguments]

/-- Raw opening uses the same fixed KDF interface and preserves the actual optional plaintext callback. -/
def liveOwnerReceivePrimitive {m : Type → Type} [Monad m]
    (execute : KdfInterpreter)
    (opening : RawCtxWholeOwner.OpenInput → m (core.option.Option Pqxdh.Bytes)) :
    QueryImpl RawCtxWholeOwner.PrimitiveSpec m
  | .inl request => pure (execute request)
  | .inr input => opening input

/-- A normalized token opening carries the original raw buffer and frame and wraps only the actual callback result. -/
def liveOwnerOpening {m : Type → Type} [Monad m]
    (opening : RawCtxWholeOwner.OpenInput → m (core.option.Option Pqxdh.Bytes))
    (material : RatchetMaterial) (sequence : Nat) (context : RawCtxWholeOwner.OpenContext) :
    m (core.option.Option RawCtxWholeOwner.Decrypted) :=
  match liveWord sequence with
  | none => pure .None
  | some word => do
      let input : RawCtxWholeOwner.OpenInput := ⟨material, word, context⟩
      let reply ← opening input
      pure (RawCtxOwnerResult.mapReply (RawCtxWholeOwner.decrypted input) reply)

/-- Actual total getters discharge the normalized opening adapter without a successful-plaintext premise. -/
theorem live_owner_receive_adapter {m : Type → Type} [Monad m] [LawfulMonad m]
    (execute : KdfInterpreter)
    (opening : RawCtxWholeOwner.OpenInput → m (core.option.Option Pqxdh.Bytes)) :
    liveOwnerReceivePrimitive execute opening ∘ₛ RawCtxWholeOwner.adapter =
      liveReceiveImpl execute (liveOpening (liveOwnerOpening opening)) := by
  funext request
  rcases request with request | pending
  · simp [QueryImpl.compose, RawCtxWholeOwner.adapter, liveOwnerReceivePrimitive, liveReceiveImpl]
  · simp only [QueryImpl.compose, RawCtxWholeOwner.adapter, liveReceiveImpl, liveOpening,
      RawCtxWholeOwner.arguments]
    obtain ⟨material, materialEq⟩ := pending.material_total
    obtain ⟨sequence, sequenceEq⟩ := pending.sequence_total
    cases material <;> simp [materialEq, sequenceEq,
      liveOwnerOpening, live_word_source, liveOwnerReceivePrimitive]

abbrev LiveOwnerSpec := RawCtxSourceSend.ApplicationSpec + RawCtxWholeOwner.RawSpec

/-- Public owner calls still run the original source adapters and publish their whole source owner. -/
noncomputable def liveOwnerSourceImpl {Metadata PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι} (execute : KdfInterpreter)
    (sealing : RawCtxSourceSend.SealInput → StateT PrimitiveState (OracleComp base) (Option Pqxdh.Bytes))
    (opening : RawCtxWholeOwner.OpenInput → StateT PrimitiveState (OracleComp base) (core.option.Option Pqxdh.Bytes))
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl LiveOwnerSpec (StateT (RawCtxWholeOwner.OwnerState Metadata × PrimitiveState) (OracleComp base))
  | .inl plaintext => RawCtxSourceSend.ownerImpl (liveOwnerSendPrimitive execute sealing) sender plaintext
  | .inr raw => RawCtxWholeOwner.ownerImpl (liveOwnerReceivePrimitive execute opening) decode raw

/-- The private process also retains the source ghost count; the primitive state is unchanged by the projection. -/
abbrev LiveOwnerConfiguration (Metadata PrimitiveState : Type) :=
  (LiveToken (LiveOwnerContext Metadata) × Nat) × PrimitiveState

def liveSendContext {Metadata : Type} (context : LiveOwnerContext Metadata)
    (plaintext : Pqxdh.Bytes) : RawCtxSourceSend.SealContext :=
  ⟨plaintext, context.expected, context.sender, context.associatedData⟩

def liveRawContext {Metadata : Type} (context : LiveOwnerContext Metadata)
    (raw : Pqxdh.Bytes) (frame : RawCtxReceive.DecodedFrame) : RawCtxWholeOwner.OpenContext :=
  ⟨raw, frame, context.associatedData⟩

/-- These outer worker branches select every inner context from immutable owner fields; they add no cryptographic success or key-uniqueness assumption. -/
inductive LiveOwnerStep {AD PT CT Metadata PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (sealing : RawCtxSourceSend.SealInput → StateT PrimitiveState (OracleComp base) (Option Pqxdh.Bytes))
    (opening : RawCtxWholeOwner.OpenInput → StateT PrimitiveState (OracleComp base) (core.option.Option Pqxdh.Bytes))
    (decode : RawCtxReceive.FrameDecoder) :
    LiveOwnerConfiguration Metadata PrimitiveState →
      (query : LiveOwnerSpec.Domain) → LiveOwnerSpec.Range query →
      LiveOwnerConfiguration Metadata PrimitiveState → Prop
  | rejectSend (token) (attempts) (primitive) (plaintext) :
      LiveOwnerStep cr sealing opening decode ((token, attempts), primitive)
        (.inl plaintext) none ((token, attempts), primitive)
  | rejectRaw (token) (attempts) (primitive) (raw) :
      LiveOwnerStep cr sealing opening decode ((token, attempts), primitive)
        (.inr raw) .None ((token, attempts + 1), primitive)
  | send (token) (after) (attempts) (primitive) (post) (plaintext) (reply)
      (nonempty : plaintext.isEmpty = false)
      (core : LiveStep cr (liveOwnerSealing sealing) (liveOwnerOpening opening)
        (token, primitive) (.inl (liveSendContext token.context plaintext)) reply (after, post)) :
      LiveOwnerStep cr sealing opening decode ((token, attempts), primitive)
        (.inl plaintext) reply ((after, attempts), post)
  | raw (token) (after) (attempts) (primitive) (post) (raw) (frame) (reply)
      (nonempty : raw.isEmpty = false) (decoded : decode raw = some frame)
      (valid : RawCtxReceive.ValidFrame token.context.expected token.context.associatedData frame)
      (core : LiveStep cr (liveOwnerSealing sealing) (liveOwnerOpening opening)
        (token, primitive) (.inr (frame.sequence, liveRawContext token.context raw frame)) reply (after, post)) :
      LiveOwnerStep cr sealing opening decode ((token, attempts), primitive)
        (.inr raw) reply ((after, attempts + 1), post)

/-- Every actual owner call supplies a token step with exactly the same typed reply, full primitive poststate and immutable source metadata. -/
theorem live_owner_source_step {AD PT CT Metadata PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (execute : KdfInterpreter)
    (sealing : RawCtxSourceSend.SealInput → StateT PrimitiveState (OracleComp base) (Option Pqxdh.Bytes))
    (opening : RawCtxWholeOwner.OpenInput → StateT PrimitiveState (OracleComp base) (core.option.Option Pqxdh.Bytes))
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (state : RawCtxWholeOwner.OwnerState Metadata) (primitive : PrimitiveState)
    (token : LiveToken (LiveOwnerContext Metadata))
    (represented : LiveOwnerRepresents sender state token)
    (query : LiveOwnerSpec.Domain)
    (result : LiveOwnerSpec.Range query × (RawCtxWholeOwner.OwnerState Metadata × PrimitiveState))
    (actual : result ∈ support ((liveOwnerSourceImpl execute sealing opening sender decode query).run (state, primitive))) :
    ∃ after, LiveOwnerRepresents sender result.2.1 after ∧
      LiveOwnerStep (withInterpreter cr execute) sealing opening decode
        ((token, state.rawAttempts), primitive) query result.1 ((after, result.2.1.rawAttempts), result.2.2) := by
  cases query with
  | inl plaintext =>
      change Option RawCtxSourceSend.Encrypted × (RawCtxWholeOwner.OwnerState Metadata × PrimitiveState) at result
      change result ∈ support (RawCtxSourceSend.sendGame (liveOwnerSendPrimitive execute sealing)
        sender plaintext state primitive >>= fun sent => pure (sent.1.1, (sent.1.2, sent.2))) at actual
      rw [mem_support_bind_iff] at actual
      obtain ⟨sent, called, rfl⟩ := (by simpa only [support_pure, Set.mem_singleton_iff] using actual)
      rcases live_owner_send_prelude (liveOwnerSendPrimitive execute sealing)
        sender plaintext state primitive sent called with rejected | ⟨core, nonempty, coreCall, published⟩
      · subst sent
        exact ⟨token, represented, .rejectSend token state.rawAttempts primitive plaintext⟩
      · subst sent
        rw [live_owner_send_adapter] at coreCall
        rw [← show liveSendContext token.context plaintext =
          ⟨plaintext, state.owner.expectedSender, sender, state.owner.associatedData⟩ from
          by simp only [liveSendContext, represented.context, liveOwnerContext]] at coreCall
        have inner : (core.1.2, (core.1.1, core.2)) ∈ support
            ((liveSourceImpl execute (liveOwnerSealing sealing) (liveOwnerOpening opening)
              (.inl (liveSendContext token.context plaintext))).run (state.owner.kernel, primitive)) :=
          (mem_support_bind_iff _ _ _).mpr ⟨core, coreCall, by simp⟩
        obtain ⟨after, afterRep, step⟩ := live_source_step cr execute
          (liveOwnerSealing sealing) (liveOwnerOpening opening)
          state.owner.kernel token represented.kernel primitive
          (.inl (liveSendContext token.context plaintext)) _ inner
        exact ⟨after, ⟨afterRep, step.session.trans represented.context⟩,
          .send token after state.rawAttempts primitive core.2 plaintext core.1.2 nonempty step⟩
  | inr raw =>
      change core.option.Option RawCtxWholeOwner.Decrypted × (RawCtxWholeOwner.OwnerState Metadata × PrimitiveState) at result
      change result ∈ support (RawCtxWholeOwner.rawGame (liveOwnerReceivePrimitive execute opening)
        decode raw state primitive >>= fun received => pure (received.1.1, (received.1.2, received.2))) at actual
      rw [mem_support_bind_iff] at actual
      obtain ⟨received, called, rfl⟩ := (by simpa only [support_pure, Set.mem_singleton_iff] using actual)
      rcases live_owner_raw_prelude (liveOwnerReceivePrimitive execute opening)
        decode raw state primitive received called with rejected | ⟨frame, core, nonempty, decoded, valid, coreCall, published⟩
      · subst received
        exact ⟨token, ⟨represented.kernel, represented.context⟩, .rejectRaw token state.rawAttempts primitive raw⟩
      · subst received
        rw [live_owner_receive_adapter] at coreCall
        rw [← show token.context.associatedData = state.owner.associatedData from
          congrArg LiveOwnerContext.associatedData represented.context] at coreCall
        have inner : (core.1.2, (core.1.1, core.2)) ∈ support
            ((liveSourceImpl execute (liveOwnerSealing sealing) (liveOwnerOpening opening)
              (.inr (frame.sequence, ⟨raw, frame, token.context.associatedData⟩))).run (state.owner.kernel, primitive)) := by
          exact (mem_support_bind_iff _ _ _).mpr ⟨core, coreCall, by simp⟩
        obtain ⟨after, afterRep, step⟩ := live_source_step cr execute
          (liveOwnerSealing sealing) (liveOwnerOpening opening)
          state.owner.kernel token represented.kernel primitive
          (.inr (frame.sequence, ⟨raw, frame, token.context.associatedData⟩)) _ inner
        refine ⟨after, ⟨afterRep, step.session.trans represented.context⟩, ?_⟩
        exact .raw token after state.rawAttempts primitive core.2 raw frame core.1.2 nonempty decoded
          (by simpa only [represented.context, liveOwnerContext] using valid)
          (by exact step)

/-- Each private transcript entry is the actual raw-byte or plaintext request with its original dependent reply. -/
abbrev LiveOwnerTranscript :=
  List ((query : LiveOwnerSpec.Domain) × LiveOwnerSpec.Range query)

section OwnerTraces
variable {AD PT CT Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
  (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
  (execute : KdfInterpreter)
  (sealing : RawCtxSourceSend.SealInput → StateT PrimitiveState (OracleComp base) (Option Pqxdh.Bytes))
  (opening : RawCtxWholeOwner.OpenInput → StateT PrimitiveState (OracleComp base) (core.option.Option Pqxdh.Bytes))
  (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)

/-- Original owner calls carry the complete owner and primitive state to the next live call. -/
inductive LiveOwnerSourceTrace :
    (RawCtxWholeOwner.OwnerState Metadata × PrimitiveState) → LiveOwnerTranscript →
      (RawCtxWholeOwner.OwnerState Metadata × PrimitiveState) → Prop
  | nil (state) : LiveOwnerSourceTrace state [] state
  | step {state final} (query)
      {result : LiveOwnerSpec.Range query × (RawCtxWholeOwner.OwnerState Metadata × PrimitiveState)} {rest}
      (actual : result ∈ support ((liveOwnerSourceImpl execute sealing opening sender decode query).run state))
      (tail : LiveOwnerSourceTrace result.2 rest final) :
      LiveOwnerSourceTrace state (⟨query, result.1⟩ :: rest) final

/-- The live worker consumes the same public calls while deriving their inner contexts from its private token. -/
inductive LiveOwnerTrace : LiveOwnerConfiguration Metadata PrimitiveState →
    LiveOwnerTranscript → LiveOwnerConfiguration Metadata PrimitiveState → Prop
  | nil (state) : LiveOwnerTrace state [] state
  | step {state next final} (query) (reply) {rest}
      (actual : LiveOwnerStep cr sealing opening decode state query reply next)
      (tail : LiveOwnerTrace next rest final) :
      LiveOwnerTrace state (⟨query, reply⟩ :: rest) final

/-- Every live source trace has the same raw/send transcript, actual attempt count and complete primitive poststate in the token worker. -/
theorem live_owner_source_trace
    {initial final : RawCtxWholeOwner.OwnerState Metadata × PrimitiveState}
    {transcript : LiveOwnerTranscript}
    (trace : LiveOwnerSourceTrace execute sealing opening sender decode initial transcript final)
    (token : LiveToken (LiveOwnerContext Metadata))
    (represented : LiveOwnerRepresents sender initial.1 token) :
    ∃ after, LiveOwnerRepresents sender final.1 after ∧
      LiveOwnerTrace (withInterpreter cr execute) sealing opening decode
        ((token, initial.1.rawAttempts), initial.2) transcript ((after, final.1.rawAttempts), final.2) := by
  induction trace generalizing token with
  | nil state => exact ⟨token, represented, .nil _⟩
  | @step state final query result rest actual tail ih =>
      obtain ⟨next, nextRep, step⟩ := live_owner_source_step cr execute sealing opening sender decode
        state.1 state.2 token represented query result actual
      obtain ⟨after, afterRep, trace⟩ := ih next nextRep
      exact ⟨after, afterRep, .step query result.1 step trace⟩

/-- The transcript witness comes from the original adaptive client and retains its complete result and owner/primitive poststate. -/
theorem live_owner_client_trace {Result : Type}
    (client : OracleComp LiveOwnerSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata × PrimitiveState)
    (result : Result × (RawCtxWholeOwner.OwnerState Metadata × PrimitiveState))
    (actual : result ∈ support
      ((simulateQ (liveOwnerSourceImpl execute sealing opening sender decode) client).run state)) :
    ∃ transcript, LiveOwnerSourceTrace execute sealing opening sender decode state transcript result.2 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure] at actual
      cases actual
      exact ⟨[], .nil _⟩
  | query_bind query next ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, mem_support_bind_iff] at actual
      obtain ⟨step, called, later⟩ := actual
      obtain ⟨rest, trace⟩ := ih step.1 step.2 result later
      exact ⟨⟨query, step.1⟩ :: rest, .step query called trace⟩

/-- A supported actual client yields one source trace and one matching live worker trace, with its unchanged dependent replies and full final state. -/
theorem live_owner_supported_client {Result : Type}
    (client : OracleComp LiveOwnerSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata × PrimitiveState)
    (token : LiveToken (LiveOwnerContext Metadata))
    (represented : LiveOwnerRepresents sender state.1 token)
    (result : Result × (RawCtxWholeOwner.OwnerState Metadata × PrimitiveState))
    (actual : result ∈ support
      ((simulateQ (liveOwnerSourceImpl execute sealing opening sender decode) client).run state)) :
    ∃ transcript after,
      LiveOwnerSourceTrace execute sealing opening sender decode state transcript result.2 ∧
      LiveOwnerRepresents sender result.2.1 after ∧
      LiveOwnerTrace (withInterpreter cr execute) sealing opening decode
        ((token, state.1.rawAttempts), state.2) transcript ((after, result.2.1.rawAttempts), result.2.2) := by
  obtain ⟨transcript, trace⟩ := live_owner_client_trace execute sealing opening sender decode client state result actual
  obtain ⟨after, afterRep, process⟩ := live_owner_source_trace cr execute sealing opening sender decode trace token represented
  exact ⟨transcript, after, trace, afterRep, process⟩

end OwnerTraces

end beaconcrypt_core.ratchet.concrete

/--
info: 'beaconcrypt_core.ratchet.concrete.live_owner_raw_prelude' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_owner_raw_prelude

/--
info: 'beaconcrypt_core.ratchet.concrete.live_owner_send_prelude' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_owner_send_prelude

/--
info: 'beaconcrypt_core.ratchet.concrete.live_word_source' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_word_source

/--
info: 'beaconcrypt_core.ratchet.concrete.live_owner_send_adapter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_owner_send_adapter

/--
info: 'beaconcrypt_core.ratchet.concrete.live_owner_receive_adapter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_owner_receive_adapter

/--
info: 'beaconcrypt_core.ratchet.concrete.live_owner_source_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_owner_source_step

/--
info: 'beaconcrypt_core.ratchet.concrete.live_owner_source_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_owner_source_trace

/--
info: 'beaconcrypt_core.ratchet.concrete.live_owner_client_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_owner_client_trace

/--
info: 'beaconcrypt_core.ratchet.concrete.live_owner_supported_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.live_owner_supported_client
