import BeaconcryptCore.Computational.RawCtxPositionedOpening
import BeaconcryptCore.Computational.RawCtxConsumptionGate

/-!
A position-based raw receiver is a stronger operational abstraction of one uninterrupted source owner. It keeps the original raw bytes, pure frame decoder, sender/shape checks, immutable associated data, actual position-derived material, optional opening reply and complete primitive state. It stores only private successful-position history in place of the concrete receive counter/cache/kernel. A Boolean selects whether the validated attempt reaches its opening; the matching choice is derived from the actual source admission before any primitive state or reply is known. Failed attempts retain their real primitive effects and successful positions are recorded only from the actual returned sequence.

The original fixed-functional KDF prefix is erased only after interpretation by the existing pure source KDF callback. Each step has an exact projected oracle-program equality. A private monitor executes the original adaptive raw client and constructs its actual raw/reply transcript without altering any result or source state. Erasure is exact for the complete original computation and every selective underlying uniform-query bound. The trace theorem then constructs a matching position-receiver trace with the same raw/optional-result transcript, complete final primitive state and private spent history. The source relation and its no-repeat property are derived throughout that execution; initialization and query-bounded trace/history corollaries retain the actual source initializer.

The complete trace result is support inclusion, not an equality of probability distributions for an arbitrary scheduler of the admission Boolean. The matching choice may retain source control state in the simulation proof; no executable source-free global scheduler is constructed. Material reconstruction from a private origin and repeated pure decoding/list lookup add real local work, possibly proportional to the position. Source KDF callback counts and uniform-query equalities do not declare this work free or establish native timing/traversal/allocation equality. Distinct origins or positions may have equal material values. Source overflow remains governed by the actual finite native counter.

This module covers arbitrary adaptive raw-only calls with a supplied fixed-source owner relation, including every rejected or successful attempt. Mixed sends, public services, reveals, registration/lifecycle transitions, multiple owners, restored/copied state and a concrete persistent ProVerif process still need their own trace mappings. Original origins, source kernels and proof histories remain private and are not added to reveal, snapshot, persistence or network interfaces. Actual optional API plaintext is retained; its public declassification is an outer policy. This is not a cryptographic authentication, key-independence, probability-loss or global computational-symbolic theorem, and does not discharge native primitive/codec/runtime/deployment contracts.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxPositionCapability
open RawCtxMaterialPositions RawCtxPositionedOpening RawCtxOwnerProvenance

/-- The actual fixed-response KDF prefix disappears only after its pure interpretation, preserving the reached opening computation. -/
theorem bare_prefix_complete {Context Plaintext PrimitiveState ι : Type} {base : OracleSpec ι}
    (execute : KdfInterpreter)
    (opening : ReceiveOpen Context → StateT PrimitiveState (OracleComp base) (core.option.Option Plaintext))
    {effect terminal : ReceiveEffect Context} {requests : List SymmetricRatchetKdfRequest}
    (trace : Prefix execute effect terminal requests) :
    simulateQ (bareReceiveImpl execute opening) (RawCtxOwnerOracle.program effect) =
      simulateQ (bareReceiveImpl execute opening) (RawCtxOwnerOracle.program terminal) := by
  induction trace with
  | refl => rfl
  | step pending next final requests resumed tail ih =>
    have exactNext : RawCtxOwnerOracle.resume pending (execute pending.request) = next :=
      RustM.ok.inj ((RawCtxOwnerOracle.resume_exact pending (execute pending.request)).symm.trans resumed)
    simpa only [RawCtxOwnerOracle.program, simulateQ_bind, simulateQ_spec_query,
      bareReceiveImpl, pure_bind, exactNext] using ih

/-- Removing the private terminal kernel retains exactly the actual optional opening and full primitive poststate. -/
theorem opening_reply {Context Plaintext PrimitiveState ι : Type} {base : OracleSpec ι}
    (execute : KdfInterpreter)
    (opening : ReceiveOpen Context → StateT PrimitiveState (OracleComp base) (core.option.Option Plaintext))
    (pending : ReceiveOpen Context) (state : PrimitiveState) :
    Prod.map Prod.snd id <$> (simulateQ (bareReceiveImpl execute opening)
      (RawCtxOwnerOracle.program (.ReceiveOpenRequested pending))).run state =
      (opening pending).run state := by
  simp [RawCtxOwnerOracle.program, bareReceiveImpl, RawCtxOwnerOracle.finish]

/-- The actual prepared getters reconstruct precisely the selected material, sequence and immutable context. -/
theorem arguments_exact (pending : ReceiveOpen RawCtxWholeOwner.OpenContext)
    (material : RatchetMaterial) (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (selected : pending.material = ok (.Some material))
    (sameSequence : pending.sequence = ok sequence) (sameContext : pending.context = context) :
    RawCtxWholeOwner.arguments pending = some ⟨material, sequence, context⟩ := by
  have materialEq := RustM.ok.inj (pending.material_total.choose_spec.symm.trans selected)
  have sequenceEq := RustM.ok.inj (pending.sequence_total.choose_spec.symm.trans sameSequence)
  simp only [RawCtxWholeOwner.arguments, materialEq, sequenceEq, sameContext]

noncomputable def openPosition {AD PT CT PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (origin : RatchetChain)
    (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base))) :
    StateT PrimitiveState (OracleComp base) (core.option.Option RawCtxWholeOwner.Decrypted) := do
  let input : RawCtxWholeOwner.OpenInput := ⟨Ratchet.msgKeyAt cr origin (target.val - 1), target, context⟩
  let reply ← impl (.inr input)
  pure (RawCtxOwnerResult.mapReply (RawCtxWholeOwner.decrypted input) reply)

/-- Source admission supplies one Boolean before all primitive states and opening replies, with exact reply/state projection. -/
theorem owner_reply_choice {AD PT CT PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (origin : RatchetChain) (send : Ratchet.SendState RatchetChain)
    (receive : Ratchet.RecvState RatchetChain RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : RawCtxWholeOwner.OpenContext) (target : Std.U64)
    (refines : KernelRefines (withInterpreter cr execute) origin send receive entry)
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (kdf : ∀ request, impl (.inl request) = pure (execute request)) :
    ∃ enabled : Bool, ∀ primitive,
      Prod.map Prod.snd id <$> (simulateQ impl
        (simulateQ RawCtxWholeOwner.adapter (RawCtxOwnerOracle.receive entry target context))).run primitive =
      ((if enabled then openPosition (withInterpreter cr execute) origin target context impl
        else pure .None)).run primitive := by
  obtain ⟨terminal, requests, trace, selected⟩ := receive_prefix cr execute origin send receive entry context target refines
  have hscope := prefix_scope execute target context trace (oracle_begin_scope entry target context)
  rw [← QueryImpl.simulateQ_compose, primitive_bare execute impl kdf,
    RawCtxOwnerOracle.receive, bare_prefix_complete execute _ trace]
  rcases selected with rfl | ⟨opened, rfl, material⟩
  · refine ⟨false, ?_⟩
    simp [RawCtxOwnerOracle.program, StateT.run_pure]
  · refine ⟨true, ?_⟩
    intro primitive
    rw [opening_reply]
    have args := arguments_exact opened _ target context material hscope.1 hscope.2
    simp [QueryImpl.compose, RawCtxWholeOwner.adapter, args, openPosition]

noncomputable def positionReceive {AD PT CT PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (origin : RatchetChain)
    (expectedSender : Std.U64) (associatedData : Pqxdh.Bytes)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (enabled : Bool)
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base))) :
    StateT PrimitiveState (OracleComp base) (core.option.Option RawCtxWholeOwner.Decrypted) :=
  if raw.isEmpty then pure .None else
    match decode raw with
    | none => pure .None
    | some frame => if RawCtxReceive.ValidFrame expectedSender associatedData frame then
        if enabled then openPosition cr origin frame.sequence ⟨raw, frame, associatedData⟩ impl
        else pure .None
      else pure .None

/-- Actual raw preparation preserves its source opening input and the complete private primitive computation. -/
theorem raw_prepared_reply {Metadata PrimitiveState ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (primitive : PrimitiveState)
    (frame : RawCtxReceive.DecodedFrame)
    (nonempty : raw.isEmpty = false) (decoded : decode raw = some frame)
    (valid : RawCtxReceive.ValidFrame state.owner.expectedSender state.owner.associatedData frame) :
    Prod.map Prod.fst id <$> RawCtxWholeOwner.rawGame impl decode raw state primitive =
      Prod.map Prod.snd id <$> (simulateQ impl (simulateQ RawCtxWholeOwner.adapter
        (RawCtxOwnerOracle.receive state.owner.kernel frame.sequence
          ⟨raw, frame, state.owner.associatedData⟩))).run primitive := by
  have prepared : (RawCtxWholeOwner.rawReceive decode raw).run state =
      RawCtxWholeOwner.publish state <$> simulateQ RawCtxWholeOwner.adapter
        (RawCtxOwnerOracle.receive state.owner.kernel frame.sequence
          ⟨raw, frame, state.owner.associatedData⟩) := by
    unfold RawCtxWholeOwner.rawReceive StateT.run
    simp [nonempty, decoded, valid]
  simp [RawCtxWholeOwner.rawGame, prepared, StateT.run_map, Functor.map_map,
    RawCtxWholeOwner.publish]
  rfl

/-- Disabling the stronger receiver preserves every pure early validation outcome and performs no primitive request. -/
theorem positionReceive_false {AD PT CT PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (origin : RatchetChain)
    (expectedSender : Std.U64) (associatedData : Pqxdh.Bytes)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base))) :
    positionReceive cr origin expectedSender associatedData decode raw false impl = pure .None := by
  simp only [positionReceive, Bool.false_eq_true, ↓reduceIte]
  cases decode raw <;> simp

/-- Every source raw branch has an exact position-receiver reply/state projection without a successful-opening premise. -/
theorem raw_reply_choice {AD PT CT Metadata PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (origin : RatchetChain) (send : Ratchet.SendState RatchetChain)
    (receive : Ratchet.RecvState RatchetChain RatchetMaterial)
    (state : RawCtxWholeOwner.OwnerState Metadata)
    (refines : KernelRefines (withInterpreter cr execute) origin send receive state.owner.kernel)
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (kdf : ∀ request, impl (.inl request) = pure (execute request)) :
    ∃ enabled : Bool, ∀ primitive,
      Prod.map Prod.fst id <$> RawCtxWholeOwner.rawGame impl decode raw state primitive =
        (positionReceive (withInterpreter cr execute) origin state.owner.expectedSender
          state.owner.associatedData decode raw enabled impl).run primitive := by
  have rejected (actual : (RawCtxWholeOwner.rawReceive decode raw).run state =
      pure (RawCtxWholeOwner.publish state (state.owner.kernel, .None))) :
      ∃ enabled : Bool, ∀ primitive,
        Prod.map Prod.fst id <$> RawCtxWholeOwner.rawGame impl decode raw state primitive =
          (positionReceive (withInterpreter cr execute) origin state.owner.expectedSender
            state.owner.associatedData decode raw enabled impl).run primitive := by
    refine ⟨false, ?_⟩
    simp [positionReceive_false, RawCtxWholeOwner.rawGame, actual,
      StateT.run_pure, RawCtxWholeOwner.publish]
  by_cases empty : raw.isEmpty = true
  · apply rejected
    unfold RawCtxWholeOwner.rawReceive StateT.run
    simp [empty]
  cases decoded : decode raw with
  | none =>
    apply rejected
    unfold RawCtxWholeOwner.rawReceive StateT.run
    simp [empty, decoded]
  | some frame =>
    by_cases valid : RawCtxReceive.ValidFrame state.owner.expectedSender state.owner.associatedData frame
    · obtain ⟨enabled, same⟩ := owner_reply_choice cr execute origin send receive state.owner.kernel
        ⟨raw, frame, state.owner.associatedData⟩ frame.sequence refines impl kdf
      refine ⟨enabled, fun primitive => ?_⟩
      rw [raw_prepared_reply impl decode raw state primitive frame (by simpa using empty) decoded valid, same primitive]
      simp only [positionReceive, empty, Bool.false_eq_true, ↓reduceIte, decoded, valid]
    · apply rejected
      unfold RawCtxWholeOwner.rawReceive StateT.run
      simp [empty, decoded, valid]

noncomputable def gatedPositionReceive {AD PT CT PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (origin : RatchetChain)
    (spent : List Nat) (expectedSender : Std.U64) (associatedData : Pqxdh.Bytes)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (enabled : Bool)
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base))) :
    StateT PrimitiveState (OracleComp base) (core.option.Option RawCtxWholeOwner.Decrypted) :=
  match decode raw with
  | some frame => if frame.sequence.val - 1 ∈ spent then pure .None
      else positionReceive cr origin expectedSender associatedData decode raw enabled impl
  | none => positionReceive cr origin expectedSender associatedData decode raw enabled impl

open RawCtxReceiveConsumption

/-- The source-derived spent relation justifies consumed rejection before all callbacks; every other branch retains its admission choice. -/
theorem source_gated_reply_choice {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (sendOrigin receiveOrigin : RatchetChain) (spent : List Nat)
    (state : RawCtxWholeOwner.OwnerState Metadata)
    (invariant : ConsumedRefines source.crypto sendOrigin receiveOrigin state.owner.kernel spent)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) :
    ∃ enabled : Bool, ∀ primitive : RawCtxSharedPrimitive.SharedState Auxiliary,
      Prod.map Prod.fst id <$> RawCtxWholeOwner.rawGame (receiveNative source) decode raw state primitive =
        (gatedPositionReceive (crypto source.crypto) receiveOrigin spent state.owner.expectedSender
          state.owner.associatedData decode raw enabled (receiveNative source)).run primitive := by
  have choice : ∃ enabled : Bool, ∀ primitive : RawCtxSharedPrimitive.SharedState Auxiliary,
      Prod.map Prod.fst id <$> RawCtxWholeOwner.rawGame (receiveNative source) decode raw state primitive =
        (positionReceive (crypto source.crypto) receiveOrigin state.owner.expectedSender
          state.owner.associatedData decode raw enabled (receiveNative source)).run primitive := by
    obtain ⟨send, receive, refines, _⟩ := invariant
    exact raw_reply_choice (crypto source.crypto) (RawCtxSourceHkdf.response source.crypto)
      receiveOrigin send receive state refines (receiveNative source) decode raw (source_kdf source)
  cases decoded : decode raw with
  | none => simpa only [gatedPositionReceive, decoded] using choice
  | some frame =>
    by_cases consumed : frame.sequence.val - 1 ∈ spent
    · refine ⟨false, fun primitive => ?_⟩
      rw [RawCtxConsumptionGate.rawGame_spent source.crypto sendOrigin receiveOrigin state spent invariant
        (receiveNative source) primitive decode raw frame decoded consumed]
      simp [gatedPositionReceive, decoded, consumed, RawCtxWholeOwner.publish, StateT.run_pure]
    · simpa only [gatedPositionReceive, decoded, consumed, ↓reduceIte] using choice

noncomputable def capabilityStep {AD PT CT PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (origin : RatchetChain)
    (expectedSender : Std.U64) (associatedData : Pqxdh.Bytes)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (enabled : Bool)
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base))) :
    StateT (PrimitiveState × List Nat) (OracleComp base) (core.option.Option RawCtxWholeOwner.Decrypted) :=
  fun state => do
    let result ← (gatedPositionReceive cr origin state.2 expectedSender associatedData decode raw enabled impl).run state.1
    pure (result.1, (result.2, recordReply result.1 state.2))

/-- One source raw computation projects exactly to the chosen position step and actual successful-position update. -/
theorem source_capability_step {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (sendOrigin receiveOrigin : RatchetChain) (spent : List Nat)
    (state : RawCtxWholeOwner.OwnerState Metadata)
    (invariant : ConsumedRefines source.crypto sendOrigin receiveOrigin state.owner.kernel spent)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) :
    ∃ enabled : Bool, ∀ primitive : RawCtxSharedPrimitive.SharedState Auxiliary,
      (fun result => (result.1.1, (result.2, recordReply result.1.1 spent))) <$>
        RawCtxWholeOwner.rawGame (receiveNative source) decode raw state primitive =
      (capabilityStep (crypto source.crypto) receiveOrigin state.owner.expectedSender
        state.owner.associatedData decode raw enabled (receiveNative source)).run (primitive, spent) := by
  obtain ⟨enabled, same⟩ := source_gated_reply_choice source sendOrigin receiveOrigin spent state invariant decode raw
  refine ⟨enabled, fun primitive => ?_⟩
  have recorded := congrArg (fun computation => (fun result =>
    (result.1, (result.2, recordReply result.1 spent))) <$> computation) (same primitive)
  simpa [capabilityStep, StateT.run, Functor.map_map, Function.comp_def, Prod.map] using recorded

abbrev SourceState (Metadata Auxiliary : Type) :=
  (RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) × List Nat

abbrev RawResult (Metadata Auxiliary : Type) :=
  (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Metadata) ×
    RawCtxSharedPrimitive.SharedState Auxiliary

def sourceNext {Metadata Auxiliary : Type} (state : SourceState Metadata Auxiliary)
    (result : RawResult Metadata Auxiliary) : SourceState Metadata Auxiliary :=
  ((result.1.2, result.2), recordReply result.1.1 state.2)

def project {Metadata Auxiliary : Type} (state : SourceState Metadata Auxiliary) :
    RawCtxSharedPrimitive.SharedState Auxiliary × List Nat := (state.1.2, state.2)

inductive SourceTrace {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (decode : RawCtxReceive.FrameDecoder) :
    SourceState Metadata Auxiliary → List (Pqxdh.Bytes × core.option.Option RawCtxWholeOwner.Decrypted) →
      SourceState Metadata Auxiliary → Prop where
  | nil (state : SourceState Metadata Auxiliary) : SourceTrace source decode state [] state
  | step {state : SourceState Metadata Auxiliary} {result : RawResult Metadata Auxiliary}
      {rest : List (Pqxdh.Bytes × core.option.Option RawCtxWholeOwner.Decrypted)}
      {final : SourceState Metadata Auxiliary} (raw : Pqxdh.Bytes)
      (actual : result ∈ support (RawCtxWholeOwner.rawGame (receiveNative source) decode raw state.1.1 state.1.2))
      (tail : SourceTrace source decode (sourceNext state result) rest final) :
      SourceTrace source decode state ((raw, result.1.1) :: rest) final

inductive CapabilityTrace {AD PT CT PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (origin : RatchetChain)
    (expectedSender : Std.U64) (associatedData : Pqxdh.Bytes) (decode : RawCtxReceive.FrameDecoder)
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base))) :
    (PrimitiveState × List Nat) → List (Pqxdh.Bytes × core.option.Option RawCtxWholeOwner.Decrypted) →
      (PrimitiveState × List Nat) → Prop where
  | nil (state : PrimitiveState × List Nat) : CapabilityTrace cr origin expectedSender associatedData decode impl state [] state
  | step {state final : PrimitiveState × List Nat}
      {result : core.option.Option RawCtxWholeOwner.Decrypted × (PrimitiveState × List Nat)}
      {rest : List (Pqxdh.Bytes × core.option.Option RawCtxWholeOwner.Decrypted)}
      (raw : Pqxdh.Bytes) (enabled : Bool)
      (actual : result ∈ support ((capabilityStep cr origin expectedSender associatedData decode raw enabled impl).run state))
      (tail : CapabilityTrace cr origin expectedSender associatedData decode impl result.2 rest final) :
      CapabilityTrace cr origin expectedSender associatedData decode impl state ((raw, result.1) :: rest) final

/-- Every actual source trace embeds with the same raw/optional transcript and final primitive/history state. -/
theorem source_trace_capability {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (sendOrigin receiveOrigin : RatchetChain) (decode : RawCtxReceive.FrameDecoder)
    {initial final : SourceState Metadata Auxiliary}
    {transcript : List (Pqxdh.Bytes × core.option.Option RawCtxWholeOwner.Decrypted)}
    (trace : SourceTrace source decode initial transcript final)
    (invariant : ConsumedRefines source.crypto sendOrigin receiveOrigin initial.1.1.owner.kernel initial.2) :
    CapabilityTrace (crypto source.crypto) receiveOrigin initial.1.1.owner.expectedSender
      initial.1.1.owner.associatedData decode (receiveNative source) (project initial) transcript (project final) ∧
    ConsumedRefines source.crypto sendOrigin receiveOrigin final.1.1.owner.kernel final.2 := by
  induction trace with
  | nil state => exact ⟨.nil _, invariant⟩
  | @step state result rest final raw actual tail ih =>
    have nextInvariant := raw_spent source sendOrigin receiveOrigin state.2 decode raw state.1.1
      invariant state.1.2 result actual
    obtain ⟨nextTrace, finalInvariant⟩ := ih nextInvariant
    obtain ⟨enabled, same⟩ := source_capability_step source sendOrigin receiveOrigin state.2 state.1.1
      invariant decode raw
    have supported : (result.1.1, project (sourceNext state result)) ∈
        support ((capabilityStep (crypto source.crypto) receiveOrigin state.1.1.owner.expectedSender
          state.1.1.owner.associatedData decode raw enabled (receiveNative source)).run (project state)) := by
      rw [project, ← same state.1.2, support_map]
      exact ⟨result, actual, rfl⟩
    have fields := RawCtxWholeOwner.rawGame_preserves_metadata (receiveNative source) decode raw state.1.1
      state.1.2 result actual
    refine ⟨.step raw enabled supported ?_, finalInvariant⟩
    simpa only [sourceNext, fields.2.1, fields.2.2.1] using nextTrace

abbrev Transcript := List (Pqxdh.Bytes × core.option.Option RawCtxWholeOwner.Decrypted)

noncomputable def loggedRaw {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl RawCtxWholeOwner.RawSpec (StateT (SourceState Metadata Auxiliary × Transcript) ProbComp) :=
  fun raw state => do
    let result ← RawCtxWholeOwner.rawGame (receiveNative source) decode raw state.1.1.1 state.1.1.2
    pure (result.1.1, (sourceNext state.1 result, state.2 ++ [(raw, result.1.1)]))

/-- The private per-call trace monitor erases to the unchanged actual source operation. -/
theorem logged_raw_erasure {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : SourceState Metadata Auxiliary × Transcript) :
    Prod.map id (fun state => state.1.1) <$> (loggedRaw source decode raw).run state =
      (RawCtxWholeOwner.ownerImpl (receiveNative source) decode raw).run state.1.1 := by
  simp [loggedRaw, RawCtxWholeOwner.ownerImpl, StateT.run, sourceNext]

/-- Erasing only private spent/transcript fields retains the entire arbitrary adaptive source computation. -/
theorem logged_run_erasure {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxWholeOwner.RawSpec Result) (state : SourceState Metadata Auxiliary × Transcript) :
    Prod.map id (fun state => state.1.1) <$> (simulateQ (loggedRaw source decode) client).run state =
      (simulateQ (RawCtxWholeOwner.ownerImpl (receiveNative source) decode) client).run state.1.1 := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (loggedRaw source decode) (RawCtxWholeOwner.ownerImpl (receiveNative source) decode)
    (fun state => state.1.1) (logged_raw_erasure source decode) client state

/-- Every supported monitored adaptive execution constructs its source trace internally from actual query/reply occurrences. -/
theorem logged_run_trace {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxWholeOwner.RawSpec Result)
    (state : SourceState Metadata Auxiliary × Transcript)
    (result : Result × (SourceState Metadata Auxiliary × Transcript))
    (actual : result ∈ support ((simulateQ (loggedRaw source decode) client).run state)) :
    ∃ transcript, result.2.2 = state.2 ++ transcript ∧
      SourceTrace source decode state.1 transcript result.2.1 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at actual
    subst result
    exact ⟨[], by simp, .nil _⟩
  | query_bind raw next ih =>
    rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, mem_support_bind_iff] at actual
    obtain ⟨step, hstep, htail⟩ := actual
    unfold loggedRaw StateT.run at hstep
    obtain ⟨received, hreceived, returned⟩ := mem_support_bind_peel _ _ hstep
    have stepEq := eq_of_mem_support_pure _ returned
    subst step
    obtain ⟨rest, history, trace⟩ := ih _ _ result htail
    refine ⟨(raw, received.1.1) :: rest, ?_, .step raw hreceived trace⟩
    simpa only [List.append_assoc, List.singleton_append] using history

/-- Each supported original adaptive source run has a matching capability trace and derived final source/history relation. -/
theorem source_supported_capability {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (sendOrigin receiveOrigin : RatchetChain) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxWholeOwner.RawSpec Result)
    (initial : RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary)
    (spent : List Nat)
    (invariant : ConsumedRefines source.crypto sendOrigin receiveOrigin initial.1.owner.kernel spent)
    (result : Result × (RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary))
    (actual : result ∈ support ((simulateQ (RawCtxWholeOwner.ownerImpl (receiveNative source) decode) client).run initial)) :
    ∃ finalSpent transcript,
      SourceTrace source decode (initial, spent) transcript (result.2, finalSpent) ∧
      CapabilityTrace (crypto source.crypto) receiveOrigin initial.1.owner.expectedSender
        initial.1.owner.associatedData decode (receiveNative source) (initial.2, spent) transcript (result.2.2, finalSpent) ∧
      ConsumedRefines source.crypto sendOrigin receiveOrigin result.2.1.owner.kernel finalSpent := by
  rw [← logged_run_erasure source decode client ((initial, spent), []), support_map, Set.mem_image] at actual
  obtain ⟨logged, supported, rfl⟩ := actual
  obtain ⟨transcript, _, trace⟩ := logged_run_trace source decode client ((initial, spent), []) logged supported
  obtain ⟨capability, finalInvariant⟩ := source_trace_capability source sendOrigin receiveOrigin decode trace invariant
  exact ⟨logged.2.1.2, transcript, trace, capability, finalInvariant⟩

/-- Trace length counts exact original raw attempts and preserves the immutable owner pin, associated data and metadata. -/
theorem SourceTrace.metadata {Metadata Auxiliary : Type}
    {source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource} {decode : RawCtxReceive.FrameDecoder}
    {initial final : SourceState Metadata Auxiliary} {transcript : Transcript}
    (trace : SourceTrace source decode initial transcript final) :
    final.1.1.rawAttempts = initial.1.1.rawAttempts + transcript.length ∧
      final.1.1.owner.expectedSender = initial.1.1.owner.expectedSender ∧
      final.1.1.owner.associatedData = initial.1.1.owner.associatedData ∧
      final.1.1.owner.metadata = initial.1.1.owner.metadata := by
  induction trace with
  | nil state => exact ⟨by simp, rfl, rfl, rfl⟩
  | @step state result rest final raw actual tail ih =>
    have fields := RawCtxWholeOwner.rawGame_preserves_metadata (receiveNative source) decode raw
      state.1.1 state.1.2 result actual
    simp only [sourceNext] at ih
    exact ⟨by simp only [List.length_cons]; omega, ih.2.1.trans fields.2.1,
      ih.2.2.1.trans fields.2.2.1, ih.2.2.2.trans fields.2.2.2⟩

/-- Only an actual successful reply can grow the private history, by at most one position per raw call. -/
theorem SourceTrace.history_length {Metadata Auxiliary : Type}
    {source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource} {decode : RawCtxReceive.FrameDecoder}
    {initial final : SourceState Metadata Auxiliary} {transcript : Transcript}
    (trace : SourceTrace source decode initial transcript final) :
    final.2.length ≤ initial.2.length + transcript.length := by
  induction trace with
  | nil state => simp
  | @step state result rest final raw actual tail ih =>
    have growth : (recordReply result.1.1 state.2).length ≤ state.2.length + 1 := by
      cases result.1.1 <;> simp [recordReply]
    simp only [sourceNext, List.length_cons] at *
    omega

/-- The original adaptive raw budget bounds the constructed transcript and non-repeating successful-position history. -/
theorem source_capability_bounded {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (sendOrigin receiveOrigin : RatchetChain) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxWholeOwner.RawSpec Result) (qRaw : Nat) (bounded : client.IsTotalQueryBound qRaw)
    (initial : RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary)
    (spent : List Nat)
    (invariant : ConsumedRefines source.crypto sendOrigin receiveOrigin initial.1.owner.kernel spent)
    (result : Result × (RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary))
    (actual : result ∈ support ((simulateQ (RawCtxWholeOwner.ownerImpl (receiveNative source) decode) client).run initial)) :
    ∃ finalSpent transcript,
      SourceTrace source decode (initial, spent) transcript (result.2, finalSpent) ∧
      CapabilityTrace (crypto source.crypto) receiveOrigin initial.1.owner.expectedSender
        initial.1.owner.associatedData decode (receiveNative source) (initial.2, spent) transcript (result.2.2, finalSpent) ∧
      ConsumedRefines source.crypto sendOrigin receiveOrigin result.2.1.owner.kernel finalSpent ∧
      finalSpent.Nodup ∧ finalSpent.length ≤ spent.length + qRaw ∧ transcript.length ≤ qRaw := by
  obtain ⟨finalSpent, transcript, trace, capability, finalInvariant⟩ :=
    source_supported_capability source sendOrigin receiveOrigin decode client initial spent invariant result actual
  have fields := RawCtxWholeOwner.scheduleGame_bounds (receiveNative source) decode client qRaw bounded initial result actual
  exact ⟨finalSpent, transcript, trace, capability, finalInvariant, finalInvariant.spent_nodup,
    by have counter := trace.metadata.1; have growth := trace.history_length; dsimp only at counter growth; omega,
    by have counter := trace.metadata.1; dsimp only at counter; omega⟩

open BeaconcryptCore.Refinement.PqxdhConcreteSession

/-- Either actual source initializer supplies the empty-history relation for the bounded adaptive trace embedding. -/
theorem initialized_capability {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (root : Std.Array Std.U8 32#usize) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxWholeOwner.RawSpec Result) (qRaw : Nat) (bounded : client.IsTotalQueryBound qRaw)
    (initial : RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary)
    (initialized : initializeBeacon root (RawCtxSourceHkdf.initialResponse source.crypto) = ok initial.1.owner.kernel ∨
      initializeServer root (RawCtxSourceHkdf.initialResponse source.crypto) = ok initial.1.owner.kernel)
    (result : Result × (RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary))
    (actual : result ∈ support ((simulateQ (RawCtxWholeOwner.ownerImpl (receiveNative source) decode) client).run initial)) :
    ∃ finalSpent transcript,
      SourceTrace source decode (initial, []) transcript (result.2, finalSpent) ∧
      CapabilityTrace (crypto source.crypto) initial.1.owner.kernel.refined.receive_chain initial.1.owner.expectedSender
        initial.1.owner.associatedData decode (receiveNative source) (initial.2, []) transcript (result.2.2, finalSpent) ∧
      ConsumedRefines source.crypto initial.1.owner.kernel.refined.send_chain
        initial.1.owner.kernel.refined.receive_chain result.2.1.owner.kernel finalSpent ∧
      finalSpent.Nodup ∧ finalSpent.length ≤ qRaw ∧ transcript.length ≤ qRaw := by
  simpa only [List.length_nil, Nat.zero_add] using source_capability_bounded source _ _ decode client qRaw bounded
    initial [] (initialized_spent source.crypto root initial.1.owner.kernel initialized) result actual

/-- Private trace monitoring preserves every selective underlying uniform-query bound of the original source program. -/
theorem logged_query_bounds {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxWholeOwner.RawSpec Result)
    (state : SourceState Metadata Auxiliary × Transcript)
    (predicate : unifSpec.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    ((simulateQ (loggedRaw source decode) client).run state).IsQueryBoundP predicate budget ↔
      ((simulateQ (RawCtxWholeOwner.ownerImpl (receiveNative source) decode) client).run state.1.1).IsQueryBoundP predicate budget := by
  rw [← logged_run_erasure source decode client state, isQueryBoundP_map_iff]

end BeaconcryptCore.Computational.RawCtxPositionCapability

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionCapability.bare_prefix_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionCapability.bare_prefix_complete

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionCapability.opening_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionCapability.opening_reply

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionCapability.arguments_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionCapability.arguments_exact

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionCapability.owner_reply_choice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionCapability.owner_reply_choice

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionCapability.raw_prepared_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionCapability.raw_prepared_reply

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionCapability.positionReceive_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionCapability.positionReceive_false

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionCapability.raw_reply_choice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionCapability.raw_reply_choice

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionCapability.source_gated_reply_choice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionCapability.source_gated_reply_choice

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionCapability.source_capability_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionCapability.source_capability_step

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionCapability.source_trace_capability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionCapability.source_trace_capability

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionCapability.logged_raw_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionCapability.logged_raw_erasure

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionCapability.logged_run_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionCapability.logged_run_erasure

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionCapability.logged_run_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionCapability.logged_run_trace

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionCapability.source_supported_capability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionCapability.source_supported_capability

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionCapability.SourceTrace.metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionCapability.SourceTrace.metadata

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionCapability.SourceTrace.history_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionCapability.SourceTrace.history_length

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionCapability.source_capability_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionCapability.source_capability_bounded

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionCapability.initialized_capability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionCapability.initialized_capability

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionCapability.logged_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionCapability.logged_query_bounds
