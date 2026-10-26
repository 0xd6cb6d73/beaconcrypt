import BeaconcryptCore.Computational.RawCtxReceiveConsumption

/-!
Every reached source opening, before its optional reply is known, uses the material at the original directional origin and decoded sequence minus one. The exact source zero, cached, replay, future and capacity branches give a finite KDF prefix ending in rejection or that selected opening. All skipped/current requests use the same fixed functional KDF response; no independent key table, byte injectivity, successful plaintext or decryption-correctness premise is introduced.

Scoped handler congruence preserves the complete interpreted computation, actual optional reply, source finish and whole primitive state. Log erasure removes only private proof history. The existing owner adapter retains missing-material rejection and constructs the actual decrypted metadata, while raw lifting keeps the original bytes, decoder result, sender/shape checks and immutable associated data. The concrete source handler derives its KDF law from the existing functional implementation. Its position-based callback wrapper reconstructs the same material from the original chain and actual sequence before invoking that identical opening, so the final source equality needs no assumed opening equality or successful-result premise. Failed hashes/openings retain their exact cache effects.

The position wrapper is an analysis interface. Recomputing a material from its origin can add pure HKDF/chain/list work proportional to the position; exact oracle-program and selective uniform-query equality does not make that local computation free or prove native timing, traversal, allocation, constant-time behavior or a tight runtime bound. Original private KDF callback counts and public source results are unchanged. The original chain and any proof history remain private and are not added to adversary, reveal, snapshot or persistence interfaces. The current source supports finite native indices; this normalization does not authorize outputs beyond counter exhaustion.

These statements require the ordinary source kernel/material relation for the current owner and fixed functional KDF. Existing initialization and source-position invariants can supply it along uninterrupted execution; a fresh-output hybrid, restored snapshot or copied owner must establish its own relation. Distinct origins or positions may map to equal keys/nonces. This is not a persistent ProVerif trace inclusion, cryptographic freshness/collision reduction, arbitrary adaptive ownership/reveal composition, or global computational-symbolic theorem. Native primitive, codec, compiler, library and storage contracts remain separate. Actual optional API plaintext is retained, and its network disclosure remains an explicit outer policy.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxPositionedOpening
open RawCtxMaterialPositions RawCtxOwnerProvenance

/-- Every actual fixed-response prefix preserves the original decoded target and immutable context. -/
theorem prefix_scope {Context : Type} (execute : KdfInterpreter)
    (target : Std.U64) (context : Context)
    {effect terminal : ReceiveEffect Context} {requests : List SymmetricRatchetKdfRequest}
    (trace : Prefix execute effect terminal requests) (hscope : Scope target context effect) :
    Scope target context terminal := by
  induction trace with
  | refl => exact hscope
  | step pending next final requests resumed tail ih =>
    apply ih
    have exactNext : RawCtxOwnerOracle.resume pending (execute pending.request) = next :=
      RustM.ok.inj ((RawCtxOwnerOracle.resume_exact pending (execute pending.request)).symm.trans resumed)
    simpa only [exactNext, hscope.1, hscope.2] using oracle_resume_scope pending (execute pending.request)

/-- All real source admission branches end in rejection or the exact origin-position material before any opening reply. -/
theorem receive_prefix {AD PT CT Context : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (origin : RatchetChain) (send : Ratchet.SendState RatchetChain)
    (receive : Ratchet.RecvState RatchetChain RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64)
    (refines : KernelRefines (withInterpreter cr execute) origin send receive entry) :
    ∃ terminal requests,
      Prefix execute (RawCtxOwnerOracle.begin entry target context) terminal requests ∧
      (terminal = .ReceiveRejected entry context ∨ ∃ opened,
        terminal = .ReceiveOpenRequested opened ∧
        opened.material = ok (.Some (Ratchet.msgKeyAt (withInterpreter cr execute) origin (target.val - 1)))) := by
  have rejected (actual : begin_receive entry target context = ok (.ReceiveRejected entry context)) :
      ∃ terminal requests,
        Prefix execute (RawCtxOwnerOracle.begin entry target context) terminal requests ∧
        (terminal = .ReceiveRejected entry context ∨ ∃ opened,
          terminal = .ReceiveOpenRequested opened ∧
          opened.material = ok (.Some (Ratchet.msgKeyAt (withInterpreter cr execute) origin (target.val - 1)))) := by
    have began : RawCtxOwnerOracle.begin entry target context = .ReceiveRejected entry context :=
      RustM.ok.inj ((RawCtxOwnerOracle.begin_exact entry target context).symm.trans actual)
    exact ⟨_, [], began ▸ Prefix.refl _, Or.inl rfl⟩
  by_cases zero : target = 0#u64
  · exact rejected (zero ▸ refines.begin_receive_zero
      (withInterpreter cr execute) origin send receive entry context)
  have positive : 0 < target.val := by scalar_tac
  cases stored : List.lookup (target.val - 1) receive.skipped with
  | some material =>
    obtain ⟨opened, started, ready⟩ := begin_receive_cached_refines (withInterpreter cr execute)
      origin send receive entry context target (target.val - 1) material refines (by omega) stored
    have began : RawCtxOwnerOracle.begin entry target context = .ReceiveOpenRequested opened :=
      RustM.ok.inj ((RawCtxOwnerOracle.begin_exact entry target context).symm.trans started)
    refine ⟨_, [], began ▸ Prefix.refl _, Or.inr ⟨opened, rfl, ?_⟩⟩
    have materialAt : material = Ratchet.msgKeyAt (withInterpreter cr execute) origin (target.val - 1) :=
      refines.receiveControl.keys _ (control.mem_of_lookup_eq_some stored)
    simpa only [materialAt] using
      ready.material_exact (withInterpreter cr execute) origin send receive (target.val - 1) material opened
  | none =>
    by_cases past : target.val ≤ receive.n
    · exact rejected (refines.begin_receive_replay (withInterpreter cr execute)
        origin send receive entry target context past positive stored)
    by_cases capacity : entry.refined.control.receive_cache.len.val + (target.val - receive.n - 1) ≤ 50
    · obtain ⟨pending, started, refined⟩ := refines.begin_receive_future
        (withInterpreter cr execute) origin send receive entry context target (by omega) capacity
      obtain ⟨opened, trace, ready⟩ := future_positioned_prefix cr execute origin send receive entry context target
        (target.val - receive.n) 0 pending (by simpa only [Nat.sub_zero] using refined.remaining) refined
      have began : RawCtxOwnerOracle.begin entry target context = .ReceiveKdfRequested pending :=
        RustM.ok.inj ((RawCtxOwnerOracle.begin_exact entry target context).symm.trans started)
      refine ⟨_, _, began ▸ trace, Or.inr ⟨opened, rfl, ?_⟩⟩
      simpa only [refines.receiveControl.chain, Ratchet.msgKeyAt_chainAt,
        show receive.n + (target.val - receive.n - 1) = target.val - 1 by omega] using
        ready.material_exact (withInterpreter cr execute) origin send receive entry context target opened
    · exact rejected (refines.begin_receive_capacity_rejected (withInterpreter cr execute)
        origin send receive entry target context (by omega) (by omega))

/-- Opening implementations need agree only on the actual selected material, target and context; complete states and failure effects remain. -/
theorem receive_positioned_congr {AD PT CT Context Plaintext PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (origin : RatchetChain) (send : Ratchet.SendState RatchetChain)
    (receive : Ratchet.RecvState RatchetChain RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64)
    (refines : KernelRefines (withInterpreter cr execute) origin send receive entry)
    (left right : ReceiveOpen Context → StateT PrimitiveState (OracleComp base) (core.option.Option Plaintext))
    (equal : ∀ pending,
      pending.material = ok (.Some (Ratchet.msgKeyAt (withInterpreter cr execute) origin (target.val - 1))) →
      pending.sequence = ok target → pending.context = context → left pending = right pending) :
    simulateQ (receiveImpl execute left) (RawCtxOwnerOracle.receive entry target context) =
      simulateQ (receiveImpl execute right) (RawCtxOwnerOracle.receive entry target context) := by
  obtain ⟨terminal, requests, trace, selected⟩ := receive_prefix cr execute origin send receive entry context target refines
  have hscope := prefix_scope execute target context trace (oracle_begin_scope entry target context)
  funext state
  change (simulateQ (receiveImpl execute left) (RawCtxOwnerOracle.receive entry target context)).run (state.1, state.2) =
    (simulateQ (receiveImpl execute right) (RawCtxOwnerOracle.receive entry target context)).run (state.1, state.2)
  rw [RawCtxOwnerOracle.receive, prefix_complete execute left trace state.1 state.2,
    prefix_complete execute right trace state.1 state.2]
  rcases selected with rfl | ⟨opened, rfl, material⟩
  · simp [RawCtxOwnerOracle.program]
  · rw [opened_complete, opened_complete, equal opened material hscope.1 hscope.2]

/-- Erasing only the private request log preserves the full position-scoped receive equality. -/
theorem bare_receive_positioned_congr {AD PT CT Context Plaintext PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (origin : RatchetChain) (send : Ratchet.SendState RatchetChain)
    (receive : Ratchet.RecvState RatchetChain RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64)
    (refines : KernelRefines (withInterpreter cr execute) origin send receive entry)
    (left right : ReceiveOpen Context → StateT PrimitiveState (OracleComp base) (core.option.Option Plaintext))
    (equal : ∀ pending,
      pending.material = ok (.Some (Ratchet.msgKeyAt (withInterpreter cr execute) origin (target.val - 1))) →
      pending.sequence = ok target → pending.context = context → left pending = right pending) :
    simulateQ (bareReceiveImpl execute left) (RawCtxOwnerOracle.receive entry target context) =
      simulateQ (bareReceiveImpl execute right) (RawCtxOwnerOracle.receive entry target context) := by
  funext state
  have same := congrArg (fun computation => Prod.map id Prod.fst <$> computation (state, ([] : KdfLog)))
    (receive_positioned_congr cr execute origin send receive entry context target refines left right equal)
  exact (receive_complete_erase execute left _ (state, [])).symm.trans
    (same.trans (receive_complete_erase execute right _ (state, [])))

/-- The actual present-material getter supplies that exact position and the unchanged original sequence/context. -/
theorem arguments_positioned (pending : ReceiveOpen RawCtxWholeOwner.OpenContext)
    (input : RawCtxWholeOwner.OpenInput) (material : RatchetMaterial)
    (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (arguments : RawCtxWholeOwner.arguments pending = some input)
    (selected : pending.material = ok (.Some material))
    (sequence : pending.sequence = ok target) (sameContext : pending.context = context) :
    input.material = material ∧ input.sequence = target ∧ input.context = context := by
  obtain ⟨actualMaterial, actualSequence, actualContext⟩ :=
    RawCtxWholeOwner.arguments_some pending input arguments
  exact ⟨Option.some.inj (RustM.ok.inj (actualMaterial.symm.trans selected)),
    RustM.ok.inj (actualSequence.symm.trans sequence), actualContext.trans sameContext⟩

/-- The owner adapter preserves missing-material rejection and real optional reply construction under selected-input replacement. -/
theorem adapter_positioned_congr {PrimitiveState ι : Type} {base : OracleSpec ι}
    (left right : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (material : RatchetMaterial) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (equal : ∀ input, input.material = material → input.sequence = target → input.context = context →
      left (.inr input) = right (.inr input))
    (pending : ReceiveOpen RawCtxWholeOwner.OpenContext)
    (selected : pending.material = ok (.Some material))
    (sequence : pending.sequence = ok target) (sameContext : pending.context = context) :
    (left ∘ₛ RawCtxWholeOwner.adapter) (.inr pending) =
      (right ∘ₛ RawCtxWholeOwner.adapter) (.inr pending) := by
  simp only [QueryImpl.compose, RawCtxWholeOwner.adapter]
  cases arguments : RawCtxWholeOwner.arguments pending
  · simp only [simulateQ_pure]
  · rename_i input
    obtain ⟨actualMaterial, actualSequence, actualContext⟩ :=
      arguments_positioned pending input material target context arguments selected sequence sameContext
    simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
      equal input actualMaterial actualSequence actualContext]

/-- A fixed functional KDF handler has the exact existing bare receive representation; all opening effects stay untouched. -/
theorem primitive_bare {PrimitiveState ι : Type} {base : OracleSpec ι}
    (execute : KdfInterpreter)
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (kdf : ∀ request, impl (.inl request) = pure (execute request)) :
    impl ∘ₛ RawCtxWholeOwner.adapter =
      bareReceiveImpl execute (fun pending => (impl ∘ₛ RawCtxWholeOwner.adapter) (.inr pending)) := by
  funext query
  cases query with
  | inr pending => rfl
  | inl request =>
    simpa [QueryImpl.compose, RawCtxWholeOwner.adapter, OracleSpec.query, bareReceiveImpl] using kdf request

/-- Selected material equality lifts through the actual source owner receive and finish before either optional result is observed. -/
theorem owner_receive_positioned_congr {AD PT CT PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (origin : RatchetChain) (send : Ratchet.SendState RatchetChain)
    (receive : Ratchet.RecvState RatchetChain RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : RawCtxWholeOwner.OpenContext) (target : Std.U64)
    (refines : KernelRefines (withInterpreter cr execute) origin send receive entry)
    (left right : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (leftKdf : ∀ request, left (.inl request) = pure (execute request))
    (rightKdf : ∀ request, right (.inl request) = pure (execute request))
    (equal : ∀ input,
      input.material = Ratchet.msgKeyAt (withInterpreter cr execute) origin (target.val - 1) →
      input.sequence = target → input.context = context → left (.inr input) = right (.inr input)) :
    simulateQ left (simulateQ RawCtxWholeOwner.adapter (RawCtxOwnerOracle.receive entry target context)) =
      simulateQ right (simulateQ RawCtxWholeOwner.adapter (RawCtxOwnerOracle.receive entry target context)) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose,
    primitive_bare execute left leftKdf, primitive_bare execute right rightKdf]
  exact bare_receive_positioned_congr cr execute origin send receive entry context target refines _ _
    (adapter_positioned_congr left right _ target context equal)

/-- Raw replacement retains the original validated frame and source owner while covering every early rejection. -/
theorem raw_positioned_congr {AD PT CT Metadata PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (origin : RatchetChain) (send : Ratchet.SendState RatchetChain)
    (receive : Ratchet.RecvState RatchetChain RatchetMaterial)
    (state : RawCtxWholeOwner.OwnerState Metadata)
    (refines : KernelRefines (withInterpreter cr execute) origin send receive state.owner.kernel)
    (left right : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (leftKdf : ∀ request, left (.inl request) = pure (execute request))
    (rightKdf : ∀ request, right (.inl request) = pure (execute request))
    (equal : ∀ frame input,
      raw.isEmpty = false → decode raw = some frame →
      RawCtxReceive.ValidFrame state.owner.expectedSender state.owner.associatedData frame →
      input.material = Ratchet.msgKeyAt (withInterpreter cr execute) origin (frame.sequence.val - 1) →
      input.sequence = frame.sequence → input.context = ⟨raw, frame, state.owner.associatedData⟩ →
      left (.inr input) = right (.inr input)) :
    simulateQ left ((RawCtxWholeOwner.rawReceive decode raw).run state) =
      simulateQ right ((RawCtxWholeOwner.rawReceive decode raw).run state) := by
  unfold RawCtxWholeOwner.rawReceive StateT.run
  split
  · simp only [simulateQ_pure]
  · rename_i hraw
    cases hdecode : decode raw
    · simp only [simulateQ_pure]
    · rename_i frame
      dsimp only
      split
      · rename_i hvalid
        simp only [bind_pure_comp, simulateQ_map]
        congr 1
        exact owner_receive_positioned_congr cr execute origin send receive _ _ _ refines left right leftKdf rightKdf
          (fun input => equal frame input (by simpa using hraw) hdecode hvalid)
      · simp only [simulateQ_pure]

/-- The complete owner and primitive poststate, including failed opening effects, are equal under scoped replacement. -/
theorem rawGame_positioned_congr {AD PT CT Metadata PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (origin : RatchetChain) (send : Ratchet.SendState RatchetChain)
    (receive : Ratchet.RecvState RatchetChain RatchetMaterial)
    (state : RawCtxWholeOwner.OwnerState Metadata) (primitive : PrimitiveState)
    (refines : KernelRefines (withInterpreter cr execute) origin send receive state.owner.kernel)
    (left right : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (leftKdf : ∀ request, left (.inl request) = pure (execute request))
    (rightKdf : ∀ request, right (.inl request) = pure (execute request))
    (equal : ∀ frame input,
      raw.isEmpty = false → decode raw = some frame →
      RawCtxReceive.ValidFrame state.owner.expectedSender state.owner.associatedData frame →
      input.material = Ratchet.msgKeyAt (withInterpreter cr execute) origin (frame.sequence.val - 1) →
      input.sequence = frame.sequence → input.context = ⟨raw, frame, state.owner.associatedData⟩ →
      left (.inr input) = right (.inr input)) :
    RawCtxWholeOwner.rawGame left decode raw state primitive =
      RawCtxWholeOwner.rawGame right decode raw state primitive := by
  exact congrArg (fun computation : StateT PrimitiveState (OracleComp base)
      (Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Metadata) => computation.run primitive)
    (raw_positioned_congr cr execute origin send receive state refines left right decode raw leftKdf rightKdf equal)

/-- The existing concrete functional source derives the fixed-response KDF equation without a new callback premise. -/
theorem source_kdf {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (request : SymmetricRatchetKdfRequest) :
    RawCtxReceiveConsumption.receiveNative (Auxiliary := Auxiliary) source (.inl request) =
      pure (RawCtxSourceHkdf.response source.crypto request) := by
  simp [RawCtxReceiveConsumption.receiveNative, QueryImpl.compose,
    RawCtxSourceOpen.nativeAdapter, OracleSpec.query]
  rfl

open BeaconcryptCore.Refinement.RepresentationBridge RawCtxReceiveConsumption

/-- Actual source opening can be replaced using only proved equality at its source-selected position and original raw context. -/
theorem source_raw_positioned_congr {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (origin : RatchetChain) (send : Ratchet.SendState RatchetChain)
    (receive : Ratchet.RecvState RatchetChain RatchetMaterial)
    (state : RawCtxWholeOwner.OwnerState Metadata)
    (refines : KernelRefines (crypto source.crypto) origin send receive state.owner.kernel)
    (right : QueryImpl RawCtxWholeOwner.PrimitiveSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary)
    (rightKdf : ∀ request, right (.inl request) = pure (RawCtxSourceHkdf.response source.crypto request))
    (equal : ∀ frame input,
      raw.isEmpty = false → decode raw = some frame →
      RawCtxReceive.ValidFrame state.owner.expectedSender state.owner.associatedData frame →
      input.material = Ratchet.msgKeyAt (crypto source.crypto) origin (frame.sequence.val - 1) →
      input.sequence = frame.sequence → input.context = ⟨raw, frame, state.owner.associatedData⟩ →
      RawCtxReceiveConsumption.receiveNative source (.inr input) = right (.inr input)) :
    RawCtxWholeOwner.rawGame (RawCtxReceiveConsumption.receiveNative source) decode raw state primitive =
      RawCtxWholeOwner.rawGame right decode raw state primitive := by
  exact rawGame_positioned_congr (crypto source.crypto) (RawCtxSourceHkdf.response source.crypto)
    origin send receive state primitive refines _ right decode raw (source_kdf source) rightKdf equal

noncomputable def atPosition (c : Pqxdh.Crypto) (origin : RatchetChain)
    (input : RawCtxWholeOwner.OpenInput) : RawCtxWholeOwner.OpenInput :=
  { input with material := Ratchet.msgKeyAt (crypto c) origin (input.sequence.val - 1) }

/-- Reconstructing the selected source material changes none of the actual opening input fields. -/
theorem atPosition_eq (c : Pqxdh.Crypto) (origin : RatchetChain)
    (input : RawCtxWholeOwner.OpenInput) (sequence : Std.U64)
    (selected : input.material = Ratchet.msgKeyAt (crypto c) origin (sequence.val - 1))
    (sameSequence : input.sequence = sequence) : atPosition c origin input = input := by
  simp only [atPosition, sameSequence, ← selected]
  rw [← sameSequence]

noncomputable def positionedNative {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (origin : RatchetChain) :
    QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl request => receiveNative source (.inl request)
  | .inr input => receiveNative source (.inr (atPosition source.crypto origin input))

/-- The concrete position-routed wrapper equals every original raw source computation, including failed callbacks. -/
theorem source_raw_positioned {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (origin : RatchetChain) (send : Ratchet.SendState RatchetChain)
    (receive : Ratchet.RecvState RatchetChain RatchetMaterial)
    (state : RawCtxWholeOwner.OwnerState Metadata)
    (refines : KernelRefines (crypto source.crypto) origin send receive state.owner.kernel)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) :
    RawCtxWholeOwner.rawGame (receiveNative source) decode raw state primitive =
      RawCtxWholeOwner.rawGame (positionedNative source origin) decode raw state primitive := by
  apply source_raw_positioned_congr source origin send receive state refines _ decode raw primitive
  · exact source_kdf source
  · intro frame input _ _ _ selected sameSequence _
    simp only [positionedNative]
    rw [atPosition_eq source.crypto origin input frame.sequence selected sameSequence]

/-- The reconstructed material projects to the same byte-level ratchet position without injectivity assumptions. -/
theorem atPosition_bytes (c : Pqxdh.Crypto) (origin : RatchetChain) (input : RawCtxWholeOwner.OpenInput) :
    absMaterial (atPosition c origin input).material =
      Ratchet.msgKeyAt (Pqxdh.ratchetCrypto c) (absChain origin) (input.sequence.val - 1) :=
  (source_position_bytes c origin (input.sequence.val - 1)).2

/-- Every selective underlying uniform-query bound is exactly unchanged by the proved position routing. -/
theorem source_positioned_query_bounds {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (origin : RatchetChain) (send : Ratchet.SendState RatchetChain)
    (receive : Ratchet.RecvState RatchetChain RatchetMaterial)
    (state : RawCtxWholeOwner.OwnerState Metadata)
    (refines : KernelRefines (crypto source.crypto) origin send receive state.owner.kernel)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary)
    (predicate : unifSpec.Domain → Prop) [DecidablePred predicate] (bound : Nat) :
    (RawCtxWholeOwner.rawGame (positionedNative source origin) decode raw state primitive).IsQueryBoundP predicate bound ↔
      (RawCtxWholeOwner.rawGame (receiveNative source) decode raw state primitive).IsQueryBoundP predicate bound := by
  rw [source_raw_positioned source origin send receive state refines decode raw primitive]

end BeaconcryptCore.Computational.RawCtxPositionedOpening

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionedOpening.prefix_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOpening.prefix_scope

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionedOpening.receive_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOpening.receive_prefix

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionedOpening.receive_positioned_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOpening.receive_positioned_congr

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionedOpening.bare_receive_positioned_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOpening.bare_receive_positioned_congr

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionedOpening.arguments_positioned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOpening.arguments_positioned

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionedOpening.adapter_positioned_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOpening.adapter_positioned_congr

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionedOpening.primitive_bare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOpening.primitive_bare

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionedOpening.owner_receive_positioned_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOpening.owner_receive_positioned_congr

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionedOpening.raw_positioned_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOpening.raw_positioned_congr

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionedOpening.rawGame_positioned_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOpening.rawGame_positioned_congr

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionedOpening.source_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOpening.source_kdf

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionedOpening.source_raw_positioned_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOpening.source_raw_positioned_congr

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionedOpening.atPosition_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOpening.atPosition_eq

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionedOpening.source_raw_positioned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOpening.source_raw_positioned

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionedOpening.atPosition_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOpening.atPosition_bytes

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionedOpening.source_positioned_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOpening.source_positioned_query_bounds
