import BeaconcryptCore.Computational.RawCtxInterpretedArguments
import BeaconcryptCore.Computational.RawCtxMixedOwner

/-!
One generic owner retains the actual source chains, control, material slots, sender pin, associated data, metadata and raw-attempt counter. Only material payloads are parameterized. The outer raw receiver preserves every original empty/decoder/pin/shape branch, optional API result and whole-kernel publication. The sender preserves the outer empty-input gate, target/sender distinction and advancement after active failed sealing. These comparisons use the checked source getter/primitive adapters and do not branch on material-label equality.

The mixed label interpreter has one KDF branch and selected sealing/opening calls. Its actual counterpart is the existing RawCtxMixedOwner owner and source interpreter over the same complete native primitive interface. Explicit decoded-KDF and selected primitive equations imply exact arbitrary adaptive send/raw computation equality, then complete flattened owner/primitive-state equality and every selective underlying oracle-query budget. No primitive poststate, API reply or terminal client result is discarded.

The starting native owner is explicitly the interpretation of the supplied label state. The theorem neither constructs that state from arbitrary native bytes nor infers an inverse or injective material map. A concrete label/challenger backend must realize the low-level equations, including actual optional primitive effects. No fixed functional KDF, independent key table, honest-state, nonce freshness or cryptographic security premise is introduced. Decoder, source control, copying, interpretation and primitive work remain real local computation; query equality does not prove runtime/library/allocation/timing correspondence. The scope is one represented owner with this send/raw API. Public services, reveals, multiowner/lifecycle and restore transitions, actual label generation, evolving-key distributions and global security require further composition. Labels, source contexts and complete interpreter state remain private; actual optional API plaintext retains its original outer visibility policy.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxInterpretedOwner
open RawCtxMaterialInterpretation RawCtxInterpretedArguments

structure State (Material Metadata : Type) where
  kernel : RefinedRatchet RatchetChain RatchetChain Material
  expectedSender : Std.U64
  associatedData : Pqxdh.Bytes
  metadata : Metadata
  rawAttempts : Nat

def nativeState {Material Metadata : Type} (interpret : Material → RatchetMaterial)
    (state : State Material Metadata) : RawCtxWholeOwner.OwnerState Metadata :=
  ⟨⟨⟨mapRefined interpret state.kernel⟩, state.expectedSender, state.associatedData, state.metadata⟩,
    state.rawAttempts⟩

def publish {Material Metadata : Type} (state : State Material Metadata)
    (result : RefinedRatchet RatchetChain RatchetChain Material × core.option.Option RawCtxWholeOwner.Decrypted) :
    core.option.Option RawCtxWholeOwner.Decrypted × State Material Metadata :=
  (result.2, {state with kernel := result.1, rawAttempts := state.rawAttempts + 1})

noncomputable def rawReceive {Material Metadata : Type} (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) : StateT (State Material Metadata) (OracleComp (OpenSpec Material))
      (core.option.Option RawCtxWholeOwner.Decrypted) := fun state =>
  if raw.isEmpty then pure (publish state (state.kernel, .None)) else
  match decode raw with
  | none => pure (publish state (state.kernel, .None))
  | some frame =>
    if RawCtxReceive.ValidFrame state.expectedSender state.associatedData frame then do
      let result ← simulateQ openAdapter (RawCtxInterpretedReceive.receive state.kernel frame.sequence
        ⟨raw, frame, state.associatedData⟩)
      pure (publish state result)
    else pure (publish state (state.kernel, .None))

/-- Every actual raw validation and publication branch preserves material interpretation. -/
theorem rawReceive_interpreted {Material Metadata : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Material → RatchetMaterial)
    (native : QueryImpl RawCtxWholeOwner.PrimitiveSpec m) (labels : QueryImpl (OpenSpec Material) m)
    (kdf : ∀ request, RawCtxInterpretedReceive.decodeResponse <$> native (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (opening : ∀ input, native (.inr (toOpenInput (mapInput interpret input))) = labels (.inr input))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (state : State Material Metadata) :
    simulateQ native ((RawCtxWholeOwner.rawReceive decode raw).run (nativeState interpret state)) =
      Prod.map id (nativeState interpret) <$> simulateQ labels ((rawReceive decode raw).run state) := by
  simp only [RawCtxWholeOwner.rawReceive, rawReceive, nativeState, StateT.run]
  by_cases empty : raw.isEmpty = true
  · simp only [empty, if_true, simulateQ_pure, map_pure]
    rfl
  · simp only [empty, Bool.false_eq_true, if_false]
    cases decoded : decode raw with
    | none =>
      simp only [simulateQ_pure, map_pure]
      rfl
    | some frame =>
      by_cases valid : RawCtxReceive.ValidFrame state.expectedSender state.associatedData frame
      · simp only [valid, if_true, bind_pure_comp, simulateQ_map]
        rw [RawCtxInterpretedArguments.receive_interpreted interpret native labels kdf opening]
        simp only [Functor.map_map]
        rfl
      · simp only [valid, if_false, simulateQ_pure, map_pure]
        rfl

noncomputable def sendOwner {Material Metadata : Type} (senderId : Std.U64) (plaintext : Pqxdh.Bytes) :
    StateT (State Material Metadata) (OracleComp (SealSpec Material)) (Option RawCtxSourceSend.Encrypted) :=
  fun state => if plaintext.isEmpty then pure (none, state) else do
    let context : RawCtxSourceSend.SealContext :=
      ⟨plaintext, state.expectedSender, senderId, state.associatedData⟩
    let result ← simulateQ sealAdapter (RawCtxInterpretedSend.send state.kernel context)
    pure (result.2, {state with kernel := result.1})

/-- The whole source sender retains empty rejection and actual advanced-kernel publication. -/
theorem sendOwner_interpreted {Material Metadata : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Material → RatchetMaterial)
    (native : QueryImpl RawCtxSourceSend.PrimitiveSpec m) (labels : QueryImpl (SealSpec Material) m)
    (kdf : ∀ request, RawCtxInterpretedReceive.decodeResponse <$> native (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (sealing : ∀ input, native (.inr (toSealInput (mapInput interpret input))) = labels (.inr input))
    (senderId : Std.U64) (plaintext : Pqxdh.Bytes) (state : State Material Metadata) :
    simulateQ native ((RawCtxSourceSend.sendOwner senderId plaintext).run (nativeState interpret state)) =
      Prod.map id (nativeState interpret) <$> simulateQ labels ((sendOwner senderId plaintext).run state) := by
  simp only [RawCtxSourceSend.sendOwner, sendOwner, nativeState, StateT.run]
  by_cases empty : plaintext.isEmpty = true
  · simp only [empty, if_true, simulateQ_pure, map_pure]
    rfl
  · simp only [empty, Bool.false_eq_true, if_false, bind_pure_comp, simulateQ_map]
    rw [RawCtxInterpretedArguments.send_interpreted interpret native labels kdf sealing]
    simp only [Functor.map_map]
    rfl

abbrev PrimitiveSpec (Material : Type) :=
  (SymmetricRatchetKdfRequest →ₒ (RatchetChain × Material)) +
    ((Input Material RawCtxSourceSend.SealContext →ₒ Option Pqxdh.Bytes) +
      (Input Material RawCtxWholeOwner.OpenContext →ₒ core.option.Option Pqxdh.Bytes))

def openLift {Material : Type} : QueryImpl (OpenSpec Material) (OracleComp (PrimitiveSpec Material))
  | .inl request => (PrimitiveSpec Material).query (.inl request)
  | .inr input => (PrimitiveSpec Material).query (.inr (.inr input))

def sealLift {Material : Type} : QueryImpl (SealSpec Material) (OracleComp (PrimitiveSpec Material))
  | .inl request => (PrimitiveSpec Material).query (.inl request)
  | .inr input => (PrimitiveSpec Material).query (.inr (.inl input))

noncomputable def ownerImpl {Material Metadata : Type} (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl RawCtxMixedOwner.SourceSpec (StateT (State Material Metadata) (OracleComp (PrimitiveSpec Material))) :=
  fun query state => match query with
  | .inl plaintext => simulateQ sealLift ((sendOwner senderId plaintext).run state)
  | .inr raw => simulateQ openLift ((rawReceive decode raw).run state)

/-- One mixed step uses the original native adapters and one common label primitive interface. -/
theorem owner_interpreted {Material Metadata : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Material → RatchetMaterial)
    (native : QueryImpl RawCtxMixedOwner.NativeSpec m) (labels : QueryImpl (PrimitiveSpec Material) m)
    (kdf : ∀ request, RawCtxInterpretedReceive.decodeResponse <$> native (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (sealing : ∀ input, simulateQ native (RawCtxMixedOwner.sendAdapter (.inr
      (toSealInput (mapInput interpret input)))) = labels (.inr (.inl input)))
    (opening : ∀ input, simulateQ native (RawCtxMixedOwner.receiveAdapter (.inr
      (toOpenInput (mapInput interpret input)))) = labels (.inr (.inr input)))
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : State Material Metadata) :
    simulateQ native ((RawCtxMixedOwner.ownerImpl senderId decode query).run (nativeState interpret state)) =
      Prod.map id (nativeState interpret) <$> simulateQ labels ((ownerImpl senderId decode query).run state) := by
  cases query with
  | inl plaintext =>
    simp only [RawCtxMixedOwner.ownerImpl, ownerImpl, StateT.run, ← QueryImpl.simulateQ_compose]
    apply sendOwner_interpreted
    · intro request
      simpa [QueryImpl.compose, RawCtxMixedOwner.sendAdapter, RawCtxSourceSeal.nativeAdapter,
        RawCtxMixedOwner.sendLift, sealLift, OracleSpec.query] using kdf request
    · intro input
      simpa [QueryImpl.compose, sealLift, OracleSpec.query] using sealing input
  | inr raw =>
    simp only [RawCtxMixedOwner.ownerImpl, ownerImpl, StateT.run, ← QueryImpl.simulateQ_compose]
    apply rawReceive_interpreted
    · intro request
      simpa [QueryImpl.compose, RawCtxMixedOwner.receiveAdapter, RawCtxSourceOpen.nativeAdapter,
        RawCtxMixedOwner.receiveLift, openLift, OracleSpec.query] using kdf request
    · intro input
      simpa [QueryImpl.compose, openLift, OracleSpec.query] using opening input

/-- Arbitrary adaptive send/raw continuations retain the complete interpreted owner and result. -/
theorem schedule_interpreted {Material Metadata Result : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Material → RatchetMaterial)
    (native : QueryImpl RawCtxMixedOwner.NativeSpec m) (labels : QueryImpl (PrimitiveSpec Material) m)
    (kdf : ∀ request, RawCtxInterpretedReceive.decodeResponse <$> native (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (sealing : ∀ input, simulateQ native (RawCtxMixedOwner.sendAdapter (.inr
      (toSealInput (mapInput interpret input)))) = labels (.inr (.inl input)))
    (opening : ∀ input, simulateQ native (RawCtxMixedOwner.receiveAdapter (.inr
      (toOpenInput (mapInput interpret input)))) = labels (.inr (.inr input)))
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result) (state : State Material Metadata) :
    simulateQ native ((simulateQ (RawCtxMixedOwner.ownerImpl senderId decode) client).run (nativeState interpret state)) =
      Prod.map id (nativeState interpret) <$> simulateQ labels ((simulateQ (ownerImpl senderId decode) client).run state) := by
  rw [QueryImpl.simulateQ_mapStateTBase_run, QueryImpl.simulateQ_mapStateTBase_run]
  exact (map_run_simulateQ_eq_of_query_map_eq
    (labels.mapStateTBase (ownerImpl senderId decode))
    (native.mapStateTBase (RawCtxMixedOwner.ownerImpl senderId decode))
    (nativeState interpret)
    (fun query state => (owner_interpreted interpret native labels kdf sealing opening senderId decode query state).symm)
    client state).symm

noncomputable def sourceImpl {Material Metadata PrimitiveState ι : Type} {base : OracleSpec ι}
    (labels : QueryImpl (PrimitiveSpec Material) (StateT PrimitiveState (OracleComp base)))
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl RawCtxMixedOwner.SourceSpec (StateT (State Material Metadata × PrimitiveState) (OracleComp base)) :=
  (labels.mapStateTBase (ownerImpl senderId decode)).flattenStateT

/-- Flattening retains the same whole native owner and complete primitive poststate. -/
theorem source_step {Material Metadata PrimitiveState ι : Type} {base : OracleSpec ι}
    (interpret : Material → RatchetMaterial)
    (native : QueryImpl RawCtxMixedOwner.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (labels : QueryImpl (PrimitiveSpec Material) (StateT PrimitiveState (OracleComp base)))
    (kdf : ∀ request, RawCtxInterpretedReceive.decodeResponse <$> native (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (sealing : ∀ input, simulateQ native (RawCtxMixedOwner.sendAdapter (.inr
      (toSealInput (mapInput interpret input)))) = labels (.inr (.inl input)))
    (opening : ∀ input, simulateQ native (RawCtxMixedOwner.receiveAdapter (.inr
      (toOpenInput (mapInput interpret input)))) = labels (.inr (.inr input)))
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : State Material Metadata × PrimitiveState) :
    (RawCtxMixedOwner.sourceImpl native senderId decode query).run (nativeState interpret state.1, state.2) =
      Prod.map id (Prod.map (nativeState interpret) id) <$>
        (sourceImpl labels senderId decode query).run state := by
  have hrun := congrArg (fun work : StateT PrimitiveState (OracleComp base)
      (RawCtxMixedOwner.SourceSpec.Range query × RawCtxWholeOwner.OwnerState Metadata) => work.run state.2)
    (owner_interpreted interpret native labels kdf sealing opening senderId decode query state.1)
  have reassoc := congrArg (fun work : OracleComp base
      ((RawCtxMixedOwner.SourceSpec.Range query × RawCtxWholeOwner.OwnerState Metadata) × PrimitiveState) =>
    (fun result => (result.1.1, (result.1.2, result.2))) <$> work) hrun
  simp only [StateT.run_map, Functor.map_map] at reassoc
  rw [← RawCtxMixedOwner.owner_interpretation]
  simpa only [sourceImpl, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run, StateT.mk,
    Functor.map_map, Prod.map_def, id_eq] using reassoc

/-- The actual mixed source schedule is exactly the complete mapped label computation. -/
theorem source_schedule {Material Metadata PrimitiveState Result ι : Type} {base : OracleSpec ι}
    (interpret : Material → RatchetMaterial)
    (native : QueryImpl RawCtxMixedOwner.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (labels : QueryImpl (PrimitiveSpec Material) (StateT PrimitiveState (OracleComp base)))
    (kdf : ∀ request, RawCtxInterpretedReceive.decodeResponse <$> native (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (sealing : ∀ input, simulateQ native (RawCtxMixedOwner.sendAdapter (.inr
      (toSealInput (mapInput interpret input)))) = labels (.inr (.inl input)))
    (opening : ∀ input, simulateQ native (RawCtxMixedOwner.receiveAdapter (.inr
      (toOpenInput (mapInput interpret input)))) = labels (.inr (.inr input)))
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result) (state : State Material Metadata × PrimitiveState) :
    (simulateQ (RawCtxMixedOwner.sourceImpl native senderId decode) client).run
      (nativeState interpret state.1, state.2) =
      Prod.map id (Prod.map (nativeState interpret) id) <$>
        (simulateQ (sourceImpl labels senderId decode) client).run state := by
  exact (map_run_simulateQ_eq_of_query_map_eq
    (sourceImpl labels senderId decode) (RawCtxMixedOwner.sourceImpl native senderId decode)
    (Prod.map (nativeState interpret) id)
    (fun query state => (source_step interpret native labels kdf sealing opening senderId decode query state).symm)
    client state).symm

/-- Every selective underlying query budget is preserved by complete source equality. -/
theorem source_query_bounds {Material Metadata PrimitiveState Result ι : Type} {base : OracleSpec ι}
    (interpret : Material → RatchetMaterial)
    (native : QueryImpl RawCtxMixedOwner.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (labels : QueryImpl (PrimitiveSpec Material) (StateT PrimitiveState (OracleComp base)))
    (kdf : ∀ request, RawCtxInterpretedReceive.decodeResponse <$> native (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (sealing : ∀ input, simulateQ native (RawCtxMixedOwner.sendAdapter (.inr
      (toSealInput (mapInput interpret input)))) = labels (.inr (.inl input)))
    (opening : ∀ input, simulateQ native (RawCtxMixedOwner.receiveAdapter (.inr
      (toOpenInput (mapInput interpret input)))) = labels (.inr (.inr input)))
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result) (state : State Material Metadata × PrimitiveState)
    (predicate : base.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    ((simulateQ (RawCtxMixedOwner.sourceImpl native senderId decode) client).run
      (nativeState interpret state.1, state.2)).IsQueryBoundP predicate budget ↔
      ((simulateQ (sourceImpl labels senderId decode) client).run state).IsQueryBoundP predicate budget := by
  rw [source_schedule interpret native labels kdf sealing opening senderId decode client state,
    isQueryBoundP_map_iff]

end BeaconcryptCore.Computational.RawCtxInterpretedOwner

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedOwner.rawReceive_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedOwner.rawReceive_interpreted

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedOwner.sendOwner_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedOwner.sendOwner_interpreted

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedOwner.owner_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedOwner.owner_interpreted

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedOwner.schedule_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedOwner.schedule_interpreted

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedOwner.source_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedOwner.source_step

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedOwner.source_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedOwner.source_schedule

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedOwner.source_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedOwner.source_query_bounds
