import BeaconcryptCore.Computational.RawCtxInterpretedOwner
import BeaconcryptCore.Computational.RawCtxSourceHkdf

/-!
The material label is the complete actual source KDF request: the original 32-byte input and 41-byte info. The real-source interpretation decodes the same 76-byte functional HKDF response, retaining its actual next chain and exact key/nonce projections. The KDF callback stores the unchanged request as its label. Selected seal/open callbacks reconstruct that request's material and invoke the existing native adapters on the same complete auxiliary and CTX cache state, with original sequence, context, plaintext/record and optional reply. All lower-level owner realization equations are discharged internally.

Exact full source and shared-schedule equality covers every adaptive mixed send/raw continuation, including source rejection, failed receive effects, retries, rollback and advanced send state after an active failed seal. Underlying selective query budgets agree, and the existing fixed-source uniform bound is 64*(qSend+qRaw). Both actual role initializers reuse the source 64 response, its real directional partition and the generic empty-slot constructor. A successful actual initializer therefore supplies the starting label representation without an inverse lookup or surjectivity premise.

This is an interpretation of the same supplied fixed functional HKDF source, total functional AEAD, total CTX random oracle and optional functional writer already used by RawCtxMixedShared. It is not an equality to arbitrary optional native primitive errors or a proof of the native library/compiler contract. Reconstruction repeats real local HKDF/decoding work; label copying, source execution and primitive work are not free. The labels retain earlier chain inputs and remain private analysis state, excluded from all network/reveal/snapshot/persistence interfaces. They are not a replacement native storage layout or a physical-erasure claim. Repeated requests and noninjective material values remain possible; no independent key table, source-position uniqueness, key freshness or security conclusion follows. Concrete chains and counters remain in the owner for later position/evolving-key composition. Public services, reveals, multiple owners, registration/root-generation distributions, restores and the global reduction still require their explicit extensions.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSourceMaterialLabels
open RawCtxMaterialInterpretation RawCtxInterpretedArguments RawCtxInterpretedOwner

/-- The exact source KDF request is a private material label; both input and info are retained. -/
abbrev Label := SymmetricRatchetKdfRequest

/-- Interpret a label using the same actual 76 response and source byte decoder. -/
noncomputable def materialOf (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (label : Label) : RatchetMaterial :=
  (RawCtxInterpretedReceive.decodeResponse (RawCtxSourceHkdf.response source.crypto label)).2

/-- The label retains the complete requested HKDF value and its actual chain/key/nonce slices. -/
theorem response_projections (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (request : Label) :
    BeaconcryptCore.Refinement.RepresentationBridge.absChain
        (RawCtxInterpretedReceive.decodeResponse (RawCtxSourceHkdf.response source.crypto request)).1 =
      ((source.crypto.hkdf (PqxdhRefinement.absBytes request.input)
        (PqxdhRefinement.absBytes request.info) 76).drop 32).take 32 ∧
    BeaconcryptCore.Refinement.RepresentationBridge.absMaterial (materialOf source request) =
      ((source.crypto.hkdf (PqxdhRefinement.absBytes request.input)
          (PqxdhRefinement.absBytes request.info) 76).take 32,
        (source.crypto.hkdf (PqxdhRefinement.absBytes request.input)
          (PqxdhRefinement.absBytes request.info) 76).drop 64) := by
  simpa only [materialOf, RawCtxInterpretedReceive.decodeResponse, interpretedStep,
    interpretedResponse, RawCtxSourceHkdf.response_bytes] using
    BeaconcryptCore.Refinement.RepresentationBridge.interpretedStep_bytes
      (fun _ => RawCtxSourceHkdf.response source.crypto request) (⟨request.input⟩ : RatchetChain)

/-- The already checked fixed-source HKDF and shared CTX primitive interpreter. -/
noncomputable def nativeImpl {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    QueryImpl RawCtxMixedOwner.NativeSpec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source)

/-- Retain exact KDF requests and dispatch reconstructed material through the original shared native adapters. -/
noncomputable def labelImpl {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    QueryImpl (PrimitiveSpec Label) (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl request => pure ((RawCtxInterpretedReceive.decodeResponse
      (RawCtxSourceHkdf.response source.crypto request)).1, request)
  | .inr (.inl input) => simulateQ (nativeImpl source writer)
      (RawCtxMixedOwner.sendAdapter (.inr (toSealInput (mapInput (materialOf source) input))))
  | .inr (.inr input) => simulateQ (nativeImpl source writer)
      (RawCtxMixedOwner.receiveAdapter (.inr (toOpenInput (mapInput (materialOf source) input))))

/-- The actual next chain and unchanged request label preserve the whole primitive state. -/
theorem kdf_step {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (request : Label) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (labelImpl source writer (.inl request)).run state =
      pure (((RawCtxInterpretedReceive.decodeResponse (RawCtxSourceHkdf.response source.crypto request)).1,
        request), state) := rfl

/-- The concrete backend discharges decoded-KDF realization internally. -/
theorem kdf_interpreted {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (request : SymmetricRatchetKdfRequest) :
    RawCtxInterpretedReceive.decodeResponse <$> (nativeImpl (Auxiliary := Auxiliary) source writer) (.inl request) =
      (fun reply => (reply.1, materialOf source reply.2)) <$> labelImpl source writer (.inl request) := by
  simp [nativeImpl, RawCtxMixedShared.sharedImpl, QueryImpl.compose, RawCtxMixedShared.sharedAdapter,
    OracleSpec.query, labelImpl, materialOf]
  change RawCtxInterpretedReceive.decodeResponse <$>
    (pure (RawCtxSourceHkdf.response source.crypto request) :
      StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp RatchetKdfResponse) = _
  rw [map_pure]

/-- All primitive obligations are discharged for the original adaptive mixed source computation. -/
theorem source_schedule {Auxiliary Metadata Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (state : State Label Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) :
    (simulateQ (RawCtxMixedOwner.sourceImpl (nativeImpl source writer) senderId decode) client).run
      (nativeState (materialOf source) state.1, state.2) =
      Prod.map id (Prod.map (nativeState (materialOf source)) id) <$>
        (simulateQ (RawCtxInterpretedOwner.sourceImpl (labelImpl source writer) senderId decode) client).run state := by
  exact RawCtxInterpretedOwner.source_schedule (materialOf source) (nativeImpl source writer)
    (labelImpl source writer) (kdf_interpreted source writer) (fun _ => rfl) (fun _ => rfl)
    senderId decode client state

/-- The same source law retains the complete original shared schedule and its final owner/cache state. -/
theorem shared_source {Auxiliary Metadata Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (state : State Label Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) :
    RawCtxMixedShared.sharedSchedule source.crypto writer (RawCtxSourceHkdf.kdfImpl source)
      senderId decode client (nativeState (materialOf source) state.1) state.2 =
      (fun result => ((result.1, nativeState (materialOf source) result.2.1), result.2.2)) <$>
        (simulateQ (RawCtxInterpretedOwner.sourceImpl (labelImpl source writer) senderId decode) client).run state := by
  rw [RawCtxMixedShared.shared_source]
  change (fun result => ((result.1, result.2.1), result.2.2)) <$>
    (simulateQ (RawCtxMixedOwner.sourceImpl (nativeImpl source writer) senderId decode) client).run
      (nativeState (materialOf source) state.1, state.2) = _
  rw [source_schedule, Functor.map_map]
  rfl

/-- Every selective underlying uniform-oracle budget is identical under the complete source map. -/
theorem source_query_bounds {Auxiliary Metadata Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (state : State Label Metadata × RawCtxSharedPrimitive.SharedState Auxiliary)
    (predicate : unifSpec.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    ((simulateQ (RawCtxMixedOwner.sourceImpl (nativeImpl source writer) senderId decode) client).run
      (nativeState (materialOf source) state.1, state.2)).IsQueryBoundP predicate budget ↔
      ((simulateQ (RawCtxInterpretedOwner.sourceImpl (labelImpl source writer) senderId decode) client).run state).IsQueryBoundP
        predicate budget := by
  rw [source_schedule, isQueryBoundP_map_iff]

/-- The interpreted source pays the existing 64-byte commitment cap per possible send/raw attempt. -/
theorem source_uniform {Auxiliary Metadata Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result) (qSend qRaw : Nat)
    (sendBound : client.IsQueryBoundP (fun query => query.isLeft = true) qSend)
    (rawBound : client.IsQueryBoundP (fun query => query.isRight = true) qRaw)
    (state : State Label Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) :
    ((simulateQ (RawCtxInterpretedOwner.sourceImpl (labelImpl source writer) senderId decode) client).run state).IsTotalQueryBound
      (64 * (qSend + qRaw)) := by
  have bound := RawCtxSourceHkdf.mixed_uniform source writer senderId decode client qSend qRaw
    sendBound rawBound (nativeState (materialOf source) state.1) state.2
  rw [shared_source] at bound
  exact (isQueryBound_map_iff _ _ _ _ _).mp bound

/-- The actual zero-counter source constructor creates empty label slots without inverting material bytes. -/
theorem kernel_new_interpreted (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (send receive : RatchetChain) :
    ConcreteRatchetKernel.new send receive =
      (fun kernel => (⟨mapRefined (materialOf source) kernel⟩ : ConcreteRatchetKernel)) <$>
        RefinedRatchet.new Label send receive := by
  simp only [ConcreteRatchetKernel.new, ConcreteRatchetKernel.from_counters,
    RefinedRatchet.new, from_counters_map (materialOf source), bind_map_left]
  rfl

/-- Reuse the actual initialization partition and generic source constructor. -/
def resumeInitial (pending : pqxdh.concrete.InitialRatchetKdfPending)
    (response : pqxdh.concrete.InitialRatchetKdfResponse) :
    RustM (RefinedRatchet RatchetChain RatchetChain Label) := do
  let chains ← pqxdh.split_initial_ratchet_kdf_output response.bytes pending.initialization
  RefinedRatchet.new Label chains.send_chain chains.receive_chain

/-- Every actual response and initialization branch maps to the original concrete kernel. -/
theorem resume_initial_interpreted (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : pqxdh.concrete.InitialRatchetKdfPending)
    (response : pqxdh.concrete.InitialRatchetKdfResponse) :
    pqxdh.concrete.resume_initial_ratchet_kdf pending response =
      (fun kernel => (⟨mapRefined (materialOf source) kernel⟩ : ConcreteRatchetKernel)) <$>
        resumeInitial pending response := by
  rw [pqxdh.concrete.resume_initial_ratchet_kdf_is_core_partition]
  simp only [resumeInitial, map_bind, kernel_new_interpreted source]

/-- Run the actual role start and source 64 response before creating its label kernel. -/
def initialLabels (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (beacon : Bool)
    (root : Std.Array Std.U8 32#usize) : RustM (RefinedRatchet RatchetChain RatchetChain Label) := do
  let pending ← if beacon then pqxdh.concrete.start_beacon_ratchet_kdf root
    else pqxdh.concrete.start_server_ratchet_kdf root
  resumeInitial pending (RawCtxSourceHkdf.initialResponse source.crypto pending.request)

/-- Either actual role initializer has the exact full RustM label interpretation. -/
theorem initialize_interpreted (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (beacon : Bool) (root : Std.Array Std.U8 32#usize) :
    (if beacon then BeaconcryptCore.Refinement.PqxdhConcreteSession.initializeBeacon root
        (RawCtxSourceHkdf.initialResponse source.crypto)
      else BeaconcryptCore.Refinement.PqxdhConcreteSession.initializeServer root
        (RawCtxSourceHkdf.initialResponse source.crypto)) =
      (fun kernel => (⟨mapRefined (materialOf source) kernel⟩ : ConcreteRatchetKernel)) <$>
        initialLabels source beacon root := by
  cases beacon <;> simp only [initialLabels, Bool.false_eq_true, if_false, if_true,
    BeaconcryptCore.Refinement.PqxdhConcreteSession.initializeBeacon,
    BeaconcryptCore.Refinement.PqxdhConcreteSession.initializeServer,
    map_bind, resume_initial_interpreted source]

/-- A successful native initializer derives a successful represented label kernel. -/
theorem initialized_labels (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (beacon : Bool) (root : Std.Array Std.U8 32#usize) (kernel : ConcreteRatchetKernel)
    (initialized : (if beacon then BeaconcryptCore.Refinement.PqxdhConcreteSession.initializeBeacon root
        (RawCtxSourceHkdf.initialResponse source.crypto)
      else BeaconcryptCore.Refinement.PqxdhConcreteSession.initializeServer root
        (RawCtxSourceHkdf.initialResponse source.crypto)) = ok kernel) :
    ∃ labels, initialLabels source beacon root = ok labels ∧
      (⟨mapRefined (materialOf source) labels⟩ : ConcreteRatchetKernel) = kernel := by
  rw [initialize_interpreted] at initialized
  cases completed : initialLabels source beacon root with
  | ok labels =>
    rw [completed] at initialized
    refine ⟨labels, rfl, ?_⟩
    exact ok.inj initialized
  | fail error =>
    rw [completed] at initialized
    cases initialized
  | div =>
    rw [completed] at initialized
    cases initialized

/-- Actual initialized source state supplies its own label representation and unchanged owner fields. -/
theorem initialized_owner {Metadata : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (beacon : Bool)
    (root : Std.Array Std.U8 32#usize) (state : RawCtxWholeOwner.OwnerState Metadata)
    (initialized : (if beacon then BeaconcryptCore.Refinement.PqxdhConcreteSession.initializeBeacon root
        (RawCtxSourceHkdf.initialResponse source.crypto)
      else BeaconcryptCore.Refinement.PqxdhConcreteSession.initializeServer root
        (RawCtxSourceHkdf.initialResponse source.crypto)) = ok state.owner.kernel) :
    ∃ labels : State Label Metadata, initialLabels source beacon root = ok labels.kernel ∧
      nativeState (materialOf source) labels = state := by
  obtain ⟨kernel, completed, represented⟩ := initialized_labels source beacon root state.owner.kernel initialized
  refine ⟨⟨kernel, state.owner.expectedSender, state.owner.associatedData, state.owner.metadata, state.rawAttempts⟩,
    completed, ?_⟩
  simp only [nativeState, represented]

/-- Successful actual initialization establishes the starting relation for every original adaptive continuation. -/
theorem initialized_schedule {Auxiliary Metadata Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (beacon : Bool) (root : Std.Array Std.U8 32#usize)
    (owner : RawCtxWholeOwner.OwnerState Metadata)
    (initialized : (if beacon then BeaconcryptCore.Refinement.PqxdhConcreteSession.initializeBeacon root
        (RawCtxSourceHkdf.initialResponse source.crypto)
      else BeaconcryptCore.Refinement.PqxdhConcreteSession.initializeServer root
        (RawCtxSourceHkdf.initialResponse source.crypto)) = ok owner.owner.kernel)
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) :
    ∃ labels : State Label Metadata, initialLabels source beacon root = ok labels.kernel ∧
      nativeState (materialOf source) labels = owner ∧
      (simulateQ (RawCtxMixedOwner.sourceImpl (nativeImpl source writer) senderId decode) client).run
        (owner, primitive) =
        Prod.map id (Prod.map (nativeState (materialOf source)) id) <$>
          (simulateQ (RawCtxInterpretedOwner.sourceImpl (labelImpl source writer) senderId decode) client).run
            (labels, primitive) := by
  obtain ⟨labels, completed, represented⟩ := initialized_owner source beacon root owner initialized
  refine ⟨labels, completed, represented, ?_⟩
  rw [← represented]
  exact source_schedule source writer senderId decode client (labels, primitive)

end BeaconcryptCore.Computational.RawCtxSourceMaterialLabels

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceMaterialLabels.response_projections' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceMaterialLabels.response_projections

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceMaterialLabels.kdf_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceMaterialLabels.kdf_step

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceMaterialLabels.kdf_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceMaterialLabels.kdf_interpreted

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceMaterialLabels.source_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceMaterialLabels.source_schedule

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceMaterialLabels.shared_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceMaterialLabels.shared_source

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceMaterialLabels.source_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceMaterialLabels.source_query_bounds

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceMaterialLabels.source_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceMaterialLabels.source_uniform

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceMaterialLabels.kernel_new_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceMaterialLabels.kernel_new_interpreted

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceMaterialLabels.resume_initial_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceMaterialLabels.resume_initial_interpreted

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceMaterialLabels.initialize_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceMaterialLabels.initialize_interpreted

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceMaterialLabels.initialized_labels' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceMaterialLabels.initialized_labels

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceMaterialLabels.initialized_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceMaterialLabels.initialized_owner

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceMaterialLabels.initialized_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceMaterialLabels.initialized_schedule
