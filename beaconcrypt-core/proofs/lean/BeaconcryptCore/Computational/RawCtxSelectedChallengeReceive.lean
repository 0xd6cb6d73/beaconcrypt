import BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds
import BeaconcryptCore.Computational.RawCtxSelectedOpenConsumer
import BeaconcryptCore.Computational.RawCtxSelectedOpenScope

/-!
The complete opaque receive executes actual private requests and one universal key-free opening service. Its source comparison retains every optional reply, resulting kernel and shared commitment cache. Opening context obligations are derived along the original admitted target and context, for every typed KDF response, rather than imposed on arbitrary unreachable callbacks. This is a local source simulation at a retained shared state; execution of the actual prefix in the ordinary challenger remains a separate composition obligation.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedChallengeReceive
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open RawCtxSelectedMessageKey RawCtxSelectedMessageKdf RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedMessageDriver
variable {A : Type}

noncomputable def privateImpl (prior : Prior) :
    QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp) :=
  fun request => pure (RawCtxFunctionalFamily.execute prior request)

/-- The entire native functional backend uses the actual supplied private view and the original shared primitive callbacks. -/
theorem native_private (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior) :
    RawCtxFunctionalFamily.native (A := A) source writer prior =
      RawCtxMixedShared.sharedImpl source.crypto writer (privateImpl prior) := by
  funext query state
  rcases query with request | (request | (request | (request | request)))
  all_goals simp [RawCtxFunctionalFamily.native, RawCtxFunctionalFamily.backend, QueryImpl.compose,
    RawCtxServerServices.nativeLift, RawCtxSelectiveKdfFamily.compiler, RawCtxRetainedTable.viewImpl,
    RawCtxProtocolBackend.backend, RawCtxServerServices.backendImpl, RawCtxMixedShared.sharedImpl,
    RawCtxMixedShared.sharedAdapter, RawCtxSharedPrimitive.nativeImpl, privateImpl,
    RawCtxFunctionalFamily.execute, OracleSpec.query]
  all_goals rfl

/-- The actual functional opening uses precisely the original scalar native owner adapter. -/
theorem native_opening (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (pending : ReceiveOpen RawCtxWholeOwner.OpenContext) :
    RawCtxFunctionalFamily.opening (A := A) source writer prior pending =
      simulateQ (RawCtxSharedPrimitive.nativeImpl source.crypto (privateImpl prior))
        (RawCtxSourceOpen.ownerAdapter (.inr pending)) := by
  simp only [RawCtxFunctionalFamily.opening, native_private, RawCtxMixedOwner.receiveAdapter,
    RawCtxSourceOpen.ownerAdapter, QueryImpl.compose, QueryImpl.simulateQ_compose]
  rw [← QueryImpl.simulateQ_compose, RawCtxMixedShared.shared_receive]

noncomputable def service (prior : Prior) (read : RawCtxReceive.FrameDecoder) :
    QueryImpl (ReceiveServices RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted)
      (OracleComp AdaptiveCtxDynamicKnownKeys.Spec)
  | .inl address => pure (prior address)
  | .inr pending => RawCtxSelectedOpenConsumer.service 0 read pending.context.frame.sender pending

/-- An actually reached source opening has the same optional API reply and whole commitment cache under the concrete selected/known service. -/
theorem opening_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder)
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Slot RawCtxWholeOwner.OpenContext)
    (ambient : A) (state : AdaptiveCtxDynamicKnownKeys.SourceState)
    (nonempty : pending.context.raw.isEmpty = false) (decoded : read pending.context.raw = some pending.context.frame)
    (valid : RawCtxReceive.ValidFrame pending.context.frame.sender pending.context.associatedData pending.context.frame)
    (prepared : RawCtxInterpretedOpening.sequence pending = ok pending.context.frame.sequence)
    (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload pending.context.frame.payload = some slices) :
    (receiveServices source writer prior parent key target nonce next (.inr pending)).run (ambient, state.cache) =
      (fun result => (result.1, (ambient, result.2.cache))) <$>
        (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
          (service prior read (.inr pending))).run state := by
  rw [receiveServices, native_opening]
  exact RawCtxSelectedOpenConsumer.service_source 0 read pending.context.frame.sender key source.crypto
    (privateImpl (privateTable prior parent target (response key nonce next))) pending ambient state
    nonempty decoded valid prepared slices parsed

set_option backward.isDefEq.respectTransparency false in
/-- The original complete receive has the same final opaque kernel, optional plaintext and full shared cache under concrete CTX callbacks. -/
theorem receive_cache (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (kernel : RawCtxSelectedMessageReveals.Kernel)
    (context : RawCtxWholeOwner.OpenContext) (ambient : A) (state : AdaptiveCtxDynamicKnownKeys.SourceState)
    (nonempty : context.raw.isEmpty = false) (decoded : read context.raw = some context.frame)
    (valid : RawCtxReceive.ValidFrame context.frame.sender context.associatedData context.frame)
    (slices : RawCtxFrameDecoding.Slices) (parsed : RawCtxFrameDecoding.fromPayload context.frame.payload = some slices) :
    (fun result => (result.1, (ambient, result.2.cache))) <$>
      (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
        (simulateQ (service prior read) (receive parent target nonce next kernel context.frame.sequence context))).run state =
      (simulateQ (receiveServices source writer prior parent key target nonce next)
        (receive parent target nonce next kernel context.frame.sequence context)).run (ambient, state.cache) := by
  simp only [receive, ← QueryImpl.simulateQ_compose]
  refine RawCtxSelectedOpenScope.receive_state _ _ (fun state : AdaptiveCtxDynamicKnownKeys.SourceState => (ambient, state.cache))
    kernel context.frame.sequence context ?_ ?_ state
  · intro request before
    simp only [QueryImpl.compose, receiveCompiler, ← QueryImpl.simulateQ_compose]
    change (fun result => (result.1, (ambient, result.2.cache))) <$>
      ((simulateQ (fun address => (pure (prior address) : StateT AdaptiveCtxDynamicKnownKeys.SourceState ProbComp FullOutput))
        (derive parent target nonce next request)).run before) =
      (simulateQ (fun address => (pure (prior address) : StateT (RawCtxSharedPrimitive.SharedState A) ProbComp FullOutput))
        (derive parent target nonce next request)).run (ambient, before.cache)
    rw [derive_evaluated, derive_evaluated, StateT.run_pure, StateT.run_pure, map_pure]
  · intro pending prepared same before
    simp only [QueryImpl.compose, receiveCompiler, simulateQ_spec_query]
    change (fun result : core.option.Option RawCtxWholeOwner.Decrypted × AdaptiveCtxDynamicKnownKeys.SourceState =>
      (result.1, (ambient, result.2.cache))) <$>
      (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
        (service prior read (.inr pending))).run before =
      (receiveServices source writer prior parent key target nonce next (.inr pending)).run (ambient, before.cache)
    exact (opening_source source writer prior parent key target nonce next read pending ambient before
        (by simpa only [same] using nonempty) (by simpa only [same] using decoded)
        (by simpa only [same] using valid) (by simpa only [same] using prepared) slices
        (by simpa only [same] using parsed)).symm

/-- The literal full native receive, including all private requests, rollback/consumption and final kernel, is the concrete selected/known CTX execution after interpreting only opaque material. -/
theorem native_receive (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (kernel : RawCtxSelectedMessageReveals.Kernel)
    (context : RawCtxWholeOwner.OpenContext) (ambient : A) (state : AdaptiveCtxDynamicKnownKeys.SourceState)
    (nonempty : context.raw.isEmpty = false) (decoded : read context.raw = some context.frame)
    (valid : RawCtxReceive.ValidFrame context.frame.sender context.associatedData context.frame)
    (slices : RawCtxFrameDecoding.Slices) (parsed : RawCtxFrameDecoding.fromPayload context.frame.payload = some slices) :
    (simulateQ ((RawCtxFunctionalFamily.native source writer (privateTable prior parent target (response key nonce next)) ∘ₛ
        RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
      (RawCtxOwnerOracle.receive (RawCtxSelectedMessageReveals.nativeKernel key kernel) context.frame.sequence context)).run
        (ambient, state.cache) =
      (fun result => ((RawCtxSelectedMessageReveals.nativeKernel key result.1.1, result.1.2), (ambient, result.2.cache))) <$>
        (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
          (simulateQ (service prior read) (receive parent target nonce next kernel context.frame.sequence context))).run state := by
  rw [receive_source, StateT.run_map, ← receive_cache source writer prior parent key target nonce next read kernel context ambient state
    nonempty decoded valid slices parsed]
  simp only [Functor.map_map]

/-- The actual frame admission supplies the required complete payload split; no additional parser or plaintext witness is assumed. -/
theorem receive_valid (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (kernel : RawCtxSelectedMessageReveals.Kernel)
    (context : RawCtxWholeOwner.OpenContext) (ambient : A) (state : AdaptiveCtxDynamicKnownKeys.SourceState)
    (nonempty : context.raw.isEmpty = false) (decoded : read context.raw = some context.frame)
    (valid : RawCtxReceive.ValidFrame context.frame.sender context.associatedData context.frame) :
    (fun result => (result.1, (ambient, result.2.cache))) <$>
      (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
        (simulateQ (service prior read) (receive parent target nonce next kernel context.frame.sequence context))).run state =
      (simulateQ (receiveServices source writer prior parent key target nonce next)
        (receive parent target nonce next kernel context.frame.sequence context)).run (ambient, state.cache) := by
  obtain ⟨slices, parsed⟩ := (RawCtxFrameDecoding.fromPayload_some_iff context.frame.payload).mpr valid.2.1
  exact receive_cache source writer prior parent key target nonce next read kernel context ambient state
    nonempty decoded valid slices parsed

/-- Each original receive uses at most one dynamic CTX verification request; up to 51 separately counted prior-table evaluations remain local source work. -/
theorem receive_queries (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (kernel : RawCtxSelectedMessageReveals.Kernel) (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    (simulateQ (service prior read) (receive parent target nonce next kernel sequence context)).IsTotalQueryBound 1 := by
  rw [← isQueryBoundP_true_iff]
  apply RawCtxSourceOpen.simulate_bound (service prior read) (fun query => query.isLeft = false) (fun _ => True)
    _ 1 (RawCtxSelectedMessageDriverBounds.receive_open parent target nonce next kernel sequence context)
  intro query
  cases query with
  | inl address => simp only [service]; trivial
  | inr pending =>
      exact (isQueryBoundP_true_iff _ 1).mpr (RawCtxSelectedOpenConsumer.service_total 0 read pending.context.frame.sender pending)

/-- Receive-only use of the original owner frontend; its unused send field cannot be reached by rawReceive. -/
noncomputable def receiver (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) :
    RawCtxChainOwner.Calls RawCtxSelectedMessageReveals.Kernel (OracleComp AdaptiveCtxDynamicKnownKeys.Spec) where
  receive kernel sequence context := simulateQ (service prior read) (receive parent target nonce next kernel sequence context)
  send kernel _ := pure (kernel, none)

noncomputable def raw {Metadata : Type} (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel Metadata) :=
  (RawCtxChainOwner.rawReceive (receiver prior parent target nonce next read) read bytes).run owner

/-- Arbitrary raw bytes use the exact source parsing, validation, attempt count and owner publication before the complete native receive simulation. -/
theorem raw_source {Metadata : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel Metadata)
    (ambient : A) (state : AdaptiveCtxDynamicKnownKeys.SourceState) :
    (simulateQ (RawCtxFunctionalFamily.native source writer (privateTable prior parent target (response key nonce next)) ∘ₛ
        RawCtxMixedOwner.receiveAdapter)
      ((RawCtxWholeOwner.rawReceive read bytes).run (RawCtxChainOwner.nativeState (RawCtxSelectedMessageReveals.nativeKernel key) owner))).run
        (ambient, state.cache) =
      (fun result => ((result.1.1, RawCtxChainOwner.nativeState (RawCtxSelectedMessageReveals.nativeKernel key) result.1.2),
        (ambient, result.2.cache))) <$>
        (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
          (raw prior parent target nonce next read bytes owner)).run state := by
  simp only [RawCtxWholeOwner.rawReceive, raw, RawCtxChainOwner.rawReceive, RawCtxChainOwner.nativeState, StateT.run]
  by_cases empty : bytes.isEmpty = true
  · simp only [empty, if_true, simulateQ_pure,
      RawCtxWholeOwner.publish, RawCtxChainOwner.publish]
    rfl
  · simp only [empty, Bool.false_eq_true, if_false]
    cases decoded : read bytes with
    | none =>
      simp only [simulateQ_pure, RawCtxWholeOwner.publish,
        RawCtxChainOwner.publish]
      rfl
    | some frame =>
      by_cases valid : RawCtxReceive.ValidFrame owner.expectedSender owner.associatedData frame
      · simp only [valid, if_true, receiver, bind_pure_comp, simulateQ_map, ← QueryImpl.simulateQ_compose]
        change (StateT.run _ (ambient, state.cache)) = _ <$> StateT.run _ state
        rw [StateT.run_map, StateT.run_map]
        obtain ⟨slices, parsed⟩ := (RawCtxFrameDecoding.fromPayload_some_iff frame.payload).mpr valid.2.1
        have actual := native_receive source writer prior parent key target nonce next read owner.kernel
          ⟨bytes, frame, owner.associatedData⟩ ambient state
          (by simpa only [Bool.not_eq_true] using empty) decoded ⟨rfl, valid.2⟩ slices parsed
        have mapped := congrArg (fun work => (fun result =>
          (RawCtxWholeOwner.publish (RawCtxChainOwner.nativeState (RawCtxSelectedMessageReveals.nativeKernel key) owner) result.1,
            result.2)) <$> work) actual
        simpa only [Functor.map_map, ← QueryImpl.simulateQ_compose, RawCtxWholeOwner.publish,
          RawCtxChainOwner.publish, RawCtxChainOwner.nativeState] using mapped
      · simp only [valid, if_false, simulateQ_pure,
          RawCtxWholeOwner.publish, RawCtxChainOwner.publish]
        rfl

/-- Every raw API attempt, including parser/admission rejection and cached failure, makes at most one component verification request. -/
theorem raw_queries {Metadata : Type} (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel Metadata) :
    (raw prior parent target nonce next read bytes owner).IsTotalQueryBound 1 := by
  simp only [raw, RawCtxChainOwner.rawReceive, StateT.run]
  split
  · trivial
  · split
    · trivial
    · split
      · simpa only [receiver, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
          receive_queries prior parent target nonce next read owner.kernel _ _
      · trivial

end BeaconcryptCore.Computational.RawCtxSelectedChallengeReceive

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChallengeReceive.native_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChallengeReceive.native_private

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChallengeReceive.native_opening' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChallengeReceive.native_opening

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChallengeReceive.opening_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChallengeReceive.opening_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChallengeReceive.receive_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChallengeReceive.receive_cache

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChallengeReceive.native_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChallengeReceive.native_receive

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChallengeReceive.receive_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChallengeReceive.receive_valid

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChallengeReceive.receive_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChallengeReceive.receive_queries

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChallengeReceive.raw_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChallengeReceive.raw_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChallengeReceive.raw_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChallengeReceive.raw_queries
