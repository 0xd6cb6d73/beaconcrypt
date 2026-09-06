import BeaconcryptCore.Computational.RawCtxMixedPositionCapability
import BeaconcryptCore.Computational.RawCtxServerServices

/-!
The position-capability trace now includes actual caller coins, public CTX hashing and fixed-source HKDF projections alongside adaptive sends and raw receives. Public calls use the unchanged published RawCtxServerServices handler and the same complete primitive auxiliary/cache state as private record callbacks. They leave the owner and private successful-position history unchanged. No second hash table, replacement public KDF or additional disclosure interface is introduced.

The source presentation composes the existing mixed owner operations with that exact public handler. Its private monitor records every original dependent request/reply and erases to the entire original terminal result, owner and primitive state. Every supported actual adaptive run has a matching capability trace with the same transcript and final shared primitive state, send counter and private spent history. A single constructed transcript satisfies every supplied selective call bound; raw entries alone bound successful-history growth. The actual source initializer supplies the empty-history relation, and monitoring preserves every selective underlying uniform-query budget.

This remains support inclusion with source-derived admission choices, not a probability law for arbitrary stronger choices or an executable source-free strategy. All record and public calls use the existing fixed-functional KDF, total functional AEAD/CTX ROM and optional writer interpretation. Material reconstruction and pure parsing/history work remain real local computation; positions and origins may have equal byte values. Counts do not make source/local primitive work free or prove native library, allocation, timing or traversal equality.

The theorem covers one uninterrupted established owner and this explicit record/public interface. Current-chain or skipped-key reveals, multiple owners, registration/lifecycle, restored/copied state, evolving-key distributions, the persistent ProVerif process and the global cryptographic bridge remain separate. Origins, kernels, private histories and full interpreter state are not added to public/reveal/snapshot interfaces. The public caller receives only each original requested answer and actual optional API reply; API plaintext declassification is an outer policy. No authentication, key independence, primitive security loss or global completion is claimed.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPositionPublicServices
open RawCtxReceiveConsumption

abbrev SourceSpec := RawCtxMixedOwner.SourceSpec + RawCtxServerServices.PublicSpec
abbrev SourceState (Metadata Auxiliary : Type) := RawCtxMixedPositionCapability.SourceState Metadata Auxiliary
abbrev CapabilityState (Auxiliary : Type) := RawCtxMixedPositionCapability.CapabilityState Auxiliary
abbrev project {Metadata Auxiliary : Type} (state : SourceState Metadata Auxiliary) :=
  RawCtxMixedPositionCapability.project state

noncomputable def publicImpl {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    QueryImpl RawCtxServerServices.PublicSpec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  RawCtxServerServices.backendImpl source writer (RawCtxSourceHkdf.kdfImpl source) ∘ₛ RawCtxServerServices.publicLift

/-- The original public HKDF projection evaluates the same fixed source and retains the entire primitive state. -/
theorem public_hkdf {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (query : PqxdhJointKdfGame.JointKdfViewQuery) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (publicImpl source writer (.inr (.inr query))).run state =
      pure (query.project (PqxdhJointKdf.productionStream source.crypto query.address), state) := by
  exact RawCtxServerServices.public_hkdf source writer (RawCtxSourceHkdf.kdfImpl source) query state

/-- The original public hash reads and updates exactly the same cache used by private record commitments. -/
theorem public_hash {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (bytes : Pqxdh.Bytes) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (publicImpl source writer (.inr (.inl bytes))).run state = (do
      let result ← (CtxRomAuth.ctxRandomOracle ((), bytes)).run state.2
      pure (some result.1.toList, (state.1, result.2))) := by
  exact RawCtxServerServices.public_hash source writer (RawCtxSourceHkdf.kdfImpl source) bytes state

/-- The caller receives its actual explicit uniform reply while private primitive state remains unchanged. -/
theorem public_coin {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (coin : unifSpec.Domain) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (publicImpl source writer (.inl coin)).run state = (do
      let result ← unifSpec.query coin
      pure (result, state)) := by
  exact RawCtxServerServices.public_coin source writer (RawCtxSourceHkdf.kdfImpl source) coin state

noncomputable def originalImpl {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl SourceSpec (StateT (RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  fun query state => match query with
  | .inl request => (RawCtxMixedOwner.sourceImpl
      (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source)) sender decode request).run state
  | .inr request => do
      let result ← (publicImpl source writer request).run state.2
      pure (result.1, (state.1, result.2))

noncomputable def sourceImpl {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl SourceSpec (StateT (SourceState Metadata Auxiliary) ProbComp) :=
  fun query state => match query with
  | .inl request => (trackedImpl source writer sender decode request).run state
  | .inr request => do
      let result ← (publicImpl source writer request).run state.1.2
      pure (result.1, ((state.1.1, result.2), state.2))

noncomputable def capabilityImpl {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (expectedSender sender : Std.U64)
    (associatedData : Pqxdh.Bytes) (decode : RawCtxReceive.FrameDecoder) (enabled : Bool) :
    QueryImpl SourceSpec (StateT (CapabilityState Auxiliary) ProbComp) :=
  fun query state => match query with
  | .inl request => (RawCtxMixedPositionCapability.capabilityImpl source writer sendOrigin receiveOrigin
      expectedSender sender associatedData decode enabled request).run state
  | .inr request => do
      let result ← (publicImpl source writer request).run state.1
      pure (result.1, (result.2, state.2))

/-- Removing only the private successful-position history retains the complete original record/public step. -/
theorem source_step_erasure {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (query : SourceSpec.Domain)
    (state : SourceState Metadata Auxiliary) :
    Prod.map id Prod.fst <$> (sourceImpl source writer sender decode query).run state =
      (originalImpl source writer sender decode query).run state.1 := by
  cases query <;> simp [sourceImpl, originalImpl, trackedImpl, StateT.run]

/-- Every actual public or record step preserves the supplied source consumption and material relation. -/
theorem source_step_invariant {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : SourceSpec.Domain) (state : SourceState Metadata Auxiliary)
    (invariant : ConsumedRefines source.crypto sendOrigin receiveOrigin state.1.1.owner.kernel state.2)
    (result : SourceSpec.Range query × SourceState Metadata Auxiliary)
    (present : result ∈ support ((sourceImpl source writer sender decode query).run state)) :
    ConsumedRefines source.crypto sendOrigin receiveOrigin result.2.1.1.owner.kernel result.2.2 := by
  cases query with
  | inl request =>
    exact tracked_step_spent source writer sendOrigin receiveOrigin sender decode request state invariant result present
  | inr request =>
    unfold sourceImpl StateT.run at present
    obtain ⟨actual, hactual, returned⟩ := mem_support_bind_peel _ _ present
    have equal := eq_of_mem_support_pure _ returned
    subst result
    exact invariant

/-- The actual typed step embeds with the same reply and projected shared state; public calls need no admission choice. -/
theorem source_step_capability {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : SourceSpec.Domain) (state : SourceState Metadata Auxiliary)
    (invariant : ConsumedRefines source.crypto sendOrigin receiveOrigin state.1.1.owner.kernel state.2)
    (result : SourceSpec.Range query × SourceState Metadata Auxiliary)
    (present : result ∈ support ((sourceImpl source writer sender decode query).run state)) :
    ∃ enabled, (result.1, project result.2) ∈ support
      ((capabilityImpl source writer sendOrigin receiveOrigin state.1.1.owner.expectedSender sender
        state.1.1.owner.associatedData decode enabled query).run (project state)) := by
  cases query with
  | inl request =>
    exact RawCtxMixedPositionCapability.tracked_step_capability source writer sendOrigin receiveOrigin sender decode request state invariant result present
  | inr request =>
    unfold sourceImpl StateT.run at present
    obtain ⟨actual, hactual, returned⟩ := mem_support_bind_peel _ _ present
    have equal := eq_of_mem_support_pure _ returned
    subst result
    refine ⟨false, ?_⟩
    change _ ∈ support (do
      let reply ← (publicImpl source writer request).run state.1.2
      pure (reply.1, (reply.2, (state.1.1.owner.kernel.refined.control.send_sequence.val, state.2))))
    rw [mem_support_bind_iff]
    exact ⟨actual, hactual, by simp only [support_pure, Set.mem_singleton_iff]; rfl⟩

def rawRequest : SourceSpec.Domain → Bool
  | .inl request => request.isRight
  | .inr _ => false

/-- Only actual raw requests increment the attempt counter; every operation retains immutable owner fields. -/
theorem source_step_metadata {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : SourceSpec.Domain) (state : SourceState Metadata Auxiliary)
    (result : SourceSpec.Range query × SourceState Metadata Auxiliary)
    (present : result ∈ support ((sourceImpl source writer sender decode query).run state)) :
    result.2.1.1.rawAttempts = state.1.1.rawAttempts + (if rawRequest query then 1 else 0) ∧
      RawCtxMixedOwner.ownerFields result.2.1.1 = RawCtxMixedOwner.ownerFields state.1.1 := by
  cases query with
  | inl request =>
    exact RawCtxMixedPositionCapability.tracked_step_metadata source writer sender decode request state result present
  | inr request =>
    unfold sourceImpl StateT.run at present
    obtain ⟨actual, hactual, returned⟩ := mem_support_bind_peel _ _ present
    have equal := eq_of_mem_support_pure _ returned
    subst result
    exact ⟨by simp [rawRequest], rfl⟩

abbrev Transcript := List ((query : SourceSpec.Domain) × SourceSpec.Range query)

inductive SourceTrace {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) :
    SourceState Metadata Auxiliary → Transcript → SourceState Metadata Auxiliary → Prop
  | nil (state : SourceState Metadata Auxiliary) : SourceTrace source writer sender decode state [] state
  | step {state final : SourceState Metadata Auxiliary} (query : SourceSpec.Domain)
      {result : SourceSpec.Range query × SourceState Metadata Auxiliary} {rest : Transcript}
      (actual : result ∈ support ((sourceImpl source writer sender decode query).run state))
      (tail : SourceTrace source writer sender decode result.2 rest final) :
      SourceTrace source writer sender decode state (⟨query, result.1⟩ :: rest) final

inductive CapabilityTrace {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (expectedSender sender : Std.U64)
    (associatedData : Pqxdh.Bytes) (decode : RawCtxReceive.FrameDecoder) :
    CapabilityState Auxiliary → Transcript → CapabilityState Auxiliary → Prop
  | nil (state : CapabilityState Auxiliary) :
      CapabilityTrace source writer sendOrigin receiveOrigin expectedSender sender associatedData decode state [] state
  | step {state final : CapabilityState Auxiliary} (query : SourceSpec.Domain)
      {result : SourceSpec.Range query × CapabilityState Auxiliary} {rest : Transcript}
      (enabled : Bool)
      (actual : result ∈ support ((capabilityImpl source writer sendOrigin receiveOrigin expectedSender sender
        associatedData decode enabled query).run state))
      (tail : CapabilityTrace source writer sendOrigin receiveOrigin expectedSender sender associatedData decode result.2 rest final) :
      CapabilityTrace source writer sendOrigin receiveOrigin expectedSender sender associatedData decode state (⟨query, result.1⟩ :: rest) final

/-- Every actual adaptive record/public trace embeds with its exact dependent transcript and final projected state. -/
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
    have nextInvariant := source_step_invariant source writer sendOrigin receiveOrigin sender decode query state invariant result actual
    obtain ⟨nextTrace, finalInvariant⟩ := ih nextInvariant
    obtain ⟨enabled, supported⟩ := source_step_capability source writer sendOrigin receiveOrigin sender decode query state invariant result actual
    have fields := (source_step_metadata source writer sender decode query state result actual).2
    refine ⟨.step query enabled supported ?_, finalInvariant⟩
    have pin := congrArg Prod.fst fields
    have ad := congrArg (fun fields => fields.2.1) fields
    dsimp only [RawCtxMixedOwner.ownerFields] at pin ad
    simpa only [pin, ad] using nextTrace

noncomputable def loggedImpl {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl SourceSpec (StateT (SourceState Metadata Auxiliary × Transcript) ProbComp) :=
  fun query state => do
    let result ← (sourceImpl source writer sender decode query).run state.1
    pure (result.1, (result.2, state.2 ++ [⟨query, result.1⟩]))

/-- The private transcript monitor erases to the complete original step, including all public cache effects. -/
theorem logged_step_erasure {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (query : SourceSpec.Domain)
    (state : SourceState Metadata Auxiliary × Transcript) :
    Prod.map id (fun state => state.1.1) <$> (loggedImpl source writer sender decode query).run state =
      (originalImpl source writer sender decode query).run state.1.1 := by
  simpa [loggedImpl, StateT.run, bind_pure_comp, Prod.map_def] using source_step_erasure source writer sender decode query state.1

/-- Private monitoring retains the whole original adaptive client result, owner and primitive poststate. -/
theorem logged_run_erasure {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (state : SourceState Metadata Auxiliary × Transcript) :
    Prod.map id (fun state => state.1.1) <$> (simulateQ (loggedImpl source writer sender decode) client).run state =
      (simulateQ (originalImpl source writer sender decode) client).run state.1.1 := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (loggedImpl source writer sender decode) (originalImpl source writer sender decode)
    (fun state => state.1.1) (logged_step_erasure source writer sender decode) client state

/-- Every supported monitored run constructs its source trace internally from actual request/reply occurrences. -/
theorem logged_run_trace {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (state : SourceState Metadata Auxiliary × Transcript)
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

/-- Each supported original adaptive record/public run yields a matching capability trace and final source invariant. -/
theorem source_supported_capability {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result)
    (initial : RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) (spent : List Nat)
    (invariant : ConsumedRefines source.crypto sendOrigin receiveOrigin initial.1.owner.kernel spent)
    (result : Result × (RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary))
    (actual : result ∈ support ((simulateQ (originalImpl source writer sender decode) client).run initial)) :
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

def queryCount (predicate : SourceSpec.Domain → Bool) (transcript : Transcript) : Nat :=
  transcript.countP (fun entry => predicate entry.1)

/-- Any supplied original selective call bound applies to its class in the same actual monitored transcript. -/
theorem logged_run_count {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result)
    (predicate : SourceSpec.Domain → Bool) (budget : Nat)
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
    · simp only [counted, if_true] at rest
      have positive := bounded.1.resolve_left (not_not.mpr counted)
      omega
    · simp only [counted, Bool.false_eq_true, if_false] at rest
      omega

/-- Only a raw call can grow private successful-position history, and public effects leave that history unchanged. -/
theorem source_step_growth {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : SourceSpec.Domain) (state : SourceState Metadata Auxiliary)
    (result : SourceSpec.Range query × SourceState Metadata Auxiliary)
    (present : result ∈ support ((sourceImpl source writer sender decode query).run state)) :
    result.2.2.length ≤ state.2.length + (if rawRequest query then 1 else 0) := by
  cases query with
  | inl request =>
    exact tracked_step_length source writer sender decode request state result present
  | inr request =>
    unfold sourceImpl StateT.run at present
    obtain ⟨actual, hactual, returned⟩ := mem_support_bind_peel _ _ present
    have equal := eq_of_mem_support_pure _ returned
    subst result
    simp [rawRequest]

/-- Actual raw transcript entries exactly account for the attempt counter and retain immutable routing context. -/
theorem SourceTrace.metadata {Metadata Auxiliary : Type}
    {source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource} {writer : RawCtxMixedShared.Writer}
    {sender : Std.U64} {decode : RawCtxReceive.FrameDecoder}
    {initial final : SourceState Metadata Auxiliary} {transcript : Transcript}
    (trace : SourceTrace source writer sender decode initial transcript final) :
    final.1.1.rawAttempts = initial.1.1.rawAttempts + queryCount rawRequest transcript ∧
      RawCtxMixedOwner.ownerFields final.1.1 = RawCtxMixedOwner.ownerFields initial.1.1 := by
  induction trace with
  | nil state => exact ⟨by simp [queryCount], rfl⟩
  | @step state final query result rest actual tail ih =>
    have fields := source_step_metadata source writer sender decode query state result actual
    refine ⟨?_, ih.2.trans fields.2⟩
    simp only [queryCount, List.countP_cons] at *
    omega

/-- Successful-position history grows by at most the number of actual raw entries in the complete transcript. -/
theorem SourceTrace.history_length {Metadata Auxiliary : Type}
    {source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource} {writer : RawCtxMixedShared.Writer}
    {sender : Std.U64} {decode : RawCtxReceive.FrameDecoder}
    {initial final : SourceState Metadata Auxiliary} {transcript : Transcript}
    (trace : SourceTrace source writer sender decode initial transcript final) :
    final.2.length ≤ initial.2.length + queryCount rawRequest transcript := by
  induction trace with
  | nil state => simp [queryCount]
  | @step state final query result rest actual tail ih =>
    have growth := source_step_growth source writer sender decode query state result actual
    simp only [queryCount, List.countP_cons] at *
    omega

/-- One internally constructed matching trace satisfies every supplied selective budget and retains nonrepeating successful history. -/
theorem source_capability_counted {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result)
    (initial : RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) (spent : List Nat)
    (invariant : ConsumedRefines source.crypto sendOrigin receiveOrigin initial.1.owner.kernel spent)
    (result : Result × (RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary))
    (actual : result ∈ support ((simulateQ (originalImpl source writer sender decode) client).run initial)) :
    ∃ finalSpent transcript,
      SourceTrace source writer sender decode (initial, spent) transcript (result.2, finalSpent) ∧
      CapabilityTrace source writer sendOrigin receiveOrigin initial.1.owner.expectedSender sender initial.1.owner.associatedData decode
        (project (initial, spent)) transcript (project (result.2, finalSpent)) ∧
      ConsumedRefines source.crypto sendOrigin receiveOrigin result.2.1.owner.kernel finalSpent ∧
      finalSpent.Nodup ∧ finalSpent.length ≤ spent.length + queryCount rawRequest transcript ∧
      ∀ predicate budget, client.IsQueryBoundP (fun query => predicate query = true) budget →
        queryCount predicate transcript ≤ budget := by
  rw [← logged_run_erasure source writer sender decode client ((initial, spent), []), support_map, Set.mem_image] at actual
  obtain ⟨logged, supported, rfl⟩ := actual
  obtain ⟨transcript, history, trace⟩ := logged_run_trace source writer sender decode client ((initial, spent), []) logged supported
  obtain ⟨capability, finalInvariant⟩ := source_trace_capability source writer sendOrigin receiveOrigin sender decode trace invariant
  refine ⟨logged.2.1.2, transcript, trace, capability, finalInvariant, finalInvariant.spent_nodup,
    trace.history_length, ?_⟩
  intro predicate budget bounded
  have counted := logged_run_count source writer sender decode client predicate budget bounded ((initial, spent), []) logged supported
  simp only [List.nil_append] at history
  simpa only [history, queryCount, List.countP_nil, Nat.zero_add] using counted

open BeaconcryptCore.Refinement.PqxdhConcreteSession

/-- Either actual oriented source initializer supplies the empty-history invariant for the counted public/record trace. -/
theorem initialized_capability {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (root : Std.Array Std.U8 32#usize) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result)
    (initial : RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary)
    (initialized : initializeBeacon root (RawCtxSourceHkdf.initialResponse source.crypto) = ok initial.1.owner.kernel ∨
      initializeServer root (RawCtxSourceHkdf.initialResponse source.crypto) = ok initial.1.owner.kernel)
    (result : Result × (RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary))
    (actual : result ∈ support ((simulateQ (originalImpl source writer sender decode) client).run initial)) :
    ∃ finalSpent transcript,
      SourceTrace source writer sender decode (initial, []) transcript (result.2, finalSpent) ∧
      CapabilityTrace source writer initial.1.owner.kernel.refined.send_chain initial.1.owner.kernel.refined.receive_chain
        initial.1.owner.expectedSender sender initial.1.owner.associatedData decode
        (project (initial, [])) transcript (project (result.2, finalSpent)) ∧
      ConsumedRefines source.crypto initial.1.owner.kernel.refined.send_chain
        initial.1.owner.kernel.refined.receive_chain result.2.1.owner.kernel finalSpent ∧
      finalSpent.Nodup ∧ finalSpent.length ≤ queryCount rawRequest transcript ∧
      ∀ predicate budget, client.IsQueryBoundP (fun query => predicate query = true) budget →
        queryCount predicate transcript ≤ budget := by
  simpa only [List.length_nil, Nat.zero_add] using source_capability_counted source writer _ _ sender decode
    client initial [] (initialized_spent source.crypto root initial.1.owner.kernel initialized) result actual

/-- Erasing the private monitor preserves every selective underlying uniform-query budget of the complete original computation. -/
theorem logged_query_bounds {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (state : SourceState Metadata Auxiliary × Transcript)
    (predicate : unifSpec.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    ((simulateQ (loggedImpl source writer sender decode) client).run state).IsQueryBoundP predicate budget ↔
      ((simulateQ (originalImpl source writer sender decode) client).run state.1.1).IsQueryBoundP predicate budget := by
  rw [← logged_run_erasure source writer sender decode client state, isQueryBoundP_map_iff]

end BeaconcryptCore.Computational.RawCtxPositionPublicServices

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionPublicServices.public_hkdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionPublicServices.public_hkdf

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionPublicServices.public_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionPublicServices.public_hash

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionPublicServices.public_coin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionPublicServices.public_coin

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionPublicServices.source_step_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionPublicServices.source_step_erasure

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionPublicServices.source_step_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionPublicServices.source_step_invariant

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionPublicServices.source_step_capability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionPublicServices.source_step_capability

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionPublicServices.source_step_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionPublicServices.source_step_metadata

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionPublicServices.source_trace_capability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionPublicServices.source_trace_capability

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionPublicServices.logged_step_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionPublicServices.logged_step_erasure

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionPublicServices.logged_run_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionPublicServices.logged_run_erasure

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionPublicServices.logged_run_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionPublicServices.logged_run_trace

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionPublicServices.source_supported_capability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionPublicServices.source_supported_capability

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionPublicServices.logged_run_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionPublicServices.logged_run_count

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionPublicServices.source_step_growth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionPublicServices.source_step_growth

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionPublicServices.SourceTrace.metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionPublicServices.SourceTrace.metadata

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionPublicServices.SourceTrace.history_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionPublicServices.SourceTrace.history_length

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionPublicServices.source_capability_counted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionPublicServices.source_capability_counted

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionPublicServices.initialized_capability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionPublicServices.initialized_capability

/--
info: 'BeaconcryptCore.Computational.RawCtxPositionPublicServices.logged_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionPublicServices.logged_query_bounds
