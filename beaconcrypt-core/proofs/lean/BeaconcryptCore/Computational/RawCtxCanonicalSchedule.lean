import BeaconcryptCore.Computational.RawCtxSharedPrimitive
import BeaconcryptCore.Computational.RawCtxOpeningOccurrence

/-!
The actual complete raw-only owner schedule is interpreted by source-selected canonical openings. Each reached opening derives its key and nonce from the actual prepared source material, and its normalized decoder retains the same raw bytes, decoded frame and owner context. The occurrence theorem supplies this scope before any optional reply, including failed commitments and AEAD rejection. The concrete handler equalities are proved here; there is no assumed successful plaintext, fresh key, honest target or desired protocol conclusion.

An annotated source interpreter executes every original KDF/hash/AEAD computation and retains its full auxiliary state and cache before adding canonical bookkeeping. Exact query and arbitrary-continuation projections erase only that bookkeeping. A separate canonical interpreter uses the unchanged actual KDF and invokes canonicalRaw with a key and decoder selected for each reached opening. Its complete raw schedule is equal to the annotated source schedule. The final source projection therefore retains original client result, actual optional API replies through the continuation, complete owner and complete primitive state, including all failed cache effects.

The uniform-oracle cap remains kdfCoins*qKdf + 64*qRaw with explicit actual aggregate KDF and per-callback bounds. This equality concerns the full OracleComp computation, not merely its output distribution, so pure instrumentation adds no hidden randomness. Native functional/total-ROM contracts, actual HKDF/cache consistency and local primitive/byte/cache work remain explicit. The canonical attempt counter is per reached opening, while the original owner's raw counter counts every API attempt; KDF and earlier rejection paths are unchanged.

This is an exact functional composition for source-selected evolving material, not a transfer of a one-key security theorem to a fixed global key. The retained canonical history and private state are analysis instrumentation and not new adversary capabilities. Correlated-key/session security, arbitrary interleaved sends/reveals/multiple owners, source codec/runtime/persistence/CAS contracts, API plaintext declassification and the final computational-symbolic experiment remain separate obligations. No primitive implementation or new security assumption is introduced.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxCanonicalSchedule
open CtxRomAuth RawCtxSourceOpen RawCtxCanonicalOpening RawCtxSharedPrimitive
open AdaptiveCtxCanonical

abbrev AnnotatedState (Auxiliary : Type) := Auxiliary × CanonicalState

/-- Erase only added canonical bookkeeping while retaining the actual auxiliary state and whole cache. -/
def erase {Auxiliary : Type} (state : AnnotatedState Auxiliary) : SharedState Auxiliary :=
  (state.1, state.2.ctx.cache)

/-- A KDF callback updates only the cache projection of canonical instrumentation. -/
def withCache (state : CanonicalState) (cache : CtxRO.QueryCache) : CanonicalState :=
  { state with ctx := { state.ctx with cache := cache } }

/-- Record this reached shaped opening after the actual source work, retaining all previous histories. -/
noncomputable def recordOpening (input : RawCtxWholeOwner.OpenInput)
    (state : CanonicalState) (cache : CtxRO.QueryCache) : CanonicalState :=
  match hslices : RawCtxFrameDecoding.fromPayload input.context.frame.payload with
  | none => withCache state cache
  | some slices =>
      if had : input.context.associatedData.length = 153 then
        afterOpening state (selectedTarget input slices hslices had) cache
      else withCache state cache

/-- Bookkeeping never changes the actual returned cache. -/
theorem recordOpening_cache (input : RawCtxWholeOwner.OpenInput)
    (state : CanonicalState) (cache : CtxRO.QueryCache) :
    (recordOpening input state cache).ctx.cache = cache := by
  unfold recordOpening
  split
  · rfl
  · split <;> rfl

/-- Run the original complete-state source query before adding pure opening bookkeeping. -/
noncomputable def annotatedImpl {Auxiliary : Type} (c : Pqxdh.Crypto)
    (kdf : QueryImpl KdfSpec (StateT (SharedState Auxiliary) ProbComp)) :
    QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT (AnnotatedState Auxiliary) ProbComp) :=
  fun query state => do
    let result ← ((nativeImpl c kdf ∘ₛ nativeAdapter) query).run (erase state)
    let next := match query with
      | .inl _ => withCache state.2 result.2.2
      | .inr input => recordOpening input state.2 result.2.2
    pure (result.1, (result.2.1, next))

/-- Erasing pure instrumentation preserves each complete actual primitive query. -/
theorem annotated_query {Auxiliary : Type} (c : Pqxdh.Crypto)
    (kdf : QueryImpl KdfSpec (StateT (SharedState Auxiliary) ProbComp))
    (query : RawCtxWholeOwner.PrimitiveSpec.Domain) (state : AnnotatedState Auxiliary) :
    (Prod.map id erase) <$> (annotatedImpl c kdf query).run state =
      ((nativeImpl c kdf ∘ₛ nativeAdapter) query).run (erase state) := by
  simp only [annotatedImpl, StateT.run, map_bind, map_pure]
  cases query with
  | inl request => simp [erase, withCache]
  | inr input => simp [erase, recordOpening_cache]

/-- Arbitrary adaptive primitive continuations retain their original result and complete source state. -/
theorem annotated_complete {Auxiliary Result : Type} (c : Pqxdh.Crypto)
    (kdf : QueryImpl KdfSpec (StateT (SharedState Auxiliary) ProbComp))
    (client : OracleComp RawCtxWholeOwner.PrimitiveSpec Result) (state : AnnotatedState Auxiliary) :
    (Prod.map id erase) <$> (simulateQ (annotatedImpl c kdf) client).run state =
      (simulateQ (nativeImpl c kdf ∘ₛ nativeAdapter) client).run (erase state) := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (annotatedImpl c kdf) (nativeImpl c kdf ∘ₛ nativeAdapter) erase
    (annotated_query c kdf) client state

/-- The serialized raw owner transition preserves actual optional reply and both complete states. -/
theorem annotated_owner {Metadata Auxiliary : Type} (c : Pqxdh.Crypto)
    (kdf : QueryImpl KdfSpec (StateT (SharedState Auxiliary) ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata × AnnotatedState Auxiliary) :
    (Prod.map id (Prod.map id erase)) <$>
      (RawCtxWholeOwner.ownerImpl (annotatedImpl c kdf) decode raw).run state =
      (RawCtxWholeOwner.ownerImpl (nativeImpl c kdf ∘ₛ nativeAdapter) decode raw).run
        (state.1, erase state.2) := by
  have complete := congrArg (fun computation =>
    (fun result => (result.1.1, (result.1.2, result.2))) <$> computation)
    (annotated_complete c kdf ((RawCtxWholeOwner.rawReceive decode raw).run state.1) state.2)
  simpa only [RawCtxWholeOwner.ownerImpl, StateT.run, RawCtxWholeOwner.rawGame,
    bind_pure_comp, Functor.map_map, Prod.map_def, Function.comp_def, id_eq] using complete

/-- The entire adaptive raw-only source schedule is preserved after bookkeeping erasure. -/
theorem annotated_schedule {Metadata Auxiliary Result : Type} (c : Pqxdh.Crypto)
    (kdf : QueryImpl KdfSpec (StateT (SharedState Auxiliary) ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp RawCtxWholeOwner.RawSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata × AnnotatedState Auxiliary) :
    (Prod.map id (Prod.map id erase)) <$>
      RawCtxWholeOwner.scheduleGame (annotatedImpl c kdf) decode client state =
      RawCtxWholeOwner.scheduleGame (nativeImpl c kdf ∘ₛ nativeAdapter) decode client
        (state.1, erase state.2) := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (RawCtxWholeOwner.ownerImpl (annotatedImpl c kdf) decode)
    (RawCtxWholeOwner.ownerImpl (nativeImpl c kdf ∘ₛ nativeAdapter) decode)
    (Prod.map id erase) (annotated_owner c kdf decode) client state

/-- Use actual KDF callbacks and select the canonical key/decoder anew from each source opening. -/
noncomputable def canonicalImpl {Auxiliary : Type} (c : Pqxdh.Crypto)
    (kdf : QueryImpl KdfSpec (StateT (SharedState Auxiliary) ProbComp))
    (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT (AnnotatedState Auxiliary) ProbComp) :=
  fun query state => match query with
  | .inl request => (annotatedImpl c kdf (.inl request)).run state
  | .inr input =>
      (fun result => (result.1, (state.1, result.2))) <$>
        canonicalRaw (selectedDecoder input.material input.context.frame.sender
          input.context.associatedData decode) c (sourceKey input) input.context.raw state.2

/-- Actual source slice and AD checks determine the exact reached-opening bookkeeping. -/
theorem recordOpening_selected (input : RawCtxWholeOwner.OpenInput)
    (slices : RawCtxFrameDecoding.Slices)
    (hslices : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices)
    (had : input.context.associatedData.length = 153)
    (state : CanonicalState) (cache : CtxRO.QueryCache) :
    recordOpening input state cache = afterOpening state (selectedTarget input slices hslices had) cache := by
  unfold recordOpening
  split
  · rename_i missing
    simp_all only [reduceCtorEq]
  · rename_i actual found
    have same := Option.some.inj (found.symm.trans hslices)
    subst actual
    rw [dif_pos had]

/-- The actual source-selected opening equals its concrete canonical handler before any reply is known. -/
theorem canonical_selected {Auxiliary : Type} (c : Pqxdh.Crypto)
    (kdf : QueryImpl KdfSpec (StateT (SharedState Auxiliary) ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (input : RawCtxWholeOwner.OpenInput)
    (expected : Std.U64)
    (hraw : input.context.raw.isEmpty = false)
    (hdecode : decode input.context.raw = some input.context.frame)
    (hvalid : RawCtxReceive.ValidFrame expected input.context.associatedData input.context.frame)
    (hsequence : input.sequence = input.context.frame.sequence) :
    annotatedImpl c kdf (.inr input) = canonicalImpl c kdf decode (.inr input) := by
  funext state
  obtain ⟨slices, hslices⟩ := (RawCtxFrameDecoding.fromPayload_some_iff _).mpr hvalid.2.1
  have ownValid : RawCtxReceive.ValidFrame input.context.frame.sender
      input.context.associatedData input.context.frame := ⟨rfl, hvalid.2⟩
  have decoder := selectedDecoder_source input slices hslices decode
    input.context.frame.sender hraw hdecode ownValid hsequence
  have equal := native_canonical_opening c kdf input slices hslices hvalid.2.2
    _ state.2 decoder state.1
  convert equal using 1 <;> first
  | rfl
  | simp only [annotatedImpl, QueryImpl.compose, nativeAdapter, StateT.run, erase,
      recordOpening_selected input slices hslices hvalid.2.2, bind_pure_comp]
    rfl

/-- Proved local equalities replace every reached opening in the complete adaptive owner schedule. -/
theorem canonical_schedule {Metadata Auxiliary Result : Type} (c : Pqxdh.Crypto)
    (kdf : QueryImpl KdfSpec (StateT (SharedState Auxiliary) ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp RawCtxWholeOwner.RawSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata × AnnotatedState Auxiliary) :
    RawCtxWholeOwner.scheduleGame (annotatedImpl c kdf) decode client state =
      RawCtxWholeOwner.scheduleGame (canonicalImpl c kdf decode) decode client state := by
  apply RawCtxOpeningOccurrence.rawSchedule_congr
  · intro request
    rfl
  · intro owner raw frame input hraw hdecode hvalid hsequence hcontext
    apply canonical_selected c kdf decode input owner.owner.expectedSender
    · simpa only [hcontext] using hraw
    · simpa only [hcontext] using hdecode
    · simpa only [hcontext] using hvalid
    · simpa only [hcontext] using hsequence

/-- Canonical source-selected scheduling projects exactly to the original owner and full primitive interpreter. -/
theorem canonical_source {Metadata Auxiliary Result : Type} (c : Pqxdh.Crypto)
    (kdf : QueryImpl KdfSpec (StateT (SharedState Auxiliary) ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp RawCtxWholeOwner.RawSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata × AnnotatedState Auxiliary) :
    (Prod.map id (Prod.map id erase)) <$>
      RawCtxWholeOwner.scheduleGame (canonicalImpl c kdf decode) decode client state =
      RawCtxWholeOwner.scheduleGame (nativeImpl c kdf ∘ₛ nativeAdapter) decode client
        (state.1, erase state.2) := by
  rw [← canonical_schedule]
  exact annotated_schedule c kdf decode client state

/-- Complete canonical scheduling retains the actual source KDF/hash uniform-oracle ledger. -/
theorem canonical_uniform {Metadata Auxiliary Result : Type} (c : Pqxdh.Crypto)
    (kdf : QueryImpl KdfSpec (StateT (SharedState Auxiliary) ProbComp)) (kdfCoins : Nat)
    (bounded : ∀ request state, ((kdf request).run state).IsTotalQueryBound kdfCoins)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp RawCtxWholeOwner.RawSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata × AnnotatedState Auxiliary)
    (qKdf qRaw : Nat) (rawQueries : client.IsTotalQueryBound qRaw)
    (kdfQueries : ((simulateQ (nativeOwnerImpl decode) client).run state.1).IsQueryBoundP
      (fun query => query.isLeft = true) qKdf) :
    (RawCtxWholeOwner.scheduleGame (canonicalImpl c kdf decode) decode client state).IsTotalQueryBound
      (kdfCoins * qKdf + 64 * qRaw) := by
  have source := sharedSchedule_uniform c kdf kdfCoins bounded decode client state.1
    (erase state.2) qKdf qRaw rawQueries kdfQueries
  rw [sharedSchedule_source] at source
  have actual : (RawCtxWholeOwner.scheduleGame (nativeImpl c kdf ∘ₛ nativeAdapter)
      decode client (state.1, erase state.2)).IsTotalQueryBound (kdfCoins * qKdf + 64 * qRaw) := by
    simpa only [IsTotalQueryBound, isQueryBound_map_iff] using source
  rw [← canonical_source c kdf decode client state] at actual
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using actual

end BeaconcryptCore.Computational.RawCtxCanonicalSchedule

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalSchedule.recordOpening_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalSchedule.recordOpening_cache

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalSchedule.annotated_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalSchedule.annotated_query

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalSchedule.annotated_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalSchedule.annotated_complete

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalSchedule.annotated_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalSchedule.annotated_owner

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalSchedule.annotated_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalSchedule.annotated_schedule

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalSchedule.recordOpening_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalSchedule.recordOpening_selected

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalSchedule.canonical_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalSchedule.canonical_selected

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalSchedule.canonical_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalSchedule.canonical_schedule

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalSchedule.canonical_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalSchedule.canonical_source

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalSchedule.canonical_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalSchedule.canonical_uniform
