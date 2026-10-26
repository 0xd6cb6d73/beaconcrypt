import BeaconcryptCore.Computational.RawCtxMixedShared

/-!
This module connects each actual source-selected sealing capability to the existing typed CTX sealing computation on the same shared commitment cache. The key and nonce come from the owning source material, while AD, prepared sequence, encoded sender and caller plaintext stay unchanged. Under the already explicit total functional AEAD/ROM interpretation, the source's AEAD-first ordering produces the same typed protected record and then invokes the same optional frame writer. Writer failure retains the real hash poststate. Both exact source embeddings into the common mixed handler are preserved; no independent sealing table is introduced.

All eleven statements are functional source equalities or query bounds. The all-input presentation retains AD-width rejection; simplifying the pure total AEAD result in that branch is not an equality of arbitrary native error traces or a claim that local sealing work is free. The exact OracleComp equality lifts through arbitrary stateful interpreters and continuations before probability evaluation. One reached seal issues at most one shared hash request and at most sixty-four byte-valued uniform draws, including a subsequent failed writer. Local AEAD, byte construction, copying and codec work remain real work.

The endpoint here is the existing ctxSeal computation, before any nonce-freshness gate or security-game history instrumentation. No repeated-nonce rejection, uniform/independent selected key, per-key nonce invariant, fixed-key security transfer, shared-HKDF consistency, native codec implementation or global security result is inferred. Source-selected material may be correlated across owners or directions. Writer success does not imply default-reader availability, canonical encoding or injectivity; actual successful decode provenance has its separate functional codec contract. Inherited noncomputable source normalizers are not compiled runtime realizations. Source schedules, explicit client coins/reveals, initialization and multi-owner freshness/declassification still require their own checked composition.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
open PqxdhRefinement BeaconcryptCore.Refinement.RepresentationBridge
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxCanonicalSeal
open CtxRomAuth

def sourceKey (input : RawCtxSourceSend.SealInput) : CtxKey :=
  ⟨(absMaterial input.material).1, by simp [absMaterial]⟩

def sourceNonce (input : RawCtxSourceSend.SealInput) : CtxNonce :=
  ⟨(absMaterial input.material).2, by simp [absMaterial]⟩

def sourceContext (input : RawCtxSourceSend.SealInput)
    (had : input.context.associatedData.length = 281) : CtxRecordContext :=
  ⟨⟨input.context.associatedData, input.sequence.val, input.context.senderId.val⟩,
    had, input.sequence.bv.isLt, input.context.senderId.bv.isLt⟩

def sourceInput (input : RawCtxSourceSend.SealInput)
    (had : input.context.associatedData.length = 281) : CtxSealInput :=
  ⟨sourceNonce input, sourceContext input had, input.context.plaintext⟩

def recordFrame (input : RawCtxSourceSend.SealInput) (record : CtxRomRecord) :
    RawCtxReceive.DecodedFrame :=
  ⟨input.sequence, input.context.senderId, record.encode⟩

/-- This is the same explicit total functional AEAD/ROM interpretation used by the mixed source handler. -/
def romAdapter (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer) :
    QueryImpl RawCtxSourceSeal.SealSpec (OracleComp CtxRO)
  | .inl input => pure (some (c.aeadSeal input.key input.nonce input.associatedData input.plaintext))
  | .inr (.inl bytes) => do
      let digest ← CtxRO.query ((), bytes)
      pure (some digest.toList)
  | .inr (.inr frame) => pure (writer frame)

/-- The commitment uses the actual selected material and public context, with no distribution assumption. -/
theorem hashInput_exact (input : RawCtxSourceSend.SealInput)
    (had : input.context.associatedData.length = 281) (tag : Pqxdh.Bytes) :
    RawCtxSourceSeal.hashInput input tag =
      outerInput (sourceKey input) (sourceNonce input) (sourceContext input had) tag := by
  rfl

/-- The typed output keeps all actual frame fields and the exact protected payload. -/
theorem recordFrame_fields (input : RawCtxSourceSend.SealInput) (record : CtxRomRecord) :
    (recordFrame input record).sequence = input.sequence ∧
      (recordFrame input record).sender = input.context.senderId ∧
      (recordFrame input record).payload = record.encode ∧
      Pqxdh.decodeRecord (recordFrame input record).payload = some record.toRecordCipher := by
  exact ⟨rfl, rfl, rfl, decodeRecord_romRecord record⟩

/-- Actual source sealing equals the existing typed CTX computation followed by the unchanged optional writer. -/
theorem sealInput_typed (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxSourceSend.SealInput) (had : input.context.associatedData.length = 281) :
    simulateQ (romAdapter c writer) (RawCtxSourceSeal.sealInput input) = (do
      let record ← ctxSeal c (sourceKey input) (sourceInput input had)
      pure (writer (recordFrame input record))) := by
  simp [RawCtxSourceSeal.sealInput, romAdapter, OracleSpec.query,
    RawCtxSourceSeal.aeadInput, had, c.aeadSeal_tag_length,
    ctxSeal, sourceKey, sourceNonce, sourceInput, sourceContext, outerInput,
    RawCtxSourceSeal.hashInput, recordFrame, CtxRomRecord.encode,
    CtxRomRecord.toRecordCipher, Pqxdh.RecordCipher.encode, RawCtxSourceSeal.frame]

/-- Invalid associated-data width still rejects under the stated total functional AEAD interpretation. -/
theorem sealInput_invalid (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxSourceSend.SealInput) (had : input.context.associatedData.length ≠ 281) :
    simulateQ (romAdapter c writer) (RawCtxSourceSeal.sealInput input) = pure none := by
  simp [RawCtxSourceSeal.sealInput, romAdapter, OracleSpec.query, had]

/-- The native sealing requests use the actual common mixed handler, with no second primitive cache. -/
noncomputable def sharedImpl {Auxiliary : Type} (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)) :
    QueryImpl RawCtxSourceSeal.SealSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  (RawCtxMixedShared.sharedImpl c writer kdf ∘ₛ RawCtxMixedOwner.sendLift) ∘ₛ
    RawCtxSourceSeal.sealLift

/-- The full source result and cache match the same typed-ROM query, with all auxiliary state retained. -/
theorem shared_step {Auxiliary : Type} (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (query : RawCtxSourceSeal.SealSpec.Domain) (auxiliary : Auxiliary) (cache : CtxRO.QueryCache) :
    (sharedImpl c writer kdf query).run (auxiliary, cache) =
      (fun result => (result.1, (auxiliary, result.2))) <$>
        (simulateQ ctxRandomOracle (romAdapter c writer query)).run cache := by
  rcases query with input | (bytes | frame)
  all_goals simp [sharedImpl, QueryImpl.compose, RawCtxSourceSeal.sealLift,
    RawCtxMixedOwner.sendLift, OracleSpec.query, romAdapter]
  · exact RawCtxMixedShared.shared_sealing c writer kdf input (auxiliary, cache)
  · convert RawCtxMixedShared.shared_hash c writer kdf bytes (auxiliary, cache) using 1
    simp [map_eq_bind_pure_comp, ctxRandomOracle, QueryImpl.withCaching]
  · exact RawCtxMixedShared.shared_writing c writer kdf frame (auxiliary, cache)

/-- Arbitrary sealing continuations retain the full shared cache, including a miss followed by writer failure. -/
theorem shared_complete {Auxiliary Result : Type} (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (client : OracleComp RawCtxSourceSeal.SealSpec Result)
    (auxiliary : Auxiliary) (cache : CtxRO.QueryCache) :
    (simulateQ (sharedImpl c writer kdf) client).run (auxiliary, cache) =
      (fun result => (result.1, (auxiliary, result.2))) <$>
        (simulateQ ctxRandomOracle (simulateQ (romAdapter c writer) client)).run cache := by
  simpa only [QueryImpl.simulateQ_compose, _root_.Prod.map_def, id_eq] using
    (OracleComp.map_run_simulateQ_eq_of_query_map_eq
      (ctxRandomOracle ∘ₛ romAdapter c writer) (sharedImpl c writer kdf)
      (fun state => (auxiliary, state))
      (fun query state => (shared_step c writer kdf query auxiliary state).symm) client cache).symm

/-- A reached source seal produces the existing canonical CTX record and actual optional writer result on the same complete cache. -/
theorem shared_seal {Auxiliary : Type} (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (input : RawCtxSourceSend.SealInput) (had : input.context.associatedData.length = 281)
    (auxiliary : Auxiliary) (cache : CtxRO.QueryCache) :
    (simulateQ (sharedImpl c writer kdf) (RawCtxSourceSeal.sealInput input)).run (auxiliary, cache) = (do
      let result ← (simulateQ ctxRandomOracle
        (ctxSeal c (sourceKey input) (sourceInput input had))).run cache
      pure (writer (recordFrame input result.1), (auxiliary, result.2))) := by
  rw [shared_complete, sealInput_typed c writer input had]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    map_bind, map_pure]

/-- This total source presentation keeps the actual AD-width rejection and optional frame writer. -/
def typedSource (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxSourceSend.SealInput) : OracleComp CtxRO (Option Pqxdh.Bytes) :=
  if had : input.context.associatedData.length = 281 then do
    let record ← ctxSeal c (sourceKey input) (sourceInput input had)
    pure (writer (recordFrame input record))
  else pure none

/-- The source-to-typed equality covers every input, without assuming the selected owner has valid AD. -/
theorem sealInput_complete (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxSourceSend.SealInput) :
    simulateQ (romAdapter c writer) (RawCtxSourceSeal.sealInput input) =
      typedSource c writer input := by
  unfold typedSource
  split
  · exact sealInput_typed c writer input ‹_›
  · exact sealInput_invalid c writer input ‹_›

/-- Equality holds before arbitrary interpretation, so later source work receives the same optional bytes and complete state. -/
theorem sealInput_continuation {Result PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl CtxRO (StateT PrimitiveState (OracleComp base)))
    (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer) (input : RawCtxSourceSend.SealInput)
    (next : Option Pqxdh.Bytes → StateT PrimitiveState (OracleComp base) Result)
    (state : PrimitiveState) :
    ((simulateQ impl (simulateQ (romAdapter c writer) (RawCtxSourceSeal.sealInput input))) >>= next).run state =
      ((simulateQ impl (typedSource c writer input)) >>= next).run state := by
  rw [sealInput_complete]

/-- The existing CTX computation performs one shared hash request; primitive sealing and encoding work remain local. -/
theorem typedSource_query_bound (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxSourceSend.SealInput) :
    (typedSource c writer input).IsTotalQueryBound 1 := by
  unfold typedSource
  split
  · simp only [ctxSeal, bind_assoc, pure_bind]
    rw [isTotalQueryBound_query_bind_iff]
    exact ⟨by omega, fun _ => True.intro⟩
  · trivial

/-- The actual shared cache charges at most 64 byte draws for the reached seal, including a subsequent writer failure. -/
theorem shared_seal_uniform {Auxiliary : Type} (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (input : RawCtxSourceSend.SealInput) (auxiliary : Auxiliary) (cache : CtxRO.QueryCache) :
    ((simulateQ (sharedImpl c writer kdf) (RawCtxSourceSeal.sealInput input)).run
      (auxiliary, cache)).IsTotalQueryBound 64 := by
  rw [shared_complete, sealInput_complete]
  unfold typedSource
  split
  · simp only [ctxSeal, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind, map_bind, map_pure]
    simp only [bind_pure_comp]
    unfold IsTotalQueryBound
    rw [isQueryBound_map_iff]
    exact CtxComputationalSecurity.ctxRandomOracle_total_query_bound _ cache
  · simp only [simulateQ_pure, StateT.run_pure, map_pure]
    trivial

end BeaconcryptCore.Computational.RawCtxCanonicalSeal

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalSeal.hashInput_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalSeal.hashInput_exact

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalSeal.recordFrame_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalSeal.recordFrame_fields

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalSeal.sealInput_typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalSeal.sealInput_typed

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalSeal.sealInput_invalid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalSeal.sealInput_invalid

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalSeal.shared_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalSeal.shared_step

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalSeal.shared_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalSeal.shared_complete

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalSeal.shared_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalSeal.shared_seal

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalSeal.sealInput_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalSeal.sealInput_complete

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalSeal.sealInput_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalSeal.sealInput_continuation

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalSeal.typedSource_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalSeal.typedSource_query_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalSeal.shared_seal_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalSeal.shared_seal_uniform
