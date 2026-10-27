import BeaconcryptCore.Computational.RawCtxSourceSend

/-!
This module expands the private source sealing capability into actual optional detached AEAD, commitment hashing and frame writing. It preserves production order: AEAD runs before the fallible AD/tag width conversions, then the optional unkeyed hash runs before serialization. Each failure keeps its actual complete primitive state. The commitment uses the existing extracted 357-byte builder, source-selected key/nonce, actual tag, 281-byte associated data, prepared sequence and encoded sender. The API target remains distinct from the encoded sender. Protected-payload reencoding requires the primitive tag16/commit64 width contracts and does not assert canonical Cap'n Proto serialization.

All eighteen statements are operational or query-accounting results. The arbitrary stateful interpreter may retain one shared cache for sealing and opening; no separate hash table, independent key distribution, security advantage or protocol conclusion is assumed. Each application send makes at most one KDF, AEAD, hash and writer call, and each category is bounded by qSend for an adaptive send-only schedule. Exact interpretation retains the complete owner and primitive state, including consumed send material after sealing failure. Successful source execution identifies the actual old-chain/fixed-label KDF reply and all three sealing replies in the same execution, with exactly the writer's returned ciphertext and final state.

The native primitive contracts supply ordinary perfect interface behavior, including tag/hash widths; optional failures and their effects stay explicit here. The functional frame writer remains a library/serialization boundary, and native allocation, traversal, compiler, physical erasure and timing are not proved. Empty plaintext is allowed at the inner primitive interface and rejected by the existing outer send owner. Native role handle/AD wiring, writer/reader representation, losslessness or primitive work costs inside these counted calls, mixed send/receive/reveal schedules, evolving-key/session selection and global cryptographic reductions remain separate obligations. No primitive implementation proof or independent random-table replacement is attempted.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp
open PqxdhRefinement BeaconcryptCore.Refinement.RepresentationBridge

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxSourceSeal

/-- Actual detached sealing arguments preserve the same selected key, nonce, AD and caller plaintext. -/
structure AeadInput where
  key : Pqxdh.Bytes
  nonce : Pqxdh.Bytes
  associatedData : Pqxdh.Bytes
  plaintext : Pqxdh.Bytes

/-- Native AEAD, optional commitment and frame serialization remain separate private effects. -/
abbrev SealSpec :=
  (AeadInput →ₒ Option (Pqxdh.Bytes × Pqxdh.Bytes)) +
    ((Pqxdh.Bytes →ₒ Option Pqxdh.Bytes) +
      (RawCtxReceive.DecodedFrame →ₒ Option Pqxdh.Bytes))

def aeadInput (input : RawCtxSourceSend.SealInput) : AeadInput :=
  ⟨(absMaterial input.material).1, (absMaterial input.material).2,
    input.context.associatedData, input.context.plaintext⟩

def hashInput (input : RawCtxSourceSend.SealInput) (tag : Pqxdh.Bytes) : Pqxdh.Bytes :=
  Pqxdh.ctxPreimage (absMaterial input.material)
    ⟨input.context.associatedData, input.sequence.val, input.context.senderId.val⟩ tag

/-- The encoded frame carries the sender; the API target remains outside this record. -/
def frame (input : RawCtxSourceSend.SealInput) (body tag commitment : Pqxdh.Bytes) :
    RawCtxReceive.DecodedFrame :=
  ⟨input.sequence, input.context.senderId, body ++ tag ++ commitment⟩

/-- Source order is AEAD, fallible AD/tag conversion, optional hash, append, and optional frame writer. -/
def sealInput (input : RawCtxSourceSend.SealInput) : OracleComp SealSpec (Option Pqxdh.Bytes) := do
  let sealed ← SealSpec.query (.inl (aeadInput input))
  match sealed with
  | none => pure none
  | some (body, tag) =>
      if input.context.associatedData.length = 281 then
        if tag.length = 16 then do
          let digest ← SealSpec.query (.inr (.inl (hashInput input tag)))
          match digest with
          | none => pure none
          | some commitment => SealSpec.query (.inr (.inr (frame input body tag commitment)))
        else pure none
      else pure none

/-- Every successful frame output comes from all three actual callbacks in source order and the same final state. -/
theorem sealInput_success {PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl SealSpec (StateT PrimitiveState (OracleComp base)))
    (input : RawCtxSourceSend.SealInput) (primitive finalState : PrimitiveState)
    (ciphertext : Pqxdh.Bytes)
    (hsupport : (some ciphertext, finalState) ∈ support ((simulateQ impl (sealInput input)).run primitive)) :
    ∃ body tag afterAead commitment afterHash,
      (some (body, tag), afterAead) ∈ support ((impl (.inl (aeadInput input))).run primitive) ∧
      input.context.associatedData.length = 281 ∧ tag.length = 16 ∧
      (some commitment, afterHash) ∈ support ((impl (.inr (.inl (hashInput input tag)))).run afterAead) ∧
      (some ciphertext, finalState) ∈ support
        ((impl (.inr (.inr (frame input body tag commitment)))).run afterHash) := by
  rw [sealInput, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hsupport
  obtain ⟨⟨sealed, afterAead⟩, haead, htail⟩ := hsupport
  cases sealed with
  | none => simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at htail
  | some pair =>
      rcases pair with ⟨body, tag⟩
      dsimp only at htail
      split at htail
      · rename_i had
        split at htail
        · rename_i htag
          rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at htail
          obtain ⟨⟨digest, afterHash⟩, hhash, hwrite⟩ := htail
          cases digest with
          | none => simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at hwrite
          | some commitment =>
              refine ⟨body, tag, afterAead, commitment, afterHash, haead, had, htag, hhash, ?_⟩
              simp [OracleSpec.query] at hwrite
              exact hwrite
        · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at htail
      · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at htail

inductive CallKind where
  | aead
  | hash
  | writer
  deriving DecidableEq

def callKind : SealSpec.Domain → CallKind
  | .inl _ => .aead
  | .inr (.inl _) => .hash
  | .inr (.inr _) => .writer

/-- Each actual inner interface is invoked at most once, including every failure branch. -/
theorem sealInput_bound (input : RawCtxSourceSend.SealInput) (kind : CallKind) :
    (sealInput input).IsQueryBoundP (fun query => callKind query = kind) 1 := by
  rw [sealInput, isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr (by decide), fun sealed => ?_⟩
  cases sealed with
  | none => simp
  | some pair =>
      rcases pair with ⟨body, tag⟩
      dsimp only
      split
      · split
        · rw [isQueryBoundP_query_bind_iff]
          refine ⟨?_, fun digest => ?_⟩
          · cases kind <;> simp [callKind]
          · cases digest with
            | none => simp
            | some commitment =>
                apply (isQueryBoundP_query_iff (spec := SealSpec)
                  (p := fun query => callKind query = kind) (.inr (.inr (frame input body tag commitment))) _).2
                cases kind <;> simp [callKind]
        · simp
      · simp

/-- The sealing commitment is exactly the extracted 357-byte builder at the source fields. -/
theorem hashInput_extracted (input : RawCtxSourceSend.SealInput) (tagBytes : Pqxdh.Bytes)
    (ad : Std.Array Std.U8 281#usize) (tag : Std.Array Std.U8 16#usize)
    (had : absBytes ad = input.context.associatedData) (htag : absBytes tag = tagBytes) :
    ∃ transcript, commitment.build_commitment_transcript input.material.key.bytes
      input.material.nonce.bytes ad tag input.sequence input.context.senderId = ok transcript ∧
      absBytes transcript.bytes = hashInput input tagBytes := by
  simpa only [hashInput, absMaterial, had, htag] using
    build_commitment_transcript_abs input.material.key.bytes input.material.nonce.bytes ad tag
      input.sequence input.context.senderId

/-- Source width checks produce exactly the commitment interface's input size. -/
theorem hashInput_length (input : RawCtxSourceSend.SealInput) (tag : Pqxdh.Bytes)
    (had : input.context.associatedData.length = 281) (htag : tag.length = 16) :
    (hashInput input tag).length = 357 := by
  simp [hashInput, Pqxdh.ctxPreimage, absMaterial, had, htag]

/-- Writer arguments retain the original detached body/tag and hash output with exact source metadata. -/
theorem frame_fields (input : RawCtxSourceSend.SealInput) (body tag commitment : Pqxdh.Bytes) :
    (frame input body tag commitment).sequence = input.sequence ∧
      (frame input body tag commitment).sender = input.context.senderId ∧
      (frame input body tag commitment).payload = body ++ tag ++ commitment := by
  exact ⟨rfl, rfl, rfl⟩

/-- Protected record decoding preserves all three actual callback outputs under their primitive width contracts. -/
theorem frame_record (input : RawCtxSourceSend.SealInput) (body tag commitment : Pqxdh.Bytes)
    (htag : tag.length = 16) (hcommit : commitment.length = 64) :
    Pqxdh.decodeRecord (frame input body tag commitment).payload = some ⟨body, tag, commitment⟩ :=
  Pqxdh.decodeRecord_encode ⟨body, tag, commitment⟩ htag hcommit

/-- The complete private interpreter retains the real state after AEAD, hash and writer failure alike. -/
theorem sealInput_run {PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl SealSpec (StateT PrimitiveState (OracleComp base)))
    (input : RawCtxSourceSend.SealInput) (primitive : PrimitiveState) :
    (simulateQ impl (sealInput input)).run primitive = (do
      let sealed ← (impl (.inl (aeadInput input))).run primitive
      match sealed.1 with
      | none => pure (none, sealed.2)
      | some (body, tag) =>
          if input.context.associatedData.length = 281 then
            if tag.length = 16 then do
              let digest ← (impl (.inr (.inl (hashInput input tag)))).run sealed.2
              match digest.1 with
              | none => pure (none, digest.2)
              | some commitment => (impl (.inr (.inr (frame input body tag commitment)))).run digest.2
            else pure (none, sealed.2)
          else pure (none, sealed.2)) := by
  rw [sealInput, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  apply bind_congr
  rintro ⟨sealed, afterAead⟩
  cases sealed with
  | none => simp only [simulateQ_pure, StateT.run_pure]
  | some pair =>
      rcases pair with ⟨body, tag⟩
      dsimp only
      split_ifs
      · rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
        apply bind_congr
        rintro ⟨digest, afterHash⟩
        cases digest <;> simp [OracleSpec.query]
      all_goals simp only [simulateQ_pure, StateT.run_pure]

/-- Source KDF work stays separate from all three concrete sealing effects. -/
abbrev NativeSpec := (SymmetricRatchetKdfRequest →ₒ RatchetKdfResponse) + SealSpec

def sealLift : QueryImpl SealSpec (OracleComp NativeSpec) :=
  fun query => liftM (NativeSpec.query (.inr query))

def sealingPredicate (p : SealSpec.Domain → Bool) : NativeSpec.Domain → Bool
  | .inl _ => false
  | .inr query => p query

/-- The private embedding preserves the actual inner effect category and its count. -/
theorem sealLift_bound {α : Type} (p : SealSpec.Domain → Bool)
    (source : OracleComp SealSpec α) (bound : Nat)
    (hbound : source.IsQueryBoundP (fun query => p query = true) bound) :
    (simulateQ sealLift source).IsQueryBoundP
      (fun query => sealingPredicate p query = true) bound := by
  apply RawCtxSourceOpen.simulate_bound sealLift _ _ source bound hbound
  intro query
  exact (isQueryBoundP_query_iff (spec := NativeSpec)
    (p := fun query => sealingPredicate p query = true) (.inr query) _).2 (by
      simp only [sealingPredicate]
      split_ifs <;> simp_all)

/-- Inner sealing cannot issue a source ratchet KDF query. -/
theorem sealLift_no_kdf {α : Type} (source : OracleComp SealSpec α) :
    (simulateQ sealLift source).IsQueryBoundP (fun query => query.isLeft = true) 0 := by
  apply RawCtxSourceOpen.simulate_bound sealLift (fun _ => False) _ source 0
    (isQueryBoundP_false source 0)
  exact fun query => (isQueryBoundP_query_iff (spec := NativeSpec)
    (p := fun query => query.isLeft = true) (.inr query) 0).2 (by simp)

/-- The source-selected seal expands to concrete effects; KDF requests keep their exact argument. -/
def nativeAdapter : QueryImpl RawCtxSourceSend.PrimitiveSpec (OracleComp NativeSpec)
  | .inl request => liftM (NativeSpec.query (.inl request))
  | .inr input => simulateQ sealLift (sealInput input)

/-- Expanding sealing retains the source KDF ledger under every optional callback reply. -/
theorem nativeAdapter_kdf_bound {α : Type}
    (source : OracleComp RawCtxSourceSend.PrimitiveSpec α) (bound : Nat)
    (hbound : source.IsQueryBoundP (fun query => query.isLeft = true) bound) :
    (simulateQ nativeAdapter source).IsQueryBoundP (fun query => query.isLeft = true) bound := by
  apply RawCtxSourceOpen.simulate_bound nativeAdapter _ _ source bound hbound
  intro query
  cases query with
  | inl request =>
      exact (isQueryBoundP_query_iff (spec := NativeSpec)
        (p := fun query => query.isLeft = true) (.inl request) 1).2 (by simp)
  | inr input =>
      exact sealLift_no_kdf (sealInput input)

/-- A sealing category counts no source KDF query. -/
def category (kind : CallKind) : NativeSpec.Domain → Bool :=
  sealingPredicate (fun query => decide (callKind query = kind))

/-- Every private seal invocation accounts for each concrete inner operation at most once. -/
theorem nativeAdapter_seal_bound {α : Type}
    (source : OracleComp RawCtxSourceSend.PrimitiveSpec α) (bound : Nat)
    (hbound : source.IsQueryBoundP (fun query => query.isLeft = false) bound)
    (kind : CallKind) :
    (simulateQ nativeAdapter source).IsQueryBoundP (fun query => category kind query = true) bound := by
  apply RawCtxSourceOpen.simulate_bound nativeAdapter _ _ source bound hbound
  intro query
  cases query with
  | inl request =>
      exact (isQueryBoundP_query_iff (spec := NativeSpec)
        (p := fun query => category kind query = true) (.inl request) 0).2 (by
          simp [category, sealingPredicate])
  | inr input =>
      apply sealLift_bound
      simp only [Sum.isLeft, ↓reduceIte, decide_eq_true_eq]
      exact sealInput_bound input kind

/-- One application send pays separately for KDF, AEAD, hash and frame writing, including rejection and failure. -/
theorem nativeSend_bounds {Metadata : Type} (senderId : Std.U64) (plaintext : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) :
    let program := simulateQ nativeAdapter ((RawCtxSourceSend.sendOwner senderId plaintext).run state)
    program.IsQueryBoundP (fun query => query.isLeft = true) 1 ∧
      ∀ kind, program.IsQueryBoundP (fun query => category kind query = true) 1 := by
  exact ⟨nativeAdapter_kdf_bound _ 1 (RawCtxSourceSend.sendOwner_bound senderId plaintext state true),
    fun kind => nativeAdapter_seal_bound _ 1
      (RawCtxSourceSend.sendOwner_bound senderId plaintext state false) kind⟩

/-- One whole owner serializes application sends while all concrete effects stay in the enclosing program. -/
noncomputable def nativeApplicationImpl {Metadata : Type} (senderId : Std.U64) :
    QueryImpl RawCtxSourceSend.ApplicationSpec
      (StateT (RawCtxWholeOwner.OwnerState Metadata) (OracleComp NativeSpec)) :=
  fun plaintext state => simulateQ nativeAdapter ((RawCtxSourceSend.sendOwner senderId plaintext).run state)

/-- Every adaptive send-only schedule has four separately charged qSend interface caps. -/
theorem nativeSchedule_bounds {Metadata Result : Type} (senderId : Std.U64)
    (client : OracleComp RawCtxSourceSend.ApplicationSpec Result) (qSend : Nat)
    (hbound : client.IsTotalQueryBound qSend) (state : RawCtxWholeOwner.OwnerState Metadata) :
    let program := (simulateQ (nativeApplicationImpl senderId) client).run state
    program.IsQueryBoundP (fun query => query.isLeft = true) qSend ∧
      ∀ kind, program.IsQueryBoundP (fun query => category kind query = true) qSend := by
  have hb : client.IsQueryBoundP (fun _ => True) qSend := hbound.isQueryBoundP
  exact ⟨hb.simulateQ_run_StateT_of_step
    (fun plaintext owner => (nativeSend_bounds senderId plaintext owner).1) state,
    fun kind => hb.simulateQ_run_StateT_of_step
      (fun plaintext owner => (nativeSend_bounds senderId plaintext owner).2 kind) state⟩

/-- Full-state flattening equates the concrete counted handler with the existing source send game. -/
theorem nativeOwner_interpretation {Metadata PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Std.U64) :
    (impl.mapStateTBase (nativeApplicationImpl (Metadata := Metadata) senderId)).flattenStateT =
      RawCtxSourceSend.ownerImpl (impl ∘ₛ nativeAdapter) senderId := by
  funext plaintext state
  simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run, StateT.mk,
    nativeApplicationImpl, RawCtxSourceSend.ownerImpl, RawCtxSourceSend.sendGame,
    ← QueryImpl.simulateQ_compose, bind_pure_comp]

/-- Adaptive send interpretation retains the exact API replies, whole owner and every primitive effect. -/
theorem nativeSchedule_interpretation {Metadata PrimitiveState Result : Type}
    {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Std.U64) (client : OracleComp RawCtxSourceSend.ApplicationSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata) (primitive : PrimitiveState) :
    (simulateQ impl ((simulateQ (nativeApplicationImpl senderId) client).run state)).run primitive =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (RawCtxSourceSend.ownerImpl (impl ∘ₛ nativeAdapter) senderId) client).run
          (state, primitive) := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT, nativeOwner_interpretation]

/-- Embedding forwards the same request to the same complete primitive interpreter. -/
theorem sealLift_apply {PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (query : SealSpec.Domain) :
    (impl ∘ₛ sealLift) query = impl (.inr query) := by
  simp [QueryImpl.compose, sealLift, OracleSpec.query]

/-- The actual optional API output contains the writer's ciphertext, with the target route kept separate from sender metadata. -/
theorem adapter_success_primitives {PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (pending : SendSeal RawCtxSourceSend.SealContext)
    (primitive finalState : PrimitiveState) (message : RawCtxSourceSend.Encrypted)
    (hsupport : (some message, finalState) ∈ support
      (((impl ∘ₛ nativeAdapter ∘ₛ RawCtxSourceSend.adapter) (.inr pending)).run primitive)) :
    let input := RawCtxSourceSend.arguments pending
    ∃ body tag afterAead commitment afterHash,
      message = RawCtxSourceSend.encrypted input message.ciphertext ∧
      (some (body, tag), afterAead) ∈ support
        ((impl (.inr (.inl (aeadInput input)))).run primitive) ∧
      input.context.associatedData.length = 281 ∧ tag.length = 16 ∧
      (some commitment, afterHash) ∈ support
        ((impl (.inr (.inr (.inl (hashInput input tag))))).run afterAead) ∧
      (some message.ciphertext, finalState) ∈ support
        ((impl (.inr (.inr (.inr (frame input body tag commitment))))).run afterHash) := by
  simp only [QueryImpl.apply_compose, RawCtxSourceSend.adapter, simulateQ_bind,
    simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure] at hsupport
  change (some message, finalState) ∈ support
    ((simulateQ impl (nativeAdapter (.inr (RawCtxSourceSend.arguments pending)))).run primitive >>=
      fun result => pure (result.1.map (RawCtxSourceSend.encrypted (RawCtxSourceSend.arguments pending)), result.2)) at hsupport
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hsupport
  obtain ⟨⟨ciphertext, state⟩, hseal, heq⟩ := hsupport
  cases ciphertext with
  | none => simp at heq
  | some bytes =>
      simp only [Option.map_some, Prod.mk.injEq, Option.some.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      change (some bytes, finalState) ∈ support
        ((simulateQ impl (simulateQ sealLift (sealInput (RawCtxSourceSend.arguments pending)))).run primitive) at hseal
      rw [← QueryImpl.simulateQ_compose] at hseal
      obtain ⟨body, tag, afterAead, commitment, afterHash, haead, had, htag, hhash, hwriter⟩ :=
        sealInput_success (impl ∘ₛ sealLift) (RawCtxSourceSend.arguments pending) primitive finalState bytes hseal
      rw [sealLift_apply] at haead hhash hwriter
      exact ⟨body, tag, afterAead, commitment, afterHash, rfl, haead, had, htag, hhash, hwriter⟩

/-- Successful source sends expose the actual old-chain KDF and all concrete sealing replies in one execution. -/
theorem send_success_primitives {PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (kernel : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext)
    (primitive : PrimitiveState)
    (result : (ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) × PrimitiveState)
    (hsupport : result ∈ support ((simulateQ (impl ∘ₛ nativeAdapter ∘ₛ RawCtxSourceSend.adapter)
      (RawCtxSourceSend.send kernel context)).run primitive))
    (message : RawCtxSourceSend.Encrypted) (hsuccess : result.1.2 = some message) :
    ∃ pending response afterKdf,
      pending.entry = kernel ∧ pending.context = context ∧
      pending.request.input = kernel.refined.send_chain.bytes ∧ pending.request.info = SYM_RATCHET_INFO ∧
      (response, afterKdf) ∈ support ((impl (.inl pending.request)).run primitive) ∧
      result.1.1 = (RawCtxSourceSend.resumeSend pending response).advanced ∧
      let input := RawCtxSourceSend.arguments (RawCtxSourceSend.resumeSend pending response)
      ∃ body tag afterAead commitment afterHash,
        message = RawCtxSourceSend.encrypted input message.ciphertext ∧
        (some (body, tag), afterAead) ∈ support ((impl (.inr (.inl (aeadInput input)))).run afterKdf) ∧
        input.context.associatedData.length = 281 ∧ tag.length = 16 ∧
        (some commitment, afterHash) ∈ support
          ((impl (.inr (.inr (.inl (hashInput input tag))))).run afterAead) ∧
        (some message.ciphertext, result.2) ∈ support
          ((impl (.inr (.inr (.inr (frame input body tag commitment))))).run afterHash) := by
  by_cases hmax : kernel.refined.control.send_sequence = core.num.U64.MAX
  · rw [RawCtxSourceSend.send_exhausted kernel context hmax] at hsupport
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hsupport
    simp [hsupport] at hsuccess
  · obtain ⟨pending, response, afterKdf, hentry, hcontext, hinput, hinfo, hkdf, hseal, hadvance, _⟩ :=
      RawCtxSourceSend.send_nonexhausted_support (impl ∘ₛ nativeAdapter ∘ₛ RawCtxSourceSend.adapter)
        kernel context primitive hmax result hsupport
    simp [QueryImpl.compose, RawCtxSourceSend.adapter, nativeAdapter, OracleSpec.query] at hkdf
    refine ⟨pending, response, afterKdf, hentry, hcontext, hinput, hinfo, hkdf, hadvance, ?_⟩
    apply adapter_success_primitives impl (RawCtxSourceSend.resumeSend pending response) afterKdf result.2 message
    simpa only [hsuccess] using hseal

end BeaconcryptCore.Computational.RawCtxSourceSeal

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSeal.sealInput_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSeal.sealInput_success

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSeal.sealInput_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSeal.sealInput_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSeal.hashInput_extracted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSeal.hashInput_extracted

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSeal.hashInput_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSeal.hashInput_length

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSeal.frame_fields' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSeal.frame_fields

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSeal.frame_record' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSeal.frame_record

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSeal.sealInput_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSeal.sealInput_run

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSeal.sealLift_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSeal.sealLift_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSeal.sealLift_no_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSeal.sealLift_no_kdf

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSeal.nativeAdapter_kdf_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSeal.nativeAdapter_kdf_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSeal.nativeAdapter_seal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSeal.nativeAdapter_seal_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSeal.nativeSend_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSeal.nativeSend_bounds

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSeal.nativeSchedule_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSeal.nativeSchedule_bounds

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSeal.nativeOwner_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSeal.nativeOwner_interpretation

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSeal.nativeSchedule_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSeal.nativeSchedule_interpretation

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSeal.sealLift_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSeal.sealLift_apply

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSeal.adapter_success_primitives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSeal.adapter_success_primitives

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSeal.send_success_primitives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSeal.send_success_primitives
