import BeaconcryptCore.Computational.RawCtxFrameDecoding
import BeaconcryptCore.Refinement.CommitmentSurface
import BeaconcryptCore.Computational.CtxRomAuth

/-!
This module expands the source-selected private opening capability into its actual commitment and combined-ciphertext AEAD calls. Key/nonce come from the selected material, sequence from the same prepared request, and sender/associated data/base/tag/commitment from the retained frame context. It reuses the already checked 229-byte extracted commitment builder. Hash failure and commitment mismatch retain the real post-hash state and do not call AEAD; successful opening returns only the primitive-produced optional plaintext. The preceding owner adapter still handles missing source material without an opening call.

The general private hash API retains optional failure. Its native successful fixed-length BLAKE2b-512 result and unkeyed/fixed-size invocation belong to the primitive implementation contract. `romAdapter` is an explicit stronger classical shared-ROM interpretation, making that call total; this does not derive ROM behavior from collision resistance. `baseOpen` expresses the ordinary combined/detached AEAD interface contract using exactly body plus tag, without proving ChaCha20-Poly1305 internals. `sourceRecord` is an analysis-only normalization of the unique already-proved decoded protected payload. Recomputed slice/AD checks are pure normalization under source admission, not claims about equal native parser work or physical erasure of transcript temporaries.

Every source execution retains separate KDF, hash and AEAD accounting. Its actual source continuation rank bounds KDF callbacks, with at most one hash and one AEAD attempt. An arbitrary raw-only schedule with at most qRaw calls makes at most qRaw hashes and qRaw AEAD attempts, including failures. Exact full-state interpretation relates the counted program back to the existing whole-owner/primitive-state source game. Inner primitive costs and parser work are not declared free; the classical-ROM interpretation's functional AEAD is accompanied by the separately checked AEAD query ledger.

Typed opening and shared-cache equalities identify one selected opening computation over the existing CTX ROM interface. They do not assume an honest selected key, independent evolving keys, key uniqueness, freshness or a uniform key distribution, and do not apply the sibling adaptive canonical component's security theorem or a global multi-key reduction. Native runtime/library representation, constant-time behavior, erasure, persistence/CAS and interleaved send/reveal/multi-owner global composition remain explicit separate obligations. Actual API plaintext observation is distinct from network-only observation and declassifies an unknown target plaintext if exposed in a secrecy experiment.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp
open PqxdhRefinement BeaconcryptCore.Refinement.RepresentationBridge

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxSourceOpen

/-- Native combined-ciphertext AEAD opening arguments contain no plaintext. -/
structure BaseInput where
  key : Pqxdh.Bytes
  nonce : Pqxdh.Bytes
  associatedData : Pqxdh.Bytes
  ciphertext : Pqxdh.Bytes

/-- Private primitive results retain native optional failure without substituting plaintext. -/
abbrev OpenSpec := (Pqxdh.Bytes →ₒ Option Pqxdh.Bytes) + (BaseInput →ₒ Option Pqxdh.Bytes)

/-- The exact native commitment input uses selected material and the source capability's sequence. -/
def hashInput (input : RawCtxWholeOwner.OpenInput) (slices : RawCtxFrameDecoding.Slices) :
    Pqxdh.Bytes :=
  Pqxdh.ctxPreimage (absMaterial input.material)
    ⟨input.context.associatedData, input.sequence.val, input.context.frame.sender.val⟩ slices.tag

/-- The native AEAD call receives the original retained base slice, actual material and AD. -/
def baseInput (input : RawCtxWholeOwner.OpenInput) (slices : RawCtxFrameDecoding.Slices) : BaseInput :=
  ⟨(absMaterial input.material).1, (absMaterial input.material).2,
    input.context.associatedData, slices.baseCiphertext⟩

/-- Source opening first constructs/checks CTX; only matching commitments reach AEAD. -/
def openSlices (input : RawCtxWholeOwner.OpenInput) (slices : RawCtxFrameDecoding.Slices) :
    OracleComp OpenSpec (Option Pqxdh.Bytes) := do
  let digest ← OpenSpec.query (.inl (hashInput input slices))
  match digest with
  | none => pure none
  | some actual =>
      if actual = slices.commitment then OpenSpec.query (.inr (baseInput input slices))
      else pure none

/-- Recompute only uniquely determined pure slice/AD checks before the private primitive work. -/
def openInput (input : RawCtxWholeOwner.OpenInput) : OracleComp OpenSpec (Option Pqxdh.Bytes) :=
  match RawCtxFrameDecoding.fromPayload input.context.frame.payload with
  | none => pure none
  | some slices =>
      if input.context.associatedData.length = 153 then openSlices input slices else pure none

/-- Native combined-ciphertext framing is mapped to the ordinary detached primitive interface. -/
def baseOpen (c : Pqxdh.Crypto) (input : BaseInput) : Option Pqxdh.Bytes :=
  if 16 ≤ input.ciphertext.length then
    c.aeadOpen input.key input.nonce input.associatedData
      (input.ciphertext.take (input.ciphertext.length - 16))
      (input.ciphertext.drop (input.ciphertext.length - 16))
  else none

/-- Combined and detached AEAD interfaces consume exactly the same body/tag bytes. -/
theorem baseOpen_combined (c : Pqxdh.Crypto) (key nonce ad body tag : Pqxdh.Bytes)
    (htag : tag.length = 16) :
    baseOpen c ⟨key, nonce, ad, body ++ tag⟩ = c.aeadOpen key nonce ad body tag := by
  simp [baseOpen, htag]

/-- The private hash query equals the actual extracted commitment builder on the source arrays. -/
theorem hashInput_extracted (input : RawCtxWholeOwner.OpenInput)
    (slices : RawCtxFrameDecoding.Slices)
    (ad : Std.Array Std.U8 153#usize) (tag : Std.Array Std.U8 16#usize)
    (had : absBytes ad = input.context.associatedData) (htag : absBytes tag = slices.tag) :
    ∃ transcript, commitment.build_commitment_transcript input.material.key.bytes
      input.material.nonce.bytes ad tag input.sequence input.context.frame.sender = ok transcript ∧
      absBytes transcript.bytes = hashInput input slices := by
  simpa only [hashInput, absMaterial, had, htag] using
    build_commitment_transcript_abs input.material.key.bytes input.material.nonce.bytes ad tag
      input.sequence input.context.frame.sender

/-- Every source hash preimage has the exact 229-byte input width. -/
theorem hashInput_length (input : RawCtxWholeOwner.OpenInput)
    (slices : RawCtxFrameDecoding.Slices) (had : input.context.associatedData.length = 153)
    (htag : slices.tag.length = 16) : (hashInput input slices).length = 229 := by
  simp [hashInput, Pqxdh.ctxPreimage, absMaterial, had, htag]

/-- The explicit classical-ROM/ordinary-AEAD interpretation makes the fixed-size hash call total. -/
def romAdapter (c : Pqxdh.Crypto) : QueryImpl OpenSpec (OracleComp CtxRomAuth.CtxRO)
  | .inl bytes => do
      let digest ← CtxRomAuth.CtxRO.query ((), bytes)
      pure (some digest.toList)
  | .inr input => pure (baseOpen c input)

/-- Interpretation retains the actual hash address and checks its real reply before the ordinary AEAD call. -/
theorem openSlices_rom (c : Pqxdh.Crypto) (input : RawCtxWholeOwner.OpenInput)
    (slices : RawCtxFrameDecoding.Slices) :
    simulateQ (romAdapter c) (openSlices input slices) = (do
      let digest ← CtxRomAuth.CtxRO.query ((), hashInput input slices)
      pure (if digest.toList = slices.commitment then baseOpen c (baseInput input slices) else none)) := by
  simp [openSlices, romAdapter, OracleSpec.query]
  rw [map_eq_bind_pure_comp]
  apply bind_congr
  intro digest
  split <;> simp_all

/-- Source material is viewed at its actual fixed key width; no distribution premise is added. -/
def sourceKey (input : RawCtxWholeOwner.OpenInput) : CtxRomAuth.CtxKey :=
  ⟨(absMaterial input.material).1, by simp [absMaterial]⟩

def sourceNonce (input : RawCtxWholeOwner.OpenInput) : CtxRomAuth.CtxNonce :=
  ⟨(absMaterial input.material).2, by simp [absMaterial]⟩

/-- The typed component context uses actual prepared sequence and decoded sender, not chosen substitutes. -/
def sourceContext (input : RawCtxWholeOwner.OpenInput)
    (had : input.context.associatedData.length = 153) : CtxRomAuth.CtxRecordContext :=
  ⟨⟨input.context.associatedData, input.sequence.val, input.context.frame.sender.val⟩,
    had, input.sequence.bv.isLt, input.context.frame.sender.bv.isLt⟩

/-- Normalize only the already-proved unique protected-payload decoding into component widths. -/
noncomputable def sourceRecord (input : RawCtxWholeOwner.OpenInput)
    (slices : RawCtxFrameDecoding.Slices)
    (hslices : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices) :
    CtxRomAuth.CtxRomRecord :=
  let record := (RawCtxFrameDecoding.fromPayload_record input.context.frame.payload slices hslices).choose
  let facts := (RawCtxFrameDecoding.fromPayload_record input.context.frame.payload slices hslices).choose_spec
  ⟨record.body, record.tag, facts.2.2.2.2.1, ⟨record.commit, facts.2.2.2.2.2.1⟩⟩

/-- The component record retains the exact decoded protected payload and native slices. -/
theorem sourceRecord_spec (input : RawCtxWholeOwner.OpenInput)
    (slices : RawCtxFrameDecoding.Slices)
    (hslices : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices) :
    let record := sourceRecord input slices hslices
    Pqxdh.decodeRecord input.context.frame.payload = some record.toRecordCipher ∧
      slices.baseCiphertext = record.body ++ record.tag ∧ slices.tag = record.tag ∧
      slices.commitment = record.commit.toList ∧ 0 < record.body.length ∧
      record.encode = input.context.frame.payload := by
  obtain ⟨hdecode, hbase, htag, hcommit, _, _, hbody, hencode⟩ :=
    (RawCtxFrameDecoding.fromPayload_record input.context.frame.payload slices hslices).choose_spec
  exact ⟨hdecode, hbase, htag, hcommit, hbody, hencode⟩

/-- One exact typed component opening at the existing shared-ROM address. No plaintext is supplied. -/
def typedOpen (c : Pqxdh.Crypto) (key : CtxRomAuth.CtxKey) (nonce : CtxRomAuth.CtxNonce)
    (context : CtxRomAuth.CtxRecordContext) (record : CtxRomAuth.CtxRomRecord) :
    OracleComp CtxRomAuth.CtxRO (Option Pqxdh.Bytes) := do
  let digest ← CtxRomAuth.CtxRO.query ((), CtxRomAuth.outerInput key nonce context record.tag)
  pure (if record.commit = digest then
    c.aeadOpen key.toList nonce.toList context.ad.bytes record.body record.tag else none)

/-- Source opening is the typed actual optional-plaintext computation under the explicit ROM contract. -/
theorem openInput_typed (c : Pqxdh.Crypto) (input : RawCtxWholeOwner.OpenInput)
    (slices : RawCtxFrameDecoding.Slices)
    (hslices : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices)
    (had : input.context.associatedData.length = 153) :
    simulateQ (romAdapter c) (openInput input) =
      typedOpen c (sourceKey input) (sourceNonce input) (sourceContext input had)
        (sourceRecord input slices hslices) := by
  simp only [openInput, hslices, ite_eq_left had, openSlices_rom]
  obtain ⟨_, hbase, htag, hcommit, _, _⟩ := sourceRecord_spec input slices hslices
  have hhash : hashInput input slices = CtxRomAuth.outerInput (sourceKey input)
      (sourceNonce input) (sourceContext input had) (sourceRecord input slices hslices).tag :=
    congrArg (Pqxdh.ctxPreimage (absMaterial input.material)
      ⟨input.context.associatedData, input.sequence.val, input.context.frame.sender.val⟩) htag
  rw [hhash]
  unfold typedOpen
  apply bind_congr
  intro digest
  simp only [hcommit, List.Vector.toList_injective.eq_iff, eq_comm, baseInput, hbase,
    baseOpen_combined c _ _ _ _ _ (sourceRecord input slices hslices).tagLength]
  rfl

/-- Every source opening attempts at most one actual hash call, including rejected candidates. -/
theorem openSlices_hash_bound (input : RawCtxWholeOwner.OpenInput)
    (slices : RawCtxFrameDecoding.Slices) :
    (openSlices input slices).IsQueryBoundP (fun query => query.isLeft = true) 1 := by
  rw [openSlices, isQueryBoundP_query_bind_iff]
  simp only [Sum.isLeft, not_true_eq_false, false_or, ite_true]
  refine ⟨by omega, fun reply => ?_⟩
  cases reply
  · simp
  · dsimp only
    split_ifs <;> simp

/-- Every source opening makes at most one AEAD attempt after its successful commitment check. -/
theorem openSlices_aead_bound (input : RawCtxWholeOwner.OpenInput)
    (slices : RawCtxFrameDecoding.Slices) :
    (openSlices input slices).IsQueryBoundP (fun query => query.isRight = true) 1 := by
  rw [openSlices, isQueryBoundP_query_bind_iff]
  simp only [Sum.isRight, Bool.false_eq_true, not_false_eq_true, true_or, ite_false, true_and]
  intro reply
  cases reply
  · simp
  · dsimp only
    split_ifs <;> simp

/-- The raw selected-input interpreter counts all inner hash/AEAD work, including failures. -/
theorem openInput_bounds (input : RawCtxWholeOwner.OpenInput) :
    (openInput input).IsQueryBoundP (fun query => query.isLeft = true) 1 ∧
      (openInput input).IsQueryBoundP (fun query => query.isRight = true) 1 := by
  unfold openInput
  split
  · simp
  · split
    · exact ⟨openSlices_hash_bound input _, openSlices_aead_bound input _⟩
    · simp

/-- The complete interpreter retains the actual hash poststate on rejection and before AEAD. -/
theorem openSlices_run {PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl OpenSpec (StateT PrimitiveState (OracleComp base)))
    (input : RawCtxWholeOwner.OpenInput) (slices : RawCtxFrameDecoding.Slices)
    (primitive : PrimitiveState) :
    (simulateQ impl (openSlices input slices)).run primitive = (do
      let result ← (impl (.inl (hashInput input slices))).run primitive
      match result.1 with
      | none => pure (none, result.2)
      | some digest =>
          if digest = slices.commitment then (impl (.inr (baseInput input slices))).run result.2
          else pure (none, result.2)) := by
  simp [openSlices, OracleSpec.query, StateT.run_bind]
  apply bind_congr
  intro result
  cases result.1
  · simp
  · dsimp only
    split <;> simp

/-- Successful source opening exposes only the actual primitive-produced plaintext and final state. -/
theorem openSlices_success {PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl OpenSpec (StateT PrimitiveState (OracleComp base)))
    (input : RawCtxWholeOwner.OpenInput) (slices : RawCtxFrameDecoding.Slices)
    (primitive final : PrimitiveState) (plaintext : Pqxdh.Bytes)
    (h : (some plaintext, final) ∈ support ((simulateQ impl (openSlices input slices)).run primitive)) :
    ∃ afterHash,
      (some slices.commitment, afterHash) ∈ support ((impl (.inl (hashInput input slices))).run primitive) ∧
      (some plaintext, final) ∈ support ((impl (.inr (baseInput input slices))).run afterHash) := by
  rw [openSlices_run, mem_support_bind_iff] at h
  obtain ⟨⟨digest, afterHash⟩, hhash, htail⟩ := h
  cases digest
  · simp at htail
  · rename_i digest
    dsimp only at htail
    split at htail
    · rename_i hmatch
      exact ⟨afterHash, hmatch ▸ hhash, htail⟩
    · simp at htail

/-- A failed or mismatching hash reply retains its actual poststate and makes no AEAD request. -/
theorem openSlices_hash_rejection {PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl OpenSpec (StateT PrimitiveState (OracleComp base)))
    (input : RawCtxWholeOwner.OpenInput) (slices : RawCtxFrameDecoding.Slices)
    (primitive afterHash : PrimitiveState) (reply : Option Pqxdh.Bytes)
    (hhash : (reply, afterHash) ∈ support ((impl (.inl (hashInput input slices))).run primitive))
    (hfailed : reply = none ∨ ∃ digest, reply = some digest ∧ digest ≠ slices.commitment) :
    (none, afterHash) ∈ support ((simulateQ impl (openSlices input slices)).run primitive) := by
  rw [openSlices_run, mem_support_bind_iff]
  refine ⟨(reply, afterHash), hhash, ?_⟩
  rcases hfailed with rfl | ⟨digest, rfl, hmismatch⟩
  · simp
  · simp [hmismatch]

/-- Source-selected input success requires actual slice/AD checks and both actual primitive replies. -/
theorem openInput_success {PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl OpenSpec (StateT PrimitiveState (OracleComp base)))
    (input : RawCtxWholeOwner.OpenInput) (primitive final : PrimitiveState) (plaintext : Pqxdh.Bytes)
    (h : (some plaintext, final) ∈ support ((simulateQ impl (openInput input)).run primitive)) :
    ∃ slices afterHash, RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices ∧
      input.context.associatedData.length = 153 ∧
      (some slices.commitment, afterHash) ∈ support ((impl (.inl (hashInput input slices))).run primitive) ∧
      (some plaintext, final) ∈ support ((impl (.inr (baseInput input slices))).run afterHash) := by
  unfold openInput at h
  split at h
  · simp at h
  · split at h
    · obtain ⟨afterHash, hhash, haead⟩ := openSlices_success impl input _ primitive final plaintext h
      exact ⟨_, afterHash, by assumption, by assumption, hhash, haead⟩
    · simp at h

/-- Structural simulation accounting needs no finite/uniform distribution for optional plaintext replies. -/
theorem simulate_bound {ι κ α : Type} {source : OracleSpec ι} {target : OracleSpec κ}
    (impl : QueryImpl source (OracleComp target)) (p : ι → Prop) (q : κ → Prop)
    [DecidablePred p] [DecidablePred q] (program : OracleComp source α) (n : Nat)
    (h : program.IsQueryBoundP p n)
    (hstep : ∀ query, (impl query).IsQueryBoundP q (if p query then 1 else 0)) :
    (simulateQ impl program).IsQueryBoundP q n := by
  induction program using OracleComp.inductionOn generalizing n with
  | pure value => simp
  | query_bind query continuation ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      rw [simulateQ_query_bind]
      refine (isQueryBoundP_bind (hstep query) (fun reply _ => ih reply _ (h.2 reply))).mono ?_
      split_ifs with hquery
      · have hn : 0 < n := h.1.resolve_left (not_not.mpr hquery)
        omega
      · omega

/-- The complete private source executor keeps KDF requests distinct from hash and AEAD calls. -/
abbrev NativeSpec := (SymmetricRatchetKdfRequest →ₒ RatchetKdfResponse) + OpenSpec

def openLift : QueryImpl OpenSpec (OracleComp NativeSpec) :=
  fun query => liftM (NativeSpec.query (.inr query))

/-- Select one opening-call category while counting no unrelated KDF work in that category. -/
def openingPredicate (p : OpenSpec.Domain → Bool) : NativeSpec.Domain → Bool
  | .inl _ => false
  | .inr query => p query

/-- Embedding an opening preserves its actual hash/AEAD category bound. -/
theorem openLift_bound {α : Type} (p : OpenSpec.Domain → Bool) (program : OracleComp OpenSpec α)
    (n : Nat) (h : program.IsQueryBoundP (fun query => p query = true) n) :
    (simulateQ openLift program).IsQueryBoundP (fun query => openingPredicate p query = true) n := by
  apply simulate_bound openLift _ _ program n h
  intro query
  exact (isQueryBoundP_query_iff (spec := NativeSpec)
    (p := fun query => openingPredicate p query = true) (.inr query) _).2 (by
      simp only [openingPredicate]
      split_ifs <;> simp_all)

/-- Whole-owner KDF calls stay unchanged; its selected opening is expanded into the actual inner calls. -/
def nativeAdapter : QueryImpl RawCtxWholeOwner.PrimitiveSpec (OracleComp NativeSpec)
  | .inl request => liftM (NativeSpec.query (.inl request))
  | .inr input => simulateQ openLift (openInput input)

/-- The combined capability adapter retains missing-material rejection and exact optional-result wrapping. -/
noncomputable def ownerAdapter :
    QueryImpl (RawCtxOwnerOracle.ReceiveSpec RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted)
      (OracleComp NativeSpec) :=
  nativeAdapter ∘ₛ RawCtxWholeOwner.adapter

/-- One source opening-capability bound transfers to any proved inner opening-call category. -/
theorem owner_open_bound (effect : ReceiveEffect RawCtxWholeOwner.OpenContext)
    (p : OpenSpec.Domain → Bool)
    (hinner : ∀ input, (openInput input).IsQueryBoundP (fun query => p query = true) 1) :
    (simulateQ ownerAdapter (RawCtxOwnerOracle.program (Plaintext := RawCtxWholeOwner.Decrypted) effect)).IsQueryBoundP
      (fun query => openingPredicate p query = true) 1 := by
  apply simulate_bound ownerAdapter _ _ _ 1 (RawCtxOwnerOracle.program_open_bound effect)
  intro query
  cases query
  · rename_i request
    simp [ownerAdapter, QueryImpl.compose, RawCtxWholeOwner.adapter, nativeAdapter,
      OracleSpec.query, openingPredicate]
    exact (isQueryBoundP_query_iff (spec := NativeSpec)
      (p := fun query => openingPredicate p query = true) (.inl request) 0).2 (by simp [openingPredicate])
  · rename_i pending
    simp only [ownerAdapter, QueryImpl.apply_compose, RawCtxWholeOwner.adapter, Sum.isRight, ite_true]
    cases RawCtxWholeOwner.arguments pending
    · simp
    · rename_i input
      simpa [nativeAdapter, OracleSpec.query] using openLift_bound p (openInput input) 1 (hinner input)

/-- Private opening dispatch cannot manufacture a source KDF request. -/
theorem openLift_no_kdf {α : Type} (program : OracleComp OpenSpec α) :
    (simulateQ openLift program).IsQueryBoundP (fun query => query.isLeft = true) 0 := by
  apply simulate_bound openLift (fun _ => False) _ program 0 (isQueryBoundP_false program 0)
  intro query
  exact (isQueryBoundP_query_iff (spec := NativeSpec)
    (p := fun query => query.isLeft = true) (.inr query) 0).2 (by simp)

/-- Expanding actual source openings preserves the source-rank bound on KDF callbacks. -/
theorem owner_kdf_bound (effect : ReceiveEffect RawCtxWholeOwner.OpenContext) :
    (simulateQ ownerAdapter (RawCtxOwnerOracle.program (Plaintext := RawCtxWholeOwner.Decrypted) effect)).IsQueryBoundP
      (fun query => query.isLeft = true) (effectDepth effect) := by
  apply simulate_bound ownerAdapter _ _ _ _ (RawCtxOwnerOracle.program_kdf_bound effect)
  intro query
  cases query
  · rename_i request
    simp [ownerAdapter, QueryImpl.compose, RawCtxWholeOwner.adapter, nativeAdapter, OracleSpec.query]
    exact (isQueryBoundP_query_iff (spec := NativeSpec)
      (p := fun query => query.isLeft = true) (.inl request) 1).2 (by simp)
  · rename_i pending
    simp only [ownerAdapter, QueryImpl.apply_compose, RawCtxWholeOwner.adapter, Sum.isLeft]
    cases RawCtxWholeOwner.arguments pending
    · simp
    · rename_i input
      simp [nativeAdapter, OracleSpec.query]
      change (simulateQ openLift (openInput input)).IsQueryBoundP (fun query => query.isLeft = true) 0
      exact openLift_no_kdf (openInput input)

/-- Complete source execution charges KDF, hash and AEAD separately, under all actual optional replies. -/
theorem owner_primitive_bounds (effect : ReceiveEffect RawCtxWholeOwner.OpenContext) :
    let program := simulateQ ownerAdapter
      (RawCtxOwnerOracle.program (Plaintext := RawCtxWholeOwner.Decrypted) effect)
    program.IsQueryBoundP (fun query => query.isLeft = true) (effectDepth effect) ∧
      program.IsQueryBoundP (fun query => openingPredicate Sum.isLeft query = true) 1 ∧
      program.IsQueryBoundP (fun query => openingPredicate Sum.isRight query = true) 1 := by
  exact ⟨owner_kdf_bound effect,
    owner_open_bound effect Sum.isLeft (fun input => (openInput_bounds input).1),
    owner_open_bound effect Sum.isRight (fun input => (openInput_bounds input).2)⟩

/-- The embedding forwards each exact opening request and its complete stateful response. -/
theorem openLift_apply {PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (query : OpenSpec.Domain) :
    (impl ∘ₛ openLift) query = impl (.inr query) := by
  simp [QueryImpl.compose, openLift, OracleSpec.query]

/-- The typed source opening equality preserves the entire canonical shared hash cache. -/
theorem openInput_shared_cache (c : Pqxdh.Crypto) (input : RawCtxWholeOwner.OpenInput)
    (slices : RawCtxFrameDecoding.Slices)
    (hslices : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices)
    (had : input.context.associatedData.length = 153) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (simulateQ CtxRomAuth.ctxRandomOracle (simulateQ (romAdapter c) (openInput input))).run cache =
      (simulateQ CtxRomAuth.ctxRandomOracle
        (typedOpen c (sourceKey input) (sourceNonce input) (sourceContext input had)
          (sourceRecord input slices hslices))).run cache := by
  rw [openInput_typed c input slices hslices had]

/-- Every actual whole-owner raw success reaches the exact inner hash and AEAD callbacks and their real plaintext. -/
theorem raw_success_primitives {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (primitive : PrimitiveState)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Metadata) × PrimitiveState)
    (hsupport : result ∈ support (RawCtxWholeOwner.rawGame (impl ∘ₛ nativeAdapter) decode raw state primitive))
    (message : RawCtxWholeOwner.Decrypted) (hsuccess : result.1.1 = .Some message) :
    ∃ (frame : RawCtxReceive.DecodedFrame) (pending : ReceiveOpen RawCtxWholeOwner.OpenContext)
      (input : RawCtxWholeOwner.OpenInput) (slices : RawCtxFrameDecoding.Slices)
      (plaintext : Pqxdh.Bytes) (before afterHash : PrimitiveState),
      decode raw = some frame ∧ RawCtxReceive.ValidFrame state.owner.expectedSender state.owner.associatedData frame ∧
      RawCtxWholeOwner.arguments pending = some input ∧ pending.material = ok (.Some input.material) ∧
      input.sequence = frame.sequence ∧ input.context = ⟨raw, frame, state.owner.associatedData⟩ ∧
      message = RawCtxWholeOwner.decrypted input plaintext ∧
      RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices ∧
      (some slices.commitment, afterHash) ∈ support ((impl (.inr (.inl (hashInput input slices)))).run before) ∧
      (some plaintext, result.2) ∈ support ((impl (.inr (.inr (baseInput input slices)))).run afterHash) := by
  obtain ⟨frame, pending, input, plaintext, before, hdecode, hvalid, hargs, hmaterial,
    hsequence, hcontext, hmessage, hreply⟩ := RawCtxOwnerProvenance.raw_success
      (impl ∘ₛ nativeAdapter) decode raw state primitive result hsupport message hsuccess
  change (some plaintext, result.2) ∈ support
    ((simulateQ impl (simulateQ openLift (openInput input))).run before) at hreply
  rw [← QueryImpl.simulateQ_compose] at hreply
  obtain ⟨slices, afterHash, hslices, _, hhash, haead⟩ :=
    openInput_success (impl ∘ₛ openLift) input before result.2 plaintext hreply
  rw [openLift_apply] at hhash haead
  exact ⟨frame, pending, input, slices, plaintext, before, afterHash, hdecode, hvalid, hargs,
    hmaterial, hsequence, hcontext, hmessage, hslices, hhash, haead⟩

/-- One arbitrary raw owner call issues at most one hash and one AEAD query, including every rejection path. -/
theorem raw_primitive_bounds {Metadata : Type} (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : RawCtxWholeOwner.OwnerState Metadata) :
    let program := simulateQ nativeAdapter (RawCtxWholeOwner.rawReceive decode raw state)
    program.IsQueryBoundP (fun query => openingPredicate Sum.isLeft query = true) 1 ∧
      program.IsQueryBoundP (fun query => openingPredicate Sum.isRight query = true) 1 := by
  unfold RawCtxWholeOwner.rawReceive
  split
  · simp
  · split
    · simp
    · split
      · simp only [bind_pure_comp, simulateQ_map, isQueryBoundP_map_iff,
          ← QueryImpl.simulateQ_compose, RawCtxOwnerOracle.receive]
        exact (owner_primitive_bounds _).2
      · simp

/-- Raw scheduling keeps one complete owner while its real primitive operations remain in the outer oracle program. -/
noncomputable def nativeOwnerImpl {Metadata : Type} (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl RawCtxWholeOwner.RawSpec
      (StateT (RawCtxWholeOwner.OwnerState Metadata) (OracleComp NativeSpec)) :=
  fun raw state => simulateQ nativeAdapter (RawCtxWholeOwner.rawReceive decode raw state)

/-- An arbitrary adaptive raw-only owner schedule charges every hash/AEAD attempt against qRaw. -/
theorem nativeSchedule_bounds {Metadata Result : Type} (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxWholeOwner.RawSpec Result) (qRaw : Nat)
    (hbound : client.IsTotalQueryBound qRaw) (state : RawCtxWholeOwner.OwnerState Metadata) :
    let program := (simulateQ (nativeOwnerImpl decode) client).run state
    program.IsQueryBoundP (fun query => openingPredicate Sum.isLeft query = true) qRaw ∧
      program.IsQueryBoundP (fun query => openingPredicate Sum.isRight query = true) qRaw := by
  have hb : client.IsQueryBoundP (fun _ => True) qRaw := hbound.isQueryBoundP
  exact ⟨hb.simulateQ_run_StateT_of_step
    (fun raw owner => (raw_primitive_bounds decode raw owner).1) state,
    hb.simulateQ_run_StateT_of_step
    (fun raw owner => (raw_primitive_bounds decode raw owner).2) state⟩

/-- Flattening the counted native handler preserves the existing complete owner/primitive-state interpreter. -/
theorem nativeOwner_interpretation {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) :
    (impl.mapStateTBase (nativeOwnerImpl (Metadata := Metadata) decode)).flattenStateT =
      RawCtxWholeOwner.ownerImpl (impl ∘ₛ nativeAdapter) decode := by
  funext raw state
  simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run, StateT.mk,
    nativeOwnerImpl, RawCtxWholeOwner.ownerImpl, RawCtxWholeOwner.rawGame,
    ← QueryImpl.simulateQ_compose, bind_pure_comp]

/-- Counted adaptive raw scheduling and the complete source game have identical replies and both full states. -/
theorem nativeSchedule_interpretation {Metadata PrimitiveState Result : Type}
    {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp RawCtxWholeOwner.RawSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata) (primitive : PrimitiveState) :
    (simulateQ impl ((simulateQ (nativeOwnerImpl decode) client).run state)).run primitive =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        RawCtxWholeOwner.scheduleGame (impl ∘ₛ nativeAdapter) decode client (state, primitive) := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT, nativeOwner_interpretation]
  rfl

end BeaconcryptCore.Computational.RawCtxSourceOpen

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceOpen.baseOpen_combined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOpen.baseOpen_combined

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceOpen.hashInput_extracted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOpen.hashInput_extracted

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceOpen.hashInput_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOpen.hashInput_length

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceOpen.openSlices_rom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOpen.openSlices_rom

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceOpen.sourceRecord_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOpen.sourceRecord_spec

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceOpen.openInput_typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOpen.openInput_typed

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceOpen.openSlices_hash_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOpen.openSlices_hash_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceOpen.openSlices_aead_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOpen.openSlices_aead_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceOpen.openInput_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOpen.openInput_bounds

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceOpen.openSlices_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOpen.openSlices_run

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceOpen.openSlices_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOpen.openSlices_success

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceOpen.openSlices_hash_rejection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOpen.openSlices_hash_rejection

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceOpen.openInput_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOpen.openInput_success

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceOpen.simulate_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOpen.simulate_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceOpen.openLift_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOpen.openLift_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceOpen.owner_open_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOpen.owner_open_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceOpen.openLift_no_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOpen.openLift_no_kdf

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceOpen.owner_kdf_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOpen.owner_kdf_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceOpen.owner_primitive_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOpen.owner_primitive_bounds

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceOpen.openLift_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOpen.openLift_apply

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceOpen.openInput_shared_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOpen.openInput_shared_cache

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceOpen.raw_success_primitives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOpen.raw_success_primitives

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceOpen.raw_primitive_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOpen.raw_primitive_bounds

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceOpen.nativeSchedule_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOpen.nativeSchedule_bounds

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceOpen.nativeOwner_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOpen.nativeOwner_interpretation

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceOpen.nativeSchedule_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOpen.nativeSchedule_interpretation
