import BeaconcryptCore.Computational.PqxdhJointDhExtractRoot
import BeaconcryptCore.Computational.PqxdhExtractRomSeparation

/-!
# The zero-salt Extract random-oracle family (route R1)

This module is the second stage of the server-authentication proof (Milestone B, route R1). It defines `romImpl`, the interpretation of the existing joint-DH Extract family interface `PqxdhJointDhExtractFamily.Spec` in which zero-salt HKDF-Extract on 192-byte inputs is one lazily sampled random table. The honest root derivations of the Server and the Beacon (the family's `.derive` requests) and the adversary's public HMAC queries under the zero key on 192-byte messages read and fill the same table. Every other public HMAC query is answered by the real function, as in the existing family `PqxdhJointDhExtractFamily.impl`. That includes every HKDF-Expand query the protocol makes, whose messages have 42, 47, 106 or 111 bytes (stage B1), and in particular the 47-byte root Expand that follows each derivation; an adversary query shaped like an Expand block that happens to be 192 bytes long under the zero key is a table query like any other. This is the idealization that the owner approved for route R1, stated as an interpretation of an unchanged interface: `impl`, `protectedExtract`, `realImpl` and `idealImpl` are not modified, and `romImpl` reuses `PqxdhJointDhExtractFamily.State`, so it plugs into every existing client of that interface, in particular the root-valued reduction `PqxdhJointDhExtractRoot.reduction`.

The table. The table is the family state's `cache`, and every table read is `HmacOracle.randomOracle`: a cached entry is returned unchanged, and a missing entry is sampled uniformly from the 64-byte blocks and recorded. A derivation reads the table at its actual 192-byte input bytes, `PqxdhJointDhExtractFamily.input`, which the challenger computes with the Server seed and, for the Beacon's request, the Beacon's prekey scalar. The table is therefore indexed by the input bytes and never by the request's peer encodings or constructor, so every encoding alias of one input shares one entry. A request whose input does not exist, because one of its DH replies is rejected, is logged and leaves the table unchanged, exactly as in the existing family. The family history logs every request with its answer, as before, so it holds key material; the lemmas here show that no answer depends on it.

What is proved. `rom_coin` and `rom_sign`: coins and same-seed signing are exactly the existing family's, and `rom_public_real`: outside the table domain a public HMAC query is the existing family's real branch, in each case for every Extract service of that family. `rom_public_oracle` and `rom_derive_oracle` write a public table query and a derivation with an actual input as one table read, logged with its answer. `rom_hit` and `rom_miss`: a public table query returns a cached entry unchanged, or samples, records and returns a fresh one. `rom_derive_hit` and `rom_derive_miss` are the same statements for a derivation, and `rom_rejected` is the rejection branch. `rom_side`: an honest derivation and the adversary's public table query at the same input bytes are the same table read, with the same answer and the same resulting table; this is why a side session that the adversary can compute itself stays consistent with its own Extract evaluations, the role that `PqxdhJointDhExtractFamily.side_real` plays for the existing family; consistency between an honest derivation and an adversary query made at different times is `derive_then_public` and `public_then_derive`. `rootExpand_outside` and `rom_root`: a root request of the reduction `PqxdhJointDhExtractRoot.reduction` reads the table once and then makes one real 47-byte Expand query, so the returned root is the real Expand of the table entry; `rom_forward` states that the reduction forwards every other query unchanged. `rom_history_append` states that each query only appends to the history and that neither its answer nor its resulting table depends on the history, and `rom_cache_mono` (with `oracle_step`, one table read) states that the table only grows; `rom_reduction_history_append` and `rom_reduction_cache_mono` are the same statements for the composed family `romImpl … ∘ₛ PqxdhJointDhExtractRoot.reduction` that the experiment runs. `rom_public_patch` and `rom_derive_patch` connect the family with the patched HMAC `PqxdhExtractRomSeparation.romHmac` of stage B1: every answer is that patched function at any table that extends the resulting cache.

Scope and trust boundary. The table covers exactly the function that route R1 idealizes: HMAC-SHA-512 under the 64-byte all-zero key on 192-byte messages, which is zero-salt HKDF-Extract on the PQXDH root input. The separation lemmas of stage B1 show that no other HMAC evaluation of the protocol lands in that slice. That production makes exactly one Extract per root derivation, with the 192-byte root input as input keying material, is adapter-level trust (`beaconcrypt/src/pqxdh.rs:46-58`). libsodium is a correct black box, and nothing about it, SHA-512 or HMAC is proved. Messages are abstract byte strings that each side can decode, and no serialization-library behaviour is used.

Premises. The module states no security law and adds no premise. The real HMAC, the joint primitives and the DH interface are parameters, and every statement holds for all of them. The axioms used are `propext`, `Classical.choice` and `Quot.sound` only.
-/

open OracleComp OracleSpec
set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhExtractRomFamily
open PqxdhJointIdentity PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhJointDhExtractFamily
open PqxdhJointGapDh (DhInterface ScalarBytes)
open PqxdhExtractRomSeparation (romHmac)

/-- Route R1 interpretation of the joint-DH Extract family. Coins and same-seed signing are as in `PqxdhJointDhExtractFamily.impl`. A public HMAC query under the zero key on a 192-byte message reads the lazily sampled table held in the state's cache; every other public HMAC query is the real function. A derivation reads the same table at its actual 192-byte input, or is rejected and logged when that input does not exist. Every request is logged with its answer. -/
noncomputable def romImpl (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) :
    QueryImpl PqxdhJointDhExtractFamily.Spec (StateT State ProbComp) := fun query state =>
  match query with
  | .inl coin => do
      let value ← unifSpec.query coin
      pure (value, state)
  | .inr (.sign message) =>
      let signature := joint.sign seed message
      pure (signature, { state with history := state.history ++ [.sign message signature] })
  | .inr (.publicHmac key message) =>
      if key = zeroSalt ∧ message.length = 192 then do
        let result ← (HmacOracle.randomOracle message).run state.cache
        pure (result.1, ⟨state.history ++ [.publicHmac key message result.1], result.2⟩)
      else
        let block := hmac.eval key message
        pure (block, { state with history := state.history ++ [.publicHmac key message block] })
  | .inr (.derive message) =>
      match input joint dh seed scalar message with
      | none => pure (none, { state with history := state.history ++ [.derive message none] })
      | some bytes => do
          let result ← (HmacOracle.randomOracle bytes).run state.cache
          pure (some result.1, ⟨state.history ++ [.derive message (some result.1)], result.2⟩)

/-- Coin queries are forwarded exactly as in the existing family, for every Extract service of that family. -/
theorem rom_coin (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (extractImpl : QueryImpl HmacOracle (StateT HmacOracle.QueryCache ProbComp))
    (coin : ℕ) (state : State) :
    (romImpl hmac joint dh seed scalar (.inl coin)).run state =
      (impl hmac joint dh seed scalar extractImpl (.inl coin)).run state :=
  rfl

/-- Signing requests are answered with the Server seed exactly as in the existing family, for every Extract service of that family. -/
theorem rom_sign (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (extractImpl : QueryImpl HmacOracle (StateT HmacOracle.QueryCache ProbComp))
    (message : Pqxdh.Bytes) (state : State) :
    (romImpl hmac joint dh seed scalar (.inr (.sign message))).run state =
      (impl hmac joint dh seed scalar extractImpl (.inr (.sign message))).run state :=
  rfl

/-- Outside the table domain (a key other than the zero key, or a message that is not 192 bytes long) the public HMAC is the existing family's real branch, for every Extract service of that family. -/
theorem rom_public_real (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (extractImpl : QueryImpl HmacOracle (StateT HmacOracle.QueryCache ProbComp))
    (key : HmacBlock) (message : Pqxdh.Bytes)
    (outside : ¬(key = zeroSalt ∧ message.length = 192)) (state : State) :
    (romImpl hmac joint dh seed scalar (.inr (.publicHmac key message))).run state =
      (impl hmac joint dh seed scalar extractImpl (.inr (.publicHmac key message))).run state := by
  show romImpl hmac joint dh seed scalar (.inr (.publicHmac key message)) state =
    impl hmac joint dh seed scalar extractImpl (.inr (.publicHmac key message)) state
  simp only [romImpl, eq_false outside, ↓reduceIte]
  rfl

/-- Inside the table domain a public HMAC query is one lazy-table read at the message, logged with its answer. -/
theorem rom_public_oracle (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (key : HmacBlock) (message : Pqxdh.Bytes)
    (inside : key = zeroSalt ∧ message.length = 192) (state : State) :
    (romImpl hmac joint dh seed scalar (.inr (.publicHmac key message))).run state =
      (fun result : HmacBlock × HmacOracle.QueryCache =>
        (result.1, (⟨state.history ++ [.publicHmac key message result.1], result.2⟩ : State))) <$>
        (HmacOracle.randomOracle message).run state.cache := by
  show romImpl hmac joint dh seed scalar (.inr (.publicHmac key message)) state = _
  simp only [romImpl, eq_true inside, ↓reduceIte]
  rw [map_eq_bind_pure_comp]
  rfl

/-- A public table query at a message that already has an entry returns that entry and leaves the table unchanged. -/
theorem rom_hit (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (key : HmacBlock) (message : Pqxdh.Bytes)
    (inside : key = zeroSalt ∧ message.length = 192) (state : State) (block : HmacBlock)
    (hit : state.cache message = some block) :
    (romImpl hmac joint dh seed scalar (.inr (.publicHmac key message))).run state =
      pure (block, (⟨state.history ++ [.publicHmac key message block], state.cache⟩ : State)) := by
  rw [rom_public_oracle hmac joint dh seed scalar key message inside state, randomOracle.run_eq,
    hit, map_pure]

/-- A public table query at a message without an entry samples one uniform 64-byte block, records it and returns it. -/
theorem rom_miss (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (key : HmacBlock) (message : Pqxdh.Bytes)
    (inside : key = zeroSalt ∧ message.length = 192) (state : State)
    (miss : state.cache message = none) :
    (romImpl hmac joint dh seed scalar (.inr (.publicHmac key message))).run state = (do
      let block ← $ᵗ HmacBlock
      pure (block, (⟨state.history ++ [.publicHmac key message block],
        state.cache.cacheQuery message block⟩ : State))) := by
  rw [rom_public_oracle hmac joint dh seed scalar key message inside state, randomOracle.run_eq,
    miss, map_bind]
  simp only [map_pure]

/-- A derivation whose input is rejected is logged and leaves the table unchanged, exactly as in the existing family (`PqxdhJointDhExtractFamily.rejected`). -/
theorem rom_rejected (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : Message) (state : State)
    (invalid : input joint dh seed scalar message = none) :
    (romImpl hmac joint dh seed scalar (.inr (.derive message))).run state =
      pure (none, { state with history := state.history ++ [.derive message none] }) := by
  unfold romImpl
  change (match input joint dh seed scalar message with
    | none =>
        pure (none, { state with history := state.history ++ [Observation.derive message none] })
    | some bytes => _) = _
  rw [invalid]

/-- A derivation with an actual input is one lazy-table read at the input bytes, logged with its answer. -/
theorem rom_derive_oracle (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : Message) (bytes : Pqxdh.Bytes)
    (present : input joint dh seed scalar message = some bytes) (state : State) :
    (romImpl hmac joint dh seed scalar (.inr (.derive message))).run state =
      (fun result : HmacBlock × HmacOracle.QueryCache =>
        (some result.1,
          (⟨state.history ++ [.derive message (some result.1)], result.2⟩ : State))) <$>
        (HmacOracle.randomOracle bytes).run state.cache := by
  show romImpl hmac joint dh seed scalar (.inr (.derive message)) state = _
  simp only [romImpl, present]
  rw [map_eq_bind_pure_comp]
  rfl

/-- A derivation whose input bytes already have an entry returns that entry and leaves the table unchanged, whichever query created it: a Server or Beacon derivation under any peer encoding, or the adversary's public zero-key query at the same bytes. -/
theorem rom_derive_hit (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : Message) (bytes : Pqxdh.Bytes)
    (present : input joint dh seed scalar message = some bytes) (state : State) (prk : HmacBlock)
    (hit : state.cache bytes = some prk) :
    (romImpl hmac joint dh seed scalar (.inr (.derive message))).run state =
      pure (some prk, (⟨state.history ++ [.derive message (some prk)], state.cache⟩ : State)) := by
  rw [rom_derive_oracle hmac joint dh seed scalar message bytes present state, randomOracle.run_eq,
    hit, map_pure]

/-- A derivation whose input bytes have no entry samples one uniform 64-byte PRK, records it at the input bytes and returns it. -/
theorem rom_derive_miss (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : Message) (bytes : Pqxdh.Bytes)
    (present : input joint dh seed scalar message = some bytes) (state : State)
    (miss : state.cache bytes = none) :
    (romImpl hmac joint dh seed scalar (.inr (.derive message))).run state = (do
      let prk ← $ᵗ HmacBlock
      pure (some prk, (⟨state.history ++ [.derive message (some prk)],
        state.cache.cacheQuery bytes prk⟩ : State))) := by
  rw [rom_derive_oracle hmac joint dh seed scalar message bytes present state, randomOracle.run_eq,
    miss, map_bind]
  simp only [map_pure]

/-- An honest derivation and the adversary's public zero-key query at the same actual input bytes are the same table read: they give the same block (wrapped in `some` for the derivation) and the same resulting table. Only the logged request differs. -/
theorem rom_side (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : Message) (bytes : Pqxdh.Bytes)
    (present : input joint dh seed scalar message = some bytes) (state : State) :
    (fun result : Option HmacBlock × State => (result.1, result.2.cache)) <$>
        (romImpl hmac joint dh seed scalar (.inr (.derive message))).run state =
      (fun result : HmacBlock × State => (some result.1, result.2.cache)) <$>
        (romImpl hmac joint dh seed scalar (.inr (.publicHmac zeroSalt bytes))).run state := by
  rw [rom_derive_oracle hmac joint dh seed scalar message bytes present state,
    rom_public_oracle hmac joint dh seed scalar zeroSalt bytes
      ⟨rfl, input_length joint dh seed scalar message bytes present⟩ state,
    Functor.map_map, Functor.map_map]

/-- The root's Expand request, the 47-byte message `INFO_PQ ‖ 1`, is outside the table domain for every PRK, including a PRK equal to the zero key. -/
theorem rootExpand_outside (prk : HmacBlock) :
    ¬(prk = zeroSalt ∧ rootExpandInput.length = 192) := by
  simp [rootExpandInput, Pqxdh.INFO_PQ]

/-- A root request of the reduction `PqxdhJointDhExtractRoot.reduction` under the R1 family reads the table once at the actual input bytes and then makes one real 47-byte Expand query, so the returned root is the real Expand of the table entry. Both requests are logged; a rejected input is logged and returns no root. -/
theorem rom_root (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : Message) (state : State) :
    ((romImpl hmac joint dh seed scalar ∘ₛ PqxdhJointDhExtractRoot.reduction)
        (.inr (.derive message))).run state =
      match input joint dh seed scalar message with
      | none => pure (none, { state with history := state.history ++ [.derive message none] })
      | some bytes =>
          (fun result : HmacBlock × HmacOracle.QueryCache =>
            (some (expandRoot hmac result.1),
              (⟨state.history ++ [.derive message (some result.1),
                  .publicHmac result.1 rootExpandInput (hmac.eval result.1 rootExpandInput)],
                result.2⟩ : State))) <$>
            (HmacOracle.randomOracle bytes).run state.cache := by
  rw [QueryImpl.apply_compose]
  simp only [PqxdhJointDhExtractRoot.reduction, PqxdhJointDhExtractRoot.root, simulateQ_bind,
    simulateQ_spec_query, StateT.run_bind]
  cases present : input joint dh seed scalar message with
  | none =>
      rw [rom_rejected hmac joint dh seed scalar message state present]
      simp only [pure_bind, simulateQ_pure, StateT.run_pure]
  | some bytes =>
      rw [rom_derive_oracle hmac joint dh seed scalar message bytes present state, bind_map_left]
      dsimp only
      rw [map_eq_bind_pure_comp]
      refine bind_congr fun result => ?_
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind,
        StateT.run_pure]
      rw [rom_public_real hmac joint dh seed scalar (actualExtract hmac) result.1 rootExpandInput
        (rootExpand_outside result.1), public_evaluation]
      simp [expandRoot, List.append_assoc]

/-- The root-valued reduction `PqxdhJointDhExtractRoot.reduction` forwards coin, signing and public HMAC queries to the R1 family unchanged; only root requests are translated (`rom_root`). -/
theorem rom_forward (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) :
    (∀ coin : ℕ,
      (romImpl hmac joint dh seed scalar ∘ₛ PqxdhJointDhExtractRoot.reduction) (.inl coin) =
        romImpl hmac joint dh seed scalar (.inl coin)) ∧
    (∀ message : Pqxdh.Bytes,
      (romImpl hmac joint dh seed scalar ∘ₛ PqxdhJointDhExtractRoot.reduction)
          (.inr (.sign message)) =
        romImpl hmac joint dh seed scalar (.inr (.sign message))) ∧
    (∀ (key : HmacBlock) (message : Pqxdh.Bytes),
      (romImpl hmac joint dh seed scalar ∘ₛ PqxdhJointDhExtractRoot.reduction)
          (.inr (.publicHmac key message)) =
        romImpl hmac joint dh seed scalar (.inr (.publicHmac key message))) := by
  refine ⟨fun coin => ?_, fun message => ?_, fun key message => ?_⟩ <;>
    simp only [QueryImpl.apply_compose, PqxdhJointDhExtractRoot.reduction, simulateQ_spec_query]

/-- Each query only appends to the family history, and neither its answer nor its resulting table depends on the history: running from any history is running from the empty history and prepending it. -/
theorem rom_history_append (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (query : Spec.Domain)
    (history : PqxdhJointDhExtractFamily.History)
    (cache : HmacOracle.QueryCache) :
    (romImpl hmac joint dh seed scalar query).run ⟨history, cache⟩ =
      (fun result : Spec.Range query × State =>
        (result.1, (⟨history ++ result.2.history, result.2.cache⟩ : State))) <$>
        (romImpl hmac joint dh seed scalar query).run ⟨[], cache⟩ := by
  rcases query with coin | (message | ⟨key, message⟩ | message)
  · simp [romImpl, StateT.run]
  · simp [romImpl, StateT.run]
  · by_cases inside : key = zeroSalt ∧ message.length = 192
    · rw [rom_public_oracle hmac joint dh seed scalar key message inside,
        rom_public_oracle hmac joint dh seed scalar key message inside, Functor.map_map]
      simp
    · rw [rom_public_real hmac joint dh seed scalar (actualExtract hmac) key message inside,
        rom_public_real hmac joint dh seed scalar (actualExtract hmac) key message inside,
        public_evaluation, public_evaluation]
      simp
  · cases present : input joint dh seed scalar message with
    | none =>
        rw [rom_rejected hmac joint dh seed scalar message _ present,
          rom_rejected hmac joint dh seed scalar message _ present]
        simp
    | some bytes =>
        rw [rom_derive_oracle hmac joint dh seed scalar message bytes present,
          rom_derive_oracle hmac joint dh seed scalar message bytes present, Functor.map_map]
        simp

/-- The same history independence for the root-valued interface: each query of the composed family `romImpl … ∘ₛ PqxdhJointDhExtractRoot.reduction` only appends to the history, and neither its answer nor its resulting table depends on the history. -/
theorem rom_reduction_history_append (hmac : HmacSha512) (joint : Primitives)
    (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (query : PqxdhJointDhExtractRoot.RootSpec.Domain) (history : PqxdhJointDhExtractFamily.History)
    (cache : HmacOracle.QueryCache) :
    ((romImpl hmac joint dh seed scalar ∘ₛ PqxdhJointDhExtractRoot.reduction) query).run
        ⟨history, cache⟩ =
      (fun result : PqxdhJointDhExtractRoot.RootSpec.Range query × State =>
        (result.1, (⟨history ++ result.2.history, result.2.cache⟩ : State))) <$>
        ((romImpl hmac joint dh seed scalar ∘ₛ PqxdhJointDhExtractRoot.reduction) query).run
          ⟨[], cache⟩ := by
  obtain ⟨forwardCoin, forwardSign, forwardPublic⟩ := rom_forward hmac joint dh seed scalar
  rcases query with coin | (message | ⟨key, message⟩ | message)
  · rw [forwardCoin]
    exact rom_history_append hmac joint dh seed scalar (.inl coin) history cache
  · rw [forwardSign]
    exact rom_history_append hmac joint dh seed scalar (.inr (.sign message)) history cache
  · rw [forwardPublic]
    exact rom_history_append hmac joint dh seed scalar (.inr (.publicHmac key message)) history
      cache
  · rw [rom_root, rom_root]
    cases input joint dh seed scalar message with
    | none => simp
    | some bytes =>
        rw [Functor.map_map]
        simp

/-- One lazy-table read keeps every earlier entry and records its answer at the queried bytes. -/
theorem oracle_step (bytes : Pqxdh.Bytes) (cache : HmacOracle.QueryCache)
    (result : HmacBlock × HmacOracle.QueryCache)
    (reached : result ∈ support ((HmacOracle.randomOracle bytes).run cache)) :
    cache ≤ result.2 ∧ result.2 bytes = some result.1 := by
  refine ⟨QueryImpl.withCaching_cache_le uniformSampleImpl bytes cache result reached, ?_⟩
  rw [randomOracle.run_eq] at reached
  cases hit : cache bytes with
  | some block =>
      rw [hit, support_pure, Set.mem_singleton_iff] at reached
      subst reached
      exact hit
  | none =>
      rw [hit, support_bind] at reached
      simp only [support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at reached
      obtain ⟨block, _, rfl⟩ := reached
      exact QueryCache.cacheQuery_self cache bytes block

/-- The table only grows: every entry present before a query is present, with the same value, after it. -/
theorem rom_cache_mono (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (query : Spec.Domain) (state : State)
    (result : Spec.Range query × State)
    (reached : result ∈ support ((romImpl hmac joint dh seed scalar query).run state)) :
    state.cache ≤ result.2.cache := by
  rcases query with coin | (message | ⟨key, message⟩ | message)
  · simp only [romImpl, StateT.run, support_bind, support_pure, Set.mem_iUnion,
      Set.mem_singleton_iff] at reached
    obtain ⟨_, _, rfl⟩ := reached
    exact le_rfl
  · simp only [romImpl, StateT.run, support_pure, Set.mem_singleton_iff] at reached
    subst reached
    exact le_rfl
  · by_cases inside : key = zeroSalt ∧ message.length = 192
    · rw [rom_public_oracle hmac joint dh seed scalar key message inside, support_map] at reached
      obtain ⟨step, stepReached, rfl⟩ := reached
      exact (oracle_step message state.cache step stepReached).1
    · rw [rom_public_real hmac joint dh seed scalar (actualExtract hmac) key message inside,
        public_evaluation, support_pure, Set.mem_singleton_iff] at reached
      subst reached
      exact le_rfl
  · cases present : input joint dh seed scalar message with
    | none =>
        rw [rom_rejected hmac joint dh seed scalar message state present, support_pure,
          Set.mem_singleton_iff] at reached
        subst reached
        exact le_rfl
    | some bytes =>
        rw [rom_derive_oracle hmac joint dh seed scalar message bytes present state,
          support_map] at reached
        obtain ⟨step, stepReached, rfl⟩ := reached
        exact (oracle_step bytes state.cache step stepReached).1

/-- The table only grows under the root-valued interface as well: every entry present before a query of `romImpl … ∘ₛ PqxdhJointDhExtractRoot.reduction` is present, with the same value, after it. -/
theorem rom_reduction_cache_mono (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (query : PqxdhJointDhExtractRoot.RootSpec.Domain)
    (state : State) (result : PqxdhJointDhExtractRoot.RootSpec.Range query × State)
    (reached : result ∈ support
      (((romImpl hmac joint dh seed scalar ∘ₛ PqxdhJointDhExtractRoot.reduction) query).run
        state)) :
    state.cache ≤ result.2.cache := by
  obtain ⟨forwardCoin, forwardSign, forwardPublic⟩ := rom_forward hmac joint dh seed scalar
  rcases query with coin | (message | ⟨key, message⟩ | message)
  · rw [forwardCoin] at reached
    exact rom_cache_mono hmac joint dh seed scalar (.inl coin) state result reached
  · rw [forwardSign] at reached
    exact rom_cache_mono hmac joint dh seed scalar (.inr (.sign message)) state result reached
  · rw [forwardPublic] at reached
    exact rom_cache_mono hmac joint dh seed scalar (.inr (.publicHmac key message)) state result
      reached
  · rw [rom_root] at reached
    split at reached
    · rw [support_pure, Set.mem_singleton_iff] at reached
      subst reached
      exact le_rfl
    · rw [support_map] at reached
      obtain ⟨step, stepReached, rfl⟩ := reached
      exact (oracle_step _ state.cache step stepReached).1

/-- Every answer to a public HMAC query is the stage-B1 patched HMAC `romHmac hmac table` at any table that extends the resulting cache: the table entry inside the domain, the real function outside it. -/
theorem rom_public_patch (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (key : HmacBlock) (message : Pqxdh.Bytes)
    (state : State) (result : HmacBlock × State)
    (reached : result ∈ support
      ((romImpl hmac joint dh seed scalar (.inr (.publicHmac key message))).run state))
    (table : Pqxdh.Bytes → HmacBlock)
    (agrees : ∀ bytes block, result.2.cache bytes = some block → table bytes = block) :
    result.1 = (romHmac hmac table).eval key message := by
  by_cases inside : key = zeroSalt ∧ message.length = 192
  · rw [rom_public_oracle hmac joint dh seed scalar key message inside, support_map] at reached
    obtain ⟨step, stepReached, rfl⟩ := reached
    simp only [romHmac, eq_true inside, ↓reduceIte]
    exact (agrees message step.1 (oracle_step message state.cache step stepReached).2).symm
  · rw [rom_public_real hmac joint dh seed scalar (actualExtract hmac) key message inside,
      public_evaluation, support_pure, Set.mem_singleton_iff] at reached
    subst reached
    exact (PqxdhExtractRomSeparation.eval_other hmac table key message inside).symm

/-- Every answer to a derivation with an actual input is the zero-salt Extract of that input under the stage-B1 patched HMAC, at any table that extends the resulting cache. -/
theorem rom_derive_patch (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : Message) (bytes : Pqxdh.Bytes)
    (present : input joint dh seed scalar message = some bytes) (state : State)
    (result : Option HmacBlock × State)
    (reached : result ∈ support
      ((romImpl hmac joint dh seed scalar (.inr (.derive message))).run state))
    (table : Pqxdh.Bytes → HmacBlock)
    (agrees : ∀ bytes block, result.2.cache bytes = some block → table bytes = block) :
    result.1 = some (extract (romHmac hmac table) bytes) := by
  rw [rom_derive_oracle hmac joint dh seed scalar message bytes present state,
    support_map] at reached
  obtain ⟨step, stepReached, rfl⟩ := reached
  rw [PqxdhExtractRomSeparation.extract_root hmac table bytes
    (input_length joint dh seed scalar message bytes present)]
  exact congrArg some (agrees bytes step.1 (oracle_step bytes state.cache step stepReached).2).symm

/-- After an honest derivation, the adversary's public zero-key query at the same input bytes is a table hit that returns the derived PRK. -/
theorem derive_then_public (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : Message) (bytes : Pqxdh.Bytes)
    (present : input joint dh seed scalar message = some bytes) (state : State)
    (result : Option HmacBlock × State)
    (reached : result ∈ support ((romImpl hmac joint dh seed scalar (.inr (.derive message))).run state)) :
    ∃ prk, result.1 = some prk ∧
      (romImpl hmac joint dh seed scalar (.inr (.publicHmac zeroSalt bytes))).run result.2 =
        pure (prk, (⟨result.2.history ++ [.publicHmac zeroSalt bytes prk], result.2.cache⟩ : State)) := by
  rw [rom_derive_oracle hmac joint dh seed scalar message bytes present state, support_map] at reached
  obtain ⟨step, stepReached, rfl⟩ := reached
  exact ⟨step.1, rfl, rom_hit hmac joint dh seed scalar zeroSalt bytes
    ⟨rfl, input_length joint dh seed scalar message bytes present⟩ _ step.1
    (oracle_step bytes state.cache step stepReached).2⟩

/-- After the adversary's public zero-key query at 192-byte input bytes, every derivation (Server or Beacon form, under any peer encoding) whose input is those bytes returns the adversary's block. -/
theorem public_then_derive (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (bytes : Pqxdh.Bytes) (width : bytes.length = 192)
    (message : Message) (present : input joint dh seed scalar message = some bytes) (state : State)
    (result : HmacBlock × State)
    (reached : result ∈ support
      ((romImpl hmac joint dh seed scalar (.inr (.publicHmac zeroSalt bytes))).run state)) :
    (romImpl hmac joint dh seed scalar (.inr (.derive message))).run result.2 =
      pure (some result.1, (⟨result.2.history ++ [.derive message (some result.1)], result.2.cache⟩ : State)) := by
  rw [rom_public_oracle hmac joint dh seed scalar zeroSalt bytes ⟨rfl, width⟩ state, support_map] at reached
  obtain ⟨step, stepReached, rfl⟩ := reached
  exact rom_derive_hit hmac joint dh seed scalar message bytes present _ step.1
    (oracle_step bytes state.cache step stepReached).2

end BeaconcryptCore.Computational.PqxdhExtractRomFamily

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_coin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_coin

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_sign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_sign

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_public_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_public_real

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_public_oracle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_public_oracle

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_hit

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_miss

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_rejected

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_derive_oracle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_derive_oracle

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_derive_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_derive_hit

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_derive_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_derive_miss

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_side' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_side

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomFamily.rootExpand_outside' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomFamily.rootExpand_outside

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_root

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_history_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_history_append

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_reduction_history_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_reduction_history_append

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomFamily.oracle_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomFamily.oracle_step

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_cache_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_cache_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_reduction_cache_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_reduction_cache_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_public_patch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_public_patch

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_derive_patch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomFamily.rom_derive_patch

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomFamily.derive_then_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomFamily.derive_then_public

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomFamily.public_then_derive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomFamily.public_then_derive
