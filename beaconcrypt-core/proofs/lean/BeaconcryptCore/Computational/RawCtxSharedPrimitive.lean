import BeaconcryptCore.Computational.RawCtxCanonicalOpening

/-!
The actual source KDF and native commitment/opening services use one complete primitive state containing the same CTX random-oracle cache. KDF callbacks may depend on and update that state; no independent record-key table or separation from earlier hash observations is introduced. The native hash specialization returns the actual cached or newly sampled 64-byte value, and the base AEAD service uses the existing ordinary functional interpretation. Native optional-hash failure is replaced only under the explicit stronger ROM-total contract.

Exact opening equalities retain the actual optional plaintext, all prior and failed cache entries, auxiliary state and canonical attempt/suffix bookkeeping. The canonical statement concerns one reached opening under its explicit selected-target equation. The separate raw-only schedule equality is an instantiation of the existing source interpreter and retains its full owner and primitive states; it does not silently replace every evolving-key opening by one fixed-key security experiment.

The uniform-oracle ledger charges at most 64 byte-valued draws per source hash request plus an explicit bound on every actual KDF callback. The whole raw schedule derives the hash count from its outer raw-attempt cap, while the aggregate KDF count remains an explicit bound on the actual expanded source program. Each KDF uniform request can have any finite result type. Functional AEAD, KDF/local computation, byte copying, cache lookup and native parsing are not free work, and these declarations are not compiled runtime or efficiency guarantees.

Arbitrary KDF state updates are permitted for this functional equality, not asserted to implement a consistent shared random oracle. The concrete source HKDF interpreter must supply its own cache-consistency, functional and resource contracts. No primitive implementation, key-distribution or authentication premise, statistical bound, global security conclusion, native library/compiler/representation result, interleaved send/reveal action or multi-owner reduction is added. API plaintext observations and network-only confidentiality remain distinct interfaces.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxSharedPrimitive
open CtxRomAuth RawCtxSourceOpen RawCtxCanonicalOpening

abbrev KdfSpec := SymmetricRatchetKdfRequest →ₒ RatchetKdfResponse
abbrev SharedState (Auxiliary : Type) := Auxiliary × CtxRO.QueryCache

/-- Native hash and base opening retain one actual cache and all unrelated primitive state. -/
noncomputable def openingImpl {Auxiliary : Type} (c : Pqxdh.Crypto) :
    QueryImpl OpenSpec (StateT (SharedState Auxiliary) ProbComp) := fun query state =>
  match query with
  | .inl bytes => do
      let (digest, cache) ← (ctxRandomOracle ((), bytes)).run state.2
      pure (some digest.toList, (state.1, cache))
  | .inr input => pure (baseOpen c input, state)

/-- The source KDF sees the same complete primitive state and cache, without any independence assumption. -/
noncomputable def nativeImpl {Auxiliary : Type} (c : Pqxdh.Crypto)
    (kdf : QueryImpl KdfSpec (StateT (SharedState Auxiliary) ProbComp)) :
    QueryImpl NativeSpec (StateT (SharedState Auxiliary) ProbComp) := fun query state =>
  match query with
  | .inl request => (kdf request).run state
  | .inr request => (openingImpl c request).run state

/-- Embedding a real native opening forwards its unchanged request to the shared interpreter. -/
theorem opening_query {Auxiliary : Type} (c : Pqxdh.Crypto)
    (kdf : QueryImpl KdfSpec (StateT (SharedState Auxiliary) ProbComp))
    (query : OpenSpec.Domain) :
    (nativeImpl c kdf ∘ₛ openLift) query = openingImpl (Auxiliary := Auxiliary) c query := by
  rw [openLift_apply]
  rfl

/-- One native opening service is the exact ROM interpretation with unrelated primitive state retained. -/
theorem opening_step {Auxiliary : Type} (c : Pqxdh.Crypto)
    (query : OpenSpec.Domain) (auxiliary : Auxiliary) (cache : CtxRO.QueryCache) :
    (openingImpl c query).run (auxiliary, cache) =
      (fun result => (result.1, (auxiliary, result.2))) <$>
        (simulateQ ctxRandomOracle (romAdapter c query)).run cache := by
  cases query with
  | inl bytes =>
    simp only [romAdapter, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, simulateQ_pure, StateT.run_pure, map_bind, map_pure]
    rfl
  | inr input => rfl

/-- Any adaptive sequence of native opening services retains the same cache, auxiliary state and complete result. -/
theorem opening_complete {Auxiliary Result : Type} (c : Pqxdh.Crypto)
    (client : OracleComp OpenSpec Result) (auxiliary : Auxiliary) (cache : CtxRO.QueryCache) :
    (simulateQ (openingImpl c) client).run (auxiliary, cache) =
      (fun result => (result.1, (auxiliary, result.2))) <$>
        (simulateQ ctxRandomOracle (simulateQ (romAdapter c) client)).run cache := by
  simpa only [QueryImpl.simulateQ_compose, _root_.Prod.map_def, id_eq] using
    (OracleComp.map_run_simulateQ_eq_of_query_map_eq
      (ctxRandomOracle ∘ₛ romAdapter c) (openingImpl c) (fun state => (auxiliary, state))
      (fun query state => (opening_step c query auxiliary state).symm) client cache).symm

/-- Native dispatch preserves the complete opening result and paired shared-cache state. -/
theorem native_opening_complete {Auxiliary Result : Type} (c : Pqxdh.Crypto)
    (kdf : QueryImpl KdfSpec (StateT (SharedState Auxiliary) ProbComp))
    (client : OracleComp OpenSpec Result) (auxiliary : Auxiliary) (cache : CtxRO.QueryCache) :
    (simulateQ (nativeImpl c kdf) (simulateQ openLift client)).run (auxiliary, cache) =
      (fun result => (result.1, (auxiliary, result.2))) <$>
        (simulateQ ctxRandomOracle (simulateQ (romAdapter c) client)).run cache := by
  have handlers : nativeImpl c kdf ∘ₛ openLift = openingImpl (Auxiliary := Auxiliary) c :=
    funext (opening_query c kdf)
  rw [← QueryImpl.simulateQ_compose, handlers]
  exact opening_complete c client auxiliary cache

/-- The actual native opening reaches the canonical kernel with both unrelated primitive state and full canonical cache bookkeeping retained. -/
theorem native_canonical_opening {Auxiliary : Type} (c : Pqxdh.Crypto)
    (kdf : QueryImpl KdfSpec (StateT (SharedState Auxiliary) ProbComp))
    (input : RawCtxWholeOwner.OpenInput) (slices : RawCtxFrameDecoding.Slices)
    (hslices : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices)
    (had : input.context.associatedData.length = 153)
    (decode : AdaptiveCtxReceive.RawDecoder) (state : AdaptiveCtxCanonical.CanonicalState)
    (hdecode : decode input.context.raw = some (selectedTarget input slices hslices had))
    (auxiliary : Auxiliary) :
    (fun result => (result.1, (result.2.1,
      afterOpening state (selectedTarget input slices hslices had) result.2.2))) <$>
      (simulateQ (nativeImpl c kdf) (simulateQ openLift (openInput input))).run
        (auxiliary, state.ctx.cache) =
      (fun result => (result.1, (auxiliary, result.2))) <$>
        AdaptiveCtxCanonical.canonicalRaw decode c (sourceKey input) input.context.raw state := by
  rw [native_opening_complete, Functor.map_map]
  have equal := congrArg (fun computation =>
    (fun result => (result.1, (auxiliary, result.2))) <$> computation)
    (sourceOpening_canonical c input slices hslices had decode state hdecode)
  simpa only [sourceOpening, bind_pure_comp, Functor.map_map, Function.comp_def] using equal

/-- Each private service pays its actual category: an explicit KDF budget, one possible 64-byte hash draw, or no uniform draw for functional AEAD. -/
theorem native_uniform_step {Auxiliary : Type} (c : Pqxdh.Crypto)
    (kdf : QueryImpl KdfSpec (StateT (SharedState Auxiliary) ProbComp)) (kdfCoins : Nat)
    (bounded : ∀ request state, ((kdf request).run state).IsTotalQueryBound kdfCoins)
    (query : NativeSpec.Domain) (state : SharedState Auxiliary) :
    ((nativeImpl c kdf query).run state).IsTotalQueryBound
      (if query.isLeft then kdfCoins else if openingPredicate Sum.isLeft query then 64 else 0) := by
  cases query with
  | inl request => exact bounded request state
  | inr request =>
    cases request with
    | inl bytes =>
      change (do
        let result ← (ctxRandomOracle ((), bytes)).run state.2
        pure (some result.1.toList, (state.1, result.2))).IsTotalQueryBound 64
      rw [bind_pure_comp]
      unfold IsTotalQueryBound
      rw [isQueryBound_map_iff]
      exact CtxComputationalSecurity.ctxRandomOracle_total_query_bound ((), bytes) state.2
    | inr input => trivial

/-- Complete adaptive execution charges KDF and actual shared hash requests separately, retaining every state-dependent continuation. -/
theorem native_uniform_bound {Auxiliary Result : Type} (c : Pqxdh.Crypto)
    (kdf : QueryImpl KdfSpec (StateT (SharedState Auxiliary) ProbComp)) (kdfCoins : Nat)
    (bounded : ∀ request state, ((kdf request).run state).IsTotalQueryBound kdfCoins)
    (client : OracleComp NativeSpec Result) (qKdf qHash : Nat)
    (kdfQueries : client.IsQueryBoundP (fun query => query.isLeft = true) qKdf)
    (hashQueries : client.IsQueryBoundP
      (fun query => openingPredicate Sum.isLeft query = true) qHash)
    (state : SharedState Auxiliary) :
    ((simulateQ (nativeImpl c kdf) client).run state).IsTotalQueryBound
      (kdfCoins * qKdf + 64 * qHash) := by
  induction client using OracleComp.inductionOn generalizing qKdf qHash state with
  | pure value => trivial
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at kdfQueries hashQueries
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    have tail := fun (reply : NativeSpec.Range query × SharedState Auxiliary) =>
      ih reply.1 _ _ (kdfQueries.2 reply.1)
      (hashQueries.2 reply.1) reply.2
    apply (isTotalQueryBound_bind (native_uniform_step c kdf kdfCoins bounded query state) tail).mono
    cases query with
    | inl request =>
      simp only [Sum.isLeft, openingPredicate, Bool.false_eq_true, eq_self,
        ite_true, ite_false, not_true_eq_false, false_or] at kdfQueries ⊢
      have enough : kdfCoins ≤ kdfCoins * qKdf := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left kdfCoins kdfQueries.1
      rw [Nat.mul_sub_left_distrib]
      omega
    | inr request =>
      cases request with
      | inl bytes =>
        simp only [Sum.isLeft, openingPredicate, Bool.false_eq_true, eq_self,
          ite_true, ite_false, not_true_eq_false, false_or] at hashQueries ⊢
        omega
      | inr input => simp [openingPredicate]

/-- The actual owner schedule shares the KDF's entire state and the exact CTX cache. -/
noncomputable def sharedSchedule {Metadata Auxiliary Result : Type} (c : Pqxdh.Crypto)
    (kdf : QueryImpl KdfSpec (StateT (SharedState Auxiliary) ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp RawCtxWholeOwner.RawSpec Result)
    (owner : RawCtxWholeOwner.OwnerState Metadata) (primitive : SharedState Auxiliary) :
    ProbComp ((Result × RawCtxWholeOwner.OwnerState Metadata) × SharedState Auxiliary) :=
  (simulateQ (nativeImpl c kdf) ((simulateQ (nativeOwnerImpl decode) client).run owner)).run primitive

/-- Complete native interpretation is the existing actual source schedule with only state-pair reassociation. -/
theorem sharedSchedule_source {Metadata Auxiliary Result : Type} (c : Pqxdh.Crypto)
    (kdf : QueryImpl KdfSpec (StateT (SharedState Auxiliary) ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp RawCtxWholeOwner.RawSpec Result)
    (owner : RawCtxWholeOwner.OwnerState Metadata) (primitive : SharedState Auxiliary) :
    sharedSchedule c kdf decode client owner primitive =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        RawCtxWholeOwner.scheduleGame (nativeImpl c kdf ∘ₛ nativeAdapter)
          decode client (owner, primitive) := by
  exact nativeSchedule_interpretation (nativeImpl c kdf) decode client owner primitive

/-- The actual source raw-attempt cap supplies the hash budget; KDF callback count and each callback's real coin work stay explicit. -/
theorem sharedSchedule_uniform {Metadata Auxiliary Result : Type} (c : Pqxdh.Crypto)
    (kdf : QueryImpl KdfSpec (StateT (SharedState Auxiliary) ProbComp)) (kdfCoins : Nat)
    (bounded : ∀ request state, ((kdf request).run state).IsTotalQueryBound kdfCoins)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp RawCtxWholeOwner.RawSpec Result)
    (owner : RawCtxWholeOwner.OwnerState Metadata) (primitive : SharedState Auxiliary)
    (qKdf qRaw : Nat) (rawQueries : client.IsTotalQueryBound qRaw)
    (kdfQueries : ((simulateQ (nativeOwnerImpl decode) client).run owner).IsQueryBoundP
      (fun query => query.isLeft = true) qKdf) :
    (sharedSchedule c kdf decode client owner primitive).IsTotalQueryBound
      (kdfCoins * qKdf + 64 * qRaw) := by
  exact native_uniform_bound c kdf kdfCoins bounded _ qKdf qRaw kdfQueries
    (nativeSchedule_bounds decode client qRaw rawQueries owner).1 primitive

end BeaconcryptCore.Computational.RawCtxSharedPrimitive

/--
info: 'BeaconcryptCore.Computational.RawCtxSharedPrimitive.opening_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedPrimitive.opening_query

/--
info: 'BeaconcryptCore.Computational.RawCtxSharedPrimitive.opening_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedPrimitive.opening_step

/--
info: 'BeaconcryptCore.Computational.RawCtxSharedPrimitive.opening_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedPrimitive.opening_complete

/--
info: 'BeaconcryptCore.Computational.RawCtxSharedPrimitive.native_opening_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedPrimitive.native_opening_complete

/--
info: 'BeaconcryptCore.Computational.RawCtxSharedPrimitive.native_canonical_opening' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedPrimitive.native_canonical_opening

/--
info: 'BeaconcryptCore.Computational.RawCtxSharedPrimitive.native_uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedPrimitive.native_uniform_step

/--
info: 'BeaconcryptCore.Computational.RawCtxSharedPrimitive.native_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedPrimitive.native_uniform_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxSharedPrimitive.sharedSchedule_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedPrimitive.sharedSchedule_source

/--
info: 'BeaconcryptCore.Computational.RawCtxSharedPrimitive.sharedSchedule_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedPrimitive.sharedSchedule_uniform
