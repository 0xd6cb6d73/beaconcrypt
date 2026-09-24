import BeaconcryptCore.Computational.PqxdhInitialCtxFreeCallbacks

/-!
The literal ordinary prechallenge Beacon callback is evaluated with unblocked selected-key decapsulation and real fixed-HKDF root derivation. All non-raw callbacks have a concrete cache-free factorization; the raw branch remains the actual native shared-cache receive interpreter. This is the prechallenge interface, not the blocked postchallenge callback.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhOrdinaryNativeCache
open PqxdhPhase2SourceAux PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPhase1AcceptanceOracle
open PqxdhKemIndCca PqxdhJointKdfGame PqxdhPrivateKemSource PqxdhInitializerSecrecy
open PqxdhInitialCtxFreeCallbacks (Cache replace reply)
variable {ι I D K X Response A KemSK Result : Type} {baseSpec : OracleSpec ι}

abbrev NativeSpec (I D K X Response : Type) := PqxdhBeaconPhase2Publication.NativeSpec
  (PqxdhGeneratedBeaconState.IdentityHandle I) D (Option K) (X ⊕ PqxdhPhase2JointIdentity.Converted) Response

def safe : (NativeSpec I D K X Response).Domain → Prop
  | .inr (.inl _) => False
  | _ => True

section Callbacks
variable (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)

noncomputable def native : QueryImpl (NativeSpec I D K X Response) (StateT (SharedState A × BareState count) ProbComp) :=
  PqxdhPhase2NativeSource.native fixed baseImpl kem secret (directAux attachedVerify primitives count fixed localImpl)

set_option backward.isDefEq.respectTransparency false in
/-- Source preparation, real root/initializer and application preserve the CTX cache. Selected decapsulation retains its actual unblocked primitive computation and every optional result. -/
theorem native_cache (query : (NativeSpec I D K X Response).Domain) (admitted : safe query)
    (state : SharedState A × BareState count) (cache : Cache) :
    (native attachedVerify primitives count fixed localImpl baseImpl kem secret query).run (replace cache state) =
      reply cache <$> (native attachedVerify primitives count fixed localImpl baseImpl kem secret query).run state := by
  rcases query with (query | (query | query))
  · cases query with
    | decapsulate value key =>
        cases key with
        | none =>
            change ((fun result => (result, replace cache state)) <$>
              (Option.map PqxdhRootTableInitialization.rootArray <$>
                simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret (PqxdhPhase2InputBytes.ciphertext value)))) =
              reply cache <$> ((fun result => (result, state)) <$>
                (Option.map PqxdhRootTableInitialization.rootArray <$>
                  simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret (PqxdhPhase2InputBytes.ciphertext value))))
            simp only [Functor.map_map, reply, replace]
        | some key =>
            exact PqxdhInitialCtxFreeCallbacks.direct_cache attachedVerify primitives count fixed localImpl
              (.localDecapsulation value key) (by trivial) state cache
    | eraseShared secrets =>
        simp only [native, PqxdhPhase2NativeSource.native, StateT.run_pure, map_pure, reply, replace]
    | _ =>
        simp only [native, PqxdhPhase2NativeSource.native]
        apply PqxdhInitialCtxFreeCallbacks.direct_cache attachedVerify primitives count fixed localImpl
        trivial
  · exact False.elim admitted
  · cases query with
    | root input =>
        simp only [native, PqxdhPhase2NativeSource.native, StateT.run_pure, map_pure, reply, replace]
    | _ =>
        simp only [native, PqxdhPhase2NativeSource.native]
        apply PqxdhInitialCtxFreeCallbacks.direct_cache attachedVerify primitives count fixed localImpl
        trivial

noncomputable def evaluated : QueryImpl (PqxdhPhase2SourceScheduler.NativeSpec I D K X Response)
    (StateT (SharedState (A × BareState count)) ProbComp) := fun query state =>
  simulateQ (PqxdhPhase2NativeSource.interpretation baseImpl kem secret)
    ((PqxdhPhase2SourceScheduler.ordinaryNative attachedVerify primitives count fixed localImpl query).run state)

noncomputable def packedSource : QueryImpl (PqxdhPhase2SourceScheduler.NativeSpec I D K X Response)
    (StateT (SharedState (A × BareState count)) ProbComp) :=
  PqxdhPhase2SharedIdentity.packed
    (native attachedVerify primitives count fixed localImpl baseImpl kem secret ∘ₛ
      PqxdhPhase2KemHandles.native PqxdhPhase2KemProvenance.encode)

set_option backward.isDefEq.respectTransparency false in
/-- The actual ordinary prechallenge service and original private native interpreter agree with their complete packed state and unblocked decapsulation. -/
theorem evaluated_source (query : (PqxdhPhase2SourceScheduler.NativeSpec I D K X Response).Domain)
    (state : SharedState (A × BareState count)) :
    (evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret query).run state =
      (packedSource attachedVerify primitives count fixed localImpl baseImpl kem secret query).run state := by
  change simulateQ (PqxdhPhase2NativeSource.interpretation baseImpl kem secret)
    ((simulateQ (PqxdhPhase2SharedIdentity.packed (PqxdhPhase2PreChallenge.pre (baseSpec := baseSpec) fixed
      (borrowedAux attachedVerify primitives count fixed localImpl)))
        (PqxdhPhase2KemHandles.native PqxdhPhase2KemProvenance.encode query)).run state) = _
  have original := PqxdhPhase2SharedIdentity.packed_run
    (PqxdhPhase2PreChallenge.pre (baseSpec := baseSpec) fixed (borrowedAux attachedVerify primitives count fixed localImpl))
    (PqxdhPhase2KemHandles.native PqxdhPhase2KemProvenance.encode query) (PqxdhPhase2SharedIdentity.unpack state)
  simp only [PqxdhPhase2SharedIdentity.pack, PqxdhPhase2SharedIdentity.unpack, Prod.mk.eta] at original
  rw [← original, simulateQ_map, PqxdhPhase2NativeSource.pre_complete]
  rfl

def sourceSafe : (PqxdhPhase2SourceScheduler.NativeSpec I D K X Response).Domain → Prop
  | .inr (.inl _) => False
  | _ => True

noncomputable def mapped : QueryImpl (PqxdhPhase2SourceScheduler.NativeSpec I D K X Response)
    (StateT (SharedState A × BareState count) ProbComp) :=
  native attachedVerify primitives count fixed localImpl baseImpl kem secret ∘ₛ
    PqxdhPhase2KemHandles.native PqxdhPhase2KemProvenance.encode

set_option backward.isDefEq.respectTransparency false in
/-- The existing generated/prior KEM argument translation preserves actual non-raw cache independence and all real decapsulation replies. -/
theorem mapped_cache (query : (PqxdhPhase2SourceScheduler.NativeSpec I D K X Response).Domain)
    (admitted : sourceSafe query) (state : SharedState A × BareState count) (cache : Cache) :
    (mapped attachedVerify primitives count fixed localImpl baseImpl kem secret query).run (replace cache state) =
      reply cache <$> (mapped attachedVerify primitives count fixed localImpl baseImpl kem secret query).run state := by
  rcases query with (query | (query | query))
  · cases query
    all_goals
      simp only [mapped, QueryImpl.compose, PqxdhPhase2KemHandles.native,
        PqxdhPhase2KemHandles.preparation, simulateQ_spec_query]
      apply native_cache attachedVerify primitives count fixed localImpl baseImpl kem secret
      trivial
  · exact False.elim admitted
  · simp only [mapped, QueryImpl.compose, PqxdhPhase2KemHandles.native, simulateQ_spec_query]
    apply native_cache attachedVerify primitives count fixed localImpl baseImpl kem secret
    trivial

/-- The original ordinary callback evaluated at an empty CTX cache, projecting away only that unused component. -/
noncomputable def cacheFree : QueryImpl (PqxdhPhase2SourceScheduler.NativeSpec I D K X Response)
    (StateT (A × BareState count) ProbComp) := fun query state =>
  (fun result => (result.1, result.2.1)) <$>
    (evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret query).run (state, ∅)

set_option backward.isDefEq.respectTransparency false in
/-- Every non-raw ordinary callback is its concrete local computation with the same incoming CTX cache restored. The full result and both private poststates agree. -/
theorem local_source (query : (PqxdhPhase2SourceScheduler.NativeSpec I D K X Response).Domain)
    (admitted : sourceSafe query) (state : A × BareState count) (cache : Cache) :
    (evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret query).run (state, cache) =
      (fun result => (result.1, (result.2, cache))) <$>
        (cacheFree attachedVerify primitives count fixed localImpl baseImpl kem secret query).run state := by
  change (evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret query).run (state, cache) =
    (fun result => (result.1, (result.2, cache))) <$>
      ((fun result => (result.1, result.2.1)) <$>
        (evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret query).run (state, ∅))
  simp only [Functor.map_map]
  rw [evaluated_source, evaluated_source]
  simp only [packedSource, PqxdhPhase2SharedIdentity.packed, StateT.run, Functor.map_map]
  change (fun result => (result.1, PqxdhPhase2SharedIdentity.pack result.2)) <$>
      (mapped attachedVerify primitives count fixed localImpl baseImpl kem secret query).run ((state.1, cache), state.2) =
    (fun result => (result.1, ((result.2.1.1, result.2.2), cache))) <$>
      (mapped attachedVerify primitives count fixed localImpl baseImpl kem secret query).run ((state.1, ∅), state.2)
  have equality := mapped_cache attachedVerify primitives count fixed localImpl baseImpl kem secret query admitted
    ((state.1, ∅), state.2) cache
  change (mapped attachedVerify primitives count fixed localImpl baseImpl kem secret query).run ((state.1, cache), state.2) = _ at equality
  rw [equality]
  simp only [Functor.map_map, reply, replace, PqxdhPhase2SharedIdentity.pack]

set_option backward.isDefEq.respectTransparency false in
/-- The raw callback is the literal source native shared-cache receive service on the same complete packed auxiliary/identity state. -/
theorem raw_source (query : RawCtxSourceOpen.NativeSpec.Domain)
    (state : SharedState (A × BareState count)) :
    (evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret (.inr (.inl query))).run state =
      (RawCtxSharedPrimitive.nativeImpl fixed.crypto (RawCtxSourceHkdf.kdfImpl fixed) query).run state := by
  rw [evaluated_source]
  unfold packedSource PqxdhPhase2SharedIdentity.packed
  simp only [QueryImpl.compose, PqxdhPhase2KemHandles.native, simulateQ_spec_query]
  unfold native
  simp only [PqxdhPhase2NativeSource.native, directAux]
  rcases query with request | (bytes | input)
  · rfl
  · simp only [rawRun, RawCtxSharedPrimitive.nativeImpl, RawCtxSharedPrimitive.openingImpl,
      StateT.run, PqxdhPhase2SharedIdentity.pack, PqxdhPhase2SharedIdentity.unpack,
      bind_pure_comp, StateT.mk, Functor.map_map, Prod.mk.eta]
  · rfl

/-- No local primitive work disappears: its full uniform-query allowance is equivalent to the actual ordinary callback's bound at any incoming cache. -/
theorem local_uniform (query : (PqxdhPhase2SourceScheduler.NativeSpec I D K X Response).Domain)
    (admitted : sourceSafe query) (state : A × BareState count) (cache : Cache) (q : Nat) :
    ((cacheFree attachedVerify primitives count fixed localImpl baseImpl kem secret query).run state).IsTotalQueryBound q ↔
      ((evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret query).run (state, cache)).IsTotalQueryBound q := by
  rw [local_source attachedVerify primitives count fixed localImpl baseImpl kem secret query admitted state cache]
  simp only [IsTotalQueryBound, isQueryBound_map_iff]

end Callbacks
end BeaconcryptCore.Computational.PqxdhOrdinaryNativeCache

/-- info: 'BeaconcryptCore.Computational.PqxdhOrdinaryNativeCache.native_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrdinaryNativeCache.native_cache

/-- info: 'BeaconcryptCore.Computational.PqxdhOrdinaryNativeCache.evaluated_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrdinaryNativeCache.evaluated_source

/-- info: 'BeaconcryptCore.Computational.PqxdhOrdinaryNativeCache.mapped_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrdinaryNativeCache.mapped_cache

/-- info: 'BeaconcryptCore.Computational.PqxdhOrdinaryNativeCache.local_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrdinaryNativeCache.local_source

/-- info: 'BeaconcryptCore.Computational.PqxdhOrdinaryNativeCache.raw_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrdinaryNativeCache.raw_source

/-- info: 'BeaconcryptCore.Computational.PqxdhOrdinaryNativeCache.local_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrdinaryNativeCache.local_uniform
