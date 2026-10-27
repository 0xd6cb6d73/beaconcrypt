import BeaconcryptCore.Computational.PqxdhOrdinaryNativeCache
import BeaconcryptCore.Computational.RawCtxSelectiveSharedRom

/-!
The concrete ordinary prechallenge callback is compiled into explicit uniform and shared-hash requests. The raw native branch forwards its actual hash bytes; every non-raw branch executes its full source computation with all original uniform draws. Selected KEM decapsulation is unblocked and fixed-HKDF root derivation remains real. No selected message key is an argument of this compiler.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhOrdinaryNativeSharedRom
open PqxdhPhase2SourceAux PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPhase1AcceptanceOracle
open PqxdhKemIndCca PqxdhJointKdfGame PqxdhPrivateKemSource PqxdhInitializerSecrecy
open CtxRomAuth AdaptiveCtxSharedHash
open PqxdhOrdinaryNativeCache (cacheFree evaluated sourceSafe)
variable {ι I D K X Response A KemSK Result : Type} {baseSpec : OracleSpec ι}

/-- The original raw receive surface with its real fixed KDF and opening, exposing only the actual commitment hash call. -/
noncomputable def raw (fixed : FixedHkdfSha512NoSaltSource) : QueryImpl RawCtxSourceOpen.NativeSpec (OracleComp HashSpec)
  | .inl request => pure (RawCtxSourceHkdf.response fixed.crypto request)
  | .inr (.inl bytes) => (fun digest => some digest.toList) <$> HashSpec.query (.inr ((), bytes))
  | .inr (.inr input) => pure (RawCtxSourceOpen.baseOpen fixed.crypto input)

set_option backward.isDefEq.respectTransparency false in
/-- Raw replies and the complete cache agree with the original source interpreter, including the optional plaintext of native opening. -/
theorem raw_source (fixed : FixedHkdfSha512NoSaltSource) (query : RawCtxSourceOpen.NativeSpec.Domain)
    (ambient : A) (cache : CtxRO.QueryCache) :
    (RawCtxSharedPrimitive.nativeImpl fixed.crypto (RawCtxSourceHkdf.kdfImpl fixed) query).run (ambient, cache) =
      (fun result => (result.1, (ambient, result.2))) <$> (simulateQ hashImpl (raw fixed query)).run cache := by
  rcases query with request | (bytes | input)
  · rfl
  · simp only [raw, simulateQ_map, simulateQ_spec_query, StateT.run_map]
    change (do let result ← (ctxRandomOracle ((), bytes)).run cache
               pure (some result.1.toList, (ambient, result.2))) = _
    simp only [bind_pure_comp, Functor.map_map]
    rfl
  · rfl

section Callbacks
variable (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)

/-- The concrete ordinary callback, keeping the private native state local and the shared CTX cache in the hash challenger. -/
noncomputable def compiler : QueryImpl (PqxdhPhase2SourceScheduler.NativeSpec I D K X Response)
    (StateT (A × BareState count) (OracleComp HashSpec))
  | .inr (.inl query) => fun state => (fun result => (result, state)) <$> raw fixed query
  | query => fun state => simulateQ RawCtxSelectiveSharedRom.coins
      ((cacheFree attachedVerify primitives count fixed localImpl baseImpl kem secret query).run state)

set_option backward.isDefEq.respectTransparency false in
/-- One actual ordinary callback, all local private effects and the reached shared cache agree after compilation. This statement includes unblocked selected decapsulation and all rejected replies. -/
theorem step (query : (PqxdhPhase2SourceScheduler.NativeSpec I D K X Response).Domain)
    (state : A × BareState count) (cache : CtxRO.QueryCache) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ hashImpl ((compiler attachedVerify primitives count fixed localImpl baseImpl kem secret query).run state)).run cache =
        (evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret query).run (state, cache) := by
  rcases query with preparation | (query | application)
  · change (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ hashImpl (simulateQ RawCtxSelectiveSharedRom.coins
        ((cacheFree attachedVerify primitives count fixed localImpl baseImpl kem secret (.inl preparation)).run state))).run cache = _
    rw [RawCtxSelectiveSharedRom.coins_complete, Functor.map_map,
      PqxdhOrdinaryNativeCache.local_source attachedVerify primitives count fixed localImpl baseImpl kem secret (.inl preparation) (by trivial)]
  · rw [PqxdhOrdinaryNativeCache.raw_source]
    change (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ hashImpl ((fun result => (result, state)) <$> raw fixed query)).run cache = _
    simp only [simulateQ_map, StateT.run_map, Functor.map_map]
    exact (raw_source fixed query state cache).symm
  · change (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ hashImpl (simulateQ RawCtxSelectiveSharedRom.coins
        ((cacheFree attachedVerify primitives count fixed localImpl baseImpl kem secret (.inr (.inr application))).run state))).run cache = _
    rw [RawCtxSelectiveSharedRom.coins_complete, Functor.map_map,
      PqxdhOrdinaryNativeCache.local_source attachedVerify primitives count fixed localImpl baseImpl kem secret (.inr (.inr application)) (by trivial)]

/-- The full adaptive ordinary program retains both private states and the cache built by its actual previous queries. No cache is installed retrospectively. -/
theorem program (client : OracleComp (PqxdhPhase2SourceScheduler.NativeSpec I D K X Response) Result)
    (state : A × BareState count) (cache : CtxRO.QueryCache) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ hashImpl ((simulateQ (compiler attachedVerify primitives count fixed localImpl baseImpl kem secret) client).run state)).run cache =
        (simulateQ (evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret) client).run (state, cache) := by
  have perQuery : ∀ query before,
      Prod.map id (id : (A × BareState count) × CtxRO.QueryCache → (A × BareState count) × CtxRO.QueryCache) <$>
        (((hashImpl.mapStateTBase (compiler attachedVerify primitives count fixed localImpl baseImpl kem secret)).flattenStateT query).run before) =
        (evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret query).run before := by
    intro query before
    simpa only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run, StateT.mk, Functor.map_map, Prod.map_def, id_eq] using
      step attachedVerify primitives count fixed localImpl baseImpl kem secret query before.1 before.2
  have whole := map_run_simulateQ_eq_of_query_map_eq
    ((hashImpl.mapStateTBase (compiler attachedVerify primitives count fixed localImpl baseImpl kem secret)).flattenStateT)
    (evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret)
    id perQuery client (state, cache)
  have unpacked := congrArg (fun work => (fun result => (result.1.1, (result.1.2, result.2))) <$> work)
    (simulateQ_mapStateTBase_run_eq_map_flattenStateT hashImpl
      (compiler attachedVerify primitives count fixed localImpl baseImpl kem secret) client state cache)
  simp only [Functor.map_map, Prod.map_def, id_eq] at unpacked whole
  exact unpacked.trans whole

/-- The compiled whole execution is the literal source ordinaryNative program under its original local prechallenge KEM interpretation. -/
theorem original (client : OracleComp (PqxdhPhase2SourceScheduler.NativeSpec I D K X Response) Result)
    (state : A × BareState count) (cache : CtxRO.QueryCache) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ hashImpl ((simulateQ (compiler attachedVerify primitives count fixed localImpl baseImpl kem secret) client).run state)).run cache =
        simulateQ (PqxdhPhase2NativeSource.interpretation baseImpl kem secret)
          ((simulateQ (PqxdhPhase2SourceScheduler.ordinaryNative attachedVerify primitives count fixed localImpl) client).run (state, cache)) := by
  rw [program, QueryImpl.simulateQ_mapStateTBase_run]
  rfl

/-- Every raw native callback asks at most one hash query and no uniform query; fixed KDF and known-key opening remain actual deterministic work. -/
theorem raw_bills (query : RawCtxSourceOpen.NativeSpec.Domain) :
    (raw fixed query).IsQueryBoundP (HashClass true) 1 ∧
      (raw fixed query).IsQueryBoundP (HashClass false) 0 := by
  rcases query with request | (bytes | input)
  · simp [raw]
  · simp only [raw, isQueryBoundP_map_iff]
    exact ⟨(isQueryBoundP_query_iff (spec := HashSpec) (p := HashClass true) (.inr ((), bytes)) 1).2 (by simp [HashClass]),
      (isQueryBoundP_query_iff (spec := HashSpec) (p := HashClass false) (.inr ((), bytes)) 0).2 (by simp [HashClass])⟩
  · simp [raw]

/-- The concrete local callback forwards every original uniform draw and makes no hash call. Its allowance is a bound on the whole original local computation. -/
theorem local_bills (query : (PqxdhPhase2SourceScheduler.NativeSpec I D K X Response).Domain)
    (admitted : sourceSafe query) (state : A × BareState count) (q : Nat)
    (bounded : ((cacheFree attachedVerify primitives count fixed localImpl baseImpl kem secret query).run state).IsTotalQueryBound q) :
    ((compiler attachedVerify primitives count fixed localImpl baseImpl kem secret query).run state).IsQueryBoundP (HashClass true) 0 ∧
      ((compiler attachedVerify primitives count fixed localImpl baseImpl kem secret query).run state).IsQueryBoundP (HashClass false) q := by
  rcases query with preparation | (query | application)
  · exact ⟨RawCtxSelectiveSharedRom.coins_no_hash _, RawCtxSelectiveSharedRom.coins_bound _ q bounded⟩
  · exact False.elim admitted
  · exact ⟨RawCtxSelectiveSharedRom.coins_no_hash _, RawCtxSelectiveSharedRom.coins_bound _ q bounded⟩

set_option backward.isDefEq.respectTransparency false in
/-- A single callback uses at most one hash and its supplied complete native uniform allowance, including rejected queries. -/
theorem bills (query : (PqxdhPhase2SourceScheduler.NativeSpec I D K X Response).Domain)
    (state : A × BareState count) (q : Nat)
    (bounded : sourceSafe query → ((cacheFree attachedVerify primitives count fixed localImpl baseImpl kem secret query).run state).IsTotalQueryBound q) :
    ((compiler attachedVerify primitives count fixed localImpl baseImpl kem secret query).run state).IsQueryBoundP (HashClass true) 1 ∧
      ((compiler attachedVerify primitives count fixed localImpl baseImpl kem secret query).run state).IsQueryBoundP (HashClass false) q := by
  rcases query with preparation | (query | application)
  · obtain ⟨hash, coins⟩ := local_bills attachedVerify primitives count fixed localImpl baseImpl kem secret (.inl preparation) (by trivial) state q (bounded (by trivial))
    exact ⟨hash.mono (by omega), coins⟩
  · simpa only [compiler, StateT.run, isQueryBoundP_map_iff] using
      And.intro (raw_bills fixed query).1 ((raw_bills fixed query).2.mono (Nat.zero_le q))
  · obtain ⟨hash, coins⟩ := local_bills attachedVerify primitives count fixed localImpl baseImpl kem secret (.inr (.inr application)) (by trivial) state q (bounded (by trivial))
    exact ⟨hash.mono (by omega), coins⟩

/-- Across an adaptive native program, the source call cap bounds all hash calls and multiplies the complete local uniform allowance. Rejected calls remain in the same budget. -/
theorem program_bills (client : OracleComp (PqxdhPhase2SourceScheduler.NativeSpec I D K X Response) Result)
    (state : A × BareState count) (qCalls qLocal : Nat)
    (clientBound : client.IsTotalQueryBound qCalls)
    (localBound : ∀ query state, sourceSafe query →
      ((cacheFree attachedVerify primitives count fixed localImpl baseImpl kem secret query).run state).IsTotalQueryBound qLocal) :
    ((simulateQ (compiler attachedVerify primitives count fixed localImpl baseImpl kem secret) client).run state).IsQueryBoundP (HashClass true) qCalls ∧
      ((simulateQ (compiler attachedVerify primitives count fixed localImpl baseImpl kem secret) client).run state).IsQueryBoundP (HashClass false) (qCalls * qLocal) := by
  induction client using OracleComp.inductionOn generalizing qCalls state with
  | pure value => simp
  | query_bind query next ih =>
    cases qCalls with
    | zero => simp only [isTotalQueryBound_query_bind_iff, Nat.not_lt_zero, false_and] at clientBound
    | succ qCalls =>
      rw [isTotalQueryBound_query_bind_iff] at clientBound
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      have first := bills attachedVerify primitives count fixed localImpl baseImpl kem secret query state qLocal (localBound query state)
      have rest := fun result : (PqxdhPhase2SourceScheduler.NativeSpec I D K X Response).Range query × (A × BareState count) => ih result.1 result.2 qCalls (by simpa using clientBound.2 result.1)
      constructor
      · simpa only [Nat.add_comm] using isQueryBoundP_bind first.1 (fun result _ => (rest result).1)
      · simpa only [Nat.succ_mul, Nat.add_comm] using isQueryBoundP_bind first.2 (fun result _ => (rest result).2)

end Callbacks
end BeaconcryptCore.Computational.PqxdhOrdinaryNativeSharedRom

/-- info: 'BeaconcryptCore.Computational.PqxdhOrdinaryNativeSharedRom.raw_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrdinaryNativeSharedRom.raw_source

/-- info: 'BeaconcryptCore.Computational.PqxdhOrdinaryNativeSharedRom.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrdinaryNativeSharedRom.step

/-- info: 'BeaconcryptCore.Computational.PqxdhOrdinaryNativeSharedRom.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrdinaryNativeSharedRom.program

/-- info: 'BeaconcryptCore.Computational.PqxdhOrdinaryNativeSharedRom.original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrdinaryNativeSharedRom.original

/-- info: 'BeaconcryptCore.Computational.PqxdhOrdinaryNativeSharedRom.raw_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrdinaryNativeSharedRom.raw_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhOrdinaryNativeSharedRom.local_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrdinaryNativeSharedRom.local_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhOrdinaryNativeSharedRom.bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrdinaryNativeSharedRom.bills

/-- info: 'BeaconcryptCore.Computational.PqxdhOrdinaryNativeSharedRom.program_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrdinaryNativeSharedRom.program_bills
