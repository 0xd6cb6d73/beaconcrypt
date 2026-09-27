import BeaconcryptCore.Computational.PqxdhInitialRootContext
import BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor

/-!
The common private initializer service records complete64-byte replies under the exact original request. Both source orientations therefore reuse the same reply. Real-source memoization is operationally exact and does not change public HKDF. A separate uniform64 service is only an explicit comparison interface: no assumption says it is secure for arbitrary source inputs, and same-address evolving76 responses must preserve the shared prefix in any consumer.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialResponseCache
open PqxdhInitialResponseService PqxdhSecretInputKdf PqxdhJointKdfGame
variable {ι Result : Type} {base : OracleSpec ι}

noncomputable local instance : DecidableEq SymmetricRatchetKdfRequest := Classical.decEq _

abbrev Table := InitialSpec.QueryCache

def Consistent (fixed : FixedHkdfSha512NoSaltSource) (table : Table) : Prop :=
  ∀ request response, table request = some response → response = RawCtxSourceHkdf.initialResponse fixed.crypto request

/-- The actual source cache starts without an additional input or output assumption. -/
theorem consistent_empty (fixed : FixedHkdfSha512NoSaltSource) : Consistent fixed ∅ := by
  intro request response found
  simp at found

/-- Recording the exact source reply preserves every earlier complete request/reply binding. -/
theorem consistent_record (fixed : FixedHkdfSha512NoSaltSource) (table : Table)
    (consistent : Consistent fixed table) (request : SymmetricRatchetKdfRequest) :
    Consistent fixed (table.cacheQuery request (RawCtxSourceHkdf.initialResponse fixed.crypto request)) := by
  intro previous response found
  by_cases same : previous = request
  · subst previous
    simpa using found.symm
  · rw [QueryCache.cacheQuery_of_ne table _ same] at found
    exact consistent previous response found

noncomputable def memo (fixed : FixedHkdfSha512NoSaltSource) :
    QueryImpl InitialSpec (StateT Table (OracleComp base)) :=
  QueryImpl.withCaching (spec := InitialSpec)
    (fun request => (pure (RawCtxSourceHkdf.initialResponse fixed.crypto request) : OracleComp base _))

/-- Complete initializer hits and misses return exactly the original deterministic source reply and preserve the entire private cache. -/
theorem memo_step (fixed : FixedHkdfSha512NoSaltSource) (table : Table)
    (consistent : Consistent fixed table) (request : SymmetricRatchetKdfRequest) :
    (memo (base := base) fixed request).run table =
      pure (RawCtxSourceHkdf.initialResponse fixed.crypto request,
        table.cacheQuery request (RawCtxSourceHkdf.initialResponse fixed.crypto request)) := by
  cases found : table request with
  | none => simp [memo, found]
  | some response =>
    have actual := consistent request response found
    subst response
    have retained : table.cacheQuery request (RawCtxSourceHkdf.initialResponse fixed.crypto request) = table := by
      funext previous
      by_cases same : previous = request
      · subst previous
        simpa using found.symm
      · exact QueryCache.cacheQuery_of_ne table _ same
    simp [memo, found, retained]

noncomputable def cachedSource (fixed : FixedHkdfSha512NoSaltSource) :
    QueryImpl (Spec base) (StateT Table (OracleComp base))
  | .inl query => fun table => do
      let answer ← base.query query
      pure (answer, table)
  | .inr request => memo fixed request

set_option backward.isDefEq.respectTransparency false in
/-- Erasing only the added private memo table recovers the complete original adaptive source program; every base effect and original result remain intact. -/
theorem source_program (fixed : FixedHkdfSha512NoSaltSource) (work : OracleComp (Spec base) Result)
    (table : Table) (consistent : Consistent fixed table) :
    Prod.fst <$> (simulateQ (cachedSource fixed) work).run table = simulateQ (source fixed) work := by
  induction work using OracleComp.inductionOn generalizing table with
  | pure result => rfl
  | query_bind query next ih =>
      cases query with
      | inl query =>
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
          change (Prod.fst <$> (do
            let answer ← (base.query query : OracleComp base _)
            (simulateQ (cachedSource fixed) (next answer)).run table)) = _
          simp only [map_bind, ih _ table consistent]
          rfl
      | inr request =>
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, cachedSource,
            memo_step fixed table consistent, pure_bind]
          rw [ih _ _ (consistent_record fixed table consistent request)]
          rfl

noncomputable def uniform : QueryImpl InitialSpec (StateT Table ProbComp) :=
  QueryImpl.withCaching (spec := InitialSpec)
    (fun _ => RawCtxSelectedInitialConstructor.response64 <$> ($ᵗ HmacBlock))

set_option backward.isDefEq.respectTransparency false in
/-- A fresh comparison initializer samples exactly64 bytes and stores the complete original reply once at its actual request. -/
theorem uniform_miss (table : Table) (request : SymmetricRatchetKdfRequest)
    (absent : table request = none) :
    (uniform request).run table = (do
      let output ← $ᵗ HmacBlock
      let response := RawCtxSelectedInitialConstructor.response64 output
      pure (response, table.cacheQuery request response)) := by
  rw [show uniform request = QueryImpl.withCaching (spec := InitialSpec)
    (fun _ => RawCtxSelectedInitialConstructor.response64 <$> ($ᵗ HmacBlock)) request by rfl]
  rw [QueryImpl.withCaching_run_none _ absent]
  rw [Functor.map_map]
  rw [map_eq_bind_pure_comp]
  change (($ᵗ HmacBlock) >>= fun output =>
    pure (RawCtxSelectedInitialConstructor.response64 output,
      table.cacheQuery request (RawCtxSelectedInitialConstructor.response64 output))) = _
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every repeated request reuses its earlier complete64-byte reply and draws no new bytes. -/
theorem uniform_hit (table : Table) (request : SymmetricRatchetKdfRequest)
    (response : pqxdh.concrete.InitialRatchetKdfResponse) (present : table request = some response) :
    (uniform request).run table = pure (response, table) := by
  exact QueryImpl.withCaching_run_some _ present

set_option maxRecDepth 10000 in
/-- The comparison's uniform-query bill is zero on a hit and64 on a miss; request comparisons, memo work and reply conversion are explicit local operations. -/
theorem uniform_bound (table : Table) (request : SymmetricRatchetKdfRequest) :
    ((uniform request).run table).IsTotalQueryBound (if (table request).isSome then 0 else 64) := by
  cases found : table request with
  | none =>
      rw [uniform_miss table request found]
      simpa only [Option.isSome_none, Bool.false_eq_true, if_false, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
        (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64)
  | some response =>
      rw [uniform_hit table request response found]
      trivial

/-- The opposite role reuses the same recorded64-byte reply for the same root; role orientation never creates another initializer sample. -/
theorem recorded_roles (table : Table) (root : RootOutput)
    (response : pqxdh.concrete.InitialRatchetKdfResponse) :
    (uniform (pending true root).request).run (table.cacheQuery (pending false root).request response) =
      pure (response, table.cacheQuery (pending false root).request response) := by
  apply uniform_hit
  exact QueryCache.cacheQuery_self table (pending false root).request response

end BeaconcryptCore.Computational.PqxdhInitialResponseCache

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialResponseCache.consistent_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialResponseCache.consistent_empty

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialResponseCache.consistent_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialResponseCache.consistent_record

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialResponseCache.memo_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialResponseCache.memo_step

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialResponseCache.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialResponseCache.source_program

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialResponseCache.uniform_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialResponseCache.uniform_miss

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialResponseCache.uniform_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialResponseCache.uniform_hit

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialResponseCache.uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialResponseCache.uniform_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialResponseCache.recorded_roles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialResponseCache.recorded_roles
