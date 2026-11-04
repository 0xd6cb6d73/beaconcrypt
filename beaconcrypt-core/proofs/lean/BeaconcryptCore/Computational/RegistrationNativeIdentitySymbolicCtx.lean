-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicRom
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxBackend

/-! The alias-preserving symbolic table uses the literal CTX digest sampler and reconstructs the entire physical backend cache, input journal and per-call draw cost. Only the private realization receives the hidden address. Internal token queries append a symbolic token to the client journal, while the private source journal receives its actual address. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicCtx
open RegistrationNativeIdentitySymbolicRom (address project counted)
variable {Value : Type}

abbrev HashSpec := Option Pqxdh.Bytes →ₒ (CtxRomAuth.CtxDigest × Nat)
abbrev ByteCache := (Pqxdh.Bytes →ₒ CtxRomAuth.CtxDigest).QueryCache
abbrev Cache := (Option Pqxdh.Bytes →ₒ CtxRomAuth.CtxDigest).QueryCache
abbrev State := Cache × List (Option Pqxdh.Bytes)

def sampler : ProbComp CtxRomAuth.CtxDigest := $ᵗ CtxRomAuth.CtxDigest

def unitCache (cache : ByteCache) : CtxRomAuth.CtxRO.QueryCache := ⟨fun query => cache query.2⟩

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem unit_update (cache : ByteCache) (input : Pqxdh.Bytes) (digest : CtxRomAuth.CtxDigest) :
    unitCache (cache.cacheQuery input digest) = (unitCache cache).cacheQuery ((), input) digest := by
  apply QueryCache.ext
  rintro ⟨tag, bytes⟩
  cases tag
  by_cases same : bytes = input
  · subst bytes
    simp only [unitCache, QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne _ _ (fun equal => same (congrArg Prod.snd equal))]
    exact QueryCache.cacheQuery_of_ne _ _ same

private theorem byte_query (input : Pqxdh.Bytes) (cache : ByteCache) :
    Prod.map id unitCache <$> (RegistrationNativeIdentitySymbolicRom.cached sampler input).run cache =
      (CtxRomAuth.ctxRandomOracle ((), input)).run (unitCache cache) := by
  have lookup : unitCache cache ((), input) = cache input := rfl
  unfold RegistrationNativeIdentitySymbolicRom.cached CtxRomAuth.ctxRandomOracle
  cases found : cache input with
  | none =>
    rw [QueryImpl.withCaching_run_none _ found, QueryImpl.withCaching_run_none _ (lookup.trans found)]
    simp only [Functor.map_map, Prod.map_def, id_eq]
    congr 1
    funext digest
    exact congrArg (fun table => (digest, table)) (unit_update cache input digest)
  | some digest =>
    rw [QueryImpl.withCaching_run_some _ found, QueryImpl.withCaching_run_some _ (lookup.trans found), map_pure]
    rfl

noncomputable def implementation : QueryImpl HashSpec (StateT State ProbComp) := fun input before =>
  (fun result => (result.1, (result.2, before.2 ++ [input]))) <$> (counted sampler input).run before.1

def realize (hidden : Pqxdh.Bytes) (before : State) : RegistrationNativePlatformCtxBackend.State :=
  (unitCache (project hidden before.1), before.2.map (address hidden))

/-- Exact digest, true draw cost, physical cache and physical chronological input list at one reached source call. -/
theorem query (hidden : Pqxdh.Bytes) (input : Option Pqxdh.Bytes) (before : State) (allowed : input ≠ some hidden) :
    Prod.map id (realize hidden) <$> (implementation input).run before =
      (RegistrationNativePlatformCtxBackend.physical (address hidden input)).run (realize hidden before) := by
  have source := byte_query (address hidden input) (project hidden before.1)
  have interpreted := congrArg (fun work => (simulateQ PqxdhRecordLiftWorld.countCoin work).run 0) source
  have observed := congrArg (fun work => (fun result => ((result.1.1, result.2),
    (result.1.2, (before.2.map (address hidden)) ++ [address hidden input]))) <$> work) interpreted
  have symbolic := RegistrationNativeIdentitySymbolicRom.counted_source sampler hidden before.1 input allowed
  have mapped := congrArg (fun distribution => (fun (result : (CtxRomAuth.CtxDigest × Nat) × ByteCache) =>
    (result.1, (unitCache result.2, before.2.map (address hidden) ++ [address hidden input]))) <$> distribution) symbolic
  calc
    _ = (fun (result : (CtxRomAuth.CtxDigest × Nat) × ByteCache) =>
        (result.1, (unitCache result.2, before.2.map (address hidden) ++ [address hidden input]))) <$>
      (counted sampler (address hidden input)).run (project hidden before.1) := by
        simpa only [implementation, StateT.run, Functor.map_map, Prod.map_def, id_eq,
          realize, List.map_append, List.map_cons, List.map_nil] using mapped
    _ = _ := by
      simpa only [RegistrationNativePlatformCtxBackend.physical, counted, StateT.run,
        simulateQ_map, map_apply, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq, realize] using observed

/-- Full adaptive CTX execution has the literal physical backend realization; the source address is absent from the executable symbolic client. -/
theorem program (hidden : Pqxdh.Bytes) (work : OracleComp HashSpec Value)
    (allowed : AllQueriesSatisfy work (fun input => input ≠ some hidden)) (before : State) :
    Prod.map id (realize hidden) <$> (simulateQ implementation work).run before =
      (simulateQ (fun input => RegistrationNativePlatformCtxBackend.physical (address hidden input)) work).run (realize hidden before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | query_bind input next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    conv_rhs => rw [← query hidden input before first]
    rw [bind_map_left]
    exact bind_congr (fun result => ih result.1 (later result.1) result.2)

end BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicCtx
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicCtx.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicCtx.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicCtx.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicCtx.program
