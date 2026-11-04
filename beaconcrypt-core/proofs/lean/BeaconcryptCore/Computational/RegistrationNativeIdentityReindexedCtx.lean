-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityReindexedRom
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxBackend

/-! An arbitrary admitted symbolic address family uses the literal CTX digest sampler and reconstructs the entire physical backend cache, input journal and true draw cost. Only private realization receives the physical-address map; executable cache and journal retain the public symbolic keys. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityReindexedCtx
open RegistrationNativeIdentitySymbolicRom (counted)
open RegistrationNativeIdentityReindexedRom (project)
variable {Symbolic Value : Type} [DecidableEq Symbolic]

abbrev HashSpec (Symbolic : Type) := Symbolic →ₒ (CtxRomAuth.CtxDigest × Nat)
abbrev ByteCache := (Pqxdh.Bytes →ₒ CtxRomAuth.CtxDigest).QueryCache
abbrev Cache (Symbolic : Type) := (Symbolic →ₒ CtxRomAuth.CtxDigest).QueryCache
abbrev State (Symbolic : Type) := Cache Symbolic × List Symbolic

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

noncomputable def implementation : QueryImpl (HashSpec Symbolic) (StateT (State Symbolic) ProbComp) := fun input before =>
  (fun result => (result.1, (result.2, before.2 ++ [input]))) <$> (counted sampler input).run before.1

def realize (address : Symbolic → Pqxdh.Bytes) (abstract : Pqxdh.Bytes → Symbolic)
    (before : State Symbolic) : RegistrationNativePlatformCtxBackend.State :=
  (unitCache (project abstract before.1), before.2.map address)

/-- The symbolic key, digest and true draw cost have exactly their reached physical cache and chronological-input realization. -/
theorem query (address : Symbolic → Pqxdh.Bytes) (abstract : Pqxdh.Bytes → Symbolic)
    (rightInverse : ∀ input, address (abstract input) = input)
    (input : Symbolic) (before : State Symbolic) (allowed : abstract (address input) = input) :
    Prod.map id (realize address abstract) <$> (implementation input).run before =
      (RegistrationNativePlatformCtxBackend.physical (address input)).run (realize address abstract before) := by
  have source := byte_query (address input) (project abstract before.1)
  have interpreted := congrArg (fun work => (simulateQ PqxdhRecordLiftWorld.countCoin work).run 0) source
  have observed := congrArg (fun work => (fun result => ((result.1.1, result.2),
    (result.1.2, (before.2.map address) ++ [address input]))) <$> work) interpreted
  have symbolic := RegistrationNativeIdentityReindexedRom.counted_source sampler address abstract rightInverse input allowed before.1
  have mapped := congrArg (fun distribution => (fun (result : (CtxRomAuth.CtxDigest × Nat) × ByteCache) =>
    (result.1, (unitCache result.2, before.2.map address ++ [address input]))) <$> distribution) symbolic
  calc
    _ = (fun (result : (CtxRomAuth.CtxDigest × Nat) × ByteCache) =>
        (result.1, (unitCache result.2, before.2.map address ++ [address input]))) <$>
      (counted sampler (address input)).run (project abstract before.1) := by
        simpa only [implementation, StateT.run, Functor.map_map, Prod.map_def, id_eq,
          realize, List.map_append, List.map_cons, List.map_nil] using mapped
    _ = _ := by
      simpa only [RegistrationNativePlatformCtxBackend.physical, counted, StateT.run,
        simulateQ_map, map_apply, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq, realize] using observed

/-- A complete adaptive symbolic-key family retains the actual full physical cache, input journal and true per-query costs. -/
theorem program (address : Symbolic → Pqxdh.Bytes) (abstract : Pqxdh.Bytes → Symbolic)
    (rightInverse : ∀ input, address (abstract input) = input) (work : OracleComp (HashSpec Symbolic) Value)
    (allowed : work.AllQueriesSatisfy (fun input => abstract (address input) = input)) (before : State Symbolic) :
    Prod.map id (realize address abstract) <$> (simulateQ implementation work).run before =
      (simulateQ (fun input => RegistrationNativePlatformCtxBackend.physical (address input)) work).run (realize address abstract before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | query_bind input next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    conv_rhs => rw [← query address abstract rightInverse input before first]
    rw [bind_map_left]
    exact bind_congr (fun result => ih result.1 (later result.1) result.2)

end BeaconcryptCore.Computational.RegistrationNativeIdentityReindexedCtx

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReindexedCtx.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReindexedCtx.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReindexedCtx.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReindexedCtx.program
