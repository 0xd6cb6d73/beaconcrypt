-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxBackend
import BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget
import BeaconcryptCore.Computational.PqxdhRecordFactsCollisionOracle
/-! The actual lazy physical CTX backend compiles each cache miss into one digest draw, returning its exact64 byte draws, and retains the complete chronological input journal. Public coins remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCompiler
open RegistrationNativePlatformCtxBackend (Spec State)
open PqxdhRecordFactsCollision (DrawSpec)
variable {A : Type}

noncomputable def plain : QueryImpl (DrawSpec CtxRomAuth.CtxDigest) ProbComp
  | .inl _ => $ᵗ CtxRomAuth.CtxDigest
  | .inr query => unifSpec.query query

noncomputable def compiler : QueryImpl Spec (StateT State (OracleComp (DrawSpec CtxRomAuth.CtxDigest)))
  | .inl bytes => fun before =>
      match before.1 ((), bytes) with
      | some digest => pure ((digest, 0), (before.1, before.2 ++ [bytes]))
      | none => do
          let digest ← ((DrawSpec CtxRomAuth.CtxDigest).query (.inl true) : OracleComp (DrawSpec CtxRomAuth.CtxDigest) _)
          pure ((digest, 64), (before.1.cacheQuery ((), bytes) digest, before.2 ++ [bytes]))
  | .inr query => fun before => do
      let reply ← ((DrawSpec CtxRomAuth.CtxDigest).query (.inr query) : OracleComp (DrawSpec CtxRomAuth.CtxDigest) _)
      pure (reply, before)

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl

/-- An actual cache hit retains its zero native draw bill and still appends the real input journal entry. -/
theorem physical_hit (bytes : Pqxdh.Bytes) (before : State) (digest : CtxRomAuth.CtxDigest)
    (hit : before.1 ((), bytes) = some digest) :
    (RegistrationNativePlatformCtxBackend.physical bytes).run before =
      pure ((digest, 0), (before.1, before.2 ++ [bytes])) := by
  change (do
    let result ← (simulateQ PqxdhRecordLiftWorld.countCoin ((CtxRomAuth.ctxRandomOracle ((), bytes)).run before.1)).run 0
    pure ((result.1.1, result.2), (result.1.2, before.2 ++ [bytes]))) = _
  rw [CtxRomAuth.ctxRandomOracle, QueryImpl.withCaching_run_some _ hit]
  simp only [StateT.run, simulateQ_pure, state_pure_apply, pure_bind]

/-- An actual missing input performs the same uniform64-byte digest sampler and literal64 native coin calls. -/
theorem physical_miss (bytes : Pqxdh.Bytes) (before : State)
    (miss : before.1 ((), bytes) = none) :
    (RegistrationNativePlatformCtxBackend.physical bytes).run before =
      (fun digest => ((digest, 64), (before.1.cacheQuery ((), bytes) digest, before.2 ++ [bytes]))) <$>
        ($ᵗ CtxRomAuth.CtxDigest) := by
  change (do
    let result ← (simulateQ PqxdhRecordLiftWorld.countCoin ((CtxRomAuth.ctxRandomOracle ((), bytes)).run before.1)).run 0
    pure ((result.1.1, result.2), (result.1.2, before.2 ++ [bytes]))) = _
  rw [CtxRomAuth.ctxRandomOracle, QueryImpl.withCaching_run_none _ miss]
  simp only [simulateQ_map, StateT.run_map, uniformSampleImpl_apply]
  rw [PqxdhRecordLiftWorldBudget.sample_fixed_bytes]
  simp only [Functor.map_map, Nat.zero_add, bind_pure_comp]

/-- Every actual hash/coin reply, cache, draw count and journal is the literal fold of the digest/coin compiler. -/
theorem query_source (query : Spec.Domain) (before : State) :
    simulateQ plain ((compiler query).run before) =
      (RegistrationNativePlatformCtxBackend.implementation query).run before := by
  cases query with
  | inl bytes =>
    cases found : before.1 ((), bytes) with
    | none =>
      rw [RegistrationNativePlatformCtxBackend.implementation, physical_miss bytes before found]
      simp only [compiler, StateT.run, found, bind_pure_comp]
      simp only [simulateQ_map, simulateQ_spec_query, plain]
      rfl
    | some digest =>
      rw [RegistrationNativePlatformCtxBackend.implementation, physical_hit bytes before digest found]
      simp only [compiler, StateT.run, found, simulateQ_pure]
  | inr query =>
    simp only [compiler, StateT.run, simulateQ_map, simulateQ_spec_query, plain,
      RegistrationNativePlatformCtxBackend.implementation, StateT.lift, bind_pure_comp]
    rfl

/-- Arbitrary adaptive hash/coin programs retain exactly the actual physical cache, journal and count-bearing replies. -/
theorem complete (work : OracleComp Spec A) (before : State) :
    simulateQ plain ((simulateQ compiler work).run before) =
      (simulateQ RegistrationNativePlatformCtxBackend.implementation work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [query_source]
    exact bind_congr (fun result => ih result.1 result.2)
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCompiler.physical_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCompiler.physical_hit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCompiler.physical_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCompiler.physical_miss

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCompiler.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCompiler.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCompiler.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCompiler.complete
