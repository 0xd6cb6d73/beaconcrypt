-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3GuardedSeedDelay
import BeaconcryptCore.Computational.RegistrationNativeG3CellEager
import BeaconcryptCore.Computational.RegistrationNativeG3Tables

/-! Completing all actual hidden-seed cells has the contextual law of one independent uniform seed table with prior cached cells retained. A shadow cache is returned by a literal finite query program, so the finite-cell eager theorem identifies the entire reached cache rather than only queried answers. Combining this source law with guarded seed delay removes full private table completion before the actual guarded continuation. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3SeedTableCompletion
open PqxdhRecordLiftInterface (Slot WorldSpec)
open PqxdhRecordLiftWorld (State SeedSpec)
open PqxdhRecordLiftSeed (Seed)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeSeedDelayCore (lens)
open RegistrationNativeSeedDelay (view)
open LazyOracleDiscard (LawEq StateLens)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

abbrev Cache (n : Nat) := (SeedSpec n).QueryCache
abbrev Table (n : Nat) := Slot n → Seed

noncomputable def cacheComplete : List (Slot n) → Cache n → ProbComp (Cache n)
  | [], cache => pure cache
  | point :: rest, cache => LazyOracleDiscard.complete point cache >>= cacheComplete rest

def remember (cache : Cache n) (point : Slot n) (answer : Seed) : Cache n :=
  match cache point with
  | some _ => cache
  | none => cache.cacheQuery point answer

def fill : List (Slot n) → Cache n → OracleComp (RegistrationNativeG3CellEager.Spec (Slot n) Seed) (Cache n)
  | [], cache => pure cache
  | point :: rest, cache => do
      let answer ← (RegistrationNativeG3CellEager.Spec (Slot n) Seed).query (.inr point)
      fill rest (remember cache point answer)

def filled : List (Slot n) → Cache n → Table n → Cache n
  | [], cache, _ => cache
  | point :: rest, cache, table => filled rest (remember cache point (table point)) table

private theorem lazy_fill (points : List (Slot n)) (cache : Cache n) :
    RegistrationNativeG3CellEager.lazyRun (fill points cache) cache = cacheComplete points cache := by
  induction points generalizing cache with
  | nil => simp only [fill, RegistrationNativeG3CellEager.lazyRun, simulateQ_pure, StateT.run'_eq,
      StateT.run_pure, map_pure, cacheComplete]
  | cons point rest ih =>
      simp only [fill, RegistrationNativeG3CellEager.lazyRun, simulateQ_bind, simulateQ_spec_query,
        RegistrationNativeG3CellEager.lazy, QueryImpl.add_apply_inr, StateT.run'_eq, StateT.run_bind,
        map_bind, cacheComplete]
      cases found : cache point with
      | some answer =>
          rw [QueryImpl.withCaching_run_some _ found, LazyOracleDiscard.complete_run]
          simp only [found, pure_bind, remember]
          exact ih cache
      | none =>
          rw [QueryImpl.withCaching_run_none _ found, LazyOracleDiscard.complete_run]
          simp only [found, bind_map_left, remember]
          apply bind_congr
          intro answer
          exact ih (cache.cacheQuery point answer)

private theorem fixed_fill (points : List (Slot n)) (cache : Cache n) (table : Table n) :
    RegistrationNativeG3CellEager.fixedRun table (fill points cache) = pure (filled points cache table) := by
  induction points generalizing cache with
  | nil => rfl
  | cons point rest ih =>
      simp only [RegistrationNativeG3CellEager.fixedRun, fill, simulateQ_bind, simulateQ_spec_query,
        RegistrationNativeG3CellEager.fixed, pure_bind, filled]
      exact ih _

private theorem remember_coherent (cache : Cache n) (table : Table n)
    (coherent : ∀ point answer, cache point = some answer → answer = table point)
    (point : Slot n) : ∀ query answer, (remember cache point (table point)) query = some answer → answer = table query := by
  intro query answer found
  cases cached : cache point with
  | some previous =>
      exact coherent query answer (by simpa only [remember, cached] using found)
  | none =>
      by_cases same : query = point
      · subst query
        simp only [remember, cached, QueryCache.cacheQuery_self, Option.some.injEq] at found
        exact found.symm
      · exact coherent query answer (by simpa only [remember, cached, QueryCache.cacheQuery_of_ne _ _ same] using found)

private theorem filled_value (points : List (Slot n)) (cache : Cache n) (table : Table n)
    (coherent : ∀ point answer, cache point = some answer → answer = table point)
    (query : Slot n) (available : query ∈ points ∨ cache query = some (table query)) :
    filled points cache table query = some (table query) := by
  induction points generalizing cache with
  | nil => exact available.resolve_left (by simp only [List.not_mem_nil, not_false_eq_true])
  | cons point rest ih =>
      change filled rest (remember cache point (table point)) table query = _
      apply ih _ (remember_coherent cache table coherent point)
      rcases available with member | cached
      · rcases List.mem_cons.mp member with same | later
        · right
          subst query
          cases found : cache point with
          | none => simp only [remember, found, QueryCache.cacheQuery_self]
          | some answer => simpa only [remember, found] using found.trans (congrArg some (coherent point answer found))
        · exact Or.inl later
      · right
        cases found : cache point with
        | some answer => simpa only [remember, found] using cached
        | none =>
            have different : query ≠ point := by intro same; subst query; rw [found] at cached; cases cached
            simpa only [remember, found, QueryCache.cacheQuery_of_ne _ _ different] using cached

private theorem filled_all (cache : Cache n) (table : Table n) :
    filled (List.finRange n) cache (OracleComp.completeTable cache table) =
      ⟨fun point => some (OracleComp.completeTable cache table point)⟩ := by
  apply QueryCache.ext
  intro point
  exact filled_value _ cache _ (fun query answer cached => by simp only [OracleComp.completeTable, cached, Option.getD_some])
    point (Or.inl (List.mem_finRange point))

/-- The actual sequential completion of all seed cells has the law of one independent full seed table, overlaid with every existing cached seed. -/
theorem cache_all (cache : Cache n) :
    LawEq (cacheComplete (List.finRange n) cache)
      ((fun table : Table n => (⟨fun point => some (OracleComp.completeTable cache table point)⟩ : Cache n)) <$> ($ᵗ (Table n))) := by
  have completed := RegistrationNativeG3CellEager.cached_eager (fill (List.finRange n) cache) cache
  rw [lazy_fill] at completed
  simpa only [fixed_fill, filled_all, bind_pure_comp] using completed

private theorem world_source (points : List (Slot n)) (before : State n) :
    RegistrationNativeG3GuardedSeedDelay.completeMany points before =
      lens.set before <$> cacheComplete points (lens.get before) := by
  induction points generalizing before with
  | nil => rfl
  | cons point rest ih =>
      simp only [RegistrationNativeG3GuardedSeedDelay.completeMany, StateLens.complete,
        cacheComplete, bind_map_left, map_bind]
      apply bind_congr
      intro cache
      rw [ih]
      simp only [lens]

/-- The full actual private World completion is exactly an independent complete seed table with its prior cached cells preserved. All non-seed fields and existing logical seed counters remain literal. -/
theorem world_all (before : State n) :
    LawEq (RegistrationNativeG3GuardedSeedDelay.completeMany (List.finRange n) before)
      ((fun table : Table n => lens.set before ⟨fun point => some (OracleComp.completeTable (lens.get before) table point)⟩) <$> ($ᵗ (Table n))) := by
  rw [world_source]
  simpa only [Functor.map_map, Function.comp_def] using (cache_all (lens.get before)).map (lens.set before)

/-- One complete uniform private seed table, with any earlier cached seeds retained, can be removed before the entire actual guarded World computation. -/
theorem uniform_program (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Value) (before : State n) :
    LawEq
      (do let table ← $ᵗ (Table n)
          Prod.map id view <$> (simulateQ (CborRecordWorldSimulation.guarded setup codec route) work).run
            (lens.set before ⟨fun point => some (OracleComp.completeTable (lens.get before) table point)⟩))
      (Prod.map id view <$> (simulateQ (CborRecordWorldSimulation.guarded setup codec route) work).run before) := by
  have first := (world_all before).symm.bind (fun reached => LawEq.refl
    (Prod.map id view <$> (simulateQ (CborRecordWorldSimulation.guarded setup codec route) work).run reached))
  simp only [bind_map_left] at first
  exact first.trans (RegistrationNativeG3GuardedSeedDelay.program_many setup codec route work (List.finRange n) before)

end BeaconcryptCore.Computational.RegistrationNativeG3SeedTableCompletion
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SeedTableCompletion.cache_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SeedTableCompletion.cache_all
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SeedTableCompletion.world_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SeedTableCompletion.world_all
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SeedTableCompletion.uniform_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SeedTableCompletion.uniform_program
