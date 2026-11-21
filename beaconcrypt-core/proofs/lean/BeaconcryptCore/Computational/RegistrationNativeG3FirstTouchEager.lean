-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3FirstTouch
import BeaconcryptCore.Computational.LazyOracleDiscard
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

/-! The first-touch slot service has the law of one complete uniform108 table sampled before the adaptive client. Literal unif coins remain in the same client, byte aliases retain their slots and the full final assignment map is observed. A cache-parametrized proof overlays prior slot values and uses uniform single-cell resampling only on a cache miss. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchEager
open RegistrationNativeG3FirstTouch (Spec Alloc Cache Table take fixed lazySlots fixed_point)
open PqxdhServerAuthKeySchedule (Output)
open PqxdhRecordLiftInterface (Slot)
open LazyOracleDiscard (LawEq)
variable {n : Nat} {Value : Type}

noncomputable def lazyRun (work : OracleComp Spec Value) (alloc : Alloc n) (cache : Cache n) :
    ProbComp (Value × Alloc n) := Prod.map id Prod.fst <$> (simulateQ lazySlots work).run (alloc, cache)

noncomputable def fixedRun (outputs : Table n) (work : OracleComp Spec Value) (alloc : Alloc n) :
    ProbComp (Value × Alloc n) := (simulateQ (fixed outputs) work).run alloc

private theorem lazy_bind (query : Spec.Domain) (next : Spec.Range query → OracleComp Spec Value)
    (alloc : Alloc n) (cache : Cache n) :
    lazyRun ((Spec.query query : OracleComp Spec _) >>= next) alloc cache =
      ((lazySlots query).run (alloc, cache) >>= fun result => lazyRun (next result.1) result.2.1 result.2.2) := by
  simp only [lazyRun, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]

private theorem fixed_bind (outputs : Table n) (query : Spec.Domain)
    (next : Spec.Range query → OracleComp Spec Value) (alloc : Alloc n) :
    fixedRun outputs ((Spec.query query : OracleComp Spec _) >>= next) alloc =
      ((fixed outputs query).run alloc >>= fun result => fixedRun outputs (next result.1) result.2) := by
  simp only [fixedRun, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

private theorem lazy_point (point : Pqxdh.Bytes) (alloc : Alloc n) (cache : Cache n) :
    (lazySlots (.inr point)).run (alloc, cache) =
      match take point alloc with
      | (some slot, after) => (fun result => (result.1, (after, result.2))) <$>
          ((Slot n →ₒ Output).randomOracle slot).run cache
      | (none, after) => (fun answer => (answer, (after, cache))) <$> ($ᵗ Output) := by
  cases found : alloc.1 point with
  | some slot =>
      rw [RegistrationNativeG3FirstTouch.lazySlots_eq,
        PqxdhRegistrationJointKemSecondEntry.slot_some _ point (alloc, cache) slot found,
        RegistrationNativeG3FirstTouch.take_hit point alloc slot found]
  | none =>
      by_cases room : alloc.2 < n
      · rw [RegistrationNativeG3FirstTouch.lazySlots_eq,
          PqxdhRegistrationJointKemSecondEntry.slot_none _ point (alloc, cache) found room,
          RegistrationNativeG3FirstTouch.take_miss point alloc found room]
      · simp only [RegistrationNativeG3FirstTouch.lazySlots_eq,
          PqxdhRegistrationJointKemSecondEntry.slotImpl, QueryImpl.add_apply_inr, StateT.run_mk,
          RegistrationNativeG3FirstTouch.take, found, dite_eq_right room]
        rfl

private theorem update_uniform (slot : Slot n) (next : Table n → ProbComp Value) :
    LawEq (do let answer ← $ᵗ Output; let table ← $ᵗ Table n; next (Function.update table slot answer))
      (do let table ← $ᵗ Table n; next table) := by
  intro Result _ continuation
  let : MeasurableSpace Output := ⊤
  let : DiscreteMeasurableSpace Output := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  simp only [bind_assoc]
  exact evalDist_bind_bind_update ($ᵗ Output) ($ᵗ Table n)
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample slot
    (fun table => next table >>= continuation)

private theorem read_eager (slot : Slot n) (next : Output → OracleComp Spec Value)
    (alloc : Alloc n) (cache : Cache n)
    (later : ∀ answer current, LawEq (lazyRun (next answer) alloc current)
      (do let outputs ← $ᵗ Table n; fixedRun (OracleComp.completeTable current outputs) (next answer) alloc)) :
    LawEq (((Slot n →ₒ Output).randomOracle slot).run cache >>= fun result => lazyRun (next result.1) alloc result.2)
      (do let outputs ← $ᵗ Table n;
          fixedRun (OracleComp.completeTable cache outputs) (next (OracleComp.completeTable cache outputs slot)) alloc) := by
  cases found : cache slot with
  | some answer =>
      rw [QueryImpl.withCaching_run_some _ found, pure_bind]
      simpa only [OracleComp.completeTable, found, Option.getD_some] using later answer cache
  | none =>
      rw [QueryImpl.withCaching_run_none _ found]
      simp only [bind_map_left]
      have first := LawEq.bind (LawEq.refl ($ᵗ Output)) (fun answer => later answer (cache.cacheQuery slot answer))
      refine first.trans ?_
      have redrawn := update_uniform slot (fun outputs => fixedRun (OracleComp.completeTable cache outputs)
        (next (OracleComp.completeTable cache outputs slot)) alloc)
      simpa only [bind_assoc, OracleComp.completeTable_cacheQuery,
        OracleComp.completeTable_update_of_none cache _ found,
        OracleComp.completeTable, found, Function.update_self, Option.getD_none] using redrawn

/-- An arbitrary adaptive coin/key client has the same full output and final assignment-map law under a single completed uniform slot table. -/
theorem cached_eager (work : OracleComp Spec Value) (alloc : Alloc n) (cache : Cache n) :
    LawEq (lazyRun work alloc cache)
      (do let outputs ← $ᵗ Table n; fixedRun (OracleComp.completeTable cache outputs) work alloc) := by
  induction work using OracleComp.inductionOn generalizing alloc cache with
  | pure value =>
      simp only [lazyRun, fixedRun, simulateQ_pure, StateT.run_pure, map_pure]
      exact (LazyOracleDiscard.lawEq_drop ($ᵗ Table n) (pure (value, alloc))).symm
  | query_bind query next ih =>
      rw [lazy_bind]
      cases query with
      | inl coin =>
          rw [RegistrationNativeG3FirstTouch.lazy_coin]
          simp only [bind_map_left]
          have first := LawEq.bind (LawEq.refl (unifSpec.query coin : ProbComp _)) (fun reply => ih reply alloc cache)
          refine first.trans ?_
          have moved := LazyOracleDiscard.lawEq_swap (unifSpec.query coin : ProbComp _) ($ᵗ Table n)
            (fun reply outputs => fixedRun (OracleComp.completeTable cache outputs) (next reply) alloc)
          simpa only [fixed_bind, RegistrationNativeG3FirstTouch.fixed_coin, bind_map_left] using moved
      | inr point =>
          rw [lazy_point]
          cases allocated : take point alloc with
          | mk selected after => cases selected with
            | some slot =>
                simp only [bind_map_left]
                simpa only [fixed_bind, fixed_point, allocated, pure_bind] using
                  read_eager slot next after cache (fun answer current => ih answer after current)
            | none =>
                simp only [bind_map_left]
                have first := LawEq.bind (LawEq.refl ($ᵗ Output)) (fun reply => ih reply after cache)
                refine first.trans ?_
                have moved := LazyOracleDiscard.lawEq_swap ($ᵗ Output) ($ᵗ Table n)
                  (fun reply outputs => fixedRun (OracleComp.completeTable cache outputs) (next reply) after)
                convert moved using 1; simp only [fixed_bind, fixed_point, allocated, bind_map_left]; rfl

end BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchEager
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchEager.cached_eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchEager.cached_eager
