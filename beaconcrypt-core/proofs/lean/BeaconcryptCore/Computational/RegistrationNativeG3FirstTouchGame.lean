-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchEager
import BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchBound

/-! The actual byte-indexed lazy G2 service is identified with a complete finite slot table, retaining literal coin queries and byte aliases. The original syntactic material cap supplies the finite capacity; the subsequent sampler split is a law through every continuation. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchGame
open PqxdhServerAuthKeySchedule (Output)
open RegistrationNativeG3FirstTouch (Spec Alloc Cache Table fixed lazySlots)
open RegistrationNativeG3FirstTouchEager (lazyRun fixedRun cached_eager)
open PqxdhRegistrationJointKemSecondEntry (emptyAlloc)
open LazyOracleDiscard (LawEq)
variable {n : Nat} {Value : Type}

noncomputable def finite (work : OracleComp Spec Value) : ProbComp Value := do
  let outputs ← $ᵗ Table n
  Prod.fst <$> fixedRun outputs work emptyAlloc

private theorem slot_projection (work : OracleComp Spec Value) :
    Prod.map id (Prod.map id Prod.fst) <$>
      (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl
        (PqxdhRegistrationJointKemSecondEntry.tableService (R := Output) (n := n))) work).run
        (emptyAlloc, PqxdhRecordLiftLazyTable.initial) =
      (simulateQ lazySlots work).run (emptyAlloc, (∅ : Cache n)) := by
  exact (PqxdhRegistrationJointKemSecondEntry.slot_natural
    (PqxdhRegistrationJointKemSecondEntry.tableService (R := Output) (n := n))
    (fun slot => ((PqxdhRecordLiftInterface.Slot n →ₒ Output).randomOracle slot))
    (fun _ => True) Prod.fst
    (fun slot state _ => LazyOracleDiscard.impl_project slot state)
    (fun _ _ _ _ _ => trivial) work emptyAlloc PqxdhRecordLiftLazyTable.initial trivial).1

/-- Discarding only lazy-table bookkeeping identifies the genuine capped byte service with the first-touch slot service. -/
theorem lazy_source (work : OracleComp Spec Value)
    (bounded : work.IsQueryBoundP RegistrationNativeG3FirstTouchBound.IsValue n) :
    (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl work).run' ∅ =
      Prod.fst <$> lazyRun work (emptyAlloc : Alloc n) ∅ := by
  have represented := PqxdhRegistrationJointKemSecondEntry.slot_lazy (n := n) work n bounded
    (emptyAlloc, PqxdhRecordLiftLazyTable.initial)
    PqxdhRegistrationJointKemSecondEntry.slotGood_empty (by simp [emptyAlloc])
  rw [PqxdhRegistrationJointKemSecondEntry.cacheOf_empty] at represented
  rw [StateT.run'_eq, ← represented]
  have projected := congrArg (Functor.map Prod.fst) (slot_projection (n := n) work)
  simpa only [Functor.map_map, Function.comp_def, Prod.map, id_eq,
    RegistrationNativeG3FirstTouchEager.lazyRun] using projected

/-- The actual capped lazy byte service has the complete finite-table law for every subsequent observer. -/
theorem lazy_finite (work : OracleComp Spec Value)
    (bounded : work.IsQueryBoundP RegistrationNativeG3FirstTouchBound.IsValue n) :
    LawEq ((simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl work).run' ∅)
      (finite (n := n) work) := by
  rw [lazy_source work bounded]
  have eager := (cached_eager work (emptyAlloc : Alloc n) (∅ : Cache n)).map Prod.fst
  simpa only [finite, map_bind, OracleComp.completeTable_empty] using eager

/-- Independent material44 and seed64 tables answer the same actual capped client under its literal first-touch aliases. -/
theorem lazy_split (work : OracleComp Spec Value)
    (bounded : work.IsQueryBoundP RegistrationNativeG3FirstTouchBound.IsValue n) :
    LawEq ((simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl work).run' ∅)
      (do
        let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable n
        let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable n
        Prod.fst <$> fixedRun (RegistrationNativeG3Tables.join materials seeds) work emptyAlloc) :=
  (lazy_finite work bounded).trans (RegistrationNativeG3Tables.uniform_tables
    (fun outputs => Prod.fst <$> fixedRun outputs work emptyAlloc))

end BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchGame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchGame.lazy_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchGame.lazy_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchGame.lazy_finite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchGame.lazy_finite
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchGame.lazy_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchGame.lazy_split
