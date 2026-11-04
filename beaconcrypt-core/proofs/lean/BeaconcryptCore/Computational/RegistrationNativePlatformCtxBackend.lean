-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorld
/-! Explicit CTX queries and actual uniform draws use separate branches. The physical interpreter owns the shared cache and a chronological query journal. Hash replies retain the actual draw bill for source counter reconstruction. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxBackend
variable {A : Type}
abbrev HashSpec := Pqxdh.Bytes →ₒ (CtxRomAuth.CtxDigest × Nat)
abbrev Spec := HashSpec + unifSpec
abbrev Cache := CtxRomAuth.CtxRO.QueryCache
abbrev State := Cache × List Pqxdh.Bytes

def coin : QueryImpl unifSpec (OracleComp Spec) := fun query => Spec.query (.inr query)
def hash (bytes : Pqxdh.Bytes) : OracleComp Spec (CtxRomAuth.CtxDigest × Nat) := Spec.query (.inl bytes)

noncomputable def physical (bytes : Pqxdh.Bytes) : StateT State ProbComp (CtxRomAuth.CtxDigest × Nat) := fun before => do
  let result ← (simulateQ PqxdhRecordLiftWorld.countCoin ((CtxRomAuth.ctxRandomOracle ((), bytes)).run before.1)).run 0
  pure ((result.1.1, result.2), (result.1.2, before.2 ++ [bytes]))

noncomputable def implementation : QueryImpl Spec (StateT State ProbComp)
  | .inl bytes => physical bytes
  | .inr query => StateT.lift (unifSpec.query query : ProbComp _)

theorem coins (work : ProbComp A) :
    simulateQ implementation (simulateQ coin work) = (StateT.lift work : StateT State ProbComp A) := by
  rw [← QueryImpl.simulateQ_compose]
  have leaves : implementation ∘ₛ coin = (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT State ProbComp) := by
    funext query
    simp only [QueryImpl.apply_compose, coin, simulateQ_spec_query, implementation]
    rfl
  rw [leaves, simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  rfl

theorem count_shift (work : ProbComp A) (start previous : Nat) :
    Prod.map id (fun count => start + count) <$> (simulateQ PqxdhRecordLiftWorld.countCoin work).run previous =
      (simulateQ PqxdhRecordLiftWorld.countCoin work).run (start + previous) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
    PqxdhRecordLiftWorld.countCoin PqxdhRecordLiftWorld.countCoin (fun count => start + count)
  intro query count
  simp only [PqxdhRecordLiftWorld.countCoin, StateT.run, Functor.map_map, Nat.add_assoc]
  rfl

theorem physical_forget (bytes : Pqxdh.Bytes) (before : State) :
    Prod.map Prod.fst Prod.fst <$> (physical bytes).run before =
      (CtxRomAuth.ctxRandomOracle ((), bytes)).run before.1 := by
  have erased := PqxdhRecordLiftWorld.countCoin_forget ((CtxRomAuth.ctxRandomOracle ((), bytes)).run before.1) 0
  simpa only [physical, StateT.run, bind_pure_comp, Functor.map_map, Prod.map_def] using erased

theorem physical_journal (bytes : Pqxdh.Bytes) (before : State)
    (after : (CtxRomAuth.CtxDigest × Nat) × State)
    (present : after ∈ support ((physical bytes).run before)) :
    after.2.2 = before.2 ++ [bytes] := by
  simp only [physical, StateT.run, bind_pure_comp, support_map] at present
  obtain ⟨result, _supported, rfl⟩ := present
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformCtxBackend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBackend.coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBackend.coins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBackend.count_shift' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBackend.count_shift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBackend.physical_forget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBackend.physical_forget

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBackend.physical_journal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBackend.physical_journal
