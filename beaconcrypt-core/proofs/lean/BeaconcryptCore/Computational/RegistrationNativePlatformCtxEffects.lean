-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxBackend
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxCacheFrame
/-! Every EnvEffects CTX request is exposed before physical lookup. Non-hash effects retain their exact native samplers and full World state; the backend alone holds the physical cache. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxEffects
open PqxdhRecordLiftInterface (EnvEffects)
open PqxdhRecordLiftWorld (State chargeEffect)
open RegistrationNativePlatformCtxBackend (Spec coin hash)
open RegistrationNativePlatformCtxCacheFrame (replace)
variable {n : Nat} {A : Type}
private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

noncomputable def program : QueryImpl (EnvEffects n) (StateT (State n) (OracleComp Spec))
  | .inr (.hash bytes) => fun before => do
      let reply ← hash bytes
      let charged := chargeEffect (.inr (.hash bytes)) before
      pure (reply.1, {charged with primitive :=
        ({charged.primitive.1 with uniform := charged.primitive.1.uniform + reply.2}, charged.primitive.2)})
  | query => fun before => simulateQ coin ((PqxdhRecordLiftWorld.effects query).run before)

abbrev Full (n : Nat) := State n × RegistrationNativePlatformCtxBackend.State

def realize (before : Full n) : State n := replace before.2.1 before.1

noncomputable def implementation : QueryImpl (EnvEffects n) (StateT (Full n) ProbComp) :=
  fun query before => (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ RegistrationNativePlatformCtxBackend.implementation ((program query).run before.1)).run before.2

theorem nonhash (query : (EnvEffects n).Domain)
    (allowed : RegistrationNativePlatformCtxCacheFrame.NonHashEffect query) (before : Full n) :
    Prod.map id realize <$> (implementation query).run before =
      (PqxdhRecordLiftWorld.effects query).run (realize before) := by
  have branch : (program query).run before.1 = simulateQ coin ((PqxdhRecordLiftWorld.effects query).run before.1) := by
    cases query with
    | inl query => rfl
    | inr request => cases request <;> first | rfl | exact False.elim allowed
  unfold implementation
  change Prod.map id realize <$> ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ RegistrationNativePlatformCtxBackend.implementation ((program query).run before.1)).run before.2) = _
  rw [branch, RegistrationNativePlatformCtxBackend.coins]
  simp only [StateT.run_lift, bind_pure_comp, Functor.map_map]
  exact RegistrationNativePlatformCtxCacheFrame.effects before.2.1 query allowed before.1

theorem hashing (bytes : Pqxdh.Bytes) (before : Full n) :
    Prod.map id realize <$> (implementation (.inr (.hash bytes))).run before =
      (PqxdhRecordLiftWorld.effects (.inr (.hash bytes))).run (realize before) := by
  have shift := RegistrationNativePlatformCtxBackend.count_shift
    ((CtxRomAuth.ctxRandomOracle ((), bytes)).run before.2.1) before.1.primitive.1.uniform 0
  simp only [Nat.add_zero] at shift
  unfold implementation program RegistrationNativePlatformCtxBackend.hash
  unfold PqxdhRecordLiftWorld.effects PqxdhRecordLiftWorld.capability PqxdhRecordLiftWorld.sampled
  simp only [realize, replace, StateT.run, chargeEffect, bind_pure_comp, Functor.map_map] at shift ⊢
  simp only [simulateQ_map, simulateQ_spec_query, RegistrationNativePlatformCtxBackend.implementation]
  simp only [state_map_apply, RegistrationNativePlatformCtxBackend.physical, StateT.run, bind_pure_comp, Functor.map_map]
  rw [← shift, Functor.map_map]
  rfl

theorem query (request : (EnvEffects n).Domain) (before : Full n) :
    Prod.map id realize <$> (implementation request).run before =
      (PqxdhRecordLiftWorld.effects request).run (realize before) := by
  cases request with
  | inl coin => exact nonhash (.inl coin) trivial before
  | inr request => cases request <;> first
    | exact hashing _ before
    | apply nonhash; trivial

/-- Arbitrary adaptive EnvEffects programs expose every actual CTX query while preserving the complete joint native result, cache and counters. -/
theorem complete (work : OracleComp (EnvEffects n) A) (before : Full n) :
    Prod.map id realize <$> (simulateQ implementation work).run before =
      (simulateQ PqxdhRecordLiftWorld.effects work).run (realize before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq implementation PqxdhRecordLiftWorld.effects realize query work before
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxEffects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxEffects.nonhash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxEffects.nonhash

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxEffects.hashing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxEffects.hashing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxEffects.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxEffects.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxEffects.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxEffects.complete
