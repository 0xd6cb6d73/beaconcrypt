-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.LazyOracleDiscard
import BeaconcryptCore.Computational.RegistrationNativeKemWorldUniform

/-! Seed completion focuses the actual persistent World seed cache. Its explicit accounting view drops only uniform-draw and lazy-seed lookup/draw totals; installed kernels, role-use bits, shared CTX cache, native/effect counts and all protocol state remain present. Original counted executions supply their separate resource bounds. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSeedDelayCore
open PqxdhRecordLiftWorld (State SeedSpec)
open LazyOracleDiscard (CacheLens Commutes StateLens)
variable {n : Nat} {Value : Type}

def lens : CacheLens (SeedSpec n) (State n) where
  get before := before.seeds.1
  set before cache := { before with seeds := (cache, before.seeds.2) }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

def mask (before : State n) : State n :=
  { before with
    primitive := ({ before.primitive.1 with uniform := 0 }, before.primitive.2)
    seeds := (before.seeds.1, ⟨0, 0⟩) }

def normalize (work : StateT (State n) ProbComp Value) : StateT (State n) ProbComp Value := fun before =>
  Prod.map id mask <$> work.run (mask before)

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (state : S) : (observe <$> work) state = Prod.map observe id <$> work state := by
  change (work state >>= fun result => pure (observe result.1, result.2)) = _
  rw [bind_pure_comp]
  rfl

/-- The projection retains the actual seed cache and all earlier role-use markers and concrete record fields. -/
theorem mask_fields (before : State n) :
    (mask before).seeds.1 = before.seeds.1 ∧ (mask before).used = before.used ∧
    (mask before).server = before.server ∧ (mask before).owners = before.owners ∧
    (mask before).ownerRaw = before.ownerRaw ∧ (mask before).produced = before.produced ∧
    (mask before).primitive.2 = before.primitive.2 ∧
    (mask before).primitive.1.native = before.primitive.1.native ∧
    (mask before).primitive.1.effects = before.primitive.1.effects :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem mask_idempotent (before : State n) : mask (mask before) = mask before := rfl

theorem mask_set (before : State n) (cache : (SeedSpec n).QueryCache) :
    mask (lens.set before cache) = lens.set (mask before) cache := rfl

/-- Actual sampling never reads the hidden-seed cache, regardless of its retained native accounting. -/
theorem sampled_frame (draw : ProbComp Value) (before : State n) (cache : (SeedSpec n).QueryCache) :
    (PqxdhRecordLiftWorld.sampled draw).run (lens.set before cache) =
      Prod.map id (fun after => lens.set after cache) <$>
        (PqxdhRecordLiftWorld.sampled draw).run before := by
  simp only [PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, Functor.map_map,
    Prod.map_def, id_eq, lens]

/-- A concrete cache frame remains a frame after the stated accounting projection. -/
theorem normalize_frame (work : StateT (State n) ProbComp Value)
    (framed : ∀ before cache, work.run (lens.set before cache) =
      Prod.map id (fun after => lens.set after cache) <$> work.run before)
    (before : State n) (cache : (SeedSpec n).QueryCache) :
    (normalize work).run (lens.set before cache) =
      Prod.map id (fun after => lens.set after cache) <$> (normalize work).run before := by
  change Prod.map id mask <$> work.run (mask (lens.set before cache)) =
    Prod.map id (fun after => lens.set after cache) <$> (Prod.map id mask <$> work.run (mask before))
  rw [mask_set, framed]
  simp only [Functor.map_map, Prod.map_def, id_eq, mask_set]

/-- Every normalized concrete cache frame commutes with lazy completion. -/
theorem normalize_commutes (work : StateT (State n) ProbComp Value)
    (framed : ∀ before cache, work.run (lens.set before cache) =
      Prod.map id (fun after => lens.set after cache) <$> work.run before) :
    Commutes lens (normalize work) :=
  LazyOracleDiscard.commutes_frame lens _ (normalize_frame work framed)

/-- Projected actual draws retain their exact source distribution and every operational World field. -/
theorem sampled_mask (draw : ProbComp Value) (before : State n) :
    Prod.map id mask <$> (PqxdhRecordLiftWorld.sampled draw).run before =
      (fun value => (value, mask before)) <$> draw := by
  have actual := RegistrationNativeKemWorldUniform.sampled_mask draw before
  have projected := congrArg (fun distribution => Prod.map id mask <$> distribution) actual
  simpa only [Functor.map_map, Prod.map_def, id_eq, mask, RegistrationNativeKemWorldUniform.mask] using projected

/-- The actual hidden resolution is the same lazy cache query after removing only its two seed counters and uniform instrumentation. -/
theorem resolve_query (role : PqxdhRecordLiftInterface.Role) (slot : PqxdhRecordLiftInterface.Slot n)
    (before : State n) :
    (normalize (PqxdhRecordLiftWorld.resolve role (.hidden slot))).run before =
      (normalize (PqxdhRecordLiftWorld.kernel role <$> lens.query slot)).run before := by
  have query := LazyOracleDiscard.impl_project slot (mask before).seeds
  have sampled := sampled_mask ((PqxdhRecordLiftLazyTable.impl slot).run (mask before).seeds) (mask before)
  have projected := congrArg (fun distribution => (fun result =>
    (PqxdhRecordLiftWorld.kernel role result.1.1,
      { result.2 with seeds := (result.1.2.1, ⟨0, 0⟩) })) <$> distribution) sampled
  have queried := congrArg (fun distribution => (fun result =>
    (PqxdhRecordLiftWorld.kernel role result.1, lens.set (mask before) result.2)) <$> distribution) query
  simp only [normalize, PqxdhRecordLiftWorld.resolve, StateT.run, bind_pure_comp,
    Functor.map_map, Prod.map_def, id_eq, mask] at projected ⊢
  rw [projected]
  simpa only [StateLens.query, StateT.run, state_map_apply, Functor.map_map, Prod.map_def, id_eq,
    lens, mask] using queried

end BeaconcryptCore.Computational.RegistrationNativeSeedDelayCore

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayCore.mask_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayCore.mask_fields
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayCore.mask_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayCore.mask_idempotent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayCore.mask_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayCore.mask_set
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayCore.sampled_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayCore.sampled_frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayCore.normalize_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayCore.normalize_frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayCore.normalize_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayCore.normalize_commutes
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayCore.sampled_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayCore.sampled_mask
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayCore.resolve_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayCore.resolve_query
