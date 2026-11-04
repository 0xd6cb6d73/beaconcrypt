-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaBadSource
import BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyStartup
import BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicSource

/-! The actual initialized protected-origin failure marker is covered by the literal original final-cache collision event and the finite family of actual dynamic generation monitors. Source startup and every failed prefix are averaged on the same original source distribution. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaInitializedCover

private theorem average {A : Type} {count : Nat} (prior : ProbComp A)
    (bad collision : A → ProbComp Bool) (trial : Fin count → A → ProbComp Bool)
    (pointwise : ∀ value ∈ support prior, Pr{let won ← bad value}[won = true] ≤
      Pr{let hit ← collision value}[hit = true] + ∑ index, Pr{let hit ← trial index value}[hit = true]) :
    Pr{let won ← prior >>= bad}[won = true] ≤
      Pr{let hit ← prior >>= collision}[hit = true] + ∑ index, Pr{let hit ← prior >>= trial index}[hit = true] := by
  simp only [prEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' value, Pr{let sampled ← prior}[sampled = value] *
        (Pr{let hit ← collision value}[hit = true] + ∑ index, Pr{let hit ← trial index value}[hit = true]) := by
      apply ENNReal.tsum_le_tsum
      intro value
      by_cases possible : value ∈ support prior
      · exact mul_le_mul' le_rfl (pointwise value possible)
      · simp only [prEvent_eq_zero_of_not_mem_support _ possible, zero_mul, le_refl]
    _ = _ := by
      simp only [mul_add, Finset.mul_sum, ENNReal.tsum_add]
      rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]

open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source)
open RegistrationNativeMldsaOpaque (Pool handleSource)
variable {n : Nat} {ι KemSK V : Type} {base : OracleSpec ι}
variable (source : Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec V)

noncomputable def badContinued (started : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × Pool source) : ProbComp Bool :=
  match started.1 with
  | none => pure false
  | some initial => (fun result => result.2.2) <$>
      (simulateQ (RegistrationNativeMldsaBadSource.handler source setup checks wire route representation initial.created initial.credential)
        (adversary initial.public)).run ((initial.state, started.2), false)

noncomputable def collisionContinued (started : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × Pool source) : ProbComp Bool :=
  match started.1 with
  | none => pure false
  | some initial => (fun result => @decide (CacheHasCollision result.2.1.server.world.world.1.primitive.2) (Classical.propDecidable _)) <$>
      (simulateQ (RegistrationNativeMldsaTableStop.callback source setup checks wire route representation initial.created initial.credential)
        (adversary initial.public)).run (initial.state, started.2)

noncomputable def badGame (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) : ProbComp Bool := do
  let started ← RegistrationNativeMldsaTableProgram.evaluate source
    (RegistrationNativeMldsaCreation.start (n := n) setup ensureInit identityIndex serverKeyId) {}
  badContinued source setup checks wire route representation adversary started

noncomputable def collisionGame (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) : ProbComp Bool := do
  let started ← RegistrationNativeMldsaTableProgram.evaluate source
    (RegistrationNativeMldsaCreation.start (n := n) setup ensureInit identityIndex serverKeyId) {}
  collisionContinued source setup checks wire route representation adversary started

/-- Actual startup and original typed creation allowances discharge every source invariant and finite-room condition in the global protected-origin cover. -/
theorem bound (cap : Nat) (bounded : ∀ publicValue, (adversary publicValue).IsQueryBoundP
    (fun query => RegistrationNativeRawAdapter.kind query = (1 : Fin 12)) cap)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    Pr{let bad ← badGame (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId}[bad = true] ≤
      Pr{let collision ← collisionGame (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId}[collision = true] +
      ∑ index : Fin (cap + 1), Pr{let candidate ← (RegistrationNativeMldsaDynamicSource.game (n := n) source setup checks wire route representation adversary
        false index.val ensureInit identityIndex serverKeyId)}[candidate.isSome = true] := by
  let start := RegistrationNativeMldsaFamilyStartup.start (n := n) (cap := cap + 1) source setup ensureInit identityIndex serverKeyId
  let bad := fun started : (Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × RegistrationNativeMldsaGhostFamily.Family (cap + 1)) × Pool source =>
    badContinued source setup checks wire route representation adversary (started.1.1, started.2)
  let collision := fun started : (Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × RegistrationNativeMldsaGhostFamily.Family (cap + 1)) × Pool source =>
    collisionContinued source setup checks wire route representation adversary (started.1.1, started.2)
  let trial := fun (index : Fin (cap + 1)) (started : (Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × RegistrationNativeMldsaGhostFamily.Family (cap + 1)) × Pool source) =>
    Option.isSome <$> RegistrationNativeMldsaDynamicSource.continued source setup checks wire route representation adversary false index.val
      (started.1.1, started.1.2 index) started.2
  have pointwise : ∀ started ∈ support start, Pr{let won ← bad started}[won = true] ≤
      Pr{let hit ← collision started}[hit = true] + ∑ index, Pr{let hit ← trial index started}[hit = true] := by
    intro started possible
    rcases started with ⟨⟨initialized, ghosts⟩, pool⟩
    cases initialized with
    | none => simp [bad, collision, trial, badContinued, collisionContinued, RegistrationNativeMldsaDynamicSource.continued]
    | some initial =>
        obtain ⟨fallback, safe, attempts⟩ := RegistrationNativeMldsaFamilyStartup.initialized source setup ensureInit identityIndex serverKeyId initial ghosts pool possible
        have covered := RegistrationNativeMldsaBadSource.bound source setup checks wire route representation initial.created initial.credential
          fallback (adversary initial.public) cap (bounded initial.public) (initial.state, (ghosts, pool)) safe
          (by simp only [RegistrationNativeMldsaFamilyCover.counter, attempts]; omega)
        simpa only [bad, collision, trial, badContinued, collisionContinued, RegistrationNativeMldsaDynamicSource.continued,
          Bool.false_eq_true, ite_false, Functor.map_map, prEvent_map, decide_eq_true_eq,
          RegistrationNativeMldsaGhostFamily.nativeState, RegistrationNativeMldsaGhostFamily.coordinateState] using covered
  have averaged := average start bad collision trial pointwise
  have bad_equal : start >>= bad = badGame (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId := by
    unfold badGame
    rw [← RegistrationNativeMldsaFamilyStartup.erase (n := n) (cap := cap + 1) source setup ensureInit identityIndex serverKeyId, bind_map_left]
  have collision_equal : start >>= collision = collisionGame (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId := by
    unfold collisionGame
    rw [← RegistrationNativeMldsaFamilyStartup.erase (n := n) (cap := cap + 1) source setup ensureInit identityIndex serverKeyId, bind_map_left]
  have trial_equal (index : Fin (cap + 1)) : start >>= trial index = Option.isSome <$>
      RegistrationNativeMldsaDynamicSource.game (n := n) source setup checks wire route representation adversary false index.val ensureInit identityIndex serverKeyId := by
    unfold RegistrationNativeMldsaDynamicSource.game
    rw [map_bind, ← RegistrationNativeMldsaFamilyStartup.coordinate (n := n) source setup ensureInit identityIndex serverKeyId index, bind_map_left]
  simpa only [bad_equal, collision_equal, trial_equal, prEvent_map] using averaged
end BeaconcryptCore.Computational.RegistrationNativeMldsaInitializedCover

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaInitializedCover.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaInitializedCover.bound
