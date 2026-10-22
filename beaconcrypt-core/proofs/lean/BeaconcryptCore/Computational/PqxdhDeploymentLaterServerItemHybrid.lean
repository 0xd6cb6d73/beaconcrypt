-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets

/-! LQ-F upstream, unit A2: the hybrid of stage S7, generic in the client (LQ-F upstream design-v2, decision D4 and section 4.4, module `…ItemHybrid`). Item 2's stage S7 (`PqxdhRegistrationJointKemSecondEntry`) proves its hybrid argument for the closed classical factored root client; its proofs never look inside that client. This module restates them for any client `client : OracleComp (EntrySpec Output) Bool` (the factored root client's interface: coins and value requests at 128-byte coordinates returning 108 bytes), on the generic hybrid `PqxdhDeploymentLaterServerItemTargets.hybridOf` and distinguisher `entryDkOf` of unit D1 (the classical `hybrid` and `entryDk` with the client abstracted: `hybrid_hybridOf`, `entryDk_entryDkOf`).

- `hybridOf_root`, `hybridOf_uniform`, `hybridOf_hop`, `hybridOf_telescope`: the `k`-th hybrid is the key-schedule game with a uniform root on `entryDkOf … k`, the `k + 1`-st is the game with 108 uniform bytes on it (eager sampling of the `k`-th fresh entry), so each hop costs G2's four key-schedule advantages (`PqxdhRegistrationJointKemSecondEntry.keyScheduleBound`, by `PqxdhKeyScheduleFromRoot.fromRoot_bound` under `SourceFullCorrect`), and the hybrids telescope.
- `entryDkOf_zero` and `uniform_hybridOf`: the distinguisher of entry 0 is the first-value-table distinguisher, so any game with the output distribution of the key-schedule game on that distinguisher has the output distribution of the 0-th hybrid.
- `hybridOf_all` and `slotGameOf_all`: with at least as many fresh-entry samplers, or slots, as value requests, the hybrid, and the first-touch slot allocator in front of the persistent lazy table, are the lazy uniform table.

The only client-specific inputs of the hybrid argument are the value-request bound and the stage S3b equality; for the logged branch these are `PqxdhDeploymentLaterServerItemOnce.entryClientL_two` and `PqxdhDeploymentLaterServerItemFactor.uniformGameL_entry`. No assumption is added: the premise of the hop is `SourceFullCorrect`, as in the classical stage S7. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option maxRecDepth 100000
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemHybrid
open PqxdhSecretInputKdf (RootOutput HmacSha512)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open PqxdhFullSecretInputKdf (SourceFullCorrect)
open PqxdhServerAuthKeySchedule (rootHybrid fromRoot)
open PqxdhRegistrationJointKemEntryFactor (Output EntrySpec firstTable)
open PqxdhRegistrationJointKemSecondEntry (IsValue keyScheduleBound sampler pin pin_congr lazyImpl slotImpl tableService
  emptyAlloc run_eager advantage_right keySchedule_hop firstTable_pinned indexed_lazy slot_lazy slotGood_empty
  cacheOf_empty)
open PqxdhDeploymentLaterServerItemTargets (hybridOf entryDkOf)

variable (source : FixedHkdfSha512NoSaltSource) (client : OracleComp (EntrySpec Output) Bool)

/-! ### The hops -/

/-- The `k`-th hybrid of any client is the key-schedule game with a uniform root on the client's `k`-th entry distinguisher. -/
theorem hybridOf_root (k : ℕ) :
    𝒟[hybridOf source client k] = 𝒟[rootHybrid source (entryDkOf source client k)] := by
  rw [hybridOf, run_eager _ k]
  simp only [sampler, lt_irrefl, ite_false, bind_map_left]
  rfl

/-- The `k + 1`-st hybrid of any client is the key-schedule game with 108 uniform bytes on the client's `k`-th entry distinguisher. -/
theorem hybridOf_uniform (k : ℕ) :
    𝒟[hybridOf source client (k + 1)] =
      𝒟[PqxdhServerAuthKeySchedule.uniformGame (entryDkOf source client k)] := by
  rw [hybridOf, run_eager _ k]
  have pinned : ∀ value, pin k value (sampler source (k + 1)) = pin k value (sampler source k) :=
    fun value => pin_congr k value _ _ fun j other => by
      simp only [sampler]
      congr 1
      exact propext ⟨fun below => Nat.lt_of_le_of_ne (Nat.le_of_lt_succ below) other,
        fun below => Nat.lt_succ_of_lt below⟩
  simp only [sampler, Nat.lt_succ_self, ite_true, pinned]
  rfl

/-- One hop for any client: replacing the `k`-th fresh entry's key-schedule output by 108 uniform bytes costs the four key-schedule advantages of G2 on the client's `k`-th entry distinguisher. -/
theorem hybridOf_hop (hmac : HmacSha512) (correct : SourceFullCorrect source hmac) (k : ℕ) :
    (hybridOf source client k).boolDistance (hybridOf source client (k + 1)) ≤
      keyScheduleBound source hmac (entryDkOf source client k) := by
  rw [PqxdhRegistrationJointKemIdealKeys.advantage_left (hybridOf_root source client k),
    advantage_right (hybridOf_uniform source client k)]
  exact keySchedule_hop source hmac correct _

/-- The hybrids of any client telescope: from the 0-th to the `q`-th hybrid, the advantage is at most the sum of the key-schedule bounds of the client's first `q` entry distinguishers. -/
theorem hybridOf_telescope (hmac : HmacSha512) (correct : SourceFullCorrect source hmac) (q : ℕ) :
    (hybridOf source client 0).boolDistance (hybridOf source client q) ≤
      ∑ k ∈ Finset.range q, keyScheduleBound source hmac (entryDkOf source client k) := by
  induction q with
  | zero => simp [ProbComp.boolDistance_self]
  | succ q ih =>
      rw [Finset.sum_range_succ]
      exact (ProbComp.boolDistance_triangle _ _ _).trans
        (add_le_add ih (hybridOf_hop source client hmac correct q))

/-! ### Entry 0 -/

/-- The distinguisher of entry 0 of any client is the first-value-table distinguisher: entry 0 answered by the given 108 bytes, every later fresh entry by the key-schedule output of a fresh uniform root. -/
theorem entryDkOf_zero :
    entryDkOf source client 0 = fun value =>
      (simulateQ (firstTable value (fromRoot source <$> ($ᵗ RootOutput))) client).run' (∅, none) := by
  funext value
  have constant : sampler source 0 = fun _ => fromRoot source <$> ($ᵗ RootOutput) := by
    funext j
    simp [sampler]
  rw [entryDkOf, firstTable_pinned, constant]

/-- A game with the output distribution of the key-schedule game on entry 0's first-value-table distinguisher has the output distribution of the 0-th hybrid. -/
theorem uniform_hybridOf (game : ProbComp Bool)
    (entry : 𝒟[game] = 𝒟[rootHybrid source (fun value =>
      (simulateQ (firstTable value (fromRoot source <$> ($ᵗ RootOutput))) client).run' (∅, none))]) :
    𝒟[game] = 𝒟[hybridOf source client 0] := by
  rw [entry, hybridOf_root, entryDkOf_zero]

/-! ### Every hidden entry ideal -/

/-- With at least as many fresh-entry samplers as value requests, the hybrid of any client is the lazy uniform table on the 128-byte coordinates. -/
theorem hybridOf_all (q : ℕ)
    (bounded : client.IsQueryBoundP (IsValue (D := PqxdhCorrelatedExtractFamily.Message) (R := Output)) q) :
    hybridOf source client q =
      (simulateQ lazyImpl client).run' (∅ : (PqxdhCorrelatedExtractFamily.Message →ₒ Output).QueryCache) := by
  have lazy := indexed_lazy (sampler source q) q (fun j below => by simp [sampler, below]) _ q bounded
    ((∅ : (PqxdhCorrelatedExtractFamily.Message →ₒ Output).QueryCache), 0) (by simp)
  rw [hybridOf, StateT.run'_eq, StateT.run'_eq, ← lazy, Functor.map_map]
  rfl

/-- With at least as many slots as value requests, the first-touch slot allocator in front of the persistent lazy table on `n` slots runs any client as the lazy uniform table. -/
theorem slotGameOf_all (n : ℕ)
    (bounded : client.IsQueryBoundP (IsValue (D := PqxdhCorrelatedExtractFamily.Message) (R := Output)) n) :
    (simulateQ (slotImpl (D := PqxdhCorrelatedExtractFamily.Message) (tableService (n := n))) client).run'
        (emptyAlloc, PqxdhRecordLiftLazyTable.initial) =
      (simulateQ lazyImpl client).run' (∅ : (PqxdhCorrelatedExtractFamily.Message →ₒ Output).QueryCache) := by
  have lazy := slot_lazy (n := n) client n bounded (emptyAlloc, PqxdhRecordLiftLazyTable.initial) slotGood_empty
    (by simp [emptyAlloc])
  rw [cacheOf_empty] at lazy
  rw [StateT.run'_eq, StateT.run'_eq, ← lazy, Functor.map_map]
  rfl

/-- Stage S7 for any client in slot form: a game with the output distribution of the key-schedule game on entry 0's first-value-table distinguisher, and the client through the first-touch slot allocator and the persistent lazy table on `n` slots, are distinguishable with advantage at most the sum of the key-schedule bounds of the client's first `n` entry distinguishers, when the client makes at most `n` value requests. -/
theorem slotOf_telescope (hmac : HmacSha512) (correct : SourceFullCorrect source hmac) (game : ProbComp Bool)
    (entry : 𝒟[game] = 𝒟[rootHybrid source (fun value =>
      (simulateQ (firstTable value (fromRoot source <$> ($ᵗ RootOutput))) client).run' (∅, none))])
    (n : ℕ) (bounded : client.IsQueryBoundP (IsValue (D := PqxdhCorrelatedExtractFamily.Message) (R := Output)) n) :
    game.boolDistance
        ((simulateQ (slotImpl (D := PqxdhCorrelatedExtractFamily.Message) (tableService (n := n))) client).run'
          (emptyAlloc, PqxdhRecordLiftLazyTable.initial)) ≤
      ∑ k ∈ Finset.range n, keyScheduleBound source hmac (entryDkOf source client k) := by
  rw [PqxdhRegistrationJointKemIdealKeys.advantage_left (uniform_hybridOf source client game entry),
    slotGameOf_all client n bounded, ← hybridOf_all source client n bounded]
  exact hybridOf_telescope source client hmac correct n

end BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemHybrid

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemHybrid.hybridOf_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemHybrid.hybridOf_root

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemHybrid.hybridOf_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemHybrid.hybridOf_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemHybrid.hybridOf_hop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemHybrid.hybridOf_hop

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemHybrid.hybridOf_telescope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemHybrid.hybridOf_telescope

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemHybrid.entryDkOf_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemHybrid.entryDkOf_zero

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemHybrid.uniform_hybridOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemHybrid.uniform_hybridOf

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemHybrid.hybridOf_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemHybrid.hybridOf_all

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemHybrid.slotGameOf_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemHybrid.slotGameOf_all

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemHybrid.slotOf_telescope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemHybrid.slotOf_telescope
