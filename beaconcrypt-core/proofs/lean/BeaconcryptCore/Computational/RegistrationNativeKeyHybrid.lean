-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKeyPhases
import BeaconcryptCore.Computational.RegistrationBoundKeySchedule
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntryTable

/-! The G1-to-G2 key hop begins with the protected entry's uniform64 PRK and includes actual root Expand, initial64 and ongoing76. Every other preparation and the entire adaptive later experiment run inside the explicit distinguisher. First-touch indices are assigned at admitted material demand after the separate proved prepare-time PRK deferral. Literal192 aliases retain one complete108 answer. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeKeyHybrid
open PqxdhRegistrationJointKemSecondEntry (indexedImpl indexed_eager_output indexed_lazy pin pin_congr IState IsValue)
open PqxdhServerAuthKeySchedule (Output Distinguisher keySchedule realGame uniformGame)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open PqxdhSecretInputKdf (HmacSha512 HmacBlock)

abbrev Spec := PqxdhRegistrationJointKemSecondEntry.Spec Pqxdh.Bytes Output
def empty : IState Pqxdh.Bytes Output := (∅, 0)

/-- PRK dependence is included from the actual root Expand; no root32 reply appears in independently sampled context. -/
noncomputable def sampler (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (count : Nat) :
    Nat → ProbComp Output := fun index =>
  if index < count then $ᵗ Output else keySchedule source hmac <$> ($ᵗ HmacBlock)

noncomputable def hybrid (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (client : OracleComp Spec Bool) (count : Nat) : ProbComp Bool :=
  (simulateQ (indexedImpl (sampler source hmac count)) client).run' empty

noncomputable def reduction (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (client : OracleComp Spec Bool) (index : Nat) : Distinguisher := fun output =>
  (simulateQ (indexedImpl (pin index output (sampler source hmac index))) client).run' empty

noncomputable def uniform (client : OracleComp Spec Bool) : ProbComp Bool :=
  (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl client).run' ∅

/-- One explicitly constructed primitive experiment contains the whole adaptive entry client, starting before the selected PRK/root Expand. -/
theorem hybrid_real (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (client : OracleComp Spec Bool) (index : Nat) :
    𝒟[hybrid source hmac client index] =
      𝒟[realGame source hmac (reduction source hmac client index)] := by
  rw [hybrid, indexed_eager_output (sampler source hmac index) index client empty]
  simp only [sampler, Nat.lt_irrefl, ite_false, bind_map_left]
  rfl

theorem hybrid_uniform (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (client : OracleComp Spec Bool) (index : Nat) :
    𝒟[hybrid source hmac client (index + 1)] =
      𝒟[uniformGame (reduction source hmac client index)] := by
  rw [hybrid, indexed_eager_output (sampler source hmac (index + 1)) index client empty]
  have pinned : ∀ output, pin index output (sampler source hmac (index + 1)) =
      pin index output (sampler source hmac index) := fun output =>
    pin_congr index output _ _ fun other different => by
      simp only [sampler]
      congr 1
      exact propext ⟨fun below => Nat.lt_of_le_of_ne (Nat.le_of_lt_succ below) different,
        fun below => Nat.lt_succ_of_lt below⟩
  simp only [sampler, Nat.lt_succ_self, ite_true, pinned]
  rfl

/-- The protected entry incurs the existing five ordinary primitive advantages, including root Expand before initial64/ongoing76. -/
theorem hop (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect source hmac)
    (client : OracleComp Spec Bool) (index : Nat) :
    (hybrid source hmac client index).boolDistance (hybrid source hmac client (index + 1)) ≤
      RegistrationBoundKeySchedule.keyLoss source hmac (reduction source hmac client index) := by
  have changed : (hybrid source hmac client index).boolDistance (hybrid source hmac client (index + 1)) =
      (realGame source hmac (reduction source hmac client index)).boolDistance
        (uniformGame (reduction source hmac client index)) := by
    unfold ProbComp.boolDistance
    rw [hybrid_real, hybrid_uniform]
  rw [changed]
  exact PqxdhServerAuthKeySchedule.keySchedule_bound source hmac correct _

theorem telescope (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect source hmac)
    (client : OracleComp Spec Bool) (count : Nat) :
    (hybrid source hmac client 0).boolDistance (hybrid source hmac client count) ≤
      ∑ index ∈ Finset.range count,
        RegistrationBoundKeySchedule.keyLoss source hmac (reduction source hmac client index) := by
  induction count with
  | zero => simp [ProbComp.boolDistance_self]
  | succ count ih =>
    rw [Finset.sum_range_succ]
    exact (ProbComp.boolDistance_triangle _ _ _).trans (add_le_add ih (hop source hmac correct client count))

/-- At most this many actual material demands imply at most this many first-touch draws. Repeats of the same full source input do not consume another hybrid index. -/
theorem all_uniform (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (client : OracleComp Spec Bool) (count : Nat)
    (bounded : client.IsQueryBoundP (IsValue (D := Pqxdh.Bytes) (R := Output)) count) :
    hybrid source hmac client count = uniform client := by
  have lazy := indexed_lazy (sampler source hmac count) count
    (fun index below => by simp only [sampler, below, ite_true]) client count bounded empty (by simp [empty])
  have final := congrArg (fun work => Prod.fst <$> work) lazy
  simpa only [hybrid, uniform, StateT.run'_eq, Functor.map_map, empty, Prod.map, id_eq] using final

/-- The computational uniform108 endpoint is the proved five-hop sum for every actually reached protected entry, not a representation assumption about its bytes. -/
theorem bound (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect source hmac)
    (client : OracleComp Spec Bool) (count : Nat)
    (bounded : client.IsQueryBoundP (IsValue (D := Pqxdh.Bytes) (R := Output)) count) :
    (hybrid source hmac client 0).boolDistance (uniform client) ≤
      ∑ index ∈ Finset.range count,
        RegistrationBoundKeySchedule.keyLoss source hmac (reduction source hmac client index) := by
  rw [← all_uniform source hmac client count bounded]
  exact telescope source hmac correct client count

end BeaconcryptCore.Computational.RegistrationNativeKeyHybrid

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyHybrid.hybrid_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyHybrid.hybrid_real
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyHybrid.hybrid_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyHybrid.hybrid_uniform
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyHybrid.hop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyHybrid.hop
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyHybrid.telescope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyHybrid.telescope
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyHybrid.all_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyHybrid.all_uniform
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyHybrid.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyHybrid.bound
