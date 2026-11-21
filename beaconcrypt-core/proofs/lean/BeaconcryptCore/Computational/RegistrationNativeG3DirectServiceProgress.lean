-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3RetainedCallbacks
import BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchBound

/-! The actual direct selective service advances its selected cursor by at most one at an original material demand and by zero at every other retained callback. These are supported-execution facts of its real reserve/cache operations, independent of material bytes, flags, optional failures and table capacity. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3DirectServiceProgress
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeG3FirstTouchBound (IsValue)
open RegistrationNativeKeyCompiler (KeySpec)
variable {n : Nat} {Value : Type}
attribute [local irreducible] uniformSample PqxdhServerAuthKeySchedule.fromRoot

private theorem reserve_progress (bytes : Pqxdh.Bytes) (before : RegistrationNativeHiddenService.State n) :
    (RegistrationNativeHiddenService.reserve bytes before).2.next ≤ before.next + 1 := by
  unfold RegistrationNativeHiddenService.reserve
  split
  · exact Nat.le_succ _
  · split
    · exact le_rfl
    · exact Nat.le_succ _

noncomputable def raw (materials : Slot n → Material) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (inside : Pqxdh.Bytes → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret) :=
  RegistrationNativeG3MetricCoins.localCoins.mapStateTBase
    (RegistrationNativeG3SelectiveService.fixedKeys materials seeds inside candidate)

private theorem raw_query (materials : Slot n → Material) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (inside : Pqxdh.Bytes → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (query : KeySpec.Domain) (before : RegistrationNativeSelectiveHiddenService.State n)
    (result : KeySpec.Range query × RegistrationNativeSelectiveHiddenService.State n)
    (supported : result ∈ support ((raw materials seeds inside candidate query).run before)) :
    result.2.1.next ≤ before.1.next + (if IsValue query then 1 else 0) := by
  change result ∈ support (simulateQ RegistrationNativeG3MetricCoins.localCoins
    ((RegistrationNativeG3SelectiveService.fixedKeys materials seeds inside candidate query).run before)) at supported
  have opened := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ supported
  cases query with
  | inl coin =>
      simp only [RegistrationNativeG3SelectiveService.fixedKeys, StateT.run_lift, bind_pure_comp, support_map] at opened
      obtain ⟨reply, _possible, rfl⟩ := opened
      simp only [IsValue, PqxdhRegistrationJointKemSecondEntry.IsValue, ite_false, Nat.add_zero]
      exact le_rfl
  | inr bytes =>
      simp only [IsValue, PqxdhRegistrationJointKemSecondEntry.IsValue, ite_true]
      cases chosen : RegistrationNativeSelectiveHiddenService.selected inside candidate bytes with
      | false =>
          simp only [RegistrationNativeG3SelectiveService.fixedKeys, StateT.run, chosen, Bool.false_eq_true, ite_false] at opened
          cases found : before.2 bytes with
          | some output =>
              simp only [RegistrationNativeSelectiveHiddenService.known, found, mem_support_pure_iff] at opened
              cases opened
              exact Nat.le_succ _
          | none =>
              simp only [RegistrationNativeSelectiveHiddenService.known, found, support_map] at opened
              obtain ⟨output, _possible, rfl⟩ := opened
              exact Nat.le_succ _
      | true =>
          simp only [RegistrationNativeG3SelectiveService.fixedKeys, StateT.run, chosen, ite_true] at opened
          have progress := reserve_progress bytes before.1
          cases allocated : RegistrationNativeHiddenService.reserve bytes before.1 with
          | mk slot after =>
              cases slot
              all_goals simp only [allocated, mem_support_pure_iff] at opened
              all_goals cases opened
              all_goals simpa only [allocated] using progress

private theorem raw_program (materials : Slot n → Material) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (inside : Pqxdh.Bytes → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (work : OracleComp KeySpec Value) (count : Nat) (bounded : work.IsQueryBoundP IsValue count)
    (before : RegistrationNativeSelectiveHiddenService.State n)
    (result : Value × RegistrationNativeSelectiveHiddenService.State n)
    (supported : result ∈ support ((simulateQ (raw materials seeds inside candidate) work).run before)) :
    result.2.1.next ≤ before.1.next + count := by
  induction work using OracleComp.inductionOn generalizing count before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      change before.1.next ≤ before.1.next + count
      omega
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, first, later⟩ := supported
      have grown := raw_query materials seeds inside candidate query before middle first
      have tail := ih middle.1 _ (bounded.2 middle.1) middle.2 later
      split_ifs at grown tail with counted
      · have positive := bounded.1.resolve_left (not_not.mpr counted)
        omega
      · omega

private theorem direct_bound (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (query : RegistrationNativeRetainedService.Spec.Domain) (before : RegistrationNativeRetainedService.Flags) :
    ((RegistrationNativeG3KeyService.direct source input inside query).run before).IsQueryBoundP IsValue
      (if RegistrationNativeRetainedService.IsDemand query then 1 else 0) := by
  cases query with
  | inl coin =>
      simp [RegistrationNativeG3KeyService.direct, StateT.run_lift, bind_pure_comp,
        RegistrationNativeRetainedService.IsDemand, RegistrationNativeKeyCompiler.coins,
        IsValue, PqxdhRegistrationJointKemSecondEntry.IsValue, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  | inr command => cases command with
    | prepare message => simp [RegistrationNativeG3KeyService.direct, StateT.run, RegistrationNativeRetainedService.IsDemand]
    | demand message =>
        cases prepared : before message
        all_goals cases formed : input message
        all_goals simp only [RegistrationNativeG3KeyService.direct, StateT.run, prepared, formed,
          RegistrationNativeRetainedService.IsDemand, Bool.false_eq_true, ite_false, ite_true]
        all_goals try trivial
        split
        · simp [isQueryBoundP_map_iff, isQueryBoundP_query_iff, IsValue, PqxdhRegistrationJointKemSecondEntry.IsValue]
        · trivial

/-- Every actual direct retained callback advances the original selected-slot cursor only within its literal material-demand bill. -/
theorem query_progress (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (materials : Slot n → Material) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (query : RegistrationNativeRetainedService.Spec.Domain) (before : RegistrationNativeSelectiveHiddenService.State n)
    (result : RegistrationNativeRetainedService.Spec.Range query × RegistrationNativeSelectiveHiddenService.State n)
    (supported : result ∈ support ((RegistrationNativeG3RetainedCallbacks.keys source input inside candidate materials seeds query).run before)) :
    result.2.1.next ≤ before.1.next + (if RegistrationNativeRetainedService.IsDemand query then 1 else 0) := by
  simp only [RegistrationNativeG3RetainedCallbacks.keys, StateT.run, RegistrationNativeG3SelectiveService.direct,
    simulateQ_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  change inner ∈ support (simulateQ RegistrationNativeG3MetricCoins.localCoins
    ((simulateQ (RegistrationNativeG3SelectiveService.fixedKeys materials seeds inside candidate)
      ((RegistrationNativeG3KeyService.direct source input inside query).run
        (RegistrationNativeG3SelectiveService.count query before).1.prepared)).run
          (RegistrationNativeG3SelectiveService.count query before))) at reached
  rw [QueryImpl.simulateQ_mapStateTBase_run] at reached
  have progress := raw_program materials seeds inside candidate
    ((RegistrationNativeG3KeyService.direct source input inside query).run (RegistrationNativeG3SelectiveService.count query before).1.prepared)
    _ (direct_bound source input inside query _) (RegistrationNativeG3SelectiveService.count query before) inner reached
  rcases query with coin | (message | message) <;> exact progress

end BeaconcryptCore.Computational.RegistrationNativeG3DirectServiceProgress
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3DirectServiceProgress.query_progress' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3DirectServiceProgress.query_progress
