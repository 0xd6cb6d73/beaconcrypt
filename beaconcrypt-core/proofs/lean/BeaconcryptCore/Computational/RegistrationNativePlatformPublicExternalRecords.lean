-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalLocal
/-! Literal ordinary sends use exactly one terminal public capacity gate; its reached external coin cost is bounded by the per-site reservation allowance. Raw receives add no external calls. Old native/cryptographic samplers and counters remain separate, and every failure and P poststate stays in the actual tree. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalRecords
open RegistrationNativePlatformPublicFrontend
open RegistrationNativePlatformPublicExternalLocal (IsExternal platformFull_bound)
open PqxdhRecordLiftInterface (RecordQuery)
variable {n : Nat} {E Platform A B KemSK : Type}

private theorem old_zero (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) :
    (old query).IsQueryBoundP (IsExternal (KemSK := KemSK)) 0 := by
  simp [old, IsExternal, isQueryBoundP_query_iff]

private theorem zero_bind {J : Type} {queries : OracleSpec J}
    (work : OracleComp queries A) (next : A → OracleComp queries B) (counted : J → Prop) [DecidablePred counted]
    (cap : Nat) (first : work.IsQueryBoundP counted 0)
    (later : ∀ value, (next value).IsQueryBoundP counted cap) :
    (work >>= next).IsQueryBoundP counted cap := by
  simpa only [Nat.zero_add] using isQueryBoundP_bind (n := 0) (m := cap) first (fun value _ => later value)

/-- The actual terminal public gate invokes its capacity reservation once, preserving either result and the exact P poststate. -/
theorem gate_bound (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (size : A → Nat)
    (output : Option A) (cap : Nat) (bounded : ∀ amount before, ((reserve amount).run before).IsTotalQueryBound cap) (before : Platform) :
    ((RegistrationNativePlatformOrdinaryGate.gate (fun amount => platformFull (n := n) (KemSK := KemSK) (reserve amount)) size output).run before).IsQueryBoundP
      (IsExternal (KemSK := KemSK)) cap := by
  cases output with
  | none => trivial
  | some value =>
    simp only [RegistrationNativePlatformOrdinaryGate.gate, StateT.run_bind]
    exact (isQueryBoundP_bind (n := cap) (m := 0)
      (platformFull_bound (reserve (size value)) before cap (bounded _ _))
      (fun result _ => by cases result.1 <;> trivial)).mono (by omega)

def IsSend : RecordQuery → Bool
  | .inl (.inl _) => true
  | .inr (_, .inl _) => true
  | _ => false

/-- Each actual ordinary send adds at most its one public reservation's external coin cap; raw receives add none. Old native and cryptographic calls remain in their separate bill. -/
theorem record_bound {source : RegistrationNativeMldsa.Source}
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (query : RecordQuery)
    (cap : Nat) (bounded : ∀ amount before, ((reserve amount).run before).IsTotalQueryBound cap)
    (before : State source Platform) :
    ((record (n := n) (KemSK := KemSK) reserve query).run before).IsQueryBoundP (IsExternal (KemSK := KemSK)) (if IsSend query then cap else 0) := by
  rcases query with (send | raw) | ⟨index, (plaintext | raw)⟩
  · simp only [record, StateT.run, IsSend, ite_true]
    apply zero_bind _ _ _ cap (old_zero (n := n) (KemSK := KemSK) (.inr (.inl (.inl send))))
    intro output
    simp only [bind_pure_comp, isQueryBoundP_map_iff]
    exact gate_bound reserve _ output cap bounded before.2
  · simpa only [record, StateT.run, IsSend, Bool.false_eq_true, ite_false, isQueryBoundP_map_iff] using
      (old_zero (n := n) (KemSK := KemSK) (.inr (.inl (.inr raw))))
  · simp only [record, StateT.run, IsSend, ite_true]
    cases before.1.beacons[index]? with
    | none => trivial
    | some owner =>
      dsimp only
      apply zero_bind _ _ _ cap (old_zero (n := n) (KemSK := KemSK) (.inr (.inr (owner.view.worldOwner, .inl plaintext))))
      intro output
      simp only [bind_pure_comp, isQueryBoundP_map_iff]
      exact gate_bound reserve _ output cap bounded before.2
  · simp only [record, StateT.run, IsSend, Bool.false_eq_true, ite_false]
    cases before.1.beacons[index]? with
    | none => trivial
    | some owner =>
      rw [isQueryBoundP_map_iff]
      exact old_zero _
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalRecords

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalRecords.gate_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalRecords.gate_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalRecords.record_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalRecords.record_bound
