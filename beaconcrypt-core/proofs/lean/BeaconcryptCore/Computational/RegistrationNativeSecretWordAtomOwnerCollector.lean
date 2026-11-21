-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconPrepare

/-! Successful actual Beacon preparation contains its same indexed decapsulation reply. The complete prefix and suffix states are retained under arbitrary concrete callback interpretation; metadata admission cannot replace or manufacture the retained opaque word. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerCollector
open RegistrationNativeSecretWordBeaconCollect (Spec Input zero ordinary collect)
open RegistrationNativeSecretWordBeaconPrefix (Header beforeDecap afterDecap)
open RegistrationNativeSecretWordBeaconPrepare (Prepared prepare)
open RegistrationNativeSecretWord (Word)
variable {I D K X Response Private : Type}
variable (completedBinding : beaconcrypt_core.session.CompletedRegistrationBinding)

/-- The exact successful collected word comes from its actual sole decapsulation at the reached prefix state. -/
theorem collect_receipt (implementation : QueryImpl (Spec I D K X Response) (StateT Private ProbComp))
    (identity : I) (oneTime : D) (kem : K) (raw : Pqxdh.Bytes) (before after : Private) (input : Input Response)
    (supported : (some input, after) ∈ support ((simulateQ implementation (collect identity oneTime kem raw)).run before)) :
    ∃ header first second word,
      (some header, first) ∈ support ((simulateQ implementation (simulateQ ordinary (beforeDecap identity raw))).run before) ∧
      (some word, second) ∈ support ((implementation (.decapsulate header.ciphertext kem)).run first) ∧
      input.kem = word := by
  simp only [collect, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨initial, first⟩, earlier, continued⟩ := supported
  cases initial with
  | none => simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at continued
  | some header =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at continued
      obtain ⟨⟨reply, second⟩, called, later⟩ := continued
      cases reply with
      | none => simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at later
      | some word =>
          simp only [simulateQ_map, StateT.run_map, support_map] at later
          obtain ⟨⟨plain, reached⟩, _finished, returned⟩ := later
          cases plain with
          | none => simp only [Option.map_none, Prod.mk.injEq, reduceCtorEq, false_and] at returned
          | some plain =>
              have same : (⟨plain, word⟩ : Input Response) = input := by
                simpa only [Option.map_some, Prod.map_apply, Option.some.injEq] using congrArg Prod.fst returned
              exact ⟨header, first, second, word, earlier, called, (congrArg Input.kem same).symm⟩

/-- Actual metadata admission preserves the same collected value and full reached state. -/
theorem prepare_receipt (implementation : QueryImpl (Spec I D K X Response) (StateT Private ProbComp))
    (control : beaconcrypt_core.pqxdh.BeaconInitSent) (identity : I) (oneTime : D) (kem : K) (raw : Pqxdh.Bytes)
    (before after : Private) (pending : Prepared Response)
    (supported : (some pending, after) ∈ support
      ((simulateQ implementation (prepare (completedBinding := completedBinding) control identity oneTime kem raw)).run before)) :
    (some pending.collected, after) ∈ support ((simulateQ implementation (collect identity oneTime kem raw)).run before) := by
  simp only [prepare, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨collected, middle⟩, called, returned⟩ := supported
  simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq] at returned
  obtain ⟨equal, rfl⟩ := returned
  cases collected with
  | none => simp only [Option.bind_none, reduceCtorEq] at equal
  | some collected =>
      simp only [Option.bind_some] at equal
      cases admitted : PqxdhPhase2DhMetadata.admitted (completedBinding := completedBinding) control collected.plain with
      | none => simp only [admitted, Option.map_none, reduceCtorEq] at equal
      | some metadata =>
          simp only [admitted, Option.map_some, Option.some.injEq] at equal
          cases equal
          exact called

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerCollector
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerCollector.collect_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerCollector.collect_receipt
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerCollector.prepare_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerCollector.prepare_receipt
