-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerFields
import BeaconcryptCore.Computational.RegistrationNativePublicSourceSupport

/-! Every successful symbolic Beacon collector has its same actual public-prefix, decapsulation and DH-suffix receipts, with all intermediate source states retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCollectReceipt
open RegistrationNativeSecretWordBeaconCollect (Spec Input ordinary collect)
open RegistrationNativeSecretWordBeaconPrefix (Header beforeDecap afterDecap)
variable {I D K X Response S : Type}

/-- The opaque word in a successful collector is exactly the reply of its actual intervening KEM callback. -/
theorem receipt (implementation : QueryImpl (Spec I D K X Response) (StateT S ProbComp))
    (identity : I) (oneTime : D) (kem : K) (raw : Pqxdh.Bytes) (before after : S) (collected : Input Response)
    (supported : (some collected, after) ∈ support ((simulateQ implementation (collect identity oneTime kem raw)).run before)) :
    ∃ header : Header X Response, ∃ middle reached,
      (some header, middle) ∈ support
        ((simulateQ implementation (simulateQ ordinary (beforeDecap (D := D) (K := K) identity raw))).run before) ∧
      (some collected.kem, reached) ∈ support ((implementation (.decapsulate header.ciphertext kem)).run middle) ∧
      collected.plain.response = header.response ∧ collected.plain.ciphertext = header.ciphertext ∧
      collected.plain.server = header.server ∧ collected.plain.serverConverted = header.serverConverted := by
  simp only [collect, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨initial, middle⟩, prepared, supported⟩ := supported
  cases initial with
  | none => simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported; cases supported
  | some header =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨word, reached⟩, getter, supported⟩ := supported
      cases word with
      | none => simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported; cases supported
      | some word =>
          simp only [simulateQ_map, StateT.run_map, support_map] at supported
          obtain ⟨⟨plain, final⟩, suffix, equal⟩ := supported
          cases plain with
          | none => cases equal
          | some plain =>
              simp only [Option.map_some, Prod.mk.injEq, Option.some.injEq] at equal
              obtain ⟨rfl, rfl⟩ := equal
              have possible : some plain ∈ support (simulateQ ordinary (afterDecap (I := I) (K := K) oneTime header RegistrationNativeSecretWordBeaconCollect.zero)) := by
                apply support_simulateQ_run'_subset implementation _ reached
                rw [StateT.run'_eq, support_map]
                exact ⟨(some plain, final), suffix, rfl⟩
              exact ⟨header, middle, reached, prepared, getter,
                RegistrationNativeSecretWordTargetOwnerFields.suffix oneTime header _ plain
                  (RegistrationNativePublicSourceSupport.simulate_support _ _ _ possible)⟩
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCollectReceipt
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCollectReceipt.receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCollectReceipt.receipt
