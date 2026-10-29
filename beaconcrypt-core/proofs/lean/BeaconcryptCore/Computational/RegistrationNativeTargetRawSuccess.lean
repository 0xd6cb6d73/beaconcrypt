-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeTargetLedgerCore

/-! Successful original raw callbacks expose their same successful typed result and unchanged concrete poststate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeTargetRawSuccess
variable {NativeState : Type}

/-- The same successful original raw build returns its literal typed key-id/serialized response pair. -/
theorem build (wire : RegistrationNativeWire.Wire)
    (typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT NativeState ProbComp))
    (handle : Nat) (payload : Option Pqxdh.Bytes) (response : PqxdhServerRegistrationPublication.Response)
    (before after : NativeState)
    (supported : (some response, after) ∈ support ((RegistrationNativeRawAdapter.handler wire typed (.inr (.build handle payload))).run before)) :
    (.ok (some (response.keyId, response.serialized)), after) ∈ support
      ((typed (.inr (.build handle (RegistrationNativeRawAdapter.application payload)))).run before) := by
  simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter] at supported
  rw [simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at supported
  obtain ⟨⟨reply, current⟩, called, returned⟩ := supported
  cases actual : reply with
  | fail error | div => simp [actual, RegistrationNativeRawAdapter.responseOption, RegistrationNativeRawAdapter.resultOption] at returned
  | ok reply => cases reply with
    | none => simp [actual, RegistrationNativeRawAdapter.responseOption, RegistrationNativeRawAdapter.resultOption] at returned
    | some pair =>
        rcases pair with ⟨keyId, bytes⟩
        simp only [actual, RegistrationNativeRawAdapter.responseOption, RegistrationNativeRawAdapter.resultOption,
          Option.map_some, Prod.mk.injEq] at returned
        obtain ⟨same, stateEq⟩ := returned
        have responseEq : (⟨bytes, keyId⟩ : PqxdhServerRegistrationPublication.Response) = response := Option.some.inj same
        cases responseEq
        cases stateEq
        simpa only [actual] using called
end BeaconcryptCore.Computational.RegistrationNativeTargetRawSuccess
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTargetRawSuccess.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTargetRawSuccess.build
