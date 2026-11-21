-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetSource
import BeaconcryptCore.Computational.RegistrationNativeParsedTarget

/-! Raw decoding preserves any source-derived parsed-attempt counter. Malformed packets do not enter the typed callback, while decoded failures consume one ordinal. This lemma is generic in the complete source state and is instantiated from the current callback proof. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetRawCounter
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeInterface (Spec)
open RegistrationNativeWire (Wire)
variable {S : Type} (wire : Wire) (typed : QueryImpl TypedSpec (StateT S ProbComp)) (counter : S → Nat)
    (step : ∀ (query : TypedSpec.Domain) (before : S) (result : TypedSpec.Range query × S),
      result ∈ support ((typed query).run before) →
      counter result.2 = counter before + (RegistrationNativeSecretWordTargetCounter.isAccept query).toNat)

def increment (wire : Wire) : Spec.Domain → Nat
  | .inr (.accept raw) => (RegistrationNativeWire.readInit wire raw).isSome.toNat
  | _ => 0

include step in
private theorem projected_counter (query : TypedSpec.Domain) {Value : Type} (project : TypedSpec.Range query → Value)
    (before : S) (result : Value × S)
    (reached : result ∈ support (Prod.map project id <$>
      (typed query).run before)) :
    counter result.2 = counter before + (RegistrationNativeSecretWordTargetCounter.isAccept query).toNat := by
  rw [support_map] at reached
  obtain ⟨inner, supported, rfl⟩ := reached
  exact step query before inner supported

include step in
/-- The original raw command increments the private counter precisely when its actual native Init decoder succeeds. -/
theorem raw_counter (query : Spec.Domain) (before : S)
    (result : Spec.Range query × S)
    (reached : result ∈ support ((RegistrationNativeRawAdapter.handler wire
      (typed) query).run before)) :
    counter result.2 = counter before + increment wire query := by
  cases query with
  | inl coin =>
      simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
        RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
      exact step (.inl coin) before result reached
  | inr command =>
      cases command with
      | create edPin mlPin keyId =>
          cases ed : PqxdhDeploymentInterface.parsePin edPin with
          | none =>
              simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
                RegistrationNativeRawAdapter.adapter, ed, simulateQ_pure, StateT.run_pure,
                mem_support_pure_iff] at reached
              subst result
              rfl
          | some edValue =>
              cases ml : RegistrationNativeWire.parseMldsaPin mlPin with
              | none =>
                  simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
                    RegistrationNativeRawAdapter.adapter, ed, ml, simulateQ_pure, StateT.run_pure,
                    mem_support_pure_iff] at reached
                  subst result
                  rfl
              | some mlValue =>
                  simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
                    RegistrationNativeRawAdapter.adapter, ed, ml, simulateQ_map,
                    simulateQ_spec_query, StateT.run_map] at reached
                  exact projected_counter typed counter step
                    (.inr (.create edValue mlValue keyId)) RegistrationNativeRawAdapter.resultOption before result reached
      | accept raw =>
          cases read : RegistrationNativeWire.readInit wire raw with
          | none =>
              simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
                RegistrationNativeRawAdapter.adapter, read, simulateQ_pure, StateT.run_pure,
                mem_support_pure_iff] at reached
              subst result
              simp only [increment, read, Option.isSome_none, Bool.toNat_false, Nat.add_zero]
          | some packet =>
              simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
                RegistrationNativeRawAdapter.adapter, read, simulateQ_map, simulateQ_spec_query,
                StateT.run_map] at reached
              simpa only [increment, read, Option.isSome_some, Bool.toNat_true,
                RegistrationNativeSecretWordTargetCounter.isAccept] using
                projected_counter typed counter step (.inr (.accept packet)) RegistrationNativeRawAdapter.resultOption before result reached
      | bundle owner =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_map, simulateQ_spec_query, StateT.run_map] at reached
          exact projected_counter typed counter step (.inr (.bundle owner)) RegistrationNativeRawAdapter.resultOption before result reached
      | build session application =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_map, simulateQ_spec_query, StateT.run_map] at reached
          exact projected_counter typed counter step (.inr (.build session (RegistrationNativeRawAdapter.application application))) RegistrationNativeRawAdapter.responseOption before result reached
      | finish owner raw =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_map, simulateQ_spec_query, StateT.run_map] at reached
          exact projected_counter typed counter step (.inr (.finish owner (RegistrationNativeWire.readResponse wire raw))) RegistrationNativeRawAdapter.resultOption before result reached
      | hmac key message =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
          exact step (.inr (.hmac key message)) before result reached
      | hash bytes =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
          exact step (.inr (.hash bytes)) before result reached
      | serverSend keyId plaintext =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
          exact step (.inr (.serverSend keyId plaintext)) before result reached
      | serverRaw raw =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
          exact step (.inr (.serverRaw raw)) before result reached
      | beaconSend owner plaintext =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
          exact step (.inr (.beaconSend owner plaintext)) before result reached
      | beaconRaw owner raw =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
          exact step (.inr (.beaconRaw owner raw)) before result reached

/-- The increment depends only on the original native entry's raw query, never its projected success reply. -/
theorem entry_increment (wire : Wire) (query : Spec.Domain) (reply : Spec.Range query) :
    increment wire query = (RegistrationNativeEvents.parsedAccept wire ⟨.inl query, reply⟩).toNat := by
  cases query with
  | inl coin => rfl
  | inr command => cases command <;> rfl

end BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetRawCounter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetRawCounter.raw_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetRawCounter.raw_counter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetRawCounter.entry_increment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetRawCounter.entry_increment
