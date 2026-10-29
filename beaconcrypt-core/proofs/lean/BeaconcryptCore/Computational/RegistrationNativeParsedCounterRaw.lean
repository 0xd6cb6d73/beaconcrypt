-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeParsedCounterSource
import BeaconcryptCore.Computational.RegistrationNativeParsedTarget

/-! Actual bounded native decoding connects each raw accept entry to the source's private parsed-call counter. Malformed packets produce their original rejection without entering the typed frontend; every decoded attempt increments before authentication and replay, including all failed outcomes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeParsedCounterRaw
open RegistrationNativeExperiment (State)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeInterface (Spec)
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {mlSource : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationNativeExperiment.handler

def increment (wire : Wire) : Spec.Domain → Nat
  | .inr (.accept raw) => (RegistrationNativeWire.readInit wire raw).isSome.toNat
  | _ => 0

private theorem projected_counter (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (query : TypedSpec.Domain) {Value : Type} (project : TypedSpec.Range query → Value)
    (before : State n KemSK mlSource) (result : Value × State n KemSK mlSource)
    (reached : result ∈ support (Prod.map project id <$>
      (RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential query).run before)) :
    result.2.parsedAccepts = before.parsedAccepts + (RegistrationNativeParsedCounterSource.isAccept query).toNat := by
  rw [support_map] at reached
  obtain ⟨inner, supported, rfl⟩ := reached
  exact RegistrationNativeParsedCounterSource.typed_counter setup checks wire route representation created credential query before inner supported

/-- The original raw command increments the private counter precisely when its actual native Init decoder succeeds. -/
theorem raw_counter (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (query : Spec.Domain) (before : State n KemSK mlSource)
    (result : Spec.Range query × State n KemSK mlSource)
    (reached : result ∈ support ((RegistrationNativeRawAdapter.handler wire
      (RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential) query).run before)) :
    result.2.parsedAccepts = before.parsedAccepts + increment wire query := by
  cases query with
  | inl coin =>
      simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
        RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
      exact RegistrationNativeParsedCounterSource.typed_counter setup checks wire route representation created credential (.inl coin) before result reached
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
                  exact projected_counter setup checks wire route representation created credential
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
                RegistrationNativeParsedCounterSource.isAccept] using
                projected_counter setup checks wire route representation created credential (.inr (.accept packet)) RegistrationNativeRawAdapter.resultOption before result reached
      | bundle owner =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_map, simulateQ_spec_query, StateT.run_map] at reached
          exact projected_counter setup checks wire route representation created credential (.inr (.bundle owner)) RegistrationNativeRawAdapter.resultOption before result reached
      | build session application =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_map, simulateQ_spec_query, StateT.run_map] at reached
          exact projected_counter setup checks wire route representation created credential (.inr (.build session (RegistrationNativeRawAdapter.application application))) RegistrationNativeRawAdapter.responseOption before result reached
      | finish owner raw =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_map, simulateQ_spec_query, StateT.run_map] at reached
          exact projected_counter setup checks wire route representation created credential (.inr (.finish owner (RegistrationNativeWire.readResponse wire raw))) RegistrationNativeRawAdapter.resultOption before result reached
      | hmac key message =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
          exact RegistrationNativeParsedCounterSource.typed_counter setup checks wire route representation created credential (.inr (.hmac key message)) before result reached
      | hash bytes =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
          exact RegistrationNativeParsedCounterSource.typed_counter setup checks wire route representation created credential (.inr (.hash bytes)) before result reached
      | serverSend keyId plaintext =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
          exact RegistrationNativeParsedCounterSource.typed_counter setup checks wire route representation created credential (.inr (.serverSend keyId plaintext)) before result reached
      | serverRaw raw =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
          exact RegistrationNativeParsedCounterSource.typed_counter setup checks wire route representation created credential (.inr (.serverRaw raw)) before result reached
      | beaconSend owner plaintext =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
          exact RegistrationNativeParsedCounterSource.typed_counter setup checks wire route representation created credential (.inr (.beaconSend owner plaintext)) before result reached
      | beaconRaw owner raw =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
          exact RegistrationNativeParsedCounterSource.typed_counter setup checks wire route representation created credential (.inr (.beaconRaw owner raw)) before result reached

/-- The increment depends only on the original native entry's raw query, never its projected success reply. -/
theorem entry_increment (wire : Wire) (query : Spec.Domain) (reply : Spec.Range query) :
    increment wire query = (RegistrationNativeEvents.parsedAccept wire ⟨.inl query, reply⟩).toNat := by
  cases query with
  | inl coin => rfl
  | inr command => cases command <;> rfl

end BeaconcryptCore.Computational.RegistrationNativeParsedCounterRaw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedCounterRaw.raw_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedCounterRaw.raw_counter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedCounterRaw.entry_increment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedCounterRaw.entry_increment
