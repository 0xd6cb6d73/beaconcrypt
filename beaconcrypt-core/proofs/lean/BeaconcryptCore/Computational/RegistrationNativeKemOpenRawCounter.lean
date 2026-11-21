-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenTypedCounter

/-! Original raw accepts advance the actual open provider counter exactly when the native decoder returns a packet. Authentication failures count; malformed raw calls do not. All original source states and private KEM phases remain in the execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenRawCounter
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeKemOpenProvider (State implementation counter)
variable {ι KemSK : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

def increment (wire : Wire) : RegistrationNativeInterface.Spec.Domain → Nat
  | .inr (.accept raw) => (RegistrationNativeWire.readInit wire raw).isSome.toNat
  | _ => 0

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
  (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (real : Bool) (parsed : Nat)

local notation "provider" => implementation (n := n) setup checks wire route representation created credential selected pairs publicKey real

noncomputable def native : QueryImpl RegistrationNativeInterface.Spec (OptionT (StateT (State n mlSource KemSK) ProbComp)) :=
  (provider ∘ₛ RegistrationNativeKemParsedRouting.handler setup checks wire parsed) ∘ₛ RegistrationNativeRawAdapter.adapter wire

private theorem mapped_counter (query : TypedSpec.Domain) {Value : Type} (project : TypedSpec.Range query → Value)
    (before after : State n mlSource KemSK) (value : Value)
    (supported : (some value, after) ∈ support
      (((simulateQ provider (simulateQ (RegistrationNativeKemParsedRouting.handler setup checks wire parsed)
        (project <$> (TypedSpec.query query : OracleComp TypedSpec _)))).run).run before)) :
    counter after = counter before + RegistrationNativeKemOpenTypedCounter.increment query := by
  simp only [simulateQ_map, simulateQ_spec_query, OptionT.run_map, StateT.run_map, support_map] at supported
  obtain ⟨⟨reply, reached⟩, called, returned⟩ := supported
  cases reply with
  | none =>
      have same := congrArg Prod.fst returned
      simp only [Option.map_none, reduceCtorEq] at same
  | some reply =>
      have same := congrArg Prod.snd returned
      change reached = after at same
      subst after
      exact RegistrationNativeKemOpenTypedCounter.parsed_counter setup checks wire route representation created credential
        selected pairs publicKey real parsed query before reached reply called

/-- The original raw source counts decoded attempts in place, independently of native acceptance, session handles and KEM candidates. -/
theorem raw_counter (query : RegistrationNativeInterface.Spec.Domain)
    (before after : State n mlSource KemSK) (value : RegistrationNativeInterface.Spec.Range query)
    (supported : (some value, after) ∈ support
      (((native setup checks wire route representation created credential selected pairs publicKey real parsed query).run).run before)) :
    counter after = counter before + increment wire query := by
  cases query with
  | inl coin =>
      simp only [native, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at supported
      exact RegistrationNativeKemOpenTypedCounter.parsed_counter setup checks wire route representation created credential
        selected pairs publicKey real parsed (.inl coin) before after value supported
  | inr command =>
      cases command with
      | create edPin mlPin keyId =>
          cases ed : PqxdhDeploymentInterface.parsePin edPin with
          | none =>
              simp only [native, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter, ed,
                simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq] at supported
              rw [supported.2]
              rfl
          | some edValue =>
              cases ml : RegistrationNativeWire.parseMldsaPin mlPin with
              | none =>
                  simp only [native, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter, ed, ml,
                    simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq] at supported
                  rw [supported.2]
                  rfl
              | some mlValue =>
                  simp only [native, QueryImpl.apply_compose, QueryImpl.simulateQ_compose, RegistrationNativeRawAdapter.adapter, ed, ml] at supported
                  exact mapped_counter setup checks wire route representation created credential selected pairs publicKey real parsed
                    (.inr (.create edValue mlValue keyId)) RegistrationNativeRawAdapter.resultOption before after value supported
      | accept raw =>
          cases read : RegistrationNativeWire.readInit wire raw with
          | none =>
              simp only [native, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter, read,
                simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq] at supported
              rw [supported.2]
              simp only [increment, read, Option.isSome_none, Bool.toNat_false, Nat.add_zero]
          | some packet =>
              simp only [native, QueryImpl.apply_compose, QueryImpl.simulateQ_compose, RegistrationNativeRawAdapter.adapter, read] at supported
              simpa only [increment, read, Option.isSome_some, Bool.toNat_true,
                RegistrationNativeKemOpenTypedCounter.increment] using
                mapped_counter setup checks wire route representation created credential selected pairs publicKey real parsed
                  (.inr (.accept packet)) RegistrationNativeRawAdapter.resultOption before after value supported
      | bundle owner =>
          simp only [native, QueryImpl.apply_compose, QueryImpl.simulateQ_compose, RegistrationNativeRawAdapter.adapter] at supported
          exact mapped_counter setup checks wire route representation created credential selected pairs publicKey real parsed
            (.inr (.bundle owner)) RegistrationNativeRawAdapter.resultOption before after value supported
      | build session application =>
          simp only [native, QueryImpl.apply_compose, QueryImpl.simulateQ_compose, RegistrationNativeRawAdapter.adapter] at supported
          exact mapped_counter setup checks wire route representation created credential selected pairs publicKey real parsed
            (.inr (.build session (RegistrationNativeRawAdapter.application application))) RegistrationNativeRawAdapter.responseOption before after value supported
      | finish owner raw =>
          simp only [native, QueryImpl.apply_compose, QueryImpl.simulateQ_compose, RegistrationNativeRawAdapter.adapter] at supported
          exact mapped_counter setup checks wire route representation created credential selected pairs publicKey real parsed
            (.inr (.finish owner (RegistrationNativeWire.readResponse wire raw))) RegistrationNativeRawAdapter.resultOption before after value supported
      | hmac key message =>
          simp only [native, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at supported
          exact RegistrationNativeKemOpenTypedCounter.parsed_counter setup checks wire route representation created credential
            selected pairs publicKey real parsed (.inr (.hmac key message)) before after value supported
      | hash bytes =>
          simp only [native, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at supported
          exact RegistrationNativeKemOpenTypedCounter.parsed_counter setup checks wire route representation created credential
            selected pairs publicKey real parsed (.inr (.hash bytes)) before after value supported
      | serverSend keyId plaintext =>
          simp only [native, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at supported
          exact RegistrationNativeKemOpenTypedCounter.parsed_counter setup checks wire route representation created credential
            selected pairs publicKey real parsed (.inr (.serverSend keyId plaintext)) before after value supported
      | serverRaw raw =>
          simp only [native, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at supported
          exact RegistrationNativeKemOpenTypedCounter.parsed_counter setup checks wire route representation created credential
            selected pairs publicKey real parsed (.inr (.serverRaw raw)) before after value supported
      | beaconSend owner plaintext =>
          simp only [native, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at supported
          exact RegistrationNativeKemOpenTypedCounter.parsed_counter setup checks wire route representation created credential
            selected pairs publicKey real parsed (.inr (.beaconSend owner plaintext)) before after value supported
      | beaconRaw owner raw =>
          simp only [native, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at supported
          exact RegistrationNativeKemOpenTypedCounter.parsed_counter setup checks wire route representation created credential
            selected pairs publicKey real parsed (.inr (.beaconRaw owner raw)) before after value supported

/-- The raw parsed-counter increment is exactly the indicator of its original native transcript entry. -/
theorem entry_increment (query : RegistrationNativeInterface.Spec.Domain) (reply : RegistrationNativeInterface.Spec.Range query) :
    increment wire query = (RegistrationNativeEvents.parsedAccept wire ⟨.inl query, reply⟩).toNat := by
  cases query with
  | inl coin => rfl
  | inr command => cases command <;> rfl

end BeaconcryptCore.Computational.RegistrationNativeKemOpenRawCounter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenRawCounter.raw_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenRawCounter.raw_counter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenRawCounter.entry_increment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenRawCounter.entry_increment
