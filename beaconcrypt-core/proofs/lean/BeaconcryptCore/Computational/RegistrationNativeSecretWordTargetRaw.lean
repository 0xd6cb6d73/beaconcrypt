-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetSource
import BeaconcryptCore.Computational.RegistrationNativeParsedTarget

/-! Bounded raw decoding connects the actual symbolic frontend and concrete combined interpreter to its parsed-call counter. Arbitrary protected-key replies are retained. Malformed packets do not enter the typed frontend; decoded failures consume exactly their original ordinal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRaw
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeInterface (Spec)
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {mlSource : RegistrationNativeMldsa.Source}
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
local notation "typed" => RegistrationNativeSecretWordTargetSource.typed (n := n) (source := mlSource)
  setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
attribute [local irreducible] RegistrationNativeSecretWordTargetSource.typed

def increment (wire : Wire) : Spec.Domain → Nat
  | .inr (.accept raw) => (RegistrationNativeWire.readInit wire raw).isSome.toNat
  | _ => 0

private theorem projected_counter (query : TypedSpec.Domain) {Value : Type} (project : TypedSpec.Range query → Value)
    (before : State n KemSK mlSource) (result : Value × State n KemSK mlSource)
    (reached : result ∈ support (Prod.map project id <$>
      (typed query).run before)) :
    result.2.1.parsedAccepts = before.1.parsedAccepts + (RegistrationNativeSecretWordTargetCounter.isAccept query).toNat := by
  rw [support_map] at reached
  obtain ⟨inner, supported, rfl⟩ := reached
  exact RegistrationNativeSecretWordTargetSource.typed_counter setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey query before inner supported

/-- The original raw command increments the private counter precisely when its actual native Init decoder succeeds. -/
theorem raw_counter (query : Spec.Domain) (before : State n KemSK mlSource)
    (result : Spec.Range query × State n KemSK mlSource)
    (reached : result ∈ support ((RegistrationNativeRawAdapter.handler wire
      (typed) query).run before)) :
    result.2.1.parsedAccepts = before.1.parsedAccepts + increment wire query := by
  cases query with
  | inl coin =>
      simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
        RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
      exact RegistrationNativeSecretWordTargetSource.typed_counter setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey (.inl coin) before result reached
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
                  exact projected_counter setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
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
                projected_counter setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey (.inr (.accept packet)) RegistrationNativeRawAdapter.resultOption before result reached
      | bundle owner =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_map, simulateQ_spec_query, StateT.run_map] at reached
          exact projected_counter setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey (.inr (.bundle owner)) RegistrationNativeRawAdapter.resultOption before result reached
      | build session application =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_map, simulateQ_spec_query, StateT.run_map] at reached
          exact projected_counter setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey (.inr (.build session (RegistrationNativeRawAdapter.application application))) RegistrationNativeRawAdapter.responseOption before result reached
      | finish owner raw =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_map, simulateQ_spec_query, StateT.run_map] at reached
          exact projected_counter setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey (.inr (.finish owner (RegistrationNativeWire.readResponse wire raw))) RegistrationNativeRawAdapter.resultOption before result reached
      | hmac key message =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
          exact RegistrationNativeSecretWordTargetSource.typed_counter setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey (.inr (.hmac key message)) before result reached
      | hash bytes =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
          exact RegistrationNativeSecretWordTargetSource.typed_counter setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey (.inr (.hash bytes)) before result reached
      | serverSend keyId plaintext =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
          exact RegistrationNativeSecretWordTargetSource.typed_counter setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey (.inr (.serverSend keyId plaintext)) before result reached
      | serverRaw raw =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
          exact RegistrationNativeSecretWordTargetSource.typed_counter setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey (.inr (.serverRaw raw)) before result reached
      | beaconSend owner plaintext =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
          exact RegistrationNativeSecretWordTargetSource.typed_counter setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey (.inr (.beaconSend owner plaintext)) before result reached
      | beaconRaw owner raw =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
          exact RegistrationNativeSecretWordTargetSource.typed_counter setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey (.inr (.beaconRaw owner raw)) before result reached

/-- The increment depends only on the original native entry's raw query, never its projected success reply. -/
theorem entry_increment (wire : Wire) (query : Spec.Domain) (reply : Spec.Range query) :
    increment wire query = (RegistrationNativeEvents.parsedAccept wire ⟨.inl query, reply⟩).toNat := by
  cases query with
  | inl coin => rfl
  | inr command => cases command <;> rfl

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRaw
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRaw.raw_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRaw.raw_counter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRaw.entry_increment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRaw.entry_increment
