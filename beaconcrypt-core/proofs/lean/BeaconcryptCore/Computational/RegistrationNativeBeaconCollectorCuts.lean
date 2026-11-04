-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconAgreementInputReceipt

/-! A successful actual Beacon collector exposes all seven reached primitive cuts in order. Each state is retained, so later operand and recipient-correctness proofs use the original source callback rather than a recomputed value. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconCollectorCuts
open RegistrationAgreementExecutor
open PqxdhBeaconPhase2Preparation (Word32)
variable {S : Type}

/-- Every supported source collection retains actual conversion, decapsulation and four ordered DH callbacks with their complete same-run states. -/
theorem collect (implementation : QueryImpl Spec (StateT S ProbComp))
    (authenticated : registration.AuthenticatedResponse)
    (input : PqxdhBeaconPhase2Preparation.Inputs registration.AuthenticatedResponse) (before after : S)
    (supported : (some input, after) ∈ support ((simulateQ implementation
      (simulateQ (RegistrationBeaconAgreementRoot.callbacks authenticated)
        (PqxdhBeaconPhase2Preparation.collect () false true () []))).run before)) :
    ∃ (converted : Word32) (convertedState identityState kemState firstState secondState thirdState : S),
      (.Some converted, convertedState) ∈ support ((implementation (.convertPublic authenticated.packet.public.identity_key)).run before) ∧
      (true, identityState) ∈ support ((implementation (.convertSecret .LocalIdentity)).run convertedState) ∧
      (.Some input.finishInputs.shared_secrets.kem_shared_secret, kemState) ∈ support
        ((implementation (.decapsulate (.Some authenticated.packet.public.kem_cipher_text))).run identityState) ∧
      (.Some input.finishInputs.shared_secrets.dh1, firstState) ∈ support
        ((implementation (.dh ⟨.BeaconPrekey, converted⟩)).run kemState) ∧
      (.Some input.finishInputs.shared_secrets.dh2, secondState) ∈ support
        ((implementation (.dh ⟨.LocalIdentity, authenticated.packet.public.ephemeral_key⟩)).run firstState) ∧
      (.Some input.finishInputs.shared_secrets.dh3, thirdState) ∈ support
        ((implementation (.dh ⟨.BeaconPrekey, authenticated.packet.public.ephemeral_key⟩)).run secondState) ∧
      (.Some input.finishInputs.shared_secrets.dh4, after) ∈ support
        ((implementation (.dh ⟨.BeaconOneTime, authenticated.packet.public.ephemeral_key⟩)).run thirdState) := by
  simp only [PqxdhBeaconPhase2Preparation.collect, OptionT.run_bind, OptionT.run_monadLift, OptionT.run_mk, OptionT.run_pure,
    Option.elimM, bind_map_left, simulateQ_bind, simulateQ_spec_query,
    RegistrationBeaconAgreementRoot.callbacks, pure_bind, Option.elim_some,
    StateT.run_bind, mem_support_bind_iff] at supported

  obtain ⟨⟨convertedReply, convertedState⟩, convertedCalled, continued⟩ := supported
  cases convertedReply with
  | none => simp [RegistrationAgreementRoot.option] at continued
  | some converted =>
    simp only [RegistrationAgreementRoot.option, Option.elim_some, simulateQ_bind, simulateQ_spec_query,
      RegistrationBeaconAgreementRoot.callbacks, bind_map_left, StateT.run_bind, mem_support_bind_iff] at continued
    obtain ⟨⟨identityReply, identityState⟩, identityCalled, continued⟩ := continued
    cases identityReply with
    | false => simp at continued
    | true =>
      simp only [ite_true, Option.elim_some, simulateQ_bind, simulateQ_spec_query,
        RegistrationBeaconAgreementRoot.callbacks, bind_map_left, StateT.run_bind, mem_support_bind_iff] at continued
      obtain ⟨⟨kemReply, kemState⟩, kemCalled, continued⟩ := continued
      cases kemReply with
      | none => simp [RegistrationAgreementRoot.option] at continued
      | some kem =>
        simp only [RegistrationAgreementRoot.option, Option.elim_some, simulateQ_bind, simulateQ_spec_query,
          RegistrationBeaconAgreementRoot.callbacks,
          bind_map_left, StateT.run_bind, mem_support_bind_iff] at continued
        obtain ⟨⟨firstReply, firstState⟩, firstCalled, continued⟩ := continued
        cases firstReply with
        | none => simp at continued
        | some first =>
          simp only [RegistrationAgreementRoot.option, Option.elim_some, simulateQ_bind, simulateQ_spec_query,
            RegistrationBeaconAgreementRoot.callbacks, bind_map_left, StateT.run_bind, mem_support_bind_iff] at continued
          obtain ⟨⟨secondReply, secondState⟩, secondCalled, continued⟩ := continued
          cases secondReply with
          | none => simp at continued
          | some second =>
            simp only [RegistrationAgreementRoot.option, Option.elim_some, simulateQ_bind, simulateQ_spec_query,
              RegistrationBeaconAgreementRoot.callbacks, bind_map_left, StateT.run_bind, mem_support_bind_iff] at continued
            obtain ⟨⟨thirdReply, thirdState⟩, thirdCalled, continued⟩ := continued
            cases thirdReply with
            | none => simp at continued
            | some third =>
              simp only [RegistrationAgreementRoot.option, Option.elim_some, simulateQ_bind, simulateQ_spec_query,
                RegistrationBeaconAgreementRoot.callbacks, bind_map_left, StateT.run_bind, mem_support_bind_iff] at continued
              obtain ⟨⟨fourthReply, fourthState⟩, fourthCalled, continued⟩ := continued
              cases fourthReply with
              | none => simp at continued
              | some fourth =>
                simp only [Option.elim_some, simulateQ_bind, simulateQ_spec_query,
                  RegistrationBeaconAgreementRoot.callbacks, pure_bind, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
                  Prod.mk.injEq, Option.some.injEq] at continued
                rcases continued with ⟨inputEq, stateEq⟩
                subst input
                subst after
                exact ⟨converted, convertedState, identityState, kemState, firstState, secondState, thirdState,
                  convertedCalled, identityCalled, kemCalled, firstCalled, secondCalled, thirdCalled, fourthCalled⟩

end BeaconcryptCore.Computational.RegistrationNativeBeaconCollectorCuts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCollectorCuts.collect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCollectorCuts.collect
