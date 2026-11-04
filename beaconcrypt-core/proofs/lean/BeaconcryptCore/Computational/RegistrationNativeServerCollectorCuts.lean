-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeServerAgreementInputReceipt

/-! Every successful actual Server collector exposes its reached ephemeral generation, encapsulation, conversions and four ordered DH callbacks with their same-run states. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerCollectorCuts
open RegistrationAgreementExecutor
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhRootTableInitialization (rootArray)
variable {S : Type}

/-- The collector's source success supplies every actual primitive cut; no DH or encapsulation value is recomputed from a later state. -/
theorem collect (implementation : QueryImpl Spec (StateT S ProbComp))
    (verified : PqxdhServerRootPreparation.Verified registration.InitPacket)
    (input : PqxdhServerRootPreparation.Inputs registration.InitPacket Unit Word32) (before after : S)
    (supported : (some input, after) ∈ support ((simulateQ implementation
      (simulateQ RegistrationAgreementRoot.callbacks (PqxdhServerRootPreparation.collectVerified verified))).run before)) :
    ∃ generatedState kemState convertedState identityState firstState secondState thirdState,
      (.Some input.ephemeral.publicKey, generatedState) ∈ support ((implementation (.generate .ServerEphemeral)).run before) ∧
      (.Some (input.ciphertext, input.kem), kemState) ∈ support
        ((implementation (.encapsulate (.Some (RegistrationAgreementRoot.pqArray verified.keys.pqKey)))).run generatedState) ∧
      (.Some input.convertedIdentity, convertedState) ∈ support
        ((implementation (.convertPublic (rootArray verified.identity))).run kemState) ∧
      (true, identityState) ∈ support ((implementation (.convertSecret .LocalIdentity)).run convertedState) ∧
      (.Some input.first, firstState) ∈ support ((implementation (.dh ⟨.LocalIdentity, rootArray verified.keys.prekey⟩)).run identityState) ∧
      (.Some input.second, secondState) ∈ support ((implementation (.dh ⟨.ServerEphemeral, input.convertedIdentity⟩)).run firstState) ∧
      (.Some input.third, thirdState) ∈ support ((implementation (.dh ⟨.ServerEphemeral, rootArray verified.keys.prekey⟩)).run secondState) ∧
      (.Some input.fourth, after) ∈ support ((implementation (.dh ⟨.ServerEphemeral, rootArray verified.keys.oneTime⟩)).run thirdState) := by
  simp only [PqxdhServerRootPreparation.collectVerified, OptionT.run_bind, OptionT.run_monadLift, OptionT.run_mk,
    Option.elimM, bind_map_left, simulateQ_bind, simulateQ_spec_query,
    RegistrationAgreementRoot.callbacks, pure_bind, Bool.not_true, Bool.false_eq_true, ite_false, Option.elim_some,
    StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨generatedReply, generatedState⟩, generatedCalled, continued⟩ := supported
  cases generatedReply with
  | none => simp [RegistrationAgreementRoot.option] at continued
  | some ephemeral =>
    simp only [OptionT.run_bind, OptionT.run_monadLift, OptionT.run_mk, Option.elimM, RegistrationAgreementRoot.option, Option.map_some, Option.elim_some, simulateQ_bind, simulateQ_spec_query,
      RegistrationAgreementRoot.callbacks, pure_bind, Bool.not_true, Bool.false_eq_true, ite_false,
      bind_map_left, StateT.run_bind, mem_support_bind_iff] at continued
    obtain ⟨⟨kemReply, kemState⟩, kemCalled, continued⟩ := continued
    cases kemReply with
    | none => simp at continued
    | some encapsulated =>
      rcases encapsulated with ⟨ciphertext, kem⟩
      simp only [RegistrationAgreementRoot.option, Option.elim_some, simulateQ_bind, simulateQ_spec_query,
        RegistrationAgreementRoot.callbacks, bind_map_left, StateT.run_bind, mem_support_bind_iff] at continued
      obtain ⟨⟨convertedReply, convertedState⟩, convertedCalled, continued⟩ := continued
      cases convertedReply with
      | none => simp at continued
      | some converted =>
        simp only [Option.elim_some, simulateQ_bind, simulateQ_spec_query,
          RegistrationAgreementRoot.callbacks, StateT.run_bind, mem_support_bind_iff] at continued
        obtain ⟨⟨identityReply, identityState⟩, identityCalled, continued⟩ := continued
        cases identityReply with
        | false => simp at continued
        | true =>
          simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, Option.elimM, Bool.not_true, Bool.false_eq_true, ite_false, simulateQ_bind, simulateQ_spec_query,
            RegistrationAgreementRoot.callbacks, bind_map_left, StateT.run_bind, mem_support_bind_iff] at continued
          obtain ⟨⟨firstReply, firstState⟩, firstCalled, continued⟩ := continued
          cases firstReply with
          | none => simp [RegistrationAgreementRoot.option] at continued
          | some first =>
            simp only [RegistrationAgreementRoot.option, Option.elim_some, simulateQ_bind, simulateQ_spec_query,
              RegistrationAgreementRoot.callbacks, bind_map_left, StateT.run_bind, mem_support_bind_iff] at continued
            obtain ⟨⟨secondReply, secondState⟩, secondCalled, continued⟩ := continued
            cases secondReply with
            | none => simp at continued
            | some second =>
              simp only [RegistrationAgreementRoot.option, Option.elim_some, simulateQ_bind, simulateQ_spec_query,
                RegistrationAgreementRoot.callbacks, bind_map_left, StateT.run_bind, mem_support_bind_iff] at continued
              obtain ⟨⟨thirdReply, thirdState⟩, thirdCalled, continued⟩ := continued
              cases thirdReply with
              | none => simp at continued
              | some third =>
                simp only [RegistrationAgreementRoot.option, Option.elim_some, simulateQ_bind, simulateQ_spec_query,
                  RegistrationAgreementRoot.callbacks, bind_map_left, StateT.run_bind, mem_support_bind_iff] at continued
                obtain ⟨⟨fourthReply, fourthState⟩, fourthCalled, continued⟩ := continued
                cases fourthReply with
                | none => simp at continued
                | some fourth =>
                  simp only [Option.elim_some, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
                    Prod.mk.injEq, Option.some.injEq] at continued
                  rcases continued with ⟨inputEq, stateEq⟩
                  subst input
                  subst after
                  exact ⟨generatedState, kemState, convertedState, identityState, firstState, secondState, thirdState,
                    generatedCalled, kemCalled, convertedCalled, identityCalled, firstCalled, secondCalled, thirdCalled, fourthCalled⟩

end BeaconcryptCore.Computational.RegistrationNativeServerCollectorCuts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerCollectorCuts.collect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerCollectorCuts.collect
