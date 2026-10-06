-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemEncapsulation
import BeaconcryptCore.Computational.PqxdhRegistrationJointNativeKemOrigin

/-! Actual attached verification before the exposed encapsulation is pure and retains its exact original raw candidate. Neither private identity state nor a challenger reply is used by this prefix. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointCutVerification
open PqxdhServerAuthExperiment PqxdhJointIdentity
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

noncomputable def handler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (identityIndex : Nat) (raw : Pqxdh.Bytes) :=
  PqxdhRegistrationJointKemEncapsulation.prefixImpl setup codec checks raw ∘ₛ
    PqxdhRegistrationJointServerPrefix.compiler identityIndex

/-- Verification in the literal exposed collector is the original public source verification and changes no consumed entry, pool, signing log or reveal state. The equality holds before any private interpreter is chosen. Its result is the attached source interface `RawSignatures.verified`; the detached `acceptPhase1Candidate setup.joint.verify` form is reached only through `RawSignatures.verified_detached` and its existing `shortRejects` premise, which this theorem does not take. -/
theorem verified_pure (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes) (consumed : List Pqxdh.Bytes) :
    (simulateQ (handler setup codec checks identityIndex raw)
      (PqxdhServerRootPreparation.verifyInput raw)).run consumed =
      pure (PqxdhRegistrationJointRawSignatures.verified setup codec checks raw, consumed) := by
  have state_pure {X : Type} (value : X) :
      (fun state : List Pqxdh.Bytes => (pure (value, state) : OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) _)) =
        (pure value : StateT (List Pqxdh.Bytes) (OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK)) X) := rfl
  simp only [PqxdhServerRootPreparation.verifyInput, handler, simulateQ_bind, simulateQ_spec_query,
    QueryImpl.apply_compose, PqxdhRegistrationJointServerPrefix.compiler,
    PqxdhRegistrationJointKemEncapsulation.prefixImpl, serverAux,
    PqxdhLiveKemBirth.coins, simulateQ_pure, StateT.run_pure,
    PqxdhRegistrationJointRawSignatures.verified, StateT.run_bind]
  dsimp only [StateT.run]
  simp only [pure_bind]
  repeat' (first
    | rfl
    | (split <;> try simp_all only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
        QueryImpl.apply_compose, PqxdhRegistrationJointServerPrefix.compiler,
        PqxdhRegistrationJointKemEncapsulation.prefixImpl, serverAux, PqxdhLiveKemBirth.coins,
        StateT.run_pure, pure_bind, Option.bind_eq_bind, Option.bind]; try dsimp [StateT.run]))

end BeaconcryptCore.Computational.PqxdhRegistrationJointCutVerification

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointCutVerification.verified_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointCutVerification.verified_pure
