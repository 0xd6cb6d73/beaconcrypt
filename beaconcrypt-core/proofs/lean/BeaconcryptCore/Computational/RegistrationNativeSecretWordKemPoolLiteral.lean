-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemPool

/-! The actual prechallenge live pool enters the word language literally, with every generated pair and prior reply retained. This conversion contains no selected candidate bytes and supports the delayed first-getter cut. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordKemPoolLiteral
open PqxdhKemIndCca (MlKemSharedSecret)
open PqxdhLiveKemBirth (Query)
open RegistrationNativeSecretWord (Word)
open RegistrationNativeSecretWordKemInterface (WordPoolSpec)
open RegistrationNativeSecretWordKemPool (Pool eval observation)
variable {KemSK : Type}

def reply : (query : Query) → (PqxdhLiveKemBirth.PoolSpec KemSK).Range query → (WordPoolSpec KemSK).Range query
  | .create, value => value
  | .decapsulate _ _, value => value.map Word.literal
  | .reveal _, value => value

def observation (value : PqxdhLiveKemBirth.Observation KemSK) : RegistrationNativeSecretWordKemPool.Observation KemSK :=
  ⟨value.1, reply value.1 value.2⟩

def literal (before : PqxdhLiveKemBirth.Pool KemSK) : Pool KemSK := ⟨before.keys, before.transcript.map observation⟩

/-- Every real earlier reply, including optional decapsulation failure, remains literally the same native observation. -/
theorem eval_observation (candidate : MlKemSharedSecret) (value : PqxdhLiveKemBirth.Observation KemSK) :
    RegistrationNativeSecretWordKemPool.observation candidate (observation value) = value := by
  rcases value with ⟨query, answer⟩
  cases query with
  | create => rfl
  | reveal handle => rfl
  | decapsulate handle ciphertext => cases answer <;> rfl

/-- Literal conversion restores the entire actual prechallenge key pool and reply transcript for every mathematical candidate. -/
theorem eval_literal (candidate : MlKemSharedSecret) (before : PqxdhLiveKemBirth.Pool KemSK) : eval candidate (literal before) = before := by
  have same : RegistrationNativeSecretWordKemPool.observation candidate ∘ observation = (id : PqxdhLiveKemBirth.Observation KemSK → _) :=
    funext (eval_observation candidate)
  cases before
  simp only [literal, eval, List.map_map, same, List.map_id]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordKemPoolLiteral
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemPoolLiteral.eval_observation' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemPoolLiteral.eval_observation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemPoolLiteral.eval_literal' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemPoolLiteral.eval_literal
