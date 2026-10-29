-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemInterface
import BeaconcryptCore.Computational.RegistrationNativeKemSwitchReserved

/-! The private symbolic KEM pool retains the actual generated key pairs and complete typed reply transcript. Only successful shared-secret replies contain an opaque word. Evaluation restores the literal original pool, including creation indices and failed or explicit reveal replies. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordKemPool
open PqxdhKemIndCca (MlKem768PublicKey MlKemSharedSecret)
open PqxdhLiveKemBirth (Query)
open RegistrationNativeSecretWord (Word)
open RegistrationNativeSecretWordKemInterface (WordPoolSpec)
variable {KemSK : Type}

abbrev Observation (KemSK : Type) := (query : Query) × (WordPoolSpec KemSK).Range query

structure Pool (KemSK : Type) where
  keys : List (MlKem768PublicKey × KemSK)
  transcript : List (Observation KemSK)

def empty : Pool KemSK := ⟨[], []⟩

def reply (candidate : MlKemSharedSecret) : (query : Query) → (WordPoolSpec KemSK).Range query → (PqxdhLiveKemBirth.PoolSpec KemSK).Range query
  | .create, value => value
  | .decapsulate _ _, value => value.map (Word.eval candidate)
  | .reveal _, value => value

def observation (candidate : MlKemSharedSecret) (value : Observation KemSK) : PqxdhLiveKemBirth.Observation KemSK :=
  ⟨value.1, reply candidate value.1 value.2⟩

def eval (candidate : MlKemSharedSecret) (before : Pool KemSK) : PqxdhLiveKemBirth.Pool KemSK :=
  ⟨before.keys, before.transcript.map (observation candidate)⟩

def record (query : Query) (value : (WordPoolSpec KemSK).Range query) (before : Pool KemSK) : Pool KemSK :=
  { before with transcript := before.transcript ++ [⟨query, value⟩] }

def created (before : Pool KemSK) (pair : MlKem768PublicKey × KemSK) : (Nat × MlKem768PublicKey) × Pool KemSK :=
  let value := (before.keys.length, pair.1)
  (value, record .create value { before with keys := before.keys ++ [pair] })

/-- Symbolic pool evaluation preserves every generated key pair literally. -/
theorem eval_keys (candidate : MlKemSharedSecret) (before : Pool KemSK) : (eval candidate before).keys = before.keys := rfl

/-- Recording a symbolic reply restores the exact original typed transcript entry. -/
theorem eval_record (candidate : MlKemSharedSecret) (query : Query) (value : (WordPoolSpec KemSK).Range query) (before : Pool KemSK) :
    eval candidate (record query value before) = PqxdhLiveKemBirth.record query (reply candidate query value) (eval candidate before) := by
  simp only [eval, record, PqxdhLiveKemBirth.record, List.map_append, List.map_singleton, observation]

/-- Actual creation indices, public-key aliases and the complete old transcript survive evaluation. -/
theorem eval_created (candidate : MlKemSharedSecret) (before : Pool KemSK) (pair : MlKem768PublicKey × KemSK) :
    Prod.map id (eval candidate) (created before pair) = PqxdhLiveKemBirth.created (eval candidate before) pair := by
  simp only [created, PqxdhLiveKemBirth.created, Prod.map_def, id_eq]
  rw [eval_record]
  rfl

/-- Empty symbolic initialization has exactly the native empty pool. -/
theorem eval_empty (candidate : MlKemSharedSecret) : eval (KemSK := KemSK) candidate empty = PqxdhLiveKemBirth.empty := rfl

end BeaconcryptCore.Computational.RegistrationNativeSecretWordKemPool
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemPool.eval_keys' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemPool.eval_keys
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemPool.eval_record' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemPool.eval_record
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemPool.eval_created' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemPool.eval_created
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemPool.eval_empty' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemPool.eval_empty
