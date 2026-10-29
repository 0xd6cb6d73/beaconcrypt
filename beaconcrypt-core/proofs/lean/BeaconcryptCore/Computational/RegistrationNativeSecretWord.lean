-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3CellEager
import BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule
import BeaconcryptCore.Computational.RegistrationNativeRootAliases
import BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling

/-! A candidate-free key language retains either a literal32-byte KEM word or one opaque atom. Evaluating the atom at a uniform word can merge two distinct symbolic keys only when a literal equals that word. The head has its exact160-byte length, so arbitrary concatenation ambiguities cannot create other merges. No concrete frontend is identified with this language in this component. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWord
open PqxdhKemIndCca (MlKemSharedSecret)
open PqxdhServerAuthKeySchedule (Output)

inductive Word where
  | literal (value : MlKemSharedSecret)
  | atom
  deriving DecidableEq

def Word.eval (candidate : MlKemSharedSecret) : Word → MlKemSharedSecret
  | .literal value => value
  | .atom => candidate

structure Key where
  head : List.Vector UInt8 160
  word : Word
  deriving DecidableEq

def eval (candidate : MlKemSharedSecret) (key : Key) : Pqxdh.Bytes :=
  key.head.toList ++ (key.word.eval candidate).toList

def normalize (candidate : MlKemSharedSecret) (key : Key) : Key :=
  { key with word := if key.word = .literal candidate then .atom else key.word }

def decode (candidate : MlKemSharedSecret) (bytes : Pqxdh.Bytes) : Option Key :=
  if width : bytes.length = 192 then
    let suffix : MlKemSharedSecret := ⟨bytes.drop 160, by simp [width]⟩
    some ⟨⟨bytes.take 160, by simp [width]⟩, if suffix = candidate then .atom else .literal suffix⟩
  else none

/-- Every evaluated symbolic key has the literal native192-byte width. -/
theorem eval_length (candidate : MlKemSharedSecret) (key : Key) : (eval candidate key).length = 192 := by
  simp [eval]

/-- Evaluation retains the entire160-byte head, without any DH or public-key injectivity assumption. -/
theorem eval_prefix (candidate : MlKemSharedSecret) (key : Key) :
    (eval candidate key).take 160 = key.head.toList := by
  simp [eval]

/-- Evaluation retains the actual final32-byte word. -/
theorem eval_suffix (candidate : MlKemSharedSecret) (key : Key) :
    (eval candidate key).drop 160 = (key.word.eval candidate).toList := by
  simp [eval]

/-- Replacing the candidate-equal literal by the atom preserves the full native bytes. -/
theorem eval_normalize (candidate : MlKemSharedSecret) (key : Key) :
    eval candidate (normalize candidate key) = eval candidate key := by
  rcases key with ⟨head, word⟩
  cases word with
  | literal value => by_cases same : value = candidate <;> simp [normalize, eval, Word.eval, same]
  | atom => simp [normalize, eval, Word.eval]

/-- Parsing an evaluated key returns precisely its canonical symbolic alias. -/
theorem decode_eval (candidate : MlKemSharedSecret) (key : Key) :
    decode candidate (eval candidate key) = some (normalize candidate key) := by
  unfold decode
  rw [dite_eq_left (eval_length candidate key)]
  have head : (⟨(eval candidate key).take 160, by simp [eval_length]⟩ : List.Vector UInt8 160) = key.head :=
    List.Vector.toList_injective (eval_prefix candidate key)
  have suffix : (⟨(eval candidate key).drop 160, by simp [eval_length]⟩ : MlKemSharedSecret) = key.word.eval candidate :=
    List.Vector.toList_injective (eval_suffix candidate key)
  rw [head, suffix]
  rcases key with ⟨head, word⟩
  cases word with
  | literal value => by_cases same : value = candidate <;> simp [normalize, Word.eval, same]
  | atom => simp [normalize, Word.eval]

/-- Every successful192-byte decode reconstructs the same bytes, including malformed-head values. -/
theorem decode_some (candidate : MlKemSharedSecret) (bytes : Pqxdh.Bytes) (key : Key)
    (parsed : decode candidate bytes = some key) : eval candidate key = bytes := by
  unfold decode at parsed
  split at parsed
  · rename_i width
    cases parsed
    dsimp only [eval]
    split
    · rename_i same
      simp only [Word.eval]
      rw [← same]
      exact List.take_append_drop 160 bytes
    · simp only [Word.eval, List.Vector.toList_mk]
      exact List.take_append_drop 160 bytes
  · cases parsed

abbrev Spec := unifSpec + (Key →ₒ Output)
abbrev Cache := (Key →ₒ Output).QueryCache

def IsKey : Spec.Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred IsKey
  | .inl _ => inferInstanceAs (Decidable False)
  | .inr _ => inferInstanceAs (Decidable True)

def literals : Spec.Domain → List MlKemSharedSecret
  | .inr ⟨_, .literal value⟩ => [value]
  | _ => []

noncomputable def symbolic : QueryImpl Spec (StateT Cache ProbComp) := RegistrationNativeG3CellEager.lazy

noncomputable def actual (candidate : MlKemSharedSecret) : QueryImpl Spec (StateT Cache ProbComp)
  | .inl coin => symbolic (.inl coin)
  | .inr key => symbolic (.inr (normalize candidate key))

/-- Normalization changes a table query only at the candidate-equal literal occurrence recorded by the actual trace. -/
theorem actual_routed (candidate : MlKemSharedSecret) :
    RawCtxSelectedAliasCoupling.routed symbolic (actual candidate) literals candidate = actual candidate := by
  funext query
  cases query with
  | inl coin => simp [RawCtxSelectedAliasCoupling.routed, literals, actual]
  | inr key =>
      rcases key with ⟨head, word⟩
      cases word with
      | literal value =>
          by_cases same : candidate = value
          · simp [RawCtxSelectedAliasCoupling.routed, literals, same]
          · have different : Word.literal value ≠ Word.literal candidate := fun equal => same (Word.literal.inj equal).symm
            simp only [RawCtxSelectedAliasCoupling.routed, literals, List.mem_singleton, ite_eq_right same, actual, normalize]
            rw [ite_eq_right different]
      | atom => simp [RawCtxSelectedAliasCoupling.routed, literals, actual, normalize]

end BeaconcryptCore.Computational.RegistrationNativeSecretWord
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWord.eval_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWord.eval_length
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWord.eval_prefix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWord.eval_prefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWord.eval_suffix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWord.eval_suffix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWord.eval_normalize' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWord.eval_normalize
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWord.decode_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWord.decode_eval
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWord.decode_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWord.decode_some
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWord.actual_routed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWord.actual_routed
