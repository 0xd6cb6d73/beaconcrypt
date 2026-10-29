-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWord
import BeaconcryptCore.Computational.RegistrationNativePublicFrontend

/-! The shared symbolic native KEM boundary retains the exact indexed query constructors and opaque private handles. Only encapsulated and decapsulated shared secrets become literal-or-atom words. Realization maps those replies back to their literal32-byte values while forwarding all other operations unchanged. This is an executable interface translation, not a concrete candidate-provider source equality. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordKemInterface
open RegistrationNativeSecretWord (Word)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext MlKemSharedSecret)
variable {KemSK Value : Type}

abbrev WordPoolSpec (KemSK : Type) : OracleSpec PqxdhLiveKemBirth.Query
  | .create => Nat × MlKem768PublicKey
  | .decapsulate _ _ => Option Word
  | .reveal _ => Option KemSK

abbrev WordEncapSpec := MlKem768PublicKey →ₒ (MlKem768Ciphertext × Word)
abbrev Routed (KemSK : Type) := (RegistrationNativeKemInterface.OtherSpec + WordEncapSpec) +
  (WordPoolSpec KemSK + WordEncapSpec)
abbrev ActualRouted (KemSK : Type) := RegistrationNativePublicFrontend.RoutedKem KemSK

def realize (candidate : MlKemSharedSecret) : QueryImpl (ActualRouted KemSK) (OracleComp (Routed KemSK))
  | .inl (.inl query) => (Routed KemSK).query (.inl (.inl query))
  | .inl (.inr key) => Prod.map id (Word.eval candidate) <$> (Routed KemSK).query (.inl (.inr key))
  | .inr (.inl .create) => (Routed KemSK).query (.inr (.inl .create))
  | .inr (.inl (.decapsulate handle ciphertext)) => Option.map (Word.eval candidate) <$>
      (Routed KemSK).query (.inr (.inl (.decapsulate handle ciphertext)))
  | .inr (.inl (.reveal handle)) => (Routed KemSK).query (.inr (.inl (.reveal handle)))
  | .inr (.inr key) => Prod.map id (Word.eval candidate) <$> (Routed KemSK).query (.inr (.inr key))

/-- Ordinary local DH and conversion callbacks retain their exact request and reply. -/
theorem realize_other (candidate : MlKemSharedSecret) (query : RegistrationNativeKemInterface.OtherSpec.Domain) :
    realize (KemSK := KemSK) candidate (.inl (.inl query)) = (Routed KemSK).query (.inl (.inl query)) := rfl

/-- Ordinary public encapsulation retains the ciphertext and evaluates only its symbolic shared-secret word. -/
theorem realize_public_encapsulate (candidate : MlKemSharedSecret) (key : MlKem768PublicKey) :
    realize (KemSK := KemSK) candidate (.inl (.inr key)) =
      Prod.map id (Word.eval candidate) <$> (Routed KemSK).query (.inl (.inr key)) := rfl

/-- Opaque generated-key creation retains the exact index and public key, without relating that index to any roster position. -/
theorem realize_create (candidate : MlKemSharedSecret) :
    realize (KemSK := KemSK) candidate (.inr (.inl .create)) = (Routed KemSK).query (.inr (.inl .create)) := rfl

/-- Indexed decapsulation preserves its optional failure and evaluates the returned word only on success. -/
theorem realize_decapsulate (candidate : MlKemSharedSecret) (handle : Nat) (ciphertext : MlKem768Ciphertext) :
    realize (KemSK := KemSK) candidate (.inr (.inl (.decapsulate handle ciphertext))) =
      Option.map (Word.eval candidate) <$> (Routed KemSK).query (.inr (.inl (.decapsulate handle ciphertext))) := rfl

/-- Explicit private-key reveals remain the same indexed operation and are never recoded as shared-secret words. -/
theorem realize_reveal (candidate : MlKemSharedSecret) (handle : Nat) :
    realize (KemSK := KemSK) candidate (.inr (.inl (.reveal handle))) =
      (Routed KemSK).query (.inr (.inl (.reveal handle))) := rfl

/-- Selected encapsulation uses the separate selected getter branch with its actual ciphertext retained. -/
theorem realize_selected_encapsulate (candidate : MlKemSharedSecret) (key : MlKem768PublicKey) :
    realize (KemSK := KemSK) candidate (.inr (.inr key)) =
      Prod.map id (Word.eval candidate) <$> (Routed KemSK).query (.inr (.inr key)) := rfl

private theorem query_bound (candidate : MlKemSharedSecret) (predicate : (Routed KemSK).Domain → Prop)
    [DecidablePred predicate] (query : (ActualRouted KemSK).Domain) :
    (realize candidate query).IsQueryBoundP predicate (if predicate query then 1 else 0) := by
  rcases query with (query | key) | (query | key)
  · simp only [realize, isQueryBoundP_query_iff]
    split_ifs with counted <;> simp [counted]
  · simp only [realize, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    split_ifs with counted <;> simp [counted]
  · cases query <;> simp only [realize, isQueryBoundP_map_iff, isQueryBoundP_query_iff] <;>
      split_ifs with counted <;> simp [counted]
  · simp only [realize, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    split_ifs with counted <;> simp [counted]

/-- Every original query-class cap, including create and reveal, is preserved through arbitrary adaptive realization. -/
theorem realize_bound (candidate : MlKemSharedSecret) (predicate : (Routed KemSK).Domain → Prop)
    [DecidablePred predicate] (work : OracleComp (ActualRouted KemSK) Value) (cap : Nat)
    (bounded : work.IsQueryBoundP predicate cap) :
    (simulateQ (realize candidate) work).IsQueryBoundP predicate cap :=
  RawCtxSourceOpen.simulate_bound _ predicate predicate work cap bounded (query_bound candidate predicate)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordKemInterface
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemInterface.realize_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemInterface.realize_other
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemInterface.realize_public_encapsulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemInterface.realize_public_encapsulate
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemInterface.realize_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemInterface.realize_create
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemInterface.realize_decapsulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemInterface.realize_decapsulate
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemInterface.realize_reveal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemInterface.realize_reveal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemInterface.realize_selected_encapsulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemInterface.realize_selected_encapsulate
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemInterface.realize_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemInterface.realize_bound
