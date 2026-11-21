-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconAgreementRoot

/-! The selected Beacon prekey remains a public peer reference in the executable root prefix. Its mathematical native interpretation makes the actual prekey DH request at both original call positions. One-time and identity DH, conversions and decapsulation retain their original backend effects. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.Computational.RegistrationBeaconRootInterpreter

open RegistrationAgreementExecutor
open PqxdhJointIdentity PqxdhJointGapDh
open PqxdhBeaconPhase2Preparation (Word32)
open RegistrationBeaconAgreementRoot (callbacks)

abbrev SumSpec := PqxdhBeaconPhase2Preparation.Spec Unit (Unit ⊕ Unit) Unit Unit registration.AuthenticatedResponse
abbrev AuxSpec := PqxdhBeaconPhase2Preparation.Spec Unit Unit Unit Unit registration.AuthenticatedResponse

def sumCallbacks (authenticated : registration.AuthenticatedResponse) : QueryImpl SumSpec (OracleComp Spec)
  | .decode raw => callbacks authenticated (.decode raw)
  | .ciphertext response => callbacks authenticated (.ciphertext response)
  | .ephemeral response => callbacks authenticated (.ephemeral response)
  | .serverIdentity response => callbacks authenticated (.serverIdentity response)
  | .publicConversion key => callbacks authenticated (.publicConversion key)
  | .privateConversion identity => callbacks authenticated (.privateConversion identity)
  | .decapsulate ciphertext kem => callbacks authenticated (.decapsulate ciphertext kem)
  | .dhPair (.inl _) key => callbacks authenticated (.dhPair false key)
  | .dhPair (.inr _) key => callbacks authenticated (.dhPair true key)
  | .dhIdentity identity key => callbacks authenticated (.dhIdentity identity key)
  | .assignedId response => callbacks authenticated (.assignedId response)
  | .eraseShared secrets => callbacks authenticated (.eraseShared secrets)

def auxImpl {m : Type → Type} [Monad m] (backend : QueryImpl Spec m)
    (authenticated : registration.AuthenticatedResponse) : QueryImpl AuxSpec m
  | .decode raw => simulateQ backend (callbacks authenticated (.decode raw))
  | .ciphertext response => simulateQ backend (callbacks authenticated (.ciphertext response))
  | .ephemeral response => simulateQ backend (callbacks authenticated (.ephemeral response))
  | .serverIdentity response => simulateQ backend (callbacks authenticated (.serverIdentity response))
  | .publicConversion key => simulateQ backend (callbacks authenticated (.publicConversion key))
  | .privateConversion identity => simulateQ backend (callbacks authenticated (.privateConversion identity))
  | .decapsulate ciphertext kem => simulateQ backend (callbacks authenticated (.decapsulate ciphertext kem))
  | .dhPair _ key => simulateQ backend (callbacks authenticated (.dhPair true key))
  | .dhIdentity identity key => simulateQ backend (callbacks authenticated (.dhIdentity identity key))
  | .assignedId response => simulateQ backend (callbacks authenticated (.assignedId response))
  | .eraseShared secrets => simulateQ backend (callbacks authenticated (.eraseShared secrets))

def sourceImpl {m : Type → Type} [Monad m] {joint : Primitives} (dh : DhInterface joint)
    (scalar : ScalarBytes) (backend : QueryImpl Spec m) (visit : Word32 → m Unit) : QueryImpl Spec m
  | .dh request => match request.secret_role with
      | .BeaconPrekey => do
          let _ ← visit request.public_key
          pure (RegistrationAgreementRoot.nativeOption ((dh.dh scalar
            (PqxdhPhase2GapDhSource.peer request.public_key)).map PqxdhPhase2GapDhSource.word))
      | _ => backend (.dh request)
  | request => backend request

private theorem option_roundtrip {Value : Type} (value : Option Value) :
    RegistrationAgreementRoot.option (RegistrationAgreementRoot.nativeOption value) = value := by
  cases value <;> rfl

theorem callbacks_source {m : Type → Type} [Monad m] [LawfulMonad m]
    {joint : Primitives} (dh : DhInterface joint) (scalar : ScalarBytes)
    (backend : QueryImpl Spec m) (visit : Word32 → m Unit)
    (authenticated : registration.AuthenticatedResponse) (query : SumSpec.Domain) :
    simulateQ (sourceImpl dh scalar backend visit) (sumCallbacks authenticated query) =
      PqxdhPhase2GapDhSource.nativeImpl dh scalar (auxImpl backend authenticated) visit query := by
  cases query <;> simp only [sumCallbacks, callbacks, auxImpl, sourceImpl,
    PqxdhPhase2GapDhSource.nativeImpl, simulateQ_pure, simulateQ_map, simulateQ_spec_query]
  case dhPair pair key =>
    cases pair <;> simp only [sourceImpl, simulateQ_map, simulateQ_spec_query, map_bind, map_pure, option_roundtrip,
      Bool.false_eq_true, ↓reduceIte]

theorem collect_sum (authenticated : registration.AuthenticatedResponse) :
    simulateQ (callbacks authenticated)
        (PqxdhBeaconPhase2Preparation.collect () false true () []) =
      simulateQ (sumCallbacks authenticated)
        (PqxdhBeaconPhase2Preparation.collect () (.inl ()) (.inr ()) () []) := by
  simp only [PqxdhBeaconPhase2Preparation.collect, OptionT.run_bind, OptionT.run_monadLift,
    OptionT.run_mk, OptionT.run_pure, Option.elimM, bind_map_left,
    simulateQ_bind, simulateQ_spec_query, sumCallbacks, callbacks,
    pure_bind, Option.elim_some, ]
  repeat' first
    | rfl
    | (simp only [Option.elim_some, simulateQ_bind, simulateQ_spec_query, sumCallbacks, callbacks, bind_map_left,
        RegistrationAgreementRoot.option, ↓reduceIte])
    | (congr 1; funext reply; cases reply)

theorem prefix_source {m : Type → Type} [Monad m] [LawfulMonad m]
    {joint : Primitives} (dh : DhInterface joint) (scalar : ScalarBytes)
    (backend : QueryImpl Spec m) (visit : Word32 → m Unit)
    (authenticated : registration.AuthenticatedResponse) :
    simulateQ (sourceImpl dh scalar backend visit)
      (simulateQ (callbacks authenticated) (PqxdhBeaconPhase2Preparation.collect () false true () [])) =
      simulateQ (PqxdhPhase2GapDhSource.nativeImpl dh scalar (auxImpl backend authenticated) visit)
        (PqxdhBeaconPhase2Preparation.collect () (.inl ()) (.inr ()) () []) := by
  rw [collect_sum, ← QueryImpl.simulateQ_compose]
  have equal : sourceImpl dh scalar backend visit ∘ₛ sumCallbacks authenticated =
      PqxdhPhase2GapDhSource.nativeImpl dh scalar (auxImpl backend authenticated) visit := by
    funext query
    exact callbacks_source dh scalar backend visit authenticated query
  rw [equal]

end BeaconcryptCore.Computational.RegistrationBeaconRootInterpreter

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRootInterpreter.callbacks_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRootInterpreter.callbacks_source

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRootInterpreter.collect_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRootInterpreter.collect_sum

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRootInterpreter.prefix_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRootInterpreter.prefix_source
