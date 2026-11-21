-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordServerSuffix
import BeaconcryptCore.Computational.RegistrationNativeSecretWordMessage
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemInterface

/-! This executable Server collector carries the selected KEM reply as an opaque word. It preserves the original thirteen callback positions, every optional exit and all public fields, while the literal shared word is restored only by the mathematical interpretation of the private root reference. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordServerCollect
open RegistrationNativeSecretWord (Word)
open PqxdhServerRootPreparation (Query Verified Ephemeral Inputs registrationId)
open PqxdhBeaconPhase2Preparation (Word32 Ciphertext)
open PqxdhRootTableInitialization (rootArray)
variable {Reader E Shared : Type}

abbrev Spec (Reader E Shared : Type) : OracleSpec (Query Reader E)
  | .encapsulate _ => Option (Ciphertext × Word)
  | query => (PqxdhServerRootPreparation.Spec Reader E Shared).Range query

def zero : Word32 := rootArray RegistrationNativeSecretWordMessage.zero

structure Input (Reader E Shared : Type) where
  plain : Inputs Reader E Shared
  kem : Word

def eval (candidate : PqxdhKemIndCca.MlKemSharedSecret) (input : Input Reader E Shared) : Inputs Reader E Shared :=
  RegistrationNativeSecretWordServerSuffix.replace (rootArray (input.kem.eval candidate)) input.plain

def realize (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    QueryImpl (PqxdhServerRootPreparation.Spec Reader E Shared) (OracleComp (Spec Reader E Shared))
  | .encapsulate key => Option.map (Prod.map id (fun word => rootArray (Word.eval candidate word))) <$>
      (Spec Reader E Shared).query (.encapsulate key)
  | .decode raw => (Spec Reader E Shared).query (.decode raw)
  | .identity reader => (Spec Reader E Shared).query (.identity reader)
  | .identityPoint key => (Spec Reader E Shared).query (.identityPoint key)
  | .pqField reader => (Spec Reader E Shared).query (.pqField reader)
  | .preField reader => (Spec Reader E Shared).query (.preField reader)
  | .oneField reader => (Spec Reader E Shared).query (.oneField reader)
  | .verify key signed => (Spec Reader E Shared).query (.verify key signed)
  | .registrationStatus identifier => (Spec Reader E Shared).query (.registrationStatus identifier)
  | .reserveRegistration => (Spec Reader E Shared).query .reserveRegistration
  | .parseDh point => (Spec Reader E Shared).query (.parseDh point)
  | .generate => (Spec Reader E Shared).query .generate
  | .parseKem key => (Spec Reader E Shared).query (.parseKem key)
  | .publicConversion key => (Spec Reader E Shared).query (.publicConversion key)
  | .privateConversion => (Spec Reader E Shared).query .privateConversion
  | .staticDh point => (Spec Reader E Shared).query (.staticDh point)
  | .ephemeralDh secret point => (Spec Reader E Shared).query (.ephemeralDh secret point)

def collect {Reader E Shared : Type} (verified : Verified Reader) :
    OracleComp (Spec Reader E Shared) (Option (Input Reader E Shared)) := OptionT.run do
  let status ← (Spec Reader E Shared).query (.registrationStatus (registrationId verified))
  match status with
  | .Consumed => failure
  | .Fresh => do
    let reserved ← (Spec Reader E Shared).query .reserveRegistration
    if !reserved then failure else do
      let prekey := rootArray verified.keys.prekey
      let oneTime := rootArray verified.keys.oneTime
      let validPrekey ← (Spec Reader E Shared).query (.parseDh prekey)
      if !validPrekey then failure else do
        let validOneTime ← (Spec Reader E Shared).query (.parseDh oneTime)
        if !validOneTime then failure else do
          let ephemeral ← OptionT.mk ((Spec Reader E Shared).query .generate)
          let validKem ← (Spec Reader E Shared).query (.parseKem verified.keys.pqKey)
          if !validKem then failure else do
            let encapsulated ← OptionT.mk ((Spec Reader E Shared).query (.encapsulate verified.keys.pqKey))
            let converted ← OptionT.mk ((Spec Reader E Shared).query (.publicConversion verified.identity))
            let privateConverted ← (Spec Reader E Shared).query .privateConversion
            if !privateConverted then failure else do
              let first ← OptionT.mk ((Spec Reader E Shared).query (.staticDh prekey))
              let second ← OptionT.mk ((Spec Reader E Shared).query (.ephemeralDh ephemeral.secret converted))
              let third ← OptionT.mk ((Spec Reader E Shared).query (.ephemeralDh ephemeral.secret prekey))
              let fourth ← OptionT.mk ((Spec Reader E Shared).query (.ephemeralDh ephemeral.secret oneTime))
              pure ⟨⟨verified, ephemeral, encapsulated.1, converted, first, second, third, fourth, zero⟩, encapsulated.2⟩

/-- Evaluating only the opaque word recovers the literal entire native collector AST, including each failure and every subsequent callback operand. -/
theorem collect_realization (candidate : PqxdhKemIndCca.MlKemSharedSecret) (verified : Verified Reader) :
    simulateQ (realize candidate) (PqxdhServerRootPreparation.collectVerified (E := E) (Shared := Shared) verified) =
      Option.map (eval candidate) <$> collect verified := by
  simp only [PqxdhServerRootPreparation.collectVerified, collect, OptionT.run_bind, OptionT.run_monadLift,
    Option.elimM, bind_map_left, simulateQ_bind, simulateQ_spec_query, realize, map_bind]
  repeat' (
    try simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift,
      OptionT.run_failure, Option.elimM, bind_map_left, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, ite_false, ite_true, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
      map_bind, map_pure, realize, Option.elim_none, Option.elim_some, Option.map_none, Option.map_some,
      Prod.map, id_eq]
    first | rfl | (congr 1; funext reply; cases reply))
  all_goals rfl

/-- Arbitrary later source interpreters preserve the complete reached state in this exact symbolic collector law. -/
theorem collect_program {m : Type → Type} [Monad m] [LawfulMonad m]
    (implementation : QueryImpl (Spec Reader E Shared) m) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (verified : Verified Reader) :
    simulateQ (implementation ∘ₛ realize candidate)
      (PqxdhServerRootPreparation.collectVerified (E := E) (Shared := Shared) verified) =
      Option.map (eval candidate) <$> simulateQ implementation (collect verified) := by
  rw [QueryImpl.simulateQ_compose, collect_realization, simulateQ_map]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordServerCollect
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServerCollect.collect_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServerCollect.collect_realization
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServerCollect.collect_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServerCollect.collect_program
