-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemReferenceCompiler

/-! After the actual Server encapsulation, its shared word is stored only in the private root input. Every subsequent conversion, selected-static visit, local DH callback, optional exit and public native field is independent of that word. The factorizations below retain the exact original callback program rather than replacing the source controller by an assumed relation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordServerSuffix
open PqxdhServerRootPreparation (Spec Inputs Verified Ephemeral)
open PqxdhBeaconPhase2Preparation (Word32 Ciphertext)
variable {Reader E Shared : Type}

def replace (kem : Word32) (input : Inputs Reader E Shared) : Inputs Reader E Shared :=
  { input with kem := kem }

def finish (verified : Verified Reader) (ephemeral : Ephemeral E)
    (ciphertext : Ciphertext) (kem : Word32) : OracleComp (Spec Reader E Shared) (Option (Inputs Reader E Shared)) := OptionT.run do
  let converted ← OptionT.mk ((Spec Reader E Shared).query (.publicConversion verified.identity))
  let privateConverted ← (Spec Reader E Shared).query .privateConversion
  if !privateConverted then failure else do
    let first ← OptionT.mk ((Spec Reader E Shared).query (.staticDh (PqxdhRootTableInitialization.rootArray verified.keys.prekey)))
    let second ← OptionT.mk ((Spec Reader E Shared).query (.ephemeralDh ephemeral.secret converted))
    let third ← OptionT.mk ((Spec Reader E Shared).query (.ephemeralDh ephemeral.secret (PqxdhRootTableInitialization.rootArray verified.keys.prekey)))
    let fourth ← OptionT.mk ((Spec Reader E Shared).query (.ephemeralDh ephemeral.secret (PqxdhRootTableInitialization.rootArray verified.keys.oneTime)))
    pure ⟨verified, ephemeral, ciphertext, converted, first, second, third, fourth, kem⟩

/-- Changing the encapsulated shared word changes only the final successful input field; all later callback operands and failure paths are literally identical. -/
theorem finish_replace (verified : Verified Reader) (ephemeral : Ephemeral E)
    (ciphertext : Ciphertext) (left right : Word32) :
    finish verified ephemeral ciphertext right =
      Option.map (replace right) <$> (finish (Shared := Shared) verified ephemeral ciphertext left) := by
  simp only [finish, OptionT.run_bind, OptionT.run_monadLift, Option.elimM, bind_map_left, map_bind]
  repeat' (
    try simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure,
      OptionT.run_failure, Option.elimM, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, ite_false, ite_true, map_bind, map_pure, Option.elim_none,
      Option.elim_some, Option.map_none, Option.map_some]
    first | rfl | (congr 1; funext reply; cases reply))
  all_goals rfl

/-- The actual source collector reaches the shared-word-independent suffix only after its original freshness, reservation, point, generation and KEM gates. -/
theorem collect_factor (verified : Verified Reader) :
    PqxdhServerRootPreparation.collectVerified (E := E) (Shared := Shared) verified =
      (show OracleComp (Spec Reader E Shared) (Option (Inputs Reader E Shared)) from OptionT.run do
        let status ← (Spec Reader E Shared).query (.registrationStatus (PqxdhServerRootPreparation.registrationId verified))
        match status with
        | .Consumed => failure
        | .Fresh => do
          let reserved ← (Spec Reader E Shared).query .reserveRegistration
          if !reserved then failure else do
            let validPrekey ← (Spec Reader E Shared).query (.parseDh (PqxdhRootTableInitialization.rootArray verified.keys.prekey))
            if !validPrekey then failure else do
              let validOneTime ← (Spec Reader E Shared).query (.parseDh (PqxdhRootTableInitialization.rootArray verified.keys.oneTime))
              if !validOneTime then failure else do
                let ephemeral ← OptionT.mk ((Spec Reader E Shared).query .generate)
                let validKem ← (Spec Reader E Shared).query (.parseKem verified.keys.pqKey)
                if !validKem then failure else do
                  let encapsulated ← OptionT.mk ((Spec Reader E Shared).query (.encapsulate verified.keys.pqKey))
                  OptionT.mk (finish verified ephemeral encapsulated.1 encapsulated.2)) := rfl

/-- Full reached interpreter state is retained when the private shared word is changed in the suffix. No callback or state-preservation hypothesis is needed. -/
theorem finish_program {m : Type → Type} [Monad m] [LawfulMonad m]
    (implementation : QueryImpl (Spec Reader E Shared) m) (verified : Verified Reader) (ephemeral : Ephemeral E)
    (ciphertext : Ciphertext) (left right : Word32) :
    simulateQ implementation (finish verified ephemeral ciphertext right) =
      Option.map (replace right) <$> simulateQ implementation (finish verified ephemeral ciphertext left) := by
  rw [finish_replace verified ephemeral ciphertext left right, simulateQ_map]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordServerSuffix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServerSuffix.finish_replace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServerSuffix.finish_replace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServerSuffix.collect_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServerSuffix.collect_factor
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServerSuffix.finish_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServerSuffix.finish_program
