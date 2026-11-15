-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAuthenticationExecutor

/-! The removed Init fingerprint executor is retired. Current Init acceptance follows only its request hash and three attached Ed checks; record AD is completed later from the exact session transcript. The unchanged accepted-state observation is retained below. -/
open OracleComp CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationFingerprintExecutor
open RegistrationAuthenticationExecutor

theorem execute_accepted (fuel : Nat) (value : registration.AuthenticatedInit) :
    execute fuel (.Accepted value) = pure (.ok ([], .Accepted value)) := by
  cases fuel <;> simp only [execute, step, continueWith, pure_bind]

end BeaconcryptCore.Computational.RegistrationFingerprintExecutor

/-- info: 'BeaconcryptCore.Computational.RegistrationFingerprintExecutor.execute_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationFingerprintExecutor.execute_accepted
