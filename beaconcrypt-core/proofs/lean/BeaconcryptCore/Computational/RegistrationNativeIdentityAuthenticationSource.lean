-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCommonSource

/-! Incoming mandatory authentication uses the unchanged native hash and verifier requests on the same mutable Env/World. It does not access or replace the generated identity table; every optional response and reached hash-cache effect is retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityAuthenticationSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentitySourceSimulation
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

theorem query_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (seeds : List PqxdhJointIdentity.IdentitySeed)
    (query : RegistrationAuthenticationExecutor.Request) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds
      (RegistrationNativeIdentityFrontend.authentication setup source query)
      (RegistrationNativeBeaconFrontend.authentication setup source query) := by
  cases query with
  | hash request =>
      exact related_bind setup checks representation created seeds _ _ _ _
        (RegistrationNativeIdentityCommonSource.effect_source setup checks representation created seeds _)
        (RegistrationNativeIdentityCommonSource.effect_keeps setup checks representation created _)
        (fun _ => related_pure setup checks representation created seeds _)
  | mldsa request | ed25519 request => exact related_pure setup checks representation created seeds _

theorem query_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : RegistrationAuthenticationExecutor.Request) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created
      (RegistrationNativeIdentityFrontend.authentication setup source query) := by
  cases query with
  | hash request =>
      exact keeps_bind setup checks representation created _ _
        (RegistrationNativeIdentityCommonSource.effect_keeps setup checks representation created _)
        (fun _ => keeps_pure setup checks representation created _)
  | mldsa request | ed25519 request => exact keeps_pure setup checks representation created _

/-- The whole actual native response-authentication controller, including failure paths, has exactly the original source replies and full state. -/
theorem program_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (seeds : List PqxdhJointIdentity.IdentitySeed)
    (work : OracleComp RegistrationAuthenticationExecutor.Spec Value) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds
      (simulateQ (RegistrationNativeIdentityFrontend.authentication setup source) work)
      (simulateQ (RegistrationNativeBeaconFrontend.authentication setup source) work) :=
  related_program setup checks representation created seeds _ _
    (query_source setup checks representation created seeds) (query_keeps setup checks representation created) work

theorem program_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (work : OracleComp RegistrationAuthenticationExecutor.Spec Value) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created
      (simulateQ (RegistrationNativeIdentityFrontend.authentication setup source) work) :=
  keeps_program setup checks representation created _ (query_keeps setup checks representation created) work

end BeaconcryptCore.Computational.RegistrationNativeIdentityAuthenticationSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityAuthenticationSource.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityAuthenticationSource.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityAuthenticationSource.query_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityAuthenticationSource.query_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityAuthenticationSource.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityAuthenticationSource.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityAuthenticationSource.program_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityAuthenticationSource.program_keeps
