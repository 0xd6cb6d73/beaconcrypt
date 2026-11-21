-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceTrusted
import BeaconcryptCore.Computational.RegistrationNativeKemBeaconFootprint

/-! The concrete local Beacon controllers lower every ordinary role primitive before their external interface. Their actual open query trees therefore satisfy the syntactic callback condition used in the native source reconstruction. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeTrustedAllowed
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePublicSourceTrusted (Allowed)
open RegistrationNativeBeaconFrontend (Trusted)
open RegistrationNativeKemBeaconFootprint (counted)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

private theorem allowed_of_zero (work : OracleComp (Trusted n KemSK) Value)
    (zero : work.IsQueryBoundP (counted (n := n) (KemSK := KemSK) .other) 0) : work.AllQueriesSatisfy (Allowed (KemSK := KemSK)) := by
  classical
  apply (isQueryBoundP_zero_iff work (Allowed (KemSK := KemSK))).mp
  apply (isQueryBoundP_congr_pred (fun query => show counted (n := n) (KemSK := KemSK) .other query ↔ ¬ Allowed query from ?_)).mp zero
  rcases query with environment | other | (pool | key)
  · simp [counted, Allowed]
  · simp [counted, Allowed]
  · cases pool <;> simp [counted, Allowed]
  · simp [counted, Allowed]

/-- Every constructor outcome exposes only its actual public World work and indexed key birth. -/
theorem create_allowed (setup : Setup base KemSK) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativeBeaconFrontend.State mlSource)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    (((RegistrationNativeBeaconFrontend.create (n := n) setup mlSource edPin mlPin keyId).run owners).run env).AllQueriesSatisfy
      (Allowed (KemSK := KemSK)) := by
  apply allowed_of_zero
  simpa using
    RegistrationNativeKemBeaconFootprint.create_bound setup .other edPin mlPin keyId owners env

/-- Failed or successful outgoing publication cannot escape to a selected-role backend. -/
theorem bundle_allowed (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (owners : RegistrationNativeBeaconFrontend.State mlSource)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    (((RegistrationNativeBeaconFrontend.bundle (n := n) setup mlSource wire index).run owners).run env).AllQueriesSatisfy
      (Allowed (KemSK := KemSK)) := by
  exact allowed_of_zero _ (RegistrationNativeKemBeaconFootprint.bundle_zero setup .other wire index owners env)

/-- Authentication, agreement and sequence-one opening retain only actual indexed decapsulation and public World callbacks. -/
theorem finish_allowed (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : RegistrationNativeBeaconFrontend.State mlSource)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    (((RegistrationNativeBeaconFrontend.finish (n := n) setup mlSource wire index packet).run owners).run env).AllQueriesSatisfy
      (Allowed (KemSK := KemSK)) := by
  exact allowed_of_zero _ (RegistrationNativeKemBeaconFootprint.finish_zero setup .other wire index packet owners env)

end BeaconcryptCore.Computational.RegistrationNativeTrustedAllowed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTrustedAllowed.create_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTrustedAllowed.create_allowed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTrustedAllowed.bundle_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTrustedAllowed.bundle_allowed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTrustedAllowed.finish_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTrustedAllowed.finish_allowed
