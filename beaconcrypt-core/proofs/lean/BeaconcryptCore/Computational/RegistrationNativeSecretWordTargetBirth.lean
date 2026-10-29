-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBirthCaps
import BeaconcryptCore.Computational.RegistrationNativeSecretWordOwners

/-! Actual constructor and outgoing bundle programs have no KEM shared-secret reply. Evaluating their symbolic realization at any candidate therefore equals evaluation at zero, with the complete native result, public owner roster and current environment retained. The necessary footprint is derived for these actual controllers. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBirth
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordTargetBirthCaps (Allowed)
open RegistrationNativeSecretWordServerSource (realize)
open RegistrationBeaconReferenceCompiler (trustedLift)
open RegistrationNativeBeaconFrontend (Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- Every permitted native callback has an identical symbolic realization at all candidate values. -/
theorem query_realize (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (query : (Trusted n KemSK).Domain) (safe : Allowed (KemSK := KemSK) query) :
    simulateQ (realize candidate) (trustedLift query) =
      simulateQ (realize RegistrationNativeSecretWordMessage.zero) (trustedLift query) := by
  rcases query with effect | other | query | key
  · rfl
  · rfl
  · cases query with
    | create | reveal handle => rfl
    | decapsulate handle ciphertext => exact safe.elim
  · exact safe.elim

/-- The native footprint extends through every adaptive continuation while preserving its exact return value. -/
theorem program_realize (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (work : OracleComp (Trusted n KemSK) Value) (safe : AllQueriesSatisfy work (Allowed (KemSK := KemSK))) :
    simulateQ (realize candidate ∘ₛ trustedLift) work =
      simulateQ (realize RegistrationNativeSecretWordMessage.zero ∘ₛ trustedLift) work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp safe
      simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.apply_compose]
      rw [query_realize candidate query first]
      congr 1
      funext reply
      exact ih reply (later reply)

/-- Actual complete public creation has exactly the same result, owner list and current environment at every realization. -/
theorem create_realize (setup : Setup base KemSK) (selected : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary) :
    simulateQ (realize candidate)
      (((RegistrationNativePublicOwners.create (n := n) setup source selected publicPrekey edPin mlPin keyId).run owners).run env) =
      simulateQ (realize RegistrationNativeSecretWordMessage.zero)
        (((RegistrationNativePublicOwners.create (n := n) setup source selected publicPrekey edPin mlPin keyId).run owners).run env) := by
  simp only [RegistrationNativePublicOwners.create, RegistrationNativePublicOwners.executeLocal,
    StateT.run, simulateQ_map]
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  exact congrArg (fun work => (fun result => ((result.1.1,
    RegistrationNativePublicOwners.pack selected publicPrekey result.1.2), result.2)) <$> work)
    (program_realize candidate _ (RegistrationNativeSecretWordTargetBirthCaps.create_safe setup edPin mlPin keyId _ env))

/-- Actual full outgoing publication retains all signing/hash failures and the exact current environment at every realization. -/
theorem bundle_realize (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (selected index : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary) :
    simulateQ (realize candidate)
      (((RegistrationNativePublicOwners.bundle (n := n) setup source wire selected publicPrekey index).run owners).run env) =
      simulateQ (realize RegistrationNativeSecretWordMessage.zero)
        (((RegistrationNativePublicOwners.bundle (n := n) setup source wire selected publicPrekey index).run owners).run env) := by
  simp only [RegistrationNativePublicOwners.bundle, RegistrationNativePublicOwners.executeLocal,
    StateT.run, simulateQ_map]
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  exact congrArg (fun work => (fun result => ((result.1.1,
    RegistrationNativePublicOwners.pack selected publicPrekey result.1.2), result.2)) <$> work)
    (program_realize candidate _ (RegistrationNativeSecretWordTargetBirthCaps.bundle_safe setup wire index _ env))

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBirth
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBirth.query_realize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBirth.query_realize
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBirth.program_realize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBirth.program_realize
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBirth.create_realize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBirth.create_realize
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBirth.bundle_realize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBirth.bundle_realize
