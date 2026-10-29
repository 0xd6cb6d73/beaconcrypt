-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceFrame

/-! Private source realization replaces each indexed public credential with its actual stored seed. The executable owner/context types remain seed-free. This projection retains all native owner fields, current histories, mutable environment and World; the indexed service's duplicate private seed table and analysis transcript are omitted. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityRealization
open PqxdhJointIdentity
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {KemSK Auxiliary Value Other : Type} {source : RegistrationNativeMldsa.Source}

def seedFor (pool : PqxdhDynamicIdentityPool.SourceState)
    (credential : RegistrationNativeIdentityInterface.Credential) : IdentitySeed :=
  (pool.seeds[credential.handle]?).getD RegistrationNativeIdentityFrontend.dummyIdentity

def owner (pool : PqxdhDynamicIdentityPool.SourceState) (current : RegistrationNativeIdentityFrontend.Owner source) :
    RegistrationNativeBeaconFrontend.Owner source :=
  RegistrationNativeIdentityFrontend.restore (seedFor pool current.identity) current

def owners (pool : PqxdhDynamicIdentityPool.SourceState) (current : RegistrationNativeIdentityFrontend.State source) :
    RegistrationNativeBeaconFrontend.State source := current.map (owner pool)

def prepared (pool : PqxdhDynamicIdentityPool.SourceState) (current : RegistrationNativeIdentityFrontend.Prepared source) :
    RegistrationNativeBeaconFrontend.Prepared source :=
  ⟨current.credentials, current.pin, seedFor pool current.identity, current.prekey⟩

def preparedReply (pool : PqxdhDynamicIdentityPool.SourceState) :
    RustM (Option (RegistrationNativeIdentityFrontend.Prepared source)) →
      RustM (Option (RegistrationNativeBeaconFrontend.Prepared source))
  | .fail error => .fail error
  | .div => .div
  | .ok result => .ok (result.map (prepared pool))

def observe (reply : PqxdhDynamicIdentityPool.SourceState → Value → Other)
    (result : ((Value × RegistrationNativeIdentityFrontend.State source) × EnvState Auxiliary) ×
      RegistrationNativeIdentityWorld.State n KemSK) :=
  (((reply result.2.identities result.1.1.1, owners result.2.identities result.1.1.2), result.1.2), result.2.context)

def Owned (primitives : Primitives) (pool : PqxdhDynamicIdentityPool.SourceState)
    (current : RegistrationNativeIdentityFrontend.State source) : Prop :=
  ∀ selected ∈ current, ∃ seed, RegistrationNativeIdentityCallbacks.Owns primitives pool selected.identity seed

/-- A generated credential is realized by exactly the privately stored seed at its index. -/
theorem seed_found (pool : PqxdhDynamicIdentityPool.SourceState)
    (credential : RegistrationNativeIdentityInterface.Credential) (seed : IdentitySeed)
    (found : pool.seeds[credential.handle]? = some seed) : seedFor pool credential = seed := by
  simp only [seedFor, found, Option.getD_some]

/-- Realizing a successfully appended owner retains its exact source creation order. -/
theorem owners_append (pool : PqxdhDynamicIdentityPool.SourceState)
    (prior : RegistrationNativeIdentityFrontend.State source) (created : RegistrationNativeIdentityFrontend.Owner source) :
    owners pool (prior ++ [created]) = owners pool prior ++ [owner pool created] := by
  simp only [owners, List.map_append, List.map_cons, List.map_nil]

end BeaconcryptCore.Computational.RegistrationNativeIdentityRealization

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityRealization.seed_found' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityRealization.seed_found
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityRealization.owners_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityRealization.owners_append
