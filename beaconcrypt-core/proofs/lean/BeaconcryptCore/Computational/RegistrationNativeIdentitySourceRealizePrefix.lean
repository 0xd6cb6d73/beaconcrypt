-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSeedPrefix
import BeaconcryptCore.Computational.RegistrationNativeIdentityRealization

/-! Existing owned credentials retain their private realization through actual arbitrary indexed-source programs. Private seed prefixes are derived from the source interpreter, not assumed as a global simulation contract. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySourceRealizePrefix
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityWorld (State implementation)
open RegistrationNativeIdentityFrontend (Trusted)
open RegistrationNativeIdentityRealization (Owned owners seedFor)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- A private seed prefix retains every earlier exact owned seed/public-key receipt. -/
theorem owns (joint : PqxdhJointIdentity.Primitives) (before after : PqxdhDynamicIdentityPool.SourceState)
    (preserved : before.seeds.IsPrefix after.seeds) (credential : RegistrationNativeIdentityInterface.Credential)
    (seed : PqxdhJointIdentity.IdentitySeed) (owned : RegistrationNativeIdentityCallbacks.Owns joint before credential seed) :
    RegistrationNativeIdentityCallbacks.Owns joint after credential seed := by
  refine ⟨?_, owned.2⟩
  obtain ⟨tail, appended⟩ := preserved
  rw [← appended, List.getElem?_append_left (List.getElem?_eq_some_iff.mp owned.1).1]
  exact owned.1

/-- Every earlier public owner realizes to the same seed-bearing source owner through a private seed prefix. -/
theorem owners_eq (joint : PqxdhJointIdentity.Primitives) (before after : PqxdhDynamicIdentityPool.SourceState)
    (preserved : before.seeds.IsPrefix after.seeds) (current : RegistrationNativeIdentityFrontend.State source)
    (owned : Owned joint before current) : owners after current = owners before current := by
  apply List.map_congr_left
  intro selected member
  obtain ⟨seed, found⟩ := owned selected member
  change RegistrationNativeIdentityFrontend.restore (seedFor after selected.identity) selected =
    RegistrationNativeIdentityFrontend.restore (seedFor before selected.identity) selected
  rw [RegistrationNativeIdentityRealization.seed_found _ _ seed (owns joint before after preserved selected.identity seed found).1,
    RegistrationNativeIdentityRealization.seed_found _ _ seed found.1]

/-- Complete actual adaptive source programs preserve the private realization of every previously owned public credential. -/
theorem program_owners (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (work : OracleComp (Trusted n KemSK) Value)
    (before : State n KemSK) (result : Value × State n KemSK)
    (current : RegistrationNativeIdentityFrontend.State source) (owned : Owned setup.joint before.identities current)
    (supported : result ∈ support ((simulateQ (implementation (mlSource := source) setup checks representation created) work).run before)) :
    owners result.2.identities current = owners before.identities current :=
  owners_eq setup.joint before.identities result.2.identities
    (RegistrationNativeIdentitySourceSeedPrefix.program_prefix setup checks representation created work before result supported) current owned

end BeaconcryptCore.Computational.RegistrationNativeIdentitySourceRealizePrefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceRealizePrefix.owns' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceRealizePrefix.owns
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceRealizePrefix.owners_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceRealizePrefix.owners_eq
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceRealizePrefix.program_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceRealizePrefix.program_owners
