-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerFields
import BeaconcryptCore.Computational.RegistrationNativePublicSourceSupport
import BeaconcryptCore.Computational.RegistrationNativePublicOwnerInvariant

/-! The scalar-free selected-owner view is an internal invariant of the complete mixed frontend. Actual constructors and bundle callbacks pack the selected key, while terminal response processing preserves that key and never manufactures a local selected scalar. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCanonical
open RegistrationNativePublicOwnerMask (Canonical At)
open RegistrationNativePublicOwners (Owner State M)
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

private theorem set_canonical (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (owners : State mlSource) (index : Nat) (owner : Owner mlSource)
    (found : owners[index]? = some owner) (valid : Canonical selected publicPrekey owners)
    (view : RegistrationBeaconReferenceCompiler.SelectedOwner mlSource)
    (same : view.prekeyPublic = owner.view.prekeyPublic) :
    Canonical selected publicPrekey (owners.set index { owner with view }) := by
  intro position current stored
  by_cases equal : position = index
  · subst position
    rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1, Option.some.injEq] at stored
    subst current
    have prior := valid index owner found
    simpa only [At, same] using prior
  · rw [List.getElem?_set_ne (Ne.symm equal)] at stored
    exact valid position current stored

/-- Actual local constructors and outgoing bundles return a canonical masked roster on every possible callback path. -/
theorem executeLocal_canonical (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : RegistrationNativeBeaconFrontend.M n KemSK mlSource Auxiliary Value)
    (owners : State mlSource) (env : EnvState Auxiliary)
    (result : (Value × State mlSource) × EnvState Auxiliary)
    (supported : result ∈ support (((RegistrationNativeSecretWordOwners.executeLocal selected publicPrekey work).run owners).run env)) :
    Canonical selected publicPrekey result.1.2 := by
  simp only [RegistrationNativeSecretWordOwners.executeLocal, StateT.run] at supported
  have original := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ supported
  exact RegistrationNativePublicOwnerInvariant.executeLocal_canonical selected publicPrekey work owners env result original

/-- Terminal response processing retains the initialized scalar mask on both selected and ordinary owner paths. -/
theorem finish_canonical (setup : Setup base KemSK) (selected : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (index : Nat)
    (packet : Option registration.ResponsePacket) (owners : State mlSource) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × State mlSource) × EnvState Auxiliary)
    (valid : Canonical selected publicPrekey owners)
    (supported : result ∈ support (((RegistrationNativeSecretWordOwners.finish (n := n) setup mlSource index packet).run owners).run env)) :
    Canonical selected publicPrekey result.1.2 := by
  simp only [RegistrationNativeSecretWordOwners.finish, StateT.run] at supported
  cases found : owners[index]? with
  | none =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact valid
  | some owner =>
      rw [found, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      have original : inner ∈ support (((RegistrationNativeSecretWordBeaconCompiler.finish (n := n) setup mlSource packet).run owner.view).run env) := by
        cases scalarEq : owner.scalar with
        | none => simpa only [scalarEq, StateT.run] using reached
        | some scalar =>
            apply RegistrationNativePublicSourceSupport.simulate_support (RegistrationNativeSecretWordOwners.ordinary setup scalar)
            simpa only [scalarEq, StateT.run] using reached
      exact set_canonical selected publicPrekey owners index owner found valid inner.1.2
        (RegistrationNativeSecretWordOwnerFields.finish_prekey setup packet owner.view env inner original)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCanonical
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCanonical.executeLocal_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCanonical.executeLocal_canonical
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCanonical.finish_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCanonical.finish_canonical
