-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSuffix

/-! Successful preparation receives a genuine source-owned public identity. The receipt is derived from actual generated append and ordinary prekey execution, without key injectivity or a caller-supplied credential-success assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySourceOwnership
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityWorld (State implementation)
open RegistrationNativeIdentitySourceBirth (born credential)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- A fresh generated credential carries both its exact private indexed seed and the correlated public identity. -/
theorem born_owned (joint : PqxdhJointIdentity.Primitives) (before : State n KemSK)
    (value : PqxdhJointIdentity.IdentitySeed) :
    RegistrationNativeIdentityCallbacks.Owns joint (born joint before value).identities (credential joint before value) value := by
  refine ⟨?_, rfl⟩
  change (before.identities.seeds ++ [value])[before.identities.seeds.length]? = some value
  simp only [List.getElem?_append, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self, List.getElem?_cons_zero]

/-- Every supported successful identity/prekey source suffix returns its actually generated source-owned credential. -/
theorem suffix_owned (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (pin : session.ServerAuthenticationPin)
    (before after : State n KemSK) (prepared : RegistrationNativeIdentityFrontend.Prepared source)
    (supported : (.ok (some prepared), after) ∈ support
      ((simulateQ (implementation (mlSource := source) setup checks representation created)
        (RegistrationNativeIdentitySourceSuffix.exposed (source := source) pin)).run before)) :
    ∃ value, RegistrationNativeIdentityCallbacks.Owns setup.joint after.identities prepared.identity value := by
  simp only [RegistrationNativeIdentitySourceSuffix.exposed, simulateQ_bind, StateT.run_bind] at supported
  rw [RegistrationNativeIdentitySourceBirth.create_source, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨value, _drawn, continued⟩ := supported
  simp only [RegistrationNativeIdentitySourceSuffix.newSample, simulateQ_bind, StateT.run_bind,
    simulateQ_pure, StateT.run_pure] at continued
  rw [RegistrationNativeIdentitySourceFrame.ambient_program, bind_map_left, mem_support_bind_iff] at continued
  obtain ⟨scalar, _sampled, returned⟩ := continued
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, RustM.ok.injEq, Option.some.injEq] at returned
  obtain ⟨preparedEq, afterEq⟩ := returned
  subst prepared
  subst after
  exact ⟨value, born_owned setup.joint before value⟩

end BeaconcryptCore.Computational.RegistrationNativeIdentitySourceOwnership

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceOwnership.born_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceOwnership.born_owned
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceOwnership.suffix_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceOwnership.suffix_owned
