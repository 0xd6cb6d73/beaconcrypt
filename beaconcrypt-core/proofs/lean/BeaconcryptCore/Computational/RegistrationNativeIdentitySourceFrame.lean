-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityWorld

/-! Ordinary native primitive programs share the original public World/KEM context while the indexed identity pool stays private and unchanged. This frame law is derived from the concrete source query interpreter and applies to complete adaptive programs. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySourceFrame
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityWorld (Context State implementation ambient)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

/-- An arbitrary ordinary native program retains the private generated-identity pool and the same complete public context. -/
theorem ambient_program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Aeneas.Std.Array Aeneas.Std.U8 151#usize))
    (work : OracleComp (RegistrationNativeIdentityFrontend.Ambient n KemSK) Value)
    (before : State n KemSK) :
    (simulateQ (implementation (mlSource := source) setup checks representation created)
      (simulateQ RegistrationNativeIdentityFrontend.ambientLift work)).run before =
      (fun result => (result.1, (⟨result.2, before.identities⟩ : State n KemSK))) <$>
        (simulateQ (ambient (mlSource := source) setup checks representation created) work).run before.context := by
  rw [← QueryImpl.simulateQ_compose]
  let embed : Context n KemSK → State n KemSK := fun current => ⟨current, before.identities⟩
  have step (query : (RegistrationNativeIdentityFrontend.Ambient n KemSK).Domain) (current : Context n KemSK) :
      Prod.map id embed <$>
        (ambient (mlSource := source) setup checks representation created query).run current =
      ((implementation (mlSource := source) setup checks representation created ∘ₛ
        RegistrationNativeIdentityFrontend.ambientLift) query).run (embed current) := by
    simp only [QueryImpl.apply_compose, RegistrationNativeIdentityFrontend.ambientLift,
      simulateQ_spec_query, implementation, embed, Prod.map_def, id_eq]
    rfl
  simpa only [embed, Prod.map_def, id_eq] using
    (OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ embed step work before.context).symm

end BeaconcryptCore.Computational.RegistrationNativeIdentitySourceFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceFrame.ambient_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceFrame.ambient_program
