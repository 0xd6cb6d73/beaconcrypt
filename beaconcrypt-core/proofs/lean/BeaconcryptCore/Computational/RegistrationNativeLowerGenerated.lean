-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeGeneratedPath
import BeaconcryptCore.Computational.RegistrationNativeStagedRootAgreement

/-! Native lowering preserves the generated private rows of every previously reached owner even while the separate local owner phase changes. This supplies captured-owner provenance at actual authentication/agreement cuts without pretending that the old phase remains in the mutable roster. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeLowerGenerated
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner M)
open RegistrationNativeMldsaShared (Local lower)
variable {n : Nat} {ι KemSK V : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- Every lowered actual subprogram preserves honest private-key rows for a fixed prior owner list, independently of its current local phases. -/
theorem lower_holds (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (owners : List (Owner source)) (work : M n KemSK source RegistrationServerRoleBackend.State V)
    (before after : Local n KemSK source) (reply : V)
    (prior : RegistrationNativeKemBirthInvariant.Holds setup owners before.2.2.pool)
    (supported : (reply, after) ∈ support ((lower setup checks representation created work).run before)) :
    RegistrationNativeKemBirthInvariant.Holds setup owners after.2.2.pool := by
  simp only [lower, StateT.run, support_map] at supported
  obtain ⟨inner, called, returned⟩ := supported
  have preserved := RegistrationNativeKemBirthInvariant.trusted_program setup checks representation created source owners
    _ before.2.2 inner.2 inner.1 prior called
  have nativeEq : inner.2 = after.2.2 := congrArg (fun value => value.2.2.2) returned
  exact nativeEq ▸ preserved

/-- A captured earlier owner retains its exact honestly generated row at every reached lowered cut, including after its phase has already been consumed. -/
theorem owner (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (owners : List (Owner source)) (selected : Owner source) (member : selected ∈ owners)
    (work : M n KemSK source RegistrationServerRoleBackend.State V) (before after : Local n KemSK source) (reply : V)
    (prior : RegistrationNativeKemBirthInvariant.Holds setup owners before.2.2.pool)
    (supported : (reply, after) ∈ support ((lower setup checks representation created work).run before)) :
    RegistrationNativeKemBirthPool.Generated setup.baseImpl setup.kem after.2.2.pool ∧
      ∃ pair, after.2.2.pool.keys[selected.kemHandle]? = some pair ∧ pair.1 = selected.kemPublic := by
  have reached := lower_holds setup checks representation created owners work before after reply prior supported
  exact ⟨reached.1, reached.2 selected member⟩

end BeaconcryptCore.Computational.RegistrationNativeLowerGenerated

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLowerGenerated.lower_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLowerGenerated.lower_holds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLowerGenerated.owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLowerGenerated.owner
