-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCountedPoolLookup
import BeaconcryptCore.Computational.RegistrationNativeMldsaShared

/-! Actual native trusted execution and the complete owner/Env lowering preserve the identical private pair at every existing KEM handle. Creation may append another row, while no public-key injectivity or private-row reconstruction is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemActualHandlePersistence
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

/-- The exact existing private pair survives every actually executed trusted request tree. -/
theorem trusted (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value)
    (before after : Native) (value : Value)
    (supported : (value, after) ∈ support ((simulateQ
      (RegistrationNativeExperiment.trusted setup checks representation created source) work).run before))
    (handle : Nat) (pair : PqxdhKemIndCca.MlKem768PublicKey × KemSK)
    (found : before.pool.keys[handle]? = some pair) : after.pool.keys[handle]? = some pair := by
  have interpreted : (value, RegistrationNativeKemCountedTrusted.project after) ∈ support
      ((RegistrationNativeKemCountedTrusted.execute setup
        (simulateQ (RegistrationNativeKemCountedTrusted.implementation setup checks representation created) work)).run
          (RegistrationNativeKemCountedTrusted.project before)) := by
    rw [RegistrationNativeKemCountedTrusted.program_source, support_map]
    exact ⟨_, supported, rfl⟩
  simp only [RegistrationNativeKemCountedTrusted.execute, StateT.run, support_map] at interpreted
  obtain ⟨⟨⟨actualValue, actualState⟩, actualPool⟩, ran, same⟩ := interpreted
  have poolEq : actualPool = after.pool := congrArg (fun result => result.2.2) same
  rw [← poolEq]
  exact RegistrationNativeKemCountedPoolLookup.program setup _ before.pool actualPool (actualValue, actualState) ran handle pair found

/-- Full actual owner/Env lowering preserves existing private pairs through authentication, collection and first-record stages. -/
theorem lower (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (before after : RegistrationNativeMldsaShared.Local n KemSK source) (value : Value)
    (supported : (value, after) ∈ support ((RegistrationNativeMldsaShared.lower setup checks representation created work).run before))
    (handle : Nat) (pair : PqxdhKemIndCca.MlKem768PublicKey × KemSK)
    (found : before.2.2.pool.keys[handle]? = some pair) : after.2.2.pool.keys[handle]? = some pair := by
  simp only [RegistrationNativeMldsaShared.lower, StateT.run, support_map] at supported
  obtain ⟨inner, called, returned⟩ := supported
  have stateEq : inner.2 = after.2.2 := congrArg (fun result => result.2.2.2) returned
  rw [← stateEq]
  exact trusted setup checks representation created _ before.2.2 inner.2 inner.1 called handle pair found

end BeaconcryptCore.Computational.RegistrationNativeKemActualHandlePersistence

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemActualHandlePersistence.trusted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemActualHandlePersistence.trusted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemActualHandlePersistence.lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemActualHandlePersistence.lower
