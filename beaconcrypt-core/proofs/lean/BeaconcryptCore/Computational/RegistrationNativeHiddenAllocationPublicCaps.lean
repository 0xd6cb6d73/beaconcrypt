-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationRuntime

/-! The actual scalar-erasing public Beacon wrapper preserves the literal native non-append footprint, including its selected public prekey replacement and every stateful publication outcome. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationPublicCaps
open RegistrationNativeHiddenAllocationCore (Allowed mapped simulation)
variable {n : Nat} {KemSK Value : Type} {source : RegistrationNativeMldsa.Source}

/-- Executing a verified non-append native program through the real public owner wrapper adds no allocation request. -/
theorem native (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (before : RegistrationNativePublicFrontend.State source)
    (safe : RegistrationNativeHiddenBeaconAllocationCaps.Safe work) :
    AllQueriesSatisfy ((RegistrationNativePublicFrontend.beacon
      (RegistrationNativePublicOwners.executeLocal selected publicPrekey work)).run before) Allowed := by
  have actual : (RegistrationNativePublicFrontend.beacon (RegistrationNativePublicOwners.executeLocal selected publicPrekey work)).run before =
      (fun result => (result.1.1, { before with beacons := RegistrationNativePublicOwners.pack selected publicPrekey result.1.2, environment := result.2 })) <$>
        simulateQ RegistrationNativeHiddenAllocationRuntime.lift
          ((work.run (before.beacons.map RegistrationNativePublicOwners.restore)).run before.environment) := by
    simp only [RegistrationNativePublicFrontend.beacon, RegistrationNativePublicOwners.executeLocal, StateT.run,
      simulateQ_map, Functor.map_map, RegistrationNativeHiddenAllocationRuntime.lift, QueryImpl.simulateQ_compose]
  rw [actual]
  apply mapped
  exact simulation RegistrationNativeHiddenAllocationRuntime.lift
    (RegistrationNativeHiddenBeaconAllocationCaps.Allowed (KemSK := KemSK)) Allowed
    RegistrationNativeHiddenAllocationRuntime.lift_query _ (safe _ _)

end BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationPublicCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationPublicCaps.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationPublicCaps.native
