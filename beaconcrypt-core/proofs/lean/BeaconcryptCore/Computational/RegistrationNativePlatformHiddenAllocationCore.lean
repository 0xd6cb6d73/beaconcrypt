-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyExecution
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationOwners
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationStartup
import BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursorWorld
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCore
open PqxdhServerAuthExperiment (Codec)
open RegistrationNativeHiddenEnvironmentWorld (lower)
open RegistrationNativeHiddenAllocationOwners (Indexed)
open RegistrationNativeHiddenAllocationCore (WorldAllowed)
variable {n : Nat} {KemSK Platform Private Reader Response Secret Value : Type} {source : RegistrationNativeMldsa.Source}
abbrev State (n : Nat) (Platform Private Secret : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativeHiddenEnvironmentWorld.State n (RegistrationNativePlatformPublicFrontend.State source Platform × Private) Secret

structure Holds (before : State n Platform Private Secret source) : Prop where
  length : before.1.2.owners.length = before.1.1.1.1.1.beacons.length
  indexed : Indexed before.1.1.1.1.1.beacons
  cursor : ∀ index, before.1.2.owners[index]? = none → before.1.1.2.owners index = none

/-- The actual missing public owner has no physical Protocol slot or cursor at the same reached state. -/
theorem missing (before : State n Platform Private Secret source) (valid : Holds before) (index : Nat)
    (absent : before.1.1.1.1.1.beacons[index]? = none) :
    before.1.2.owners[index]? = none ∧ before.1.1.2.owners index = none := by
  have physical : before.1.2.owners[index]? = none := by
    apply List.getElem?_eq_none_iff.mpr
    rw [valid.length]
    exact List.getElem?_eq_none_iff.mp absent
  exact ⟨physical, valid.cursor index physical⟩

def close (backend : QueryImpl (RegistrationNativePlatformPublicFrontend.Spec n KemSK)
    (StateT Private (OracleComp (PqxdhRecordLiftInterface.WorldSpec n))))
    (work : RegistrationNativePlatformPublicFrontend.M n KemSK Platform source Value) :
    StateT (RegistrationNativePlatformPublicFrontend.State source Platform × Private)
      (OracleComp (PqxdhRecordLiftInterface.WorldSpec n)) Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ backend (work.run before.1)).run before.2

/-- Arbitrary actual World lowering retains the literal source frontend output at its same source support point. -/
theorem local_support
    (backend : QueryImpl (RegistrationNativePlatformPublicFrontend.Spec n KemSK)
      (StateT Private (OracleComp (PqxdhRecordLiftInterface.WorldSpec n))))
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : RegistrationNativePlatformPublicFrontend.M n KemSK Platform source Value)
    (before : State n Platform Private Secret source) (result : Value × State n Platform Private Secret source)
    (supported : result ∈ support ((lower service codec route (close backend work)).run before)) :
    (result.1, result.2.1.1.1.1) ∈ support (work.run before.1.1.1.1) := by
  rw [RegistrationNativeHiddenEnvironmentWorld.lower_run, support_map] at supported
  obtain ⟨interpreted, reached, equal⟩ := supported
  have actual := RegistrationNativeHiddenAllocationStartup.interpreted_support service codec route _ _ _ _ interpreted reached
  simp only [close, StateT.run, support_map] at actual
  obtain ⟨native, possible, same⟩ := actual
  have original : native.1 ∈ support (work.run before.1.1.1.1) := by
    apply OracleComp.support_simulateQ_run'_subset backend _ before.1.1.1.2
    rw [StateT.run'_eq, support_map]
    exact ⟨native, possible, rfl⟩
  cases equal
  change (interpreted.1.1.1.1, interpreted.1.1.1.2.1) ∈ support (work.run before.1.1.1.1)
  rw [← same]
  exact original

/-- The physical cursor-domain invariant is supplied by the actual complete World lowering. -/
theorem completed
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : StateT (RegistrationNativePlatformPublicFrontend.State source Platform × Private)
      (OracleComp (PqxdhRecordLiftInterface.WorldSpec n)) Value)
    (before : State n Platform Private Secret source) (result : Value × State n Platform Private Secret source)
    (valid : Holds before) (supported : result ∈ support ((lower service codec route work).run before))
    (length : result.2.1.2.owners.length = result.2.1.1.1.1.1.beacons.length)
    (indexed : Indexed result.2.1.1.1.1.1.beacons) : Holds result.2 := by
  refine ⟨length, indexed, ?_⟩
  exact RegistrationNativeHiddenJointCursor.absent _ _
    (RegistrationNativeHiddenJointCursorWorld.lower_domain service codec route work before result supported
      (RegistrationNativeHiddenJointCursor.of_absent _ _ valid.cursor))

/-- Exact source metadata and the actual allocation-free World footprint derive the full new-platform allocation invariant. -/
theorem quiet
    (backend : QueryImpl (RegistrationNativePlatformPublicFrontend.Spec n KemSK)
      (StateT Private (OracleComp (PqxdhRecordLiftInterface.WorldSpec n))))
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : RegistrationNativePlatformPublicFrontend.M n KemSK Platform source Value)
    (before : State n Platform Private Secret source) (result : Value × State n Platform Private Secret source)
    (valid : Holds before)
    (footprint : AllQueriesSatisfy ((close backend work).run before.1.1.1) WorldAllowed)
    (localReceipt : ∀ output ∈ support (work.run before.1.1.1.1),
      output.2.1.beacons.length = before.1.1.1.1.1.beacons.length ∧ Indexed output.2.1.beacons)
    (supported : result ∈ support ((lower service codec route (close backend work)).run before)) : Holds result.2 := by
  have physical := RegistrationNativeHiddenAllocationWorld.noappend service codec route _ before result footprint supported
  have receipt := localReceipt (result.1, result.2.1.1.1.1)
    (local_support backend service codec route work before result supported)
  exact completed service codec route _ before result valid supported
    (physical.trans (valid.length.trans receipt.1.symm)) receipt.2

/-- Literal empty initialized rosters satisfy the new platform invariant without a private-key or owner-alias assumption. -/
theorem empty (before : State n Platform Private Secret source)
    (frontend : before.1.1.1.1.1.beacons = []) (physical : before.1.2.owners = [])
    (cursor : before.1.1.2.owners = fun _ => none) : Holds before := by
  refine ⟨by simp only [frontend, physical, List.length_nil], ?_, ?_⟩
  · rw [frontend]
    exact RegistrationNativeHiddenAllocationOwners.empty
  · intro index _
    rw [cursor]
end BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCore

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCore.missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCore.missing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCore.local_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCore.local_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCore.completed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCore.completed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCore.quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCore.quiet

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCore.empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCore.empty
