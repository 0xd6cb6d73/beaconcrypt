-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyEnvironment
import BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentJoint

/-! Physical owner allocation depends on the actual frontend roster, cursor and Protocol control. The selective service's additional private output cache does not enter this predicate. Its full state is retained in every execution; the projection below is used only to state the already operational allocation assertion. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocationJoint
variable {n : Nat} {KemSK ProviderState Secret : Type} {source : RegistrationNativeMldsa.Source}

abbrev State (n : Nat) (KemSK ProviderState Secret : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativeHiddenEnvironmentWorld.State n
    (RegistrationNativeSelectiveEntropyEnvironment.State n KemSK ProviderState source) Secret

def dropLocal (before : RegistrationNativeSelectiveEntropyEnvironment.State n KemSK ProviderState source) :
    RegistrationNativeHiddenEnvironment.State n KemSK ProviderState source := (before.1, before.2.1)

def drop (before : State n KemSK ProviderState Secret source) :
    RegistrationNativeHiddenEnvironmentJoint.State n KemSK ProviderState Secret source :=
  (((dropLocal before.1.1.1, before.1.1.2), before.1.2), before.2)

abbrev Holds (before : State n KemSK ProviderState Secret source) : Prop :=
  RegistrationNativeHiddenEnvironmentJoint.Holds (drop before)

/-- Every absent logical owner is physically absent in the same reached selective World. -/
theorem world_missing (before : State n KemSK ProviderState Secret source) (valid : Holds before)
    (index : Nat) (missing : before.1.1.1.1.beacons[index]? = none) : before.1.2.owners[index]? = none :=
  RegistrationNativeHiddenEnvironmentJoint.world_missing (drop before) valid index missing

/-- The unchanged cursor has no phantom owner at an absent logical index. -/
theorem cursor_missing (before : State n KemSK ProviderState Secret source) (valid : Holds before)
    (index : Nat) (missing : before.1.1.1.1.beacons[index]? = none) : before.1.1.2.owners index = none :=
  RegistrationNativeHiddenEnvironmentJoint.cursor_missing (drop before) valid index missing

end BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocationJoint
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocationJoint.world_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocationJoint.world_missing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocationJoint.cursor_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocationJoint.cursor_missing
