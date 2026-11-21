-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3LocalKeys
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedOwners

/-! The actual selective private state has a literal product view separating only its private publication receipts from the key, provider and nonselected-output state. This is a bijection, not an erasure or a reset. The frontend's separate current environment receipts are outside this view. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedState
variable {n : Nat} {KemSK ProviderState : Type}

structure Core (n : Nat) (KemSK ProviderState : Type) where
  keys : RegistrationNativeHiddenService.State n
  pool : PqxdhLiveKemBirth.Pool KemSK
  provider : ProviderState
  known : RegistrationNativeSelectiveHiddenService.KnownOracle.QueryCache

abbrev View (n : Nat) (KemSK ProviderState : Type) :=
  RegistrationNativeG3MaterializedFrontend.State n (Core n KemSK ProviderState)

def view (before : RegistrationNativeG3LocalKeys.State n KemSK ProviderState) : View n KemSK ProviderState :=
  (⟨before.1.1.keys, before.1.1.pool, before.1.1.provider, before.1.2⟩, (before.1.1.receipts, before.2))

def restore (before : View n KemSK ProviderState) : RegistrationNativeG3LocalKeys.State n KemSK ProviderState :=
  ((⟨before.1.keys, before.1.pool, before.1.provider, before.2.1⟩, before.1.known), before.2.2)

/-- The product view retains every actual private and World field literally. -/
theorem restore_view (before : RegistrationNativeG3LocalKeys.State n KemSK ProviderState) : restore (view before) = before := rfl

/-- Every material/Common view is represented by exactly its restored actual state, including the complete receipt log. -/
theorem view_restore (before : View n KemSK ProviderState) : view (restore before) = before := rfl

def getKeys (before : Core n KemSK ProviderState) : RegistrationNativeSelectiveHiddenService.State n :=
  (before.keys, before.known)

def putKeys (before : Core n KemSK ProviderState) (keys : RegistrationNativeSelectiveHiddenService.State n) :
    Core n KemSK ProviderState := { before with keys := keys.1, known := keys.2 }

/-- Updating actual key-service state commutes with the receipt-separating view and preserves the full private receipt/World frame. -/
theorem view_putKeys (before : RegistrationNativeG3LocalKeys.State n KemSK ProviderState)
    (keys : RegistrationNativeSelectiveHiddenService.State n) :
    view (RegistrationNativeG3LocalKeys.putKeys before.1 keys, before.2) =
      (putKeys (view before).1 keys, (view before).2) := rfl

/-- The named accounting view changes only the corresponding World coordinate of this bijection. -/
theorem view_project (before : RegistrationNativeG3LocalKeys.State n KemSK ProviderState) :
    view (RegistrationNativeG3LocalKeys.project before) =
      ((view before).1, ((view before).2.1, RegistrationNativeG3MetricWorld.mask (view before).2.2)) := rfl
end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedState
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedState.restore_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedState.restore_view
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedState.view_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedState.view_restore
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedState.view_putKeys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedState.view_putKeys
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedState.view_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedState.view_project
