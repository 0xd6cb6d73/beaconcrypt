-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistorySync
import BeaconcryptCore.Computational.RegistrationNativeIdentityLifecycleOwned

/-! Source-history synchronization is an internal invariant of the actual indexed native execution. A captured outgoing owner is tied to its current generated handle; every source callback retains this tie and all generated ownership receipts. Ordinary effects may change the full native context and Env without changing the identity history. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryInvariant
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityFrontend (Owner)
open RegistrationNativeIdentityHistorySync
open RegistrationNativeIdentitySourceSimulation (NewState runNew liftAmbient)
variable {ι KemSK Auxiliary Value Other : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

def Holds (joint : PqxdhJointIdentity.Primitives) (pool : PqxdhDynamicIdentityPool.SourceState)
    (owners : RegistrationNativeIdentityFrontend.State source) : Prop :=
  RegistrationNativeIdentityRealization.Owned joint pool owners ∧ Distinct owners ∧ Synced pool owners

def At (index handle : Nat) (owners : RegistrationNativeIdentityFrontend.State source) : Prop :=
  (handles owners)[index]? = some handle

def Good (joint : PqxdhJointIdentity.Primitives) (index handle : Nat)
    (before : NewState n KemSK Auxiliary source) : Prop :=
  Holds joint before.2.identities before.1.1 ∧ At index handle before.1.1

def Preserves (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index handle : Nat)
    (work : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Value) : Prop :=
  ∀ before result, Good setup.joint index handle before →
    result ∈ support (runNew setup checks representation created work before) → Good setup.joint index handle result.2

theorem at_owner (index handle : Nat) (owners : RegistrationNativeIdentityFrontend.State source)
    (located : At index handle owners) : ∃ owner, owners[index]? = some owner ∧ owner.identity.handle = handle := by
  simp only [At, handles, List.getElem?_map, Option.map_eq_some_iff] at located
  exact located

theorem at_fields (index handle : Nat) (before after : RegistrationNativeIdentityFrontend.State source)
    (same : RegistrationNativeIdentityMetadata.keys after = RegistrationNativeIdentityMetadata.keys before)
    (prior : At index handle before) : At index handle after := by
  have projected := congrArg (List.map fun value => value.1.handle) same
  have equal : handles after = handles before := by
    simpa only [RegistrationNativeIdentityMetadata.keys, RegistrationNativeIdentityMetadata.key,
      handles, List.map_map, Function.comp_def] using projected
  change (handles after)[index]? = some handle
  rw [equal]
  exact prior

theorem pure_preserves (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index handle : Nat) (value : Value) :
    Preserves (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created index handle (pure value) := by
  intro before result prior supported
  simp only [runNew, StateT.run_pure, simulateQ_pure, map_pure, mem_support_pure_iff] at supported
  cases supported
  exact prior

theorem bind_preserves (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index handle : Nat)
    (work : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Value)
    (next : Value → RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Other)
    (first : Preserves setup checks representation created index handle work)
    (later : ∀ value, Preserves setup checks representation created index handle (next value)) :
    Preserves setup checks representation created index handle (work >>= next) := by
  intro before result prior supported
  rw [RegistrationNativeIdentitySourceSimulation.runNew_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact later middle.1 middle.2 result (first before middle prior reached) continued

theorem ambient_preserves (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index handle : Nat)
    (work : StateT (RegistrationWorldAgreementCompiler.EnvState Auxiliary)
      (OracleComp (RegistrationNativeIdentityFrontend.Ambient n KemSK)) Value) :
    Preserves (source := source) setup checks representation created index handle (liftAmbient work) := by
  intro before result prior supported
  rw [RegistrationNativeIdentitySourceSimulation.runNew_lift, support_map] at supported
  obtain ⟨middle, _, returned⟩ := supported
  cases returned
  exact prior

theorem fields_preserve (joint : PqxdhJointIdentity.Primitives) (index handle : Nat)
    (before after : NewState n KemSK Auxiliary source) (prior : Good joint index handle before)
    (fields : RegistrationNativeIdentityMetadata.keys after.1.1 = RegistrationNativeIdentityMetadata.keys before.1.1)
    (seeds : after.2.identities.seeds = before.2.identities.seeds)
    (synced : Synced after.2.identities after.1.1) : Good joint index handle after :=
  ⟨⟨RegistrationNativeIdentityLifecycleOwned.owned_after_fields joint _ _ _ _ prior.1.1 fields seeds,
    distinct_fields _ _ fields prior.1.2.1, synced⟩, at_fields index handle _ _ fields prior.2⟩

theorem fields_run (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Value)
    (metadata : RegistrationNativeIdentityMetadata.Preserves work)
    (before : NewState n KemSK Auxiliary source) (result : Value × NewState n KemSK Auxiliary source)
    (supported : result ∈ support (runNew setup checks representation created work before)) :
    RegistrationNativeIdentityMetadata.keys result.2.1.1 = RegistrationNativeIdentityMetadata.keys before.1.1 := by
  rw [runNew, support_map] at supported
  obtain ⟨inner, reached, equal⟩ := supported
  cases equal
  exact RegistrationNativeIdentityLifecycleOwned.source_metadata setup checks representation created work metadata
    before.1.1 before.1.2 before.2 inner.2 inner.1 reached

theorem phase_preserves (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index handle target : Nat)
    (phase : RegistrationNativeBeaconFrontend.Phase) :
    Preserves (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created index handle
      (RegistrationNativeIdentityFrontend.updatePhase target phase) := by
  intro before result prior supported
  have fields := fields_run setup checks representation created _
    (RegistrationNativeIdentityMetadata.phase_preserves target phase) before result supported
  simp only [runNew, RegistrationNativeIdentityFrontend.updatePhase, StateT.run_modify,
    StateT.run_pure, simulateQ_pure, map_pure, mem_support_pure_iff] at supported
  cases supported
  apply fields_preserve setup.joint index handle before _ prior
  · exact fields
  · rfl
  · cases found : before.1.1[target]? with
    | none => exact prior.1.2.2
    | some owner => exact phase_sync _ _ target owner phase found prior.1.2.2

end BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryInvariant

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryInvariant.at_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryInvariant.at_owner

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryInvariant.at_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryInvariant.at_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryInvariant.pure_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryInvariant.pure_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryInvariant.bind_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryInvariant.bind_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryInvariant.ambient_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryInvariant.ambient_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryInvariant.fields_preserve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryInvariant.fields_preserve

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryInvariant.fields_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryInvariant.fields_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryInvariant.phase_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryInvariant.phase_preserves
