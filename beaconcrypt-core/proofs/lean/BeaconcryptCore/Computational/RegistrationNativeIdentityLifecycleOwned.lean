-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityLifecycleMetadata
import BeaconcryptCore.Computational.RegistrationNativeIdentityBundleRun
import BeaconcryptCore.Computational.RegistrationNativeIdentityFinishRun

/-! The initialized generated-credential invariant survives actual bundle and finish execution. Public metadata persistence and private seed-table persistence are both derived from the reached native execution, including failures. No key injectivity, caller honesty or invariant-preservation premise is added to the lifecycle endpoints. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityLifecycleOwned
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityWorld (State implementation)
open RegistrationNativeIdentityRealization (Owned)
open RegistrationWorldAgreementCompiler (EnvState)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

theorem owned_after_fields (joint : PqxdhJointIdentity.Primitives)
    (before after : PqxdhDynamicIdentityPool.SourceState)
    (current final : RegistrationNativeIdentityFrontend.State source)
    (prior : Owned joint before current)
    (metadata : RegistrationNativeIdentityMetadata.keys final = RegistrationNativeIdentityMetadata.keys current)
    (seeds : after.seeds = before.seeds) : Owned joint after final := by
  intro selected member
  have keyMember : RegistrationNativeIdentityMetadata.key selected ∈ RegistrationNativeIdentityMetadata.keys current := by
    rw [← metadata]
    exact List.mem_map.mpr ⟨selected, member, rfl⟩
  obtain ⟨original, originally, same⟩ := List.mem_map.mp keyMember
  have credential : selected.identity = original.identity := (congrArg Prod.fst same).symm
  obtain ⟨seed, receipt⟩ := prior original originally
  refine ⟨seed, ?_, ?_⟩
  · change after.seeds[selected.identity.handle]? = some seed
    rw [seeds, credential]
    exact receipt.1
  · change selected.identity.publicIdentity = joint.publicKeys seed
    rw [credential]
    exact receipt.2

theorem source_metadata (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Value)
    (metadata : RegistrationNativeIdentityMetadata.Preserves work)
    (current : RegistrationNativeIdentityFrontend.State source) (env : EnvState Auxiliary)
    (before after : State n KemSK) (result : (Value × RegistrationNativeIdentityFrontend.State source) × EnvState Auxiliary)
    (reached : (result, after) ∈ support
      ((simulateQ (implementation (mlSource := source) setup checks representation created) ((work.run current).run env)).run before)) :
    RegistrationNativeIdentityMetadata.keys result.1.2 = RegistrationNativeIdentityMetadata.keys current := by
  apply metadata current env result
  apply OracleComp.support_simulateQ_run'_subset (implementation (mlSource := source) setup checks representation created) _ before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst reached

theorem source_seeds (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Value)
    (keeps : RegistrationNativeIdentitySourceSimulation.Keeps setup checks representation created work)
    (current : RegistrationNativeIdentityFrontend.State source) (env : EnvState Auxiliary)
    (before after : State n KemSK) (result : (Value × RegistrationNativeIdentityFrontend.State source) × EnvState Auxiliary)
    (reached : (result, after) ∈ support
      ((simulateQ (implementation (mlSource := source) setup checks representation created) ((work.run current).run env)).run before)) :
    after.identities.seeds = before.identities.seeds := by
  apply keeps ((current, env), before) (result.1.1, ((result.1.2, result.2), after))
  simp only [RegistrationNativeIdentitySourceSimulation.runNew, support_map]
  exact Set.mem_image_of_mem _ reached

/-- Every reached actual bundle result retains the generated source ownership of every current owner. -/
theorem bundle_owned (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (current : RegistrationNativeIdentityFrontend.State source) (env : EnvState Auxiliary)
    (before after : State n KemSK)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativeIdentityFrontend.State source) × EnvState Auxiliary)
    (prior : Owned setup.joint before.identities current)
    (reached : (result, after) ∈ support
      ((simulateQ (implementation (mlSource := source) setup checks representation created)
        (((RegistrationNativeIdentityFrontend.bundle setup source wire index).run current).run env)).run before)) :
    Owned setup.joint after.identities result.1.2 :=
  owned_after_fields setup.joint before.identities after.identities current result.1.2 prior
    (source_metadata setup checks representation created _ (RegistrationNativeIdentityLifecycleMetadata.bundle_preserves setup wire index)
      current env before after result reached)
    (source_seeds setup checks representation created _ (RegistrationNativeIdentityBundleRun.bundle_keeps setup checks representation created wire index)
      current env before after result reached)

/-- Abort-before-admission, every optional failure, and successful record installation preserve actual generated identity ownership. -/
theorem finish_owned (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (packet : Option registration.ResponsePacket)
    (current : RegistrationNativeIdentityFrontend.State source) (env : EnvState Auxiliary)
    (before after : State n KemSK)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativeIdentityFrontend.State source) × EnvState Auxiliary)
    (prior : Owned setup.joint before.identities current)
    (reached : (result, after) ∈ support
      ((simulateQ (implementation (mlSource := source) setup checks representation created)
        (((RegistrationNativeIdentityFrontend.finish setup source wire index packet).run current).run env)).run before)) :
    Owned setup.joint after.identities result.1.2 :=
  owned_after_fields setup.joint before.identities after.identities current result.1.2 prior
    (source_metadata setup checks representation created _ (RegistrationNativeIdentityLifecycleMetadata.finish_preserves setup wire index packet)
      current env before after result reached)
    (source_seeds setup checks representation created _ (RegistrationNativeIdentityFinishRun.finish_keeps setup checks representation created wire index packet)
      current env before after result reached)

end BeaconcryptCore.Computational.RegistrationNativeIdentityLifecycleOwned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityLifecycleOwned.owned_after_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityLifecycleOwned.owned_after_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityLifecycleOwned.source_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityLifecycleOwned.source_metadata

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityLifecycleOwned.source_seeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityLifecycleOwned.source_seeds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityLifecycleOwned.bundle_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityLifecycleOwned.bundle_owned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityLifecycleOwned.finish_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityLifecycleOwned.finish_owned
