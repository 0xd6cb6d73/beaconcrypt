-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistoryRun
import BeaconcryptCore.Computational.RegistrationNativeGeneratedIdentityCollision

/-! Equal keys at distinct current Native owner positions are collisions in the same actual generated source pool. Ownership and distinct handles are discharged from the original initialized execution, with all failed constructors and callbacks retained. This is the source-index implication before the unchanged zero-query collision reduction; it introduces no public enrollment or key-injectivity premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeInitializedIdentityCollision
open PqxdhJointIdentity
open PqxdhDeploymentServerAuthInjective (Collision)
open RegistrationNativeIdentityRealization (Owned)
open RegistrationNativeIdentityHistorySync (Distinct)
variable {source : RegistrationNativeMldsa.Source}

/-- The existing private source invariant turns distinct owner positions with equal generated keys into a collision in its exact pool. -/
theorem owned_collision (joint : Primitives) (pool : PqxdhDynamicIdentityPool.SourceState)
    (owners : RegistrationNativeIdentityFrontend.State source)
    (owned : Owned joint pool owners) (distinct : Distinct owners)
    (first second : Nat) (different : first ≠ second)
    (left right : RegistrationNativeIdentityFrontend.Owner source)
    (leftAt : owners[first]? = some left) (rightAt : owners[second]? = some right)
    (same : left.identity.publicIdentity.ed25519 = right.identity.publicIdentity.ed25519) :
    Collision joint pool.seeds := by
  have credentialsOwned : ∀ credential ∈ owners.map (fun owner => owner.identity),
      ∃ seed, RegistrationNativeIdentityCallbacks.Owns joint pool credential seed := by
    intro credential member
    obtain ⟨owner, present, equal⟩ := List.mem_map.mp member
    subst credential
    exact owned owner present
  have handles : ((owners.map (fun owner => owner.identity)).map RegistrationNativeIdentityInterface.Credential.handle).Nodup := by
    simpa only [RegistrationNativeIdentityHistorySync.Distinct, RegistrationNativeIdentityHistorySync.handles,
      List.map_map, Function.comp_def] using distinct
  apply RegistrationNativeGeneratedIdentityCollision.credential_collision joint pool _ credentialsOwned handles
    first second different left.identity right.identity
  · simp only [List.getElem?_map, leftAt, Option.map_some]
  · simp only [List.getElem?_map, rightAt, Option.map_some]
  · exact same

/-- Reassembling the original native owners uses their exact privately stored seeds at the same generated indices. No equality of public bytes is used to identify an index. -/
theorem realized_collision (joint : Primitives) (pool : PqxdhDynamicIdentityPool.SourceState)
    (owners : RegistrationNativeIdentityFrontend.State source)
    (owned : Owned joint pool owners) (distinct : Distinct owners)
    (first second : Nat) (different : first ≠ second)
    (left right : RegistrationNativeBeaconFrontend.Owner source)
    (leftAt : (RegistrationNativeIdentityRealization.owners pool owners)[first]? = some left)
    (rightAt : (RegistrationNativeIdentityRealization.owners pool owners)[second]? = some right)
    (same : (joint.publicKeys left.identitySeed).ed25519 = (joint.publicKeys right.identitySeed).ed25519) :
    Collision joint pool.seeds := by
  simp only [RegistrationNativeIdentityRealization.owners, List.getElem?_map, Option.map_eq_some_iff] at leftAt rightAt
  obtain ⟨leftOwner, leftFound, leftSame⟩ := leftAt
  obtain ⟨rightOwner, rightFound, rightSame⟩ := rightAt
  have publicKey (owner : RegistrationNativeIdentityFrontend.Owner source) (member : owner ∈ owners) :
      joint.publicKeys (RegistrationNativeIdentityRealization.owner pool owner).identitySeed = owner.identity.publicIdentity := by
    obtain ⟨seed, stored⟩ := owned owner member
    change joint.publicKeys (RegistrationNativeIdentityRealization.seedFor pool owner.identity) = owner.identity.publicIdentity
    rw [RegistrationNativeIdentityRealization.seed_found pool owner.identity seed stored.1]
    exact stored.2.symm
  have leftKey := publicKey leftOwner (List.mem_of_getElem? leftFound)
  have rightKey := publicKey rightOwner (List.mem_of_getElem? rightFound)
  rw [← leftSame, ← rightSame, leftKey, rightKey] at same
  exact owned_collision joint pool owners owned distinct first second different leftOwner rightOwner leftFound rightFound same

/-- Every supported original-ledger execution from the actual empty initialization derives its own source ownership and distinct indices before transporting an owner-key collision. -/
theorem initialized_collision {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (context : RegistrationNativeIdentityWorld.Context n KemSK)
    (result : (Value × (RegistrationNativeLedger.State × RegistrationNativeIdentityMain.State n KemSK source)) ×
      PqxdhDynamicIdentityPool.SourceState)
    (supported : result ∈ support ((simulateQ (RegistrationNativeIdentityMainSource.implementation setup.joint)
      (RegistrationNativeIdentityMain.run setup checks wire route representation created credential bounds mode work
        ⟨context, []⟩)).run PqxdhDynamicIdentityPool.initialState))
    (first second : Nat) (different : first ≠ second)
    (left right : RegistrationNativeBeaconFrontend.Owner source)
    (leftAt : (RegistrationNativeIdentityMainSource.project (result.1.2.2, result.2)).beacons[first]? = some left)
    (rightAt : (RegistrationNativeIdentityMainSource.project (result.1.2.2, result.2)).beacons[second]? = some right)
    (same : (setup.joint.publicKeys left.identitySeed).ed25519 = (setup.joint.publicKeys right.identitySeed).ed25519) :
    Collision setup.joint result.2.seeds := by
  have invariant := RegistrationNativeIdentityMainHistoryRun.initialized_run_inv setup checks wire route representation created
    credential bounds mode work context result supported
  exact realized_collision setup.joint result.2 result.1.2.2.beacons invariant.1.1 invariant.1.2.1
    first second different left right leftAt rightAt same

end BeaconcryptCore.Computational.RegistrationNativeInitializedIdentityCollision

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitializedIdentityCollision.owned_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitializedIdentityCollision.owned_collision

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitializedIdentityCollision.realized_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitializedIdentityCollision.realized_collision

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitializedIdentityCollision.initialized_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitializedIdentityCollision.initialized_collision
