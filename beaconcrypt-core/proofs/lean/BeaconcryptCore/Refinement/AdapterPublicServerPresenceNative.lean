-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerCompletionFrame
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The concrete native peer-presence request has exactly the readonly source map-membership reply under the existing Server material relation. Its sole additional state change is the chronological administrative charge at that actual source request cut. No map mutation, codec law or controller conclusion is assumed. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerPresenceNative
open BeaconcryptCore.Computational
open AdapterPublicWrapperState AdapterPublicWrapperStorage
variable {n : Nat} {KemSK : Type} {mlSource : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]

def charged (before : RegistrationServerFrontendCompiler.State n) (identifier : U64) : RegistrationServerFrontendCompiler.State n :=
  {before with world := {before.world with world :=
    (PqxdhRecordLiftWorld.chargeEffect (.inr (.peerPresent identifier)) before.world.world.1, before.world.world.2)}}

theorem material_related (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : beaconcrypt_public_wrapper.server.Server) (before : RegistrationServerFrontendCompiler.State n)
    (related : Server view views created credential self before) (identifier : U64) :
    Server view views created credential self (charged before identifier) := by
  exact ⟨related.identity, related.control, related.pinIdentity, related.pinIdentifier, related.pinMldsa, related.replay, related.peers⟩

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem source (coins : QueryImpl unifSpec m)
    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : beaconcrypt_public_wrapper.server.Server) (before : RegistrationServerFrontendCompiler.State n)
    (related : Server view views created credential self before) (identifier : U64) :
    (RegistrationNativePlatformCompletionSdk.nativePresent coins identifier).run before =
      pure ((views.peer self.known_ids identifier).isSome, charged before identifier) := by
  rcases related.peers with ⟨records, reached, _sender, _identity, peers⟩
  change (fun result => (result.1, {before with world := result.2})) <$>
    simulateQ coins ((RegistrationWorldServerCompletion.capability (.peerPresent identifier)).run before.world) = _
  have computed : (RegistrationWorldServerCompletion.capability (.peerPresent identifier)).run before.world =
      pure ((before.world.world.1.server.bind fun server => server.records.server.peers identifier).isSome,
        {before.world with world := (PqxdhRecordLiftWorld.chargeEffect (.inr (.peerPresent identifier)) before.world.world.1, before.world.world.2)}) := rfl
  rw [computed, simulateQ_pure, map_pure, reached, Option.bind_some, ← (peers identifier).2]
  rfl

theorem readonly (coins : QueryImpl unifSpec m)
    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : beaconcrypt_public_wrapper.server.Server) (before : RegistrationServerFrontendCompiler.State n)
    (related : Server view views created credential self before) (identifier : U64) :
    Prod.fst <$> (RegistrationNativePlatformCompletionSdk.nativePresent coins identifier).run before =
      pure ((views.peer self.known_ids identifier).isSome) := by
  rw [source coins view views created credential self before related identifier, map_pure]
end BeaconcryptCore.Refinement.AdapterPublicServerPresenceNative
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerPresenceNative.material_related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerPresenceNative.material_related
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerPresenceNative.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerPresenceNative.source
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerPresenceNative.readonly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerPresenceNative.readonly
