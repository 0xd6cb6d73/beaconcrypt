-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerRetainNative
import BeaconcryptCore.Computational.RegistrationNativePlatformExperiment
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
/-! The actual source reserved-set insertion maps to native one-use retention in the same arbitrary outer platform monad. Every complete Native coordinate and external platform state is retained; source RNG/private object values remain in the underlying SDK run. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerRetainPlatform
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {KemSK R : Type} {source : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
local notation "NativeM" => RegistrationNativePlatformExperiment.M n KemSK source m

omit material platform ed [LawfulMonad m] in
theorem native (coins : QueryImpl unifSpec m) (created : PqxdhLiveServerConstruction.Created Unit)
    (before : RegistrationNativeExperiment.State n KemSK source) (completed : agreement.ServerAgreement) :
    (RegistrationNativePlatformExperiment.liftNative coins
      (RegistrationNativeExperiment.server (RegistrationServerNativeSource.retain created completed))).run before =
      pure (.ok (AdapterPublicServerRetain.handle before.server completed),
        { before with server := AdapterPublicServerRetain.after before.server completed }) := by
  change simulateQ coins ((RegistrationNativeExperiment.server (RegistrationServerNativeSource.retain created completed)).run before) = _
  rw [AdapterPublicServerRetainNative.native, simulateQ_pure]

variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [containers : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source) m))]

theorem source_record (coins : QueryImpl unifSpec m) (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (views : AdapterPublicWrapperStorage.Views) (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential source) (self : beaconcrypt_public_wrapper.server.Server)
    (before : RegistrationNativeExperiment.State n KemSK source) (rng : R) (completed : agreement.ServerAgreement)
    (reply : Bool × AdapterPublicWrapperStorage.ReplaySet)
    (related : AdapterPublicWrapperState.Server view views created credential self before.server)
    (operation : AdapterPublicServerAcceptBody.setInsert (m := StateT (RegistrationNativeExperiment.State n KemSK source) m)
      self.consumed_registrations completed.pending.registration_id.bytes = pure reply)
    (footprint : AdapterPublicWrapperStorage.ReplayInsert views self.consumed_registrations completed.pending.registration_id.bytes reply) :
    AdapterPublicServerRetainNative.project completed <$>
      (((AdapterPublicServerAcceptBody.record (m := StateT (RegistrationNativeExperiment.State n KemSK source) m) self rng (.ServerComplete completed)).run).run before) =
      (RegistrationNativePlatformExperiment.liftNative coins
        (RegistrationNativeExperiment.server (RegistrationServerNativeSource.retain created completed))).run before := by
  have flag := AdapterPublicServerRetain.inserted_flag views self before.server completed reply related.replay footprint
  rw [AdapterPublicServerToken.record, operation, pure_bind, RustT.run_pure, StateT.run_pure, map_pure, native]
  rw [flag]
  cases present : before.server.consumed.contains (PqxdhRefinement.absBytes completed.pending.registration_id.bytes) <;>
    simp only [AdapterPublicServerToken.result, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      AdapterPublicServerRetainNative.project, AdapterPublicServerRetain.handle, AdapterPublicServerRetain.after,
      AdapterPublicWrapperStorage.inserted, present, ↓reduceIte]
end BeaconcryptCore.Refinement.AdapterPublicServerRetainPlatform

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerRetainPlatform.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerRetainPlatform.native

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerRetainPlatform.source_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerRetainPlatform.source_record
