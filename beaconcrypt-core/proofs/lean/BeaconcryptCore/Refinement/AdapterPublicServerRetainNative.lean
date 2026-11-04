-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerRetain
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
/-! The actual source replay-insertion result determines the native one-use handle and private session. The projection uses the actual returned token and the reached registration identifier, preserves the complete Native state, and forgets only the source representation and caller RNG. Those values remain in the original supported source run. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerRetainNative
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {KemSK R : Type} {source : RegistrationNativeMldsa.Source}

noncomputable def project (completed : agreement.ServerAgreement)
    (result : RustM (core.option.Option beaconcrypt_public_wrapper.server.RegistrationOutput × beaconcrypt_public_wrapper.server.Server × R) ×
      RegistrationNativeExperiment.State n KemSK source) :
    RustM (Option Nat) × RegistrationNativeExperiment.State n KemSK source :=
  match result.1 with
  | .fail error => (.fail error, result.2)
  | .div => (.div, result.2)
  | .ok (token, _, _) =>
      let history := AdapterPublicWrapperStorage.inserted result.2.server.consumed completed.pending.registration_id.bytes
      match token with
      | .None => (.ok none, { result.2 with server := { result.2.server with consumed := history } })
      | .Some token => (.ok (some result.2.server.sessions.length), { result.2 with server :=
          { result.2.server with consumed := history, sessions := result.2.server.sessions ++ [some token.registration] } })

omit material platform ed in
theorem native (created : PqxdhLiveServerConstruction.Created Unit)
    (before : RegistrationNativeExperiment.State n KemSK source) (completed : agreement.ServerAgreement) :
    (RegistrationNativeExperiment.server (RegistrationServerNativeSource.retain created completed)).run before =
      pure (.ok (AdapterPublicServerRetain.handle before.server completed),
        { before with server := AdapterPublicServerRetain.after before.server completed }) := by
  change (fun result => (result.1, { before with server := result.2 })) <$>
    (RegistrationServerNativeSource.retain created completed).run before.server = _
  rw [AdapterPublicServerRetain.native, map_pure]

variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [containers : ContainerOperations (RustT (RegistrationNativeExperiment.M n KemSK source))]

theorem source_record (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (views : AdapterPublicWrapperStorage.Views) (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential source) (self : beaconcrypt_public_wrapper.server.Server)
    (before : RegistrationNativeExperiment.State n KemSK source) (rng : R) (completed : agreement.ServerAgreement)
    (reply : Bool × AdapterPublicWrapperStorage.ReplaySet)
    (related : AdapterPublicWrapperState.Server view views created credential self before.server)
    (operation : AdapterPublicServerAcceptBody.setInsert (m := RegistrationNativeExperiment.M n KemSK source)
      self.consumed_registrations completed.pending.registration_id.bytes = pure reply)
    (footprint : AdapterPublicWrapperStorage.ReplayInsert views self.consumed_registrations completed.pending.registration_id.bytes reply) :
    project completed <$>
      (((AdapterPublicServerAcceptBody.record (m := RegistrationNativeExperiment.M n KemSK source)
        self rng (.ServerComplete completed)).run).run before) =
      (RegistrationNativeExperiment.server (RegistrationServerNativeSource.retain created completed)).run before := by
  have flag := AdapterPublicServerRetain.inserted_flag views self before.server completed reply related.replay footprint
  rw [AdapterPublicServerToken.record, operation, pure_bind, RustT.run_pure, StateT.run_pure, map_pure, native]
  rw [flag]
  cases present : before.server.consumed.contains (PqxdhRefinement.absBytes completed.pending.registration_id.bytes) <;>
    simp only [AdapterPublicServerToken.result, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      project, AdapterPublicServerRetain.handle, AdapterPublicServerRetain.after,
      AdapterPublicWrapperStorage.inserted, present, ↓reduceIte]
end BeaconcryptCore.Refinement.AdapterPublicServerRetainNative

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerRetainNative.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerRetainNative.native

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerRetainNative.source_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerRetainNative.source_record
