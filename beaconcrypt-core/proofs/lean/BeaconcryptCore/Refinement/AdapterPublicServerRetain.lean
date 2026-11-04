-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerToken
import BeaconcryptCore.Refinement.AdapterPublicServerAgreementMaterial
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
/-! Actual source replay insertion and native one-use session creation agree under the reserved-set insertion footprint. Earlier allocation and agreement effects remain in their actual shared state. The token retains the exact private agreement. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerRetain
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable {n : Nat}
def after (before : RegistrationServerFrontendCompiler.State n) (completed : agreement.ServerAgreement) :
    RegistrationServerFrontendCompiler.State n :=
  { before with
    consumed := AdapterPublicWrapperStorage.inserted before.consumed completed.pending.registration_id.bytes,
    sessions := if before.consumed.contains (PqxdhRefinement.absBytes completed.pending.registration_id.bytes) then before.sessions
      else before.sessions ++ [some ⟨completed⟩] }
def handle (before : RegistrationServerFrontendCompiler.State n) (completed : agreement.ServerAgreement) : Option Nat :=
  if before.consumed.contains (PqxdhRefinement.absBytes completed.pending.registration_id.bytes) then none
  else some before.sessions.length

omit material platform primitive in
theorem native (created : PqxdhLiveServerConstruction.Created Unit)
    (before : RegistrationServerFrontendCompiler.State n) (completed : agreement.ServerAgreement) :
    (RegistrationServerNativeSource.retain created completed).run before = pure (.ok (handle before completed), after before completed) := by
  unfold RegistrationServerNativeSource.retain RegistrationServerNativeSource.sourceStep
    RegistrationWorldServerFrontend.retain StateT.run
  dsimp only [StateT.run, RegistrationServerFrontendCompiler.restore]
  cases present : before.consumed.contains (PqxdhRefinement.absBytes completed.pending.registration_id.bytes) with
  | false =>
    rw [RegistrationReplaySchedule.consume_fresh completed before.consumed present]
    simp only [map_pure, handle, after, AdapterPublicWrapperStorage.inserted, present, Bool.false_eq_true, ↓reduceIte]
    rfl
  | true =>
    rw [RegistrationReplaySchedule.consume_replayed completed before.consumed present]
    simp only [map_pure, handle, after, AdapterPublicWrapperStorage.inserted, present, ↓reduceIte]
    rfl

variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
variable [PublicWrapperPlatform.ContainerOperations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [containers : ContainerOperations (RustT m)]
variable {mldsaSource : RegistrationNativeMldsa.Source} {KemSK : Type}
omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem inserted_flag (views : AdapterPublicWrapperStorage.Views)
    (self : beaconcrypt_public_wrapper.server.Server) (before : RegistrationServerFrontendCompiler.State n)
    (completed : agreement.ServerAgreement) (reply : Bool × AdapterPublicWrapperStorage.ReplaySet)
    (related : AdapterPublicWrapperStorage.ReplayRelated views self.consumed_registrations before.consumed)
    (footprint : AdapterPublicWrapperStorage.ReplayInsert views self.consumed_registrations completed.pending.registration_id.bytes reply) :
    reply.1 = !before.consumed.contains (PqxdhRefinement.absBytes completed.pending.registration_id.bytes) := by
  rw [footprint.1]
  congr 1
  apply Bool.eq_iff_iff.mpr
  exact (related _).trans (by simp)

theorem source {R : Type} (view : AdapterPublicWrapperState.MaterialView mldsaSource KemSK)
    (views : AdapterPublicWrapperStorage.Views) (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential mldsaSource) (self : beaconcrypt_public_wrapper.server.Server)
    (before : RegistrationServerFrontendCompiler.State n) (rng : R) (completed : agreement.ServerAgreement)
    (reply : Bool × AdapterPublicWrapperStorage.ReplaySet)
    (related : AdapterPublicWrapperState.Server view views created credential self before)
    (operation : AdapterPublicServerAcceptBody.setInsert (m := m) self.consumed_registrations completed.pending.registration_id.bytes = pure reply)
    (footprint : AdapterPublicWrapperStorage.ReplayInsert views self.consumed_registrations completed.pending.registration_id.bytes reply) :
    AdapterPublicServerAcceptBody.record (m := m) self rng (.ServerComplete completed) =
      pure (AdapterPublicServerToken.result self rng completed reply.1 reply.2) ∧
    AdapterPublicWrapperState.Server view views created credential
      { self with consumed_registrations := reply.2 } (after before completed) := by
  constructor
  · rw [AdapterPublicServerToken.record, operation, pure_bind]
  · have updated := AdapterPublicWrapperState.replay_inserted view views created credential self before related
      completed.pending.registration_id.bytes reply footprint
    exact ⟨updated.identity, updated.control, updated.pinIdentity, updated.pinIdentifier, updated.pinMldsa,
      updated.replay, updated.peers⟩

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem token {R : Type} (self : beaconcrypt_public_wrapper.server.Server) (rng : R)
    (before : RegistrationServerFrontendCompiler.State n) (completed : agreement.ServerAgreement)
    (reply : Bool × AdapterPublicWrapperStorage.ReplaySet)
    (flag : reply.1 = !before.consumed.contains (PqxdhRefinement.absBytes completed.pending.registration_id.bytes)) :
    match (AdapterPublicServerToken.result self rng completed reply.1 reply.2).1, handle before completed with
    | .None, none => True
    | .Some token, some index => AdapterPublicWrapperState.Token token ⟨completed⟩ ∧
        (after before completed).sessions[index]? = some (some ⟨completed⟩)
    | _, _ => False := by
  rw [flag]
  cases present : before.consumed.contains (PqxdhRefinement.absBytes completed.pending.registration_id.bytes) <;>
    simp only [AdapterPublicServerToken.result, handle, after, present, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte]
  · exact ⟨⟨rfl, rfl⟩, by simp⟩
end BeaconcryptCore.Refinement.AdapterPublicServerRetain

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerRetain.native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerRetain.native

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerRetain.inserted_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerRetain.inserted_flag

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerRetain.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerRetain.source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerRetain.token' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerRetain.token
