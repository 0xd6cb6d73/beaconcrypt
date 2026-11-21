-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerBuildPrefix
import BeaconcryptCore.Refinement.AdapterPublicServerAgreementPost
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The public source token is moved by value at build entry. Its already derived opaque token/slot relation identifies the exact native one-use capability, whose slot is cleared before any later normalization, pin, lookup or allocation. This adds only ownership bookkeeping around the original source receipt. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerBuildOwnership
open BeaconcryptCore.Computational
open AdapterPublicWrapperState AdapterPublicWrapperStorage
variable {n : Nat} {KemSK : Type} {mlSource : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource

def moved (handle : Nat) (before : Native) : Native :=
  {before with server := {before.server with sessions := before.server.sessions.set handle none}}

omit material platform ed in
private theorem set_none {A : Type} (values : List (Option A)) (handle : Nat) (token : A)
    (live : values[handle]? = some (some token)) : (values.set handle none)[handle]? = some none := by
  induction values generalizing handle with
  | nil => cases handle <;> simp at live
  | cons head tail ih =>
    cases handle with
    | zero => rfl
    | succ handle =>
      simp only [List.getElem?_cons_succ] at live
      simpa only [List.set_cons_succ, List.getElem?_cons_succ] using ih handle live

theorem material_retained (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : beaconcrypt_public_wrapper.server.Server) (before : Native)
    (related : Server view views created credential self before.server) (handle : Nat) :
    Server view views created credential self (moved handle before).server := by
  exact ⟨related.identity, related.control, related.pinIdentity, related.pinIdentifier, related.pinMldsa,
    related.replay, related.peers⟩

omit material platform ed in
theorem move (token : beaconcrypt_public_wrapper.server.RegistrationOutput) (consumed : peer.ConsumedRegistration)
    (before : Native) (handle : Nat) (related : Token token consumed)
    (live : before.server.sessions[handle]? = some (some consumed)) :
    RegistrationServerSdkSource.take handle before.server = (some token.registration, (moved handle before).server) ∧
    (moved handle before).server.sessions[handle]? = some none ∧
    RegistrationServerSdkSource.take handle (moved handle before).server = (none, (moved handle before).server) := by
  have cleared := set_none before.server.sessions handle consumed live
  refine ⟨?_, cleared, ?_⟩
  · rw [RegistrationServerSdkSource.take_live handle consumed before.server live, ← related.1]
    rfl
  · simp only [RegistrationServerSdkSource.take, moved, cleared]

variable {m : Type → Type} [Monad m]
variable {A : Type}
def entry (handle : Nat)
    (work : StateT (RegistrationNativePlatformCutJournal.State Native) m A) :
    StateT (RegistrationNativePlatformCutJournal.State Native) m A := fun before =>
  work (moved handle before.1, before.2)

omit material platform ed [Monad m] in
theorem entry_run (handle : Nat)
    (work : StateT (RegistrationNativePlatformCutJournal.State Native) m A)
    (before : RegistrationNativePlatformCutJournal.State Native) :
    (entry handle work).run before = work.run (moved handle before.1, before.2) := rfl

omit material platform ed in
theorem build_live
    (deriveAd : RegistrationNativePlatformCompletionSdk.AdHash n m)
    (pin : StateT (RegistrationServerFrontendCompiler.State n) m
      (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) m Bool)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) m Bool)
    (done : RegistrationNativePlatformCompletionSdk.Completion n m (alloc.vec.Vec U8))
    (token : beaconcrypt_public_wrapper.server.RegistrationOutput) (consumed : peer.ConsumedRegistration)
    (before : Native) (handle : Nat) (related : Token token consumed)
    (live : before.server.sessions[handle]? = some (some consumed)) (application : Slice U8) :
    (RegistrationNativePlatformCompletionSdk.build deriveAd pin reserve present done handle (some application)).run before.server =
      (RegistrationNativePlatformCompletionSdk.complete deriveAd pin reserve present done token.registration application).run (moved handle before).server := by
  unfold RegistrationNativePlatformCompletionSdk.build
  simp only [StateT.run]
  rw [(move token consumed before handle related live).1]

end BeaconcryptCore.Refinement.AdapterPublicServerBuildOwnership

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerBuildOwnership.material_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerBuildOwnership.material_retained

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerBuildOwnership.move' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerBuildOwnership.move

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerBuildOwnership.entry_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerBuildOwnership.entry_run

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerBuildOwnership.build_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerBuildOwnership.build_live
