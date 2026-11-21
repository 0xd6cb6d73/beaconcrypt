-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceHashBounds
/-! The actual opaque-owner source interpreter forwards only explicit Env hashes into the one shared physical CTX branch. Independent native/KEM/platform coins and indexed identity operations remain in their original protocol branches and have zero shared hash cost. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFrontendHashBounds
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityWorld (Context)
open RegistrationNativePlatformIdentityCtxBackend (IsHash)
open RegistrationNativePlatformIdentityCtxHashBoundsCore (Bounded backend_bound)
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private theorem coin_bound {Value : Type} (work : ProbComp Value) :
    (simulateQ RegistrationNativePlatformCtxBackend.coin work).IsQueryBoundP
      RegistrationNativePlatformCtxBirthdayBudget.IsHash 0 := by
  apply (isQueryBoundP_false work 0).simulateQ_of_step (fun _ impossible => impossible.elim)
  intro query _
  simp [RegistrationNativePlatformCtxBackend.coin, RegistrationNativePlatformCtxBirthdayBudget.IsHash]

/-- Each literal Env operation forwards exactly its syntactic hash charge through the physical Context lens. -/
theorem effect_bound (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (before : Context n KemSK) :
    ((RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created (.inl query)).run before).IsQueryBoundP
      RegistrationNativePlatformCtxBirthdayBudget.IsHash
      (if RegistrationNativePlatformIdentityFrontendHashBounds.IsHash (KemSK := KemSK) (.inl (.inl query)) then 1 else 0) := by
  cases query with
  | inl query =>
    simp only [RegistrationNativePlatformIdentityCtxAmbient.program, RegistrationNativePlatformIdentityCtxAmbient.world,
      RegistrationNativePlatformCtxEffects.program, StateT.run, isQueryBoundP_map_iff,
      RegistrationNativePlatformIdentityFrontendHashBounds.IsHash, ite_false]
    exact coin_bound _
  | inr query =>
    cases query <;>
      simp only [RegistrationNativePlatformIdentityCtxAmbient.program, RegistrationNativePlatformIdentityCtxAmbient.world,
        RegistrationNativePlatformCtxEffects.program, StateT.run, isQueryBoundP_map_iff,
        RegistrationNativePlatformIdentityFrontendHashBounds.IsHash, ite_false, ite_true]
    all_goals first
      | exact coin_bound _
      | simp [RegistrationNativePlatformCtxBackend.hash, RegistrationNativePlatformCtxBirthdayBudget.IsHash]

/-- The literal source compiler charges one shared hash only for an Env hash query. -/
theorem query_bound (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (RegistrationNativePlatformIdentityProgram.Spec n KemSK).Domain) (before : Context n KemSK) :
    ((RegistrationNativePlatformIdentityCtxCompiler.free
      (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created) query).run before).IsQueryBoundP IsHash
      (if RegistrationNativePlatformIdentitySourceHashBounds.IsHash (KemSK := KemSK) query then 1 else 0) := by
  cases query with
  | inl query =>
      simp [RegistrationNativePlatformIdentityCtxCompiler.free, RegistrationNativePlatformIdentityCtxCompiler.implementation,
        RegistrationNativePlatformIdentityCtxCompiler.coins, StateT.run, IsHash, RegistrationNativePlatformIdentitySourceHashBounds.IsHash]
  | inr query => cases query with
    | inl query => cases query with
      | inl query => exact backend_bound _ _ (effect_bound setup checks representation created query before)
      | inr query =>
        apply backend_bound
        exact coin_bound _
    | inr query =>
      cases query <;> simp [RegistrationNativePlatformIdentityCtxCompiler.free, RegistrationNativePlatformIdentityCtxCompiler.implementation,
        RegistrationNativePlatformIdentityCtxCompiler.joint, StateT.run, IsHash,
        RegistrationNativePlatformIdentitySourceHashBounds.IsHash, RegistrationNativePlatformIdentityFrontendHashBounds.IsHash]

/-- Arbitrary source scripts preserve their exact shared hash caps through actual Context compilation. -/
theorem program_bound (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : OracleComp (RegistrationNativePlatformIdentityProgram.Spec n KemSK) A) (cap : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativePlatformIdentitySourceHashBounds.IsHash (KemSK := KemSK)) cap)
    (before : Context n KemSK) :
    ((simulateQ (RegistrationNativePlatformIdentityCtxCompiler.free
      (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created)) work).run before).IsQueryBoundP IsHash cap :=
  bounded.simulateQ_run_StateT_of_step (query_bound setup checks representation created) before

/-- Closing all owner/Env/Main/P state keeps the same literal source cap. -/
theorem beacon_bound (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativePlatformIdentityProgram.M n KemSK RegistrationServerRoleBackend.State Platform source A)
    (cap : Nat) (bounded : RegistrationNativePlatformIdentitySourceHashBounds.Bounded work cap) :
    Bounded (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created work) cap := by
  intro before
  simp only [RegistrationNativePlatformIdentityCtxMain.beacon, RegistrationNativePlatformIdentityCtxCompiler.beacon,
    StateT.run, isQueryBoundP_map_iff]
  exact program_bound setup checks representation created _ cap
    (bounded before.1.beacons (RegistrationWorldAgreementCompiler.erase before.1.context.server.world) before.2) before.1.context
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFrontendHashBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFrontendHashBounds.effect_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFrontendHashBounds.effect_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFrontendHashBounds.query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFrontendHashBounds.query_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFrontendHashBounds.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFrontendHashBounds.program_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFrontendHashBounds.beacon_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFrontendHashBounds.beacon_bound
