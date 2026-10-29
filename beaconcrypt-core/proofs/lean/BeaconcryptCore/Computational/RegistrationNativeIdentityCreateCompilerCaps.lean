-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMain
import BeaconcryptCore.Computational.RegistrationNativeIdentityBirthCaps

/-! The actual opaque-identity compiler preserves the indexed identity-creation bill. Ordinary World and KEM work adds only local source randomness; each trusted Ed-create request forwards exactly one ordinary dynamic create request. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCreateCompilerCaps
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityBirthCaps (Creates)
open PqxdhDynamicIdentityPool (DynamicSpec IsCreate)
open PqxdhJointPhase1Reports (SourceClass ProtocolSpec)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

theorem dynamic_coins_zero (work : ProbComp Value) :
    (simulateQ RegistrationNativeIdentityCompiler.coins work).IsQueryBoundP IsCreate 0 := by
  apply OracleComp.IsQueryBoundP.simulateQ_of_step (OracleComp.isQueryBoundP_false work 0)
    (fun _ impossible => impossible.elim)
  intro query _
  simp [RegistrationNativeIdentityCompiler.coins, IsCreate, isQueryBoundP_query_iff]

theorem query_bound (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (query : (RegistrationNativeIdentityFrontend.Trusted n KemSK).Domain)
    (before : RegistrationNativeIdentityWorld.Context n KemSK) :
    ((RegistrationNativeIdentityCompiler.implementation (source := source) setup checks representation created query).run before).IsQueryBoundP
      IsCreate (if Creates n KemSK query then 1 else 0) := by
  cases query with
  | inl query => exact dynamic_coins_zero _
  | inr query => cases query with
    | create =>
        simp only [RegistrationNativeIdentityCompiler.implementation, StateT.run, bind_pure_comp,
          isQueryBoundP_map_iff, Creates, RegistrationNativeIdentityNoCreate.Allowed, not_false_eq_true, ite_true]
        simp [IsCreate, isQueryBoundP_query_iff]
    | service handle request | reveal handle =>
        simp only [RegistrationNativeIdentityCompiler.implementation, StateT.run_lift, bind_pure_comp,
          isQueryBoundP_map_iff, Creates, RegistrationNativeIdentityNoCreate.Allowed, not_true_eq_false, ite_false]
        simp [IsCreate, isQueryBoundP_query_iff]

/-- The complete actual stateful compiler preserves a trusted-AST creation cap for every initial public context. -/
theorem program_bound (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : OracleComp (RegistrationNativeIdentityFrontend.Trusted n KemSK) Value) (cap : Nat)
    (bounded : work.IsQueryBoundP (Creates n KemSK) cap) (before : RegistrationNativeIdentityWorld.Context n KemSK) :
    ((simulateQ (RegistrationNativeIdentityCompiler.implementation (source := source) setup checks representation created) work).run before).IsQueryBoundP
      IsCreate cap :=
  OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step bounded (fun query current => query_bound setup checks representation created query current) before

theorem dynamic_bound (work : OracleComp DynamicSpec Value) (cap : Nat) (bounded : work.IsQueryBoundP IsCreate cap) :
    (simulateQ RegistrationNativeIdentityMain.dynamicLift work).IsQueryBoundP (SourceClass IsCreate) cap := by
  apply RawCtxSourceOpen.simulate_bound RegistrationNativeIdentityMain.dynamicLift IsCreate (SourceClass IsCreate) work cap bounded
  intro query
  by_cases creates : IsCreate query <;>
    simp [RegistrationNativeIdentityMain.dynamicLift, SourceClass, isQueryBoundP_query_iff, creates]

/-- The whole executable native Beacon wrapper retains the same ordinary indexed creation bill. -/
theorem beacon_bound (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeIdentityFrontend.M n KemSK RegistrationServerRoleBackend.State source Value) (cap : Nat)
    (bounded : ∀ owners env, ((work.run owners).run env).IsQueryBoundP (Creates n KemSK) cap)
    (before : RegistrationNativeIdentityMain.State n KemSK source) :
    ((RegistrationNativeIdentityMain.beacon setup checks representation created work).run before).IsQueryBoundP (SourceClass IsCreate) cap := by
  simp only [RegistrationNativeIdentityMain.beacon, StateT.run, bind_pure_comp, isQueryBoundP_map_iff]
  apply dynamic_bound
  exact program_bound setup checks representation created _ cap
    (bounded before.beacons (RegistrationWorldAgreementCompiler.erase before.context.server.world)) before.context

end BeaconcryptCore.Computational.RegistrationNativeIdentityCreateCompilerCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCreateCompilerCaps.dynamic_coins_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCreateCompilerCaps.dynamic_coins_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCreateCompilerCaps.query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCreateCompilerCaps.query_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCreateCompilerCaps.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCreateCompilerCaps.program_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCreateCompilerCaps.dynamic_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCreateCompilerCaps.dynamic_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCreateCompilerCaps.beacon_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCreateCompilerCaps.beacon_bound
