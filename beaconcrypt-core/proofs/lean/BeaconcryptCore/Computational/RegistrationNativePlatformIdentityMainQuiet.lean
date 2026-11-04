-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityQuiet
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainProfile
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCapsCore

/-! Exact structural quietness of the effectful indexed compiler: ambient/random/writer work cannot create or reveal an Ed identity, while signing and allowed static DH remain explicit joint-service requests. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainQuiet
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformIdentityMain (M)
open RegistrationNativeIdentityMain (State)
open RegistrationNativeIdentityMainNoRevealCore (mapped)
variable {n : Nat} {ι KemSK Value Platform : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def DynamicQuiet : PqxdhDynamicIdentityPool.DynamicSpec.Domain → Prop
  | .inl _ | .inr (.service _ _) => True
  | _ => False

def Quiet : PqxdhJointPhase1Reports.ProtocolSpec.Domain → Prop
  | .inl query => DynamicQuiet query
  | .inr _ => True

private theorem dynamic_coins (work : ProbComp Value) :
    AllQueriesSatisfy (simulateQ RegistrationNativeIdentityCompiler.coins work) DynamicQuiet := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityCompiler.coins]
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

private theorem query_quiet (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (query : (RegistrationNativePlatformIdentityProgram.Spec n KemSK).Domain)
    (allowed : RegistrationNativePlatformIdentityQuiet.PlatformAllowed n KemSK query)
    (before : RegistrationNativeIdentityWorld.Context n KemSK) :
    AllQueriesSatisfy ((RegistrationNativePlatformIdentityCompiler.implementation (source := source)
      setup checks representation created query).run before) DynamicQuiet := by
  cases query with
  | inl query =>
    simp only [RegistrationNativePlatformIdentityCompiler.implementation, StateT.run_lift, bind_pure_comp]
    exact mapped _ _ DynamicQuiet ((allQueriesSatisfy_query_iff _ _).mpr trivial)
  | inr query => cases query with
    | inl query => exact dynamic_coins _
    | inr query => cases query with
      | create | reveal handle => exact False.elim allowed
      | service handle request =>
        simp only [RegistrationNativePlatformIdentityCompiler.implementation, RegistrationNativeIdentityCompiler.implementation,
          StateT.run_lift, bind_pure_comp]
        exact mapped _ _ DynamicQuiet ((allQueriesSatisfy_query_iff _ _).mpr trivial)

private theorem program_quiet (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : OracleComp (RegistrationNativePlatformIdentityProgram.Spec n KemSK) Value)
    (allowed : AllQueriesSatisfy work (RegistrationNativePlatformIdentityQuiet.PlatformAllowed n KemSK))
    (before : RegistrationNativeIdentityWorld.Context n KemSK) :
    AllQueriesSatisfy ((simulateQ (RegistrationNativePlatformIdentityCompiler.implementation (source := source)
      setup checks representation created) work).run before) DynamicQuiet := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]; trivial
  | query_bind query next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact allQueriesSatisfy_bind (query_quiet setup checks representation created query first before)
      (fun result => ih result.1 (later result.1) result.2)

private theorem dynamic_lift (work : OracleComp PqxdhDynamicIdentityPool.DynamicSpec Value)
    (prior : AllQueriesSatisfy work DynamicQuiet) :
    AllQueriesSatisfy (simulateQ RegistrationNativeIdentityMain.dynamicLift work) Quiet := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp prior
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityMain.dynamicLift]
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨first, fun reply => ih reply (later reply)⟩

/-- Every quiet actual effectful frontend compiles to a client with no create/reveal request on any reply. -/
theorem beacon_quiet (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativePlatformIdentityProgram.M n KemSK RegistrationServerRoleBackend.State Platform source Value)
    (prior : RegistrationNativePlatformIdentityQuiet.PlatformSafe work)
    (before : State n KemSK source × Platform) :
    AllQueriesSatisfy ((RegistrationNativePlatformIdentityMain.beacon setup checks representation created work).run before) Quiet := by
  simp only [RegistrationNativePlatformIdentityMain.beacon, StateT.run, bind_pure_comp]
  apply mapped _ _ Quiet
  apply dynamic_lift
  exact program_quiet setup checks representation created _
    (prior before.1.beacons (RegistrationWorldAgreementCompiler.erase before.1.context.server.world) before.2) before.1.context

/-- Actual closed auxiliary/native/platform work emits only independent ordinary uniform requests. -/
theorem ordinary_quiet (work : StateT (RegistrationNativeIdentityWorld.Context n KemSK × Platform) ProbComp Value)
    (before : State n KemSK source × Platform) :
    AllQueriesSatisfy ((RegistrationNativePlatformIdentityMainOrdinary.ordinary work).run before) Quiet := by
  unfold RegistrationNativePlatformIdentityMainOrdinary.ordinary
  apply mapped _ _ Quiet
  induction (work.run (before.1.context, before.2)) using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityMain.coins]
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

/-- The syntactic quiet property implies the exact zero indexed-identity creation bill. -/
theorem quiet_zero {A : Type} (work : OracleComp PqxdhJointPhase1Reports.ProtocolSpec A)
    (prior : AllQueriesSatisfy work Quiet) :
    work.IsQueryBoundP RegistrationNativeIdentityMainCreateCapsCore.Creates 0 := by
  classical
  have never : AllQueriesSatisfy work (fun query => ¬ RegistrationNativeIdentityMainCreateCapsCore.Creates query) := by
    apply prior.mono
    intro query quiet
    cases query with
    | inr report => simp only [RegistrationNativeIdentityMainCreateCapsCore.Creates, PqxdhJointPhase1Reports.SourceClass, not_false_eq_true]
    | inl query => cases query with
      | inl coin => simp only [RegistrationNativeIdentityMainCreateCapsCore.Creates, PqxdhJointPhase1Reports.SourceClass, PqxdhDynamicIdentityPool.IsCreate, not_false_eq_true]
      | inr query => cases query with
        | create => intro _; exact quiet
        | service handle request | reveal handle => simp only [RegistrationNativeIdentityMainCreateCapsCore.Creates, PqxdhJointPhase1Reports.SourceClass, PqxdhDynamicIdentityPool.IsCreate, not_false_eq_true]
  simpa only [not_not] using (isQueryBoundP_zero_iff work
    (fun query => ¬ RegistrationNativeIdentityMainCreateCapsCore.Creates query)).mpr never

/-- The same structural fact forbids generated-identity reveals, independently of success or scheduling. -/
theorem quiet_no_reveal {A : Type} (work : OracleComp PqxdhJointPhase1Reports.ProtocolSpec A)
    (prior : AllQueriesSatisfy work Quiet) :
    AllQueriesSatisfy work RegistrationNativeIdentityMainNoRevealCore.Allowed := by
  apply prior.mono
  intro query quiet
  cases query with
  | inr report => trivial
  | inl query => cases query with
    | inl coin => trivial
    | inr query => cases query with
      | create | service handle request => trivial
      | reveal handle => exact quiet

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainQuiet
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainQuiet.beacon_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainQuiet.beacon_quiet
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainQuiet.ordinary_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainQuiet.ordinary_quiet
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainQuiet.quiet_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainQuiet.quiet_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainQuiet.quiet_no_reveal' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainQuiet.quiet_no_reveal
