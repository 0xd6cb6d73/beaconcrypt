-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore

/-! The actual indexed identity compiler forwards only creation, signing and static-DH requests from the proved native lifecycle ASTs. Native auxiliary randomness remains ordinary uniform queries. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealBeacon
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityMainNoRevealCore (Allowed DynamicAllowed Safe mapped)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

/-- Every allowed actual trusted identity callback compiles to an ordinary non-revealing joint program. -/
theorem query_safe (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (query : (RegistrationNativeIdentityFrontend.Trusted n KemSK).Domain)
    (allowed : RegistrationNativeIdentityNoReveal.Allowed n KemSK query)
    (before : RegistrationNativeIdentityWorld.Context n KemSK) :
    AllQueriesSatisfy ((RegistrationNativeIdentityCompiler.implementation (source := mlSource)
      setup checks representation created query).run before) DynamicAllowed := by
  cases query with
  | inl query => exact RegistrationNativeIdentityMainNoRevealCore.dynamic_coins_safe _
  | inr query => cases query with
    | create =>
        simp only [RegistrationNativeIdentityCompiler.implementation, StateT.run, bind_pure_comp]
        exact mapped _ _ DynamicAllowed ((allQueriesSatisfy_query_iff _ _).mpr trivial)
    | service handle request =>
        simp only [RegistrationNativeIdentityCompiler.implementation, StateT.run_lift, bind_pure_comp]
        exact mapped _ _ DynamicAllowed ((allQueriesSatisfy_query_iff _ _).mpr trivial)
    | reveal handle => exact False.elim allowed

/-- All oracle replies and adaptive trusted callbacks preserve structural non-reveal safety through compilation. -/
theorem program_safe (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : OracleComp (RegistrationNativeIdentityFrontend.Trusted n KemSK) Value)
    (allowed : AllQueriesSatisfy work (RegistrationNativeIdentityNoReveal.Allowed n KemSK))
    (before : RegistrationNativeIdentityWorld.Context n KemSK) :
    AllQueriesSatisfy ((simulateQ (RegistrationNativeIdentityCompiler.implementation (source := mlSource)
      setup checks representation created) work).run before) DynamicAllowed := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]; trivial
  | query_bind query next ih =>
      obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact allQueriesSatisfy_bind (query_safe setup checks representation created query first before)
        (fun result => ih result.1 (later result.1) result.2)

/-- Actual whole native Beacon execution contains no generated-identity reveal operation. -/
theorem beacon_safe (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeIdentityFrontend.M n KemSK RegistrationServerRoleBackend.State mlSource Value)
    (allowed : RegistrationNativeIdentityNoReveal.Safe work) :
    Safe (RegistrationNativeIdentityMain.beacon setup checks representation created work) := by
  intro before
  simp only [RegistrationNativeIdentityMain.beacon, StateT.run, bind_pure_comp]
  apply mapped _ _ Allowed
  apply RegistrationNativeIdentityMainNoRevealCore.dynamic_safe
  exact program_safe setup checks representation created _
    (allowed before.beacons (RegistrationWorldAgreementCompiler.erase before.context.server.world)) before.context

end BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealBeacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealBeacon.query_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealBeacon.query_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealBeacon.program_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealBeacon.program_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealBeacon.beacon_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealBeacon.beacon_safe
