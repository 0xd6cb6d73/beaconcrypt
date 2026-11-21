-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenBeaconCounter

/-! Actual typed native calls retain one parsed-attempt counter across real and candidate KEM service phases. Its update is derived from the literal SDK/Beacon compilers; successful sessions and getter counts remain separate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenTypedCounter
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeKemOpenProvider (State implementation counter)
open RegistrationNativeKemOpenFrame (NoPut lower)
variable {ι KemSK : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

private theorem lower_program {Value : Type} (chosen : Bool)
    (work : OracleComp (RegistrationNativeKemServerInterface.Spec n mlSource KemSK) Value) :
    simulateQ (lower chosen) work = simulateQ (RegistrationNativeKemRouting.route chosen)
      (simulateQ RegistrationNativeKemFrontendInterface.lift work) := by
  simp only [lower, QueryImpl.simulateQ_compose]

def increment : TypedSpec.Domain → Nat
  | .inr (.accept _) => 1
  | _ => 0

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
  (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (real : Bool)

local notation "provider" => implementation (n := n) setup checks wire route representation created credential selected pairs publicKey real

/-- Every actual dispatcher branch changes the open source counter exactly once for an accept, and zero times for every other native call. -/
theorem dispatcher_counter (chosen : Bool) (query : TypedSpec.Domain)
    (before after : State n mlSource KemSK) (value : TypedSpec.Range query)
    (supported : (some value, after) ∈ support
      (((simulateQ provider (simulateQ (RegistrationNativeKemRouting.route chosen)
        (RegistrationNativeKemDispatcherCompiler.handler setup wire checks query))).run).run before)) :
    counter after = counter before + increment query := by
  let compiled := simulateQ (RegistrationNativeKemRouting.route chosen)
    (RegistrationNativeKemDispatcherCompiler.handler (n := n) (mlSource := mlSource) setup wire checks query)
  cases query with
  | inl coin =>
      have kept := RegistrationNativeKemOpenFrame.no_put_keeps setup checks wire route representation created credential
        selected pairs publicKey real compiled ((allQueriesSatisfy_query_iff _ _).mpr trivial) before after value supported
      exact kept
  | inr command =>
      cases command with
      | accept packet =>
          simp only [RegistrationNativeKemDispatcherCompiler.handler, ← lower_program] at supported
          exact RegistrationNativeKemOpenSdkCounter.typed_counter setup checks wire route representation created credential
            selected pairs publicKey real chosen packet before after value supported
      | create edPin mlPin keyId =>
          simp only [RegistrationNativeKemDispatcherCompiler.handler, ← lower_program] at supported
          exact RegistrationNativeKemOpenBeaconCounter.beacon_counter setup checks wire route representation created credential
            selected pairs publicKey real chosen (RegistrationNativeBeaconFrontend.create setup mlSource edPin mlPin keyId)
            before after value supported
      | bundle owner =>
          simp only [RegistrationNativeKemDispatcherCompiler.handler, ← lower_program] at supported
          exact RegistrationNativeKemOpenBeaconCounter.beacon_counter setup checks wire route representation created credential
            selected pairs publicKey real chosen (RegistrationNativeBeaconFrontend.bundle setup mlSource wire owner)
            before after value supported
      | finish owner packet =>
          simp only [RegistrationNativeKemDispatcherCompiler.handler, ← lower_program] at supported
          exact RegistrationNativeKemOpenBeaconCounter.beacon_counter setup checks wire route representation created credential
            selected pairs publicKey real chosen (RegistrationNativeBeaconFrontend.finish setup mlSource wire owner packet)
            before after value supported
      | _ =>
          have kept := RegistrationNativeKemOpenFrame.no_put_keeps setup checks wire route representation created credential
            selected pairs publicKey real compiled (by first
              | exact allQueriesSatisfy_pure _ _
              | exact (allQueriesSatisfy_query_iff _ _).mpr trivial) before after value supported
          exact kept

/-- The actual selected parsed-attempt wrapper reads its retained counter before advancing that attempt; every source reply keeps the same original counter update. -/
theorem parsed_counter (parsed : Nat) (query : TypedSpec.Domain)
    (before after : State n mlSource KemSK) (value : TypedSpec.Range query)
    (supported : (some value, after) ∈ support
      (((simulateQ provider (RegistrationNativeKemParsedRouting.handler setup checks wire parsed query)).run).run before)) :
    counter after = counter before + increment query := by
  let call := query
  cases query with
  | inl coin =>
      exact dispatcher_counter setup checks wire route representation created credential selected pairs publicKey real
        false (.inl coin) before after value supported
  | inr command =>
      cases command with
      | accept packet =>
          simp only [RegistrationNativeKemParsedRouting.handler, RegistrationNativeKemParsedRouting.get,
            simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind] at supported
          rw [RegistrationNativeKemOpenProvider.get_run] at supported
          simp only [pure_bind, Option.elim_some] at supported
          exact dispatcher_counter setup checks wire route representation created credential selected pairs publicKey real
            _ (.inr (.accept packet)) _ after value supported
      | _ =>
          exact dispatcher_counter setup checks wire route representation created credential selected pairs publicKey real
            false call before after value supported

end BeaconcryptCore.Computational.RegistrationNativeKemOpenTypedCounter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenTypedCounter.dispatcher_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenTypedCounter.dispatcher_counter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenTypedCounter.parsed_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenTypedCounter.parsed_counter
