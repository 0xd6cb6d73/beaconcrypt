-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreter
import BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyBackend
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicFrontendCaps

/-! The actual corrected shared-platform tree is locally closed over the opaque-slot material service and EnvEffects. Allocator uniform requests use an explicit counted coin embedding here; literal uncounted source state is a separate operational interpreter, and its event/cost projection remains explicit. No selected record root, hidden64 seed or chain kernel is stored in this service state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyBackend
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (WorldSpec EnvEffects effectLift)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveHiddenInterpreter (State)
open RegistrationNativeHiddenEnvironmentHandler (project effects_project)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

noncomputable def handler (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) :
    QueryImpl (RegistrationNativePlatformPublicFrontend.Spec n KemSK)
      (StateT (State n KemSK ProviderState) (OracleComp (WorldSpec n)))
  | .inl query => RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider query
  | .inr coin => StateT.lift (PqxdhRecordLiftInterface.coinLift coin)

noncomputable def restricted (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) :
    QueryImpl (RegistrationNativePlatformPublicFrontend.Spec n KemSK)
      (StateT (State n KemSK ProviderState) (OracleComp (EnvEffects n)))
  | .inl query => RegistrationNativeSelectiveEntropyBackend.restricted setup wire sign seed scalar candidate provider query
  | .inr coin => StateT.lift ((EnvEffects n).query (.inl coin))

/-- Each actual local callback has exactly the restricted effect program, including external allocation draws. -/
theorem local_query (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (query : (RegistrationNativePlatformPublicFrontend.Spec n KemSK).Domain)
    (localQuery : ¬RegistrationNativePlatformPublicFrontendCaps.IsRecord query) (before : State n KemSK ProviderState) :
    simulateQ effectLift ((restricted setup wire sign seed scalar candidate provider query).run before) =
      (handler setup wire sign seed scalar candidate provider query).run before := by
  cases query with
  | inl query => cases query with
    | inl query =>
        exact RegistrationNativeSelectiveEntropyBackend.local_query setup wire sign seed scalar candidate provider query before
    | inr query => exact (localQuery trivial).elim
  | inr coin =>
      simp only [restricted, handler, StateT.run_lift, bind_pure_comp, simulateQ_map,
        simulateQ_spec_query, effectLift, PqxdhRecordLiftInterface.coinLift]

/-- Arbitrary adaptive corrected local trees retain their full service and external state when closed into the shared World. -/
theorem program_local (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativePlatformPublicFrontend.Spec n KemSK) Value)
    (bounded : work.IsQueryBoundP RegistrationNativePlatformPublicFrontendCaps.IsRecord 0)
    (before : State n KemSK ProviderState) :
    simulateQ effectLift ((simulateQ (restricted setup wire sign seed scalar candidate provider) work).run before) =
      (simulateQ (handler setup wire sign seed scalar candidate provider) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      have localQuery := bounded.1.resolve_right (Nat.not_lt_zero _)
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [local_query setup wire sign seed scalar candidate provider query localQuery]
      apply bind_congr
      intro result
      exact ih result.1 (by simpa using bounded.2 result.1) result.2
end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyBackend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyBackend.local_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyBackend.local_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyBackend.program_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyBackend.program_local
