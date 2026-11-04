-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeReferenceCosts
import BeaconcryptCore.Computational.RegistrationNativeWeightedContext

/-! The actual response-authentication controller has at most two primitive callback slots. Its native interpretation charges the original shared response hash and keeps optional hash failure and rejected ML verification. The conservative two-slot hash bill requires no successful-authentication premise. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeResponseCosts
open PqxdhRecordLiftInterface (EffectKind)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_indicator weighted_simulate)
open RegistrationNativeWeightedContext (query_bound map_bound)
open RegistrationNativePublicationCosts (hashCost)
variable {n : Nat} {KemSK Input : Type}

private theorem continue_bound (action : RustM Input)
    (next : Input → OracleComp RegistrationAuthenticationExecutor.Spec (RustM RegistrationResponseExecutor.ResponseResult)) (count : Nat)
    (bounded : ∀ value, (next value).IsTotalQueryBound count) :
    (RegistrationAuthenticationExecutor.continueWith action next).IsTotalQueryBound count := by
  cases action with
  | ok value => exact bounded value
  | fail error => trivial
  | div => trivial

private theorem result_bound (action : RustM (core.result.Result Input pqxdh.BeaconAborted))
    (next : Input → OracleComp RegistrationAuthenticationExecutor.Spec (RustM RegistrationResponseExecutor.ResponseResult)) (count : Nat)
    (bounded : ∀ value, (next value).IsTotalQueryBound count) :
    (RegistrationResponseExecutor.continueResult action next).IsTotalQueryBound count := by
  cases action with
  | ok reply => cases reply with
    | Ok value => exact bounded value
    | Err error => trivial
  | fail error => trivial
  | div => trivial

/-- Every actual response-authentication path has the same two-slot allowance. -/
theorem begin_bound (pending : registration.BeaconPending) (packet : core.option.Option registration.ResponsePacket) :
    (RegistrationResponseExecutor.begin pending packet).IsTotalQueryBound 2 := by
  unfold RegistrationResponseExecutor.begin
  apply result_bound
  intro hashState
  apply continue_bound
  intro hashRequest
  rw [isTotalQueryBound_query_bind_iff]
  refine ⟨by decide, fun digest => ?_⟩
  apply result_bound
  intro verificationState
  apply continue_bound
  intro request
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun _ => by trivial⟩

/-- The literal native response program retains its original shared CTX requests under the public-reference cost embedding. -/
theorem compiled_bound (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (pending : registration.BeaconPending) (packet : core.option.Option registration.ResponsePacket)
    (qSign qKem : Nat) (kind : EffectKind) :
    Weighted (fun query => RegistrationNativeReferenceCosts.bill (n := n) qSign qKem query kind)
      (simulateQ (RegistrationBeaconReferenceCompiler.effect (KemSK := KemSK))
        (simulateQ (RegistrationAuthenticationCompiler.callbacks crypto verify) (RegistrationResponseExecutor.begin pending packet)))
      (hashCost kind * 2) := by
  rw [← QueryImpl.simulateQ_compose]
  apply weighted_simulate (fun _ => hashCost kind) _ _ _ _ ?_ ?_
  · simpa only [ite_true] using weighted_indicator (fun _ => True) (hashCost kind) _ 2
      ((isQueryBoundP_true_iff _ _).mpr (begin_bound pending packet))
  · intro query
    cases query with
    | hash request =>
        simp only [QueryImpl.compose, RegistrationAuthenticationCompiler.callbacks, bind_pure_comp,
          simulateQ_map, simulateQ_spec_query, RegistrationBeaconReferenceCompiler.effect]
        exact map_bound _ _ _ _ (by cases kind <;> exact query_bound _ _)
    | mldsa request => trivial
    | ed25519 request => trivial

end BeaconcryptCore.Computational.RegistrationNativeResponseCosts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseCosts.begin_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseCosts.begin_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseCosts.compiled_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseCosts.compiled_bound
