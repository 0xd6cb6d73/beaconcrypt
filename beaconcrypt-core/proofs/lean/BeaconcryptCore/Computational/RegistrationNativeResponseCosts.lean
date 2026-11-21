-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeReferenceCosts
import BeaconcryptCore.Computational.RegistrationNativeWeightedContext
import BeaconcryptCore.Computational.RegistrationResponseHashBounds

/-! The actual response-authentication controller has at most three primitive callback slots. Its native interpretation charges the shared response and record-AD hashes and keeps optional hash failure and rejected ML verification. The exact two-position hash bill requires no successful-authentication premise. -/

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

/-- Every actual response-authentication path has the same three-callback allowance. -/
theorem begin_bound (pending : registration.BeaconPending) (packet : core.option.Option registration.ResponsePacket) :
    (RegistrationResponseExecutor.begin pending packet).IsTotalQueryBound 3 :=
  RegistrationResponseHashBounds.begin_total_bound pending packet

/-- The literal native response program retains its original shared CTX requests under the public-reference cost embedding. -/
theorem compiled_bound (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (pending : registration.BeaconPending) (packet : core.option.Option registration.ResponsePacket)
    (qSign qKem : Nat) (kind : EffectKind) :
    Weighted (fun query => RegistrationNativeReferenceCosts.bill (n := n) qSign qKem query kind)
      (simulateQ (RegistrationBeaconReferenceCompiler.effect (KemSK := KemSK))
        (simulateQ (RegistrationAuthenticationCompiler.callbacks crypto verify) (RegistrationResponseExecutor.begin pending packet)))
      (hashCost kind * 2) := by
  rw [← QueryImpl.simulateQ_compose]
  apply weighted_simulate (fun query => if RegistrationResponseHashBounds.IsHash query then hashCost kind else 0) _ _ _ _ ?_ ?_
  · exact weighted_indicator RegistrationResponseHashBounds.IsHash (hashCost kind) _ 2
      (RegistrationResponseHashBounds.begin_hash_bound pending packet)
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
