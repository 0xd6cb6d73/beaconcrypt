-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconCollectCosts
import BeaconcryptCore.Computational.RegistrationNativeResponseCosts

/-! The actual terminal Beacon finish prefix pays its original response-authentication and twelve-slot public agreement bills. Root preparation uses the existing zero-effect reference request; malformed or rejected responses still consume the original InitSent capability before returning. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconPreparationCosts
open PqxdhRecordLiftInterface (EffectKind)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_bind weighted_simulate weighted_indicator)
open RegistrationNativeWeightedContext (query_bound map_bound)
open RegistrationNativePrimitiveCosts (coinCost)
open RegistrationNativePublicationCosts (hashCost)
open RegistrationNativeReferenceCosts (bill)
open RegistrationBeaconReferenceCompiler (SelectedOwner Spec)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι}

def preparationBill (qKem : Nat) (kind : EffectKind) := hashCost kind * 2 + coinCost qKem kind * 12

private theorem reference_bound (authenticated : registration.AuthenticatedResponse)
    (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse) (qSign qKem : Nat) (kind : EffectKind) :
    Weighted (fun query => bill (n := n) qSign qKem query kind)
      (simulateQ (RegistrationBeaconReferenceCompiler.prepare (KemSK := KemSK)) (RegistrationBeaconReferenceRoot.client authenticated pending)) 0 := by
  apply weighted_simulate (fun _ => 0) _ _ _ _ ?_ ?_
  · have actual := weighted_indicator (fun _ => True) 0 _ 1
      ((isQueryBoundP_true_iff _ _).mpr (RegistrationBeaconReferenceRoot.client_bound authenticated pending))
    simpa only [ite_true, Nat.zero_mul] using actual
  · intro query
    exact query_bound _ _

/-- Actual native root preparation adds no World draw or capability to the public agreement prefix. -/
theorem agreement_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (qSign qKem : Nat) (kind : EffectKind) (before : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Weighted (fun query => bill (n := n) qSign qKem query kind)
      ((RegistrationBeaconReferenceCompiler.agreement setup owner oneTime authenticated).run before) (coinCost qKem kind * 12) := by
  simp only [RegistrationBeaconReferenceCompiler.agreement, StateT.run_bind]
  rw [← Nat.add_zero (coinCost qKem kind * 12)]
  apply weighted_bind _ _ _ _ _ (RegistrationNativeBeaconCollectCosts.collect_bound setup owner oneTime authenticated qSign qKem kind before)
  intro collected
  cases collected.1 with
  | none => trivial
  | some pending =>
      simp only [StateT.run_lift, bind_pure_comp]
      exact map_bound _ _ _ _ (reference_bound authenticated pending qSign qKem kind)

/-- The actual moved native response prefix preserves every source failure poststate under its literal primitive bill. -/
theorem preparation_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (before : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (qSign qKem : Nat) (kind : EffectKind) :
    Weighted (fun query => bill (n := n) qSign qKem query kind)
      (((RegistrationBeaconReferenceCompiler.finishPreparation setup source packet).run owner).run before) (preparationBill qKem kind) := by
  simp only [RegistrationBeaconReferenceCompiler.finishPreparation, StateT.run_bind, StateT.run_get, pure_bind]
  cases owner.phase with
  | fresh | freshWithCoins oneTime | established completed | aborted aborted => trivial
  | initSent pending oneTime =>
      cases moved : pending.aborted_state with
      | fail error => simp only [moved, StateT.run_pure]; trivial
      | div => simp only [moved, StateT.run_pure]; trivial
      | ok aborted =>
          simp only [moved, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_lift, bind_assoc]
          apply weighted_bind _ _ _ (hashCost kind * 2) (coinCost qKem kind * 12)
          · exact RegistrationNativeResponseCosts.compiled_bound setup.source.crypto source.verify pending _ qSign qKem kind
          · intro accepted
            cases accepted with
            | fail error => trivial
            | div => trivial
            | ok result => cases result with
              | Err error => trivial
              | Ok authenticated =>
                  simp only [StateT.run_lift, StateT.run_map, bind_pure_comp]
                  exact map_bound _ _ _ _ (agreement_bound setup owner oneTime authenticated qSign qKem kind before)

end BeaconcryptCore.Computational.RegistrationNativeBeaconPreparationCosts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPreparationCosts.agreement_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPreparationCosts.agreement_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPreparationCosts.preparation_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPreparationCosts.preparation_bound
