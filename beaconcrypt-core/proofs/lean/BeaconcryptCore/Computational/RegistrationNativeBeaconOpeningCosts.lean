-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeWeightedContext
import BeaconcryptCore.Computational.RegistrationNativeReferenceCosts

/-! The actual paired Beacon sequence-one service charges its original shared CTX hash. KDF and AEAD are the existing deterministic source functions, and all optional hash/opening/final-admission failures remain in the source AST. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconOpeningCosts
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_indicator weighted_simulate)
open RegistrationNativeWeightedContext (query_bound)
open RegistrationNativePublicationCosts (hashCost)
variable {n : Nat}

def rawCost (kind : PqxdhRecordLiftInterface.EffectKind) (_ : RegistrationRawSealBridge.Spec.Domain) : Nat := hashCost kind

/-- Expanding an actual source opening pays one shared commitment hash and preserves every source failure prefix. -/
theorem opening_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (query : RawCtxWholeOwner.PrimitiveSpec.Domain) (kind : PqxdhRecordLiftInterface.EffectKind) :
    Weighted (rawCost kind) (RegistrationNativePairedBeaconService.opening source query) (hashCost kind) := by
  cases query with
  | inl request =>
      simp only [RegistrationNativePairedBeaconService.opening, QueryImpl.apply_compose,
        RawCtxSourceOpen.nativeAdapter, RegistrationRawReceiveBridge.modelAdapter,
        RegistrationNativePairedBeaconService.read, simulateQ_spec_query]
      trivial
  | inr input =>
      simp only [RegistrationNativePairedBeaconService.opening, QueryImpl.apply_compose,
        RawCtxSourceOpen.nativeAdapter, ← QueryImpl.simulateQ_compose]
      apply weighted_simulate (fun query : RawCtxSourceOpen.OpenSpec.Domain => if query.isLeft = true then hashCost kind else 0)
        _ _ (RawCtxSourceOpen.openInput input) _ ?_ ?_
      · simpa only [Nat.mul_one] using weighted_indicator (fun query : RawCtxSourceOpen.OpenSpec.Domain => query.isLeft = true)
          (hashCost kind) _ 1 (RawCtxSourceOpen.openInput_bounds input).1
      · intro request
        cases request with
        | inl bytes =>
            simp only [QueryImpl.compose, RawCtxSourceOpen.openLift, simulateQ_spec_query,
              RegistrationRawReceiveBridge.modelAdapter, RegistrationNativePairedBeaconService.read, bind_pure_comp, simulateQ_map, Sum.isLeft, ite_true]
            exact RegistrationNativeWeightedContext.map_bound _ _ _ _ (query_bound _ _)
        | inr input =>
            simp only [QueryImpl.compose, RawCtxSourceOpen.openLift, simulateQ_spec_query,
              RegistrationRawReceiveBridge.modelAdapter, RegistrationNativePairedBeaconService.read,
              simulateQ_bind, simulateQ_pure, pure_bind]
            trivial

/-- Missing prepared material costs nothing; present material expands exactly one original opening. -/
theorem adapter_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : ratchet.concrete.ReceiveOpen RawCtxWholeOwner.OpenContext)
    (kind : PqxdhRecordLiftInterface.EffectKind) :
    Weighted (rawCost kind)
      (simulateQ (RegistrationNativePairedBeaconService.opening source) (RawCtxWholeOwner.adapter (.inr pending))) (hashCost kind) := by
  simp only [RawCtxWholeOwner.adapter]
  cases RawCtxWholeOwner.arguments pending with
  | none => simp only [simulateQ_pure]; trivial
  | some input =>
      simp only [bind_pure_comp]
      rw [simulateQ_map (spec := RawCtxWholeOwner.PrimitiveSpec)]
      simp only [simulateQ_spec_query]
      exact RegistrationNativeWeightedContext.map_bound _ _ _ _ (opening_bound source (.inr input) kind)

/-- The literal selected first-record program has one shared commitment-hash allowance, even when opening or final admission rejects. -/
theorem program_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (output : PqxdhServerAuthKeySchedule.Output)
    (kind : PqxdhRecordLiftInterface.EffectKind) :
    Weighted (rawCost kind) (RegistrationNativePairedBeaconService.program source descriptor output) (hashCost kind) := by
  unfold RegistrationNativePairedBeaconService.program RegistrationBeaconSeed.program
  split
  · simp only [simulateQ_map, PqxdhServerAuthBeaconFactor.primLabels, QueryImpl.apply_compose,
      simulateQ_ofLift_eq_self]
    exact RegistrationNativeWeightedContext.map_bound _ _ _ _ (adapter_bound source _ kind)
  · trivial

end BeaconcryptCore.Computational.RegistrationNativeBeaconOpeningCosts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconOpeningCosts.opening_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconOpeningCosts.opening_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconOpeningCosts.adapter_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconOpeningCosts.adapter_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconOpeningCosts.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconOpeningCosts.program_bound
