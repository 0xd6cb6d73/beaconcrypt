-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconMaterialRead
import BeaconcryptCore.Computational.RegistrationNativeBeaconOpeningCosts
import BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalBuild
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBeaconOpeningBills
open PqxdhRecordLiftInterface (EnvEffects EffectKind effectKind)
open RegistrationNativePublicationCosts (hashCost)
variable {n : Nat} {Auxiliary : Type}
private theorem total_map_iff {J X Y : Type} {spec : OracleSpec J}
    (work : OracleComp spec X) (change : X → Y) (cap : Nat) :
    (change <$> work).IsTotalQueryBound cap ↔ work.IsTotalQueryBound cap :=
  isQueryBound_map_iff work change cap _ _
private theorem total_query_iff {J : Type} {spec : OracleSpec J} (query : J) (cap : Nat) :
    OracleComp.IsTotalQueryBound (spec.query query : OracleComp spec (spec.Range query)) cap ↔ 0 < cap :=
  isQueryBound_query_iff (spec := spec) query cap _ _
private theorem read_program_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (query : RegistrationRawReceiveBridge.Spec.Domain) (kind : EffectKind) :
    (RegistrationBeaconRecordSourceProgram.read (n := n) source writer query).IsQueryBoundP
      (fun effect => effectKind effect = kind) (hashCost kind) := by
  rcases query with request | request | bytes | input
  · simpa only [RegistrationBeaconRecordSourceProgram.read, QueryImpl.apply_compose,
      RegistrationNativePairedBeaconService.read, simulateQ_spec_query] using
      RegistrationNativePublicationCosts.raw_bound source writer (.inl request) kind
  · trivial
  · simpa only [RegistrationBeaconRecordSourceProgram.read, QueryImpl.apply_compose,
      RegistrationNativePairedBeaconService.read, simulateQ_spec_query] using
      RegistrationNativePublicationCosts.raw_bound source writer (.inr (.inr (.inl bytes))) kind
  · trivial
private theorem read_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (query : RegistrationRawReceiveBridge.Spec.Domain) (before : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (kind : EffectKind) :
    ((RegistrationBeaconMaterialRead.read
      (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) source writer query).run before).IsQueryBoundP
        (fun effect => effectKind effect = kind) (hashCost kind) := by
  simp only [RegistrationBeaconMaterialRead.read, RegistrationBeaconMaterialRead.charge,
    StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_lift, bind_pure_comp,
    isQueryBoundP_map_iff, simulateQ_ofLift_eq_self]
  exact read_program_bound source writer query kind
private theorem expanded_bound (query : RawCtxWholeOwner.PrimitiveSpec.Domain) :
    (simulateQ RegistrationRawReceiveBridge.modelAdapter (RawCtxSourceOpen.nativeAdapter query)).IsTotalQueryBound 2 := by
  cases query with
  | inl request => simp [RawCtxSourceOpen.nativeAdapter, RegistrationRawReceiveBridge.modelAdapter, total_query_iff]
  | inr input =>
    have total : (RawCtxSourceOpen.openInput input).IsTotalQueryBound 2 := by
      apply PqxdhBeaconPhase2Bounds.total_of_partition (fun query => query.isLeft = true) _ 1 1 (RawCtxSourceOpen.openInput_bounds input).1
      apply (isQueryBoundP_congr_pred (p' := fun query => query.isRight = true) (fun query => by cases query <;> simp)).mpr
      exact (RawCtxSourceOpen.openInput_bounds input).2
    simp only [RawCtxSourceOpen.nativeAdapter, ← QueryImpl.simulateQ_compose]
    apply PqxdhBeaconPhase2Bounds.simulate_total _ _ 2 total
    intro request
    cases request <;> simp [QueryImpl.apply_compose, RawCtxSourceOpen.openLift,
      RegistrationRawReceiveBridge.modelAdapter, total_map_iff, total_query_iff]
private theorem primitive_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (query : RawCtxWholeOwner.PrimitiveSpec.Domain) (before : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (kind : EffectKind) :
    ((RegistrationBeaconChargedSource.primitive (RegistrationBeaconMaterialRead.read
      (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) source writer) query).run before).IsQueryBoundP
        (fun effect => effectKind effect = kind) (2 * hashCost kind) := by
  simp only [RegistrationBeaconChargedSource.primitive, QueryImpl.apply_compose]
  exact RegistrationNativePlatformPublicExternalBuild.simulate_scaled (fun effect => effectKind effect = kind)
    _ (hashCost kind) (fun request current => read_bound source writer request current kind)
    _ 2 (expanded_bound query) before
private theorem seed_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (output : PqxdhServerAuthKeySchedule.Output) :
    (RegistrationBeaconSeed.program source descriptor output).IsTotalQueryBound 1 := by
  unfold RegistrationBeaconSeed.program
  split
  · simp only [total_map_iff, PqxdhServerAuthBeaconFactor.primLabels, QueryImpl.apply_compose, simulateQ_ofLift_eq_self]
    simp only [RawCtxWholeOwner.adapter]
    split
    · trivial
    · simp [total_map_iff, total_query_iff]
  · trivial
/-- The actual charged first Beacon opening retains every Env/record marker and has at most two shared hashes, with zero coin or administrative requests, on all failure paths. -/
theorem opening_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (output : PqxdhServerAuthKeySchedule.Output)
    (before : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (kind : EffectKind) :
    ((simulateQ (RegistrationBeaconChargedSource.primitive (RegistrationBeaconMaterialRead.read
      (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) source writer))
      (RegistrationBeaconSeed.program source descriptor output)).run before).IsQueryBoundP
        (fun effect => effectKind effect = kind) (2 * hashCost kind) := by
  simpa only [Nat.one_mul] using RegistrationNativePlatformPublicExternalBuild.simulate_scaled
    (fun effect => effectKind effect = kind) _ (2 * hashCost kind)
    (fun query current => primitive_bound source writer query current kind)
    _ 1 (seed_bound source descriptor output) before
end BeaconcryptCore.Computational.RegistrationNativePlatformBeaconOpeningBills

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconOpeningBills.opening_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconOpeningBills.opening_bound
