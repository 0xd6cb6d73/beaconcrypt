-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedRetainedSource
import BeaconcryptCore.Computational.RegistrationNativeG3SelectiveDirectGame
import BeaconcryptCore.Computational.RegistrationNativeOpenMaterialCaps

/-! Closing the original retained frontend by its literal probability-valued KEM provider adds no material query. The original build/finish allowance therefore bounds the actual two-pass native byte-table client, without an additional service, source or capacity premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendCaps
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeG3MaterializedRetainedSource (ordinary)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

private theorem coins_free (work : ProbComp Value) :
    (simulateQ RegistrationNativePublicRetained.coins work).IsQueryBoundP RegistrationNativeRetainedService.IsDemand 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ work 0 (isQueryBoundP_false work 0)
  intro query
  simp [RegistrationNativePublicRetained.coins, RegistrationNativeRetainedService.IsDemand, isQueryBoundP_query_iff]

private theorem close_step (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (query : (RegistrationNativeOpenRetained.Spec KemSK).Domain)
    (before : RegistrationNativeOpenRetainedSource.External KemSK ProviderState) :
    ((RegistrationNativeOpenRetainedSource.close provider query).run before).IsQueryBoundP
      RegistrationNativeRetainedService.IsDemand (if RegistrationNativeOpenMaterialCaps.IsDemand query then 1 else 0) := by
  cases query with
  | inl query =>
      simp [RegistrationNativeOpenRetainedSource.close, StateT.run_lift, bind_pure_comp,
        isQueryBoundP_map_iff, RegistrationNativeOpenMaterialCaps.IsDemand, isQueryBoundP_query_iff]
      intro counted
      simp only [ite_eq_left counted, Nat.zero_lt_succ]
  | inr query =>
      simpa only [RegistrationNativeOpenRetainedSource.close, StateT.run, RegistrationNativeOpenMaterialCaps.IsDemand, ite_false] using
        coins_free ((provider query).run before)

private theorem close_bound (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativeOpenRetained.Spec KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeOpenMaterialCaps.IsDemand (KemSK := KemSK)) count)
    (before : RegistrationNativeOpenRetainedSource.External KemSK ProviderState) :
    ((simulateQ (RegistrationNativeOpenRetainedSource.close provider) work).run' before).IsQueryBoundP
      RegistrationNativeRetainedService.IsDemand count := by
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simpa only [ite_eq_left counted] using close_step provider query current
  · intro query free current
    simpa only [ite_eq_right free] using close_step provider query current

/-- The original bounded frontend supplies the entire original two-pass material bill after the literal KEM provider is closed. -/
theorem client_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativePublicCaps.IsDemand (KemSK := KemSK)) count)
    (frame : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (world : PqxdhRecordLiftWorld.State n) :
    (RegistrationNativeG3SelectiveDirectGame.compiled setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
      (RegistrationNativeG3RetainedFrontendRun.retainedClient setup wire route sign provider work
        (ordinary frame world, frame.1.provider))).IsQueryBoundP RegistrationNativeG3FirstTouchBound.IsValue count := by
  have original := RegistrationNativeOpenMaterialCaps.retained_bound setup wire route sign work (ordinary frame world) count bounded
  have closed := close_bound provider _ count original ((ordinary frame world).pool, frame.1.provider)
  have retained : (RegistrationNativeG3RetainedFrontendRun.retainedClient setup wire route sign provider work
      (ordinary frame world, frame.1.provider)).IsQueryBoundP RegistrationNativeRetainedService.IsDemand count := by
    simpa only [RegistrationNativeOpenRetained.client, RegistrationNativeG3RetainedFrontendRun.retainedClient,
      ordinary, RegistrationNativePublicRetained.clear, RegistrationNativePublicRootFrame.replace] using closed
  exact RegistrationNativeKeyBounds.client_bound setup.source _ _ _ count
    (RegistrationNativeRetainedService.client_bound _ count retained) RegistrationNativeKeyPhases.emptyMeta

end BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendCaps.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendCaps.client_bound
