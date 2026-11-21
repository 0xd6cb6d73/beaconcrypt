-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderInterpreter

/-! The actual Server build uses deferred material, native record/signing work and current environment effects. Its complete AST contains no indexed KEM operation, on any response or cancellation branch. This structural fact permits every total KEM provider, including a uniform candidate provider, to remain an untouched frame during build. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderBuildCaps
open PqxdhServerAuthExperiment (Checks)
variable {n : Nat} {KemSK Value : Type}

def IsLocalKem : (RegistrationBeaconReferenceCompiler.Spec n Unit).Domain → Prop
  | .inr (.inr _) => True
  | _ => False

def IsRoutedKem : (RegistrationNativePublicFrontend.Spec n Unit).Domain → Prop
  | .inl (.inr (.inr _)) => True
  | _ => False

instance : DecidablePred (IsLocalKem (n := n)) := fun query => by
  rcases query with query | (query | query) <;> simp only [IsLocalKem] <;> infer_instance

instance : DecidablePred (IsRoutedKem (n := n)) := fun query => by
  rcases query with (query | (query | query)) | query <;> simp only [IsRoutedKem] <;> infer_instance

theorem effect_zero (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    (simulateQ (RegistrationBeaconReferenceCompiler.effect (KemSK := KemSK)) work).IsQueryBoundP IsLocalKem 0 := by
  apply OracleComp.IsQueryBoundP.simulateQ_of_step (OracleComp.isQueryBoundP_false work 0)
    (fun _ impossible => impossible.elim)
  intro query _
  simp only [RegistrationBeaconReferenceCompiler.effect, isQueryBoundP_query_iff, IsLocalKem]
  intro impossible
  exact impossible.elim

theorem service_zero (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePairedServerService.PublicSpec n).Domain) (before : RegistrationServerReferenceCompiler.Environment) :
    ((RegistrationNativeCommonCompiler.service (RegistrationBeaconReferenceCompiler.effect (KemSK := KemSK))
      (RegistrationServerOpenReferenceCompiler.demand (KemSK := KemSK)) hkdf writer sign query).run before).IsQueryBoundP
        IsLocalKem 0 := by
  cases query with
  | inl message =>
      simp only [RegistrationNativeCommonCompiler.service, StateT.run_lift, bind_pure_comp,
        RegistrationServerOpenReferenceCompiler.demand, isQueryBoundP_map_iff, isQueryBoundP_query_iff,
        IsLocalKem]
      intro impossible
      exact impossible.elim
  | inr query =>
      change ((RegistrationNativeCommonCompiler.common (RegistrationBeaconReferenceCompiler.effect (KemSK := KemSK)) hkdf writer sign query).run before).IsQueryBoundP _ 0
      rw [RegistrationNativeCommonCompiler.common_map]
      exact effect_zero (KemSK := KemSK) _

/-- Every actual build branch, including application conversion failure and an absent one-use token, contains no local KEM request. -/
theorem build_zero (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (wire : RegistrationNativeWire.Wire)
    (checks : Checks) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (handle : Nat) (application : Option (Slice U8)) (server : RegistrationServerMaterialFrontend.State)
    (environment : RegistrationServerReferenceCompiler.Environment) :
    (((RegistrationServerOpenReferenceCompiler.build (n := n) (KemSK := KemSK) hkdf wire checks sign handle application).run server).run environment).IsQueryBoundP IsLocalKem 0 := by
  change ((simulateQ (RegistrationNativeCommonCompiler.service (RegistrationBeaconReferenceCompiler.effect (KemSK := KemSK))
    (RegistrationServerOpenReferenceCompiler.demand (KemSK := KemSK)) hkdf wire.frameWrite sign)
      ((RegistrationServerMaterialFrontend.build wire checks.reservePeer handle application).run server)).run environment).IsQueryBoundP _ 0
  apply (isQueryBoundP_false ((RegistrationServerMaterialFrontend.build wire checks.reservePeer handle application).run server) 0).simulateQ_run_StateT_of_step
  intro query before
  exact service_zero (KemSK := KemSK) hkdf wire.frameWrite sign query before

theorem local_lift_zero (selected : Bool) (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value)
    (bounded : work.IsQueryBoundP IsLocalKem 0) :
    (simulateQ (RegistrationNativePublicFrontend.liftLocal selected) work).IsQueryBoundP IsRoutedKem 0 := by
  induction work using OracleComp.inductionOn with
  | pure value => exact isQueryBoundP_pure IsRoutedKem value 0
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      have quiet : ¬IsLocalKem query := bounded.1.resolve_right (Nat.not_lt_zero _)
      rcases query with message | (query | query)
      · simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePublicFrontend.liftLocal]
        apply (isQueryBoundP_query_bind_iff _ _ _ _).mpr
        exact ⟨Or.inl (by simp only [IsRoutedKem, not_false_eq_true]), fun reply => ih reply (by simpa using bounded.2 reply)⟩
      · simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePublicFrontend.liftLocal]
        apply (isQueryBoundP_query_bind_iff _ _ _ _).mpr
        exact ⟨Or.inl (by simp only [IsRoutedKem, not_false_eq_true]), fun reply => ih reply (by simpa using bounded.2 reply)⟩
      · exact False.elim (quiet trivial)

/-- Packing the complete build into the actual mixed native frontend cannot introduce a provider callback. -/
theorem frontend_zero (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (wire : RegistrationNativeWire.Wire)
    (checks : Checks) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (handle : Nat) (application : Option (Slice U8)) {source : RegistrationNativeMldsa.Source}
    (before : RegistrationNativePublicFrontend.State source) :
    ((RegistrationNativePublicFrontend.serverOpen false
      (RegistrationServerOpenReferenceCompiler.build (n := n) (KemSK := KemSK) hkdf wire checks sign handle application)).run before).IsQueryBoundP IsRoutedKem 0 := by
  dsimp only [RegistrationNativePublicFrontend.serverOpen, StateT.run]
  rw [isQueryBoundP_map_iff]
  exact local_lift_zero false _ (build_zero hkdf wire checks sign handle application before.server before.environment)

end BeaconcryptCore.Computational.RegistrationNativeProviderBuildCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBuildCaps.effect_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBuildCaps.effect_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBuildCaps.service_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBuildCaps.service_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBuildCaps.build_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBuildCaps.build_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBuildCaps.local_lift_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBuildCaps.local_lift_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBuildCaps.frontend_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBuildCaps.frontend_zero
