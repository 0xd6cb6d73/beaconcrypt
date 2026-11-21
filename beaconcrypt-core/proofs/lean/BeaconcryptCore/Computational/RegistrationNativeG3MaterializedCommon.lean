-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3CommonBeacon
import BeaconcryptCore.Computational.RegistrationNativeG3AuditedWorld

/-! A fixed private seed table materializes the public hidden installation references as their canonical concrete kernels. Every other common callback uses the actual shared World and chronological signing receipts. This interpreter performs actual known-kernel lifecycle and occupancy checks; it neither reads a hidden seed cache nor assumes unused roles. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommon
open RegistrationNativeG3Common (State publication)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativeG3AuditedWorld (Seeds)
variable {n : Nat} {Value : Type}

noncomputable def effect (seeds : Seeds n) : QueryImpl (EnvEffects n) (StateT (State n) ProbComp)
  | .inr (.installServer keyId binding (.hidden slot)) => RegistrationNativeG3Common.effect
      (.inr (.installServer keyId binding (.known (PqxdhRecordLiftWorld.kernel .server (seeds slot)))))
  | .inr (.installBeacon owner shell (.hidden slot)) => RegistrationNativeG3Common.effect
      (.inr (.installBeacon owner shell (.known (PqxdhRecordLiftWorld.kernel .beacon (seeds slot)))))
  | query => RegistrationNativeG3Common.effect query

noncomputable def handler (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) : QueryImpl (RegistrationNativePairedServerService.Common n) (StateT (State n) ProbComp)
  | .inl query => publication source writer sign query
  | .inr query => effect seeds query

/-- Fixed-table materialization leaves every actual hash/coin callback unchanged. -/
theorem effect_primitive (seeds : Seeds n) (query : (EnvEffects n).Domain)
    (primitive : RegistrationNativeG3Common.Primitive query) : effect seeds query = RegistrationNativeG3Common.effect query := by
  cases query with
  | inl coin => rfl
  | inr request => cases request with
    | hash bytes => rfl
    | _ => exact primitive.elim

/-- The public installation stage retains the exact actual mutable publication interpreter. -/
theorem publication_lift (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (work : OracleComp RegistrationBoundPublication.Spec Value) :
    simulateQ (handler source writer sign seeds) (simulateQ RegistrationHiddenInstall.publicationLift work) =
      simulateQ (publication source writer sign) work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : handler source writer sign seeds ∘ₛ RegistrationHiddenInstall.publicationLift = publication source writer sign := by
    funext query
    simp only [QueryImpl.compose, RegistrationHiddenInstall.publicationLift, simulateQ_spec_query, handler]
  rw [same]

/-- Materializing a public installation changes only its hidden reference to the fixed canonical known kernel. -/
theorem effect_lift (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (work : OracleComp (EnvEffects n) Value) :
    simulateQ (handler source writer sign seeds) (simulateQ RegistrationHiddenInstall.effectLift work) =
      simulateQ (effect seeds) work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : handler source writer sign seeds ∘ₛ RegistrationHiddenInstall.effectLift = effect seeds := by
    funext query
    simp only [QueryImpl.compose, RegistrationHiddenInstall.effectLift, simulateQ_spec_query, handler]
  rw [same]

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommon.effect_primitive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommon.effect_primitive
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommon.publication_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommon.publication_lift
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommon.effect_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommon.effect_lift
