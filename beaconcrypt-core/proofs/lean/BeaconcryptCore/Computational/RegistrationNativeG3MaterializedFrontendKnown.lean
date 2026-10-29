-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontend
import BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCommon

/-! Fixed-table materialization changes only hidden-reference installation queries. Actual known-kernel effects and publication remain the identical complete callbacks. The generic finite program equalities below retain all World and chronological receipt fields without a seed-cache or role-use assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontendKnown
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativePairedServerService (Common)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativeG3KnownWorldFrameCommon (Allowed EffectAllowed)
open RegistrationNativeSeedDelayFrames (ReadsSeed)
variable {n : Nat} {Value : Type}

/-- Every non-hidden actual effect is literally the same full callback under materialization. -/
theorem effect_unchanged (seeds : Seeds n) (query : (EnvEffects n).Domain) (quiet : EffectAllowed query) :
    RegistrationNativeG3Common.effect query = RegistrationNativeG3MaterializedCommon.effect seeds query := by
  cases query with
  | inl coin => rfl
  | inr query => cases query with
    | installServer keyId binding kernel => cases kernel with
      | known kernel => rfl
      | hidden slot => exact (quiet trivial).elim
    | installBeacon owner shell kernel => cases kernel with
      | known kernel => rfl
      | hidden slot => exact (quiet trivial).elim
    | _ => rfl

/-- Actual adaptive known-effect programs preserve exactly the same result, receipts and complete World. -/
theorem effect_program (seeds : Seeds n) (work : OracleComp (EnvEffects n) Value)
    (quiet : AllQueriesSatisfy work EffectAllowed) :
    simulateQ RegistrationNativeG3Common.effect work = simulateQ (RegistrationNativeG3MaterializedCommon.effect seeds) work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      obtain ⟨allowed, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp quiet
      simp only [simulateQ_bind, simulateQ_spec_query]
      rw [effect_unchanged seeds query allowed]
      congr 1
      funext reply
      exact ih reply (later reply)

/-- Every actual Common program with known installation references has the same full stateful source under the two interpreters. -/
theorem common_program (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (work : OracleComp (Common n) Value) (quiet : AllQueriesSatisfy work Allowed) :
    simulateQ (RegistrationNativeG3Common.handler source writer sign) work =
      simulateQ (RegistrationNativeG3MaterializedCommon.handler source writer sign seeds) work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      obtain ⟨allowed, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp quiet
      have same : RegistrationNativeG3Common.handler source writer sign query =
          RegistrationNativeG3MaterializedCommon.handler source writer sign seeds query := by
        cases query with
        | inl query => rfl
        | inr query => exact effect_unchanged seeds query allowed
      simp only [simulateQ_bind, simulateQ_spec_query]
      rw [same]
      congr 1
      funext reply
      exact ih reply (later reply)

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontendKnown
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontendKnown.effect_unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontendKnown.effect_unchanged
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontendKnown.effect_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontendKnown.effect_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontendKnown.common_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontendKnown.common_program
