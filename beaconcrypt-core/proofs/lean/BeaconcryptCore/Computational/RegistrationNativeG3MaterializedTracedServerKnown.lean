-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerCommon
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontendKnown

/-! Actual known-kernel callbacks retain the exact same chronological monitor before and after materialization. The only differing private effect is a hidden reference, excluded structurally by the established ordinary-effect footprint. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerKnown
open RegistrationNativeG3MaterializedTracedServerCommon (effect handler)
open RegistrationNativeG3KnownWorldFrameCommon (Allowed EffectAllowed)
open RegistrationNativeG3AuditedWorld (Seeds)
variable {n : Nat} {Value : Type}

theorem effect_unchanged (seeds : Seeds n) (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (quiet : EffectAllowed query) :
    effect true seeds query = effect false seeds query := by
  funext before
  simp only [effect, ite_true, Bool.false_eq_true, ite_false]
  rw [RegistrationNativeG3MaterializedFrontendKnown.effect_unchanged seeds query quiet]

theorem common_program (seeds : Seeds n)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (RegistrationNativePairedServerService.Common n) Value)
    (quiet : AllQueriesSatisfy work Allowed) :
    simulateQ (handler true seeds source writer sign) work = simulateQ (handler false seeds source writer sign) work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      obtain ⟨allowed, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp quiet
      have same : handler true seeds source writer sign query = handler false seeds source writer sign query := by
        cases query with
        | inl publication => rfl
        | inr effect => exact effect_unchanged seeds effect allowed
      simp only [simulateQ_bind, simulateQ_spec_query, same]
      congr 1
      funext reply
      exact ih reply (later reply)

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerKnown

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerKnown.effect_unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerKnown.effect_unchanged

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerKnown.common_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerKnown.common_program
