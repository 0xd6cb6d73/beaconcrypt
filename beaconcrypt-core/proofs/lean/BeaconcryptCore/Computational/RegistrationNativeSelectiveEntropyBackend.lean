-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreter
import BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentSource

/-! The selective material backend closes through the same restricted environment effects as the actual thin native backend. The extra nonselected108-byte cache remains part of the full local state. Local callback embedding is derived from the actual old callback or the literal new demand AST, rather than a whole-program correspondence premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyBackend
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (WorldSpec EnvEffects effectLift)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveHiddenInterpreter (State handler onBase onKeys)
open RegistrationNativeHiddenEnvironmentHandler (project effects_project)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

noncomputable def restricted (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) :
    QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (StateT (State n KemSK ProviderState) (OracleComp (EnvEffects n))) :=
  fun query before => simulateQ project ((handler setup wire sign seed scalar candidate provider query).run before)

private theorem local_other (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (query : (RegistrationNativePublicFrontend.RoutedLocalSpec n KemSK).Domain)
    (other : ¬RegistrationNativePublicCaps.IsDemand (n := n) (KemSK := KemSK) (.inl query)) (before : State n KemSK ProviderState) :
    simulateQ effectLift ((restricted setup wire sign seed scalar candidate provider (.inl query)).run before) =
      (handler setup wire sign seed scalar candidate provider (.inl query)).run before := by
  have oldLaw := RegistrationNativeHiddenEnvironmentHandler.local_query setup wire sign seed scalar provider query before.1
  unfold restricted
  rw [RegistrationNativeSelectiveHiddenInterpreter.query_other setup wire sign seed scalar candidate provider (.inl query) other]
  simp only [onBase, StateT.run, simulateQ_map]
  exact congrArg (fun distribution => (fun result => (result.1, (result.2, before.2))) <$> distribution) oldLaw

/-- Every actual selective local callback embeds back into its exact original World program, retaining both material tables and all other fields. -/
theorem local_query (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (query : (RegistrationNativePublicFrontend.RoutedLocalSpec n KemSK).Domain) (before : State n KemSK ProviderState) :
    simulateQ effectLift ((restricted setup wire sign seed scalar candidate provider (.inl query)).run before) =
      (handler setup wire sign seed scalar candidate provider (.inl query)).run before := by
  rcases query with message | ((message | publication | effect) | kem)
  · exact local_other setup wire sign seed scalar candidate provider _ (by intro impossible; cases impossible) before
  · simp only [restricted, handler, onKeys, StateT.run, simulateQ_map, effects_project]
  · exact local_other setup wire sign seed scalar candidate provider _ (by intro impossible; cases impossible) before
  · exact local_other setup wire sign seed scalar candidate provider _ (by intro impossible; cases impossible) before
  · exact local_other setup wire sign seed scalar candidate provider _ (by intro impossible; cases impossible) before

/-- Every adaptive local controller has its exact restricted interpretation from the already proved structural zero-record cap. -/
theorem program_local (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (bounded : work.IsQueryBoundP RegistrationNativeHiddenEnvironmentCaps.IsRecord 0) (before : State n KemSK ProviderState) :
    simulateQ effectLift ((simulateQ (restricted setup wire sign seed scalar candidate provider) work).run before) =
      (simulateQ (handler setup wire sign seed scalar candidate provider) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      have localQuery := bounded.1.resolve_right (Nat.not_lt_zero _)
      cases query with
      | inr record => exact (localQuery trivial).elim
      | inl query =>
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
          rw [local_query]
          apply bind_congr
          intro result
          exact ih result.1 (by simpa using bounded.2 result.1) result.2

end BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyBackend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyBackend.local_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyBackend.local_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyBackend.program_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyBackend.program_local
