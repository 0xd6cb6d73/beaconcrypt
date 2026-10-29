-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentCaps

/-! Every adaptive local native controller embeds the restricted thin environment back into its literal original World program. Structural zero-record bounds discharge the boundary; no whole-game equivalence or noninterference premise is supplied. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (effectLift)
open RegistrationNativeHiddenEnvironmentCaps (IsRecord)
open RegistrationNativeHiddenInterpreter (State Provider)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

/-- The same concrete restricted callback compiler preserves every full thin-client state through arbitrary local adaptive work. -/
theorem program_local (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (bounded : work.IsQueryBoundP IsRecord 0) (before : State n KemSK ProviderState) :
    simulateQ effectLift ((simulateQ (RegistrationNativeHiddenEnvironmentHandler.handler setup wire sign seed scalar provider) work).run before) =
      (simulateQ (RegistrationNativeHiddenInterpreter.handler setup wire sign seed scalar provider) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      have localQuery : ¬IsRecord query := bounded.1.resolve_right (Nat.not_lt_zero _)
      cases query with
      | inr record => exact (localQuery trivial).elim
      | inl query =>
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
          rw [RegistrationNativeHiddenEnvironmentHandler.local_query]
          apply bind_congr
          intro result
          exact ih result.1 (by simpa using bounded.2 result.1) result.2

/-- The literal typed registration callback has its exact restricted-environment interpretation on every native failure or success branch. -/
theorem typed_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat)
    (command : RegistrationNativeRawAdapter.Command) (environment : RegistrationNativeHiddenEnvironmentCaps.IsEnvironment command)
    (frontend : RegistrationNativePublicFrontend.State source) (before : State n KemSK ProviderState) :
    simulateQ effectLift ((simulateQ (RegistrationNativeHiddenEnvironmentHandler.handler setup wire sign seed scalar provider)
      ((RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar)
        (.inr command)).run frontend)).run before) =
      (simulateQ (RegistrationNativeHiddenInterpreter.handler setup wire sign seed scalar provider)
        ((RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar)
          (.inr command)).run frontend)).run before :=
  program_local setup wire sign seed scalar provider _
    (RegistrationNativeHiddenEnvironmentCaps.typed_zero setup checks wire source sign selectedOwner selectedAccept
      (setup.dh.publicKey scalar) command environment frontend) before

end BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentSource.program_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentSource.program_local
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentSource.typed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentSource.typed_source
