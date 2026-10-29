-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedSafe
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomCommonTrace

/-! The actual mutable Common compiler preserves paired slot provenance through every publication and current-environment callback. Its derived zero-root footprint and original one-installation bill discharge the monitor suffix proof for both complete paired material continuations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedCommon
open PqxdhRecordLiftInterface (Role)
open RegistrationNativePairedChoice (Choice)
open RegistrationNativePairedServerService (Common)
open RegistrationNativeSecretWordInterface (Spec effect liftLocal)
open RegistrationNativeSecretWordAtomCommonTrace (compile)
open RegistrationNativeSecretWordPairedTrace (State handler)
open RegistrationNativeSecretWordPairedSafe (Active Allowed)
variable {n : Nat} {KemSK Value Encoded Auxiliary : Type}

private theorem compile_bind {Next : Type} (selected : Bool)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (Common n) Value) (next : Value → OracleComp (Common n) Next)
    (before : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    compile (KemSK := KemSK) selected source writer sign (work >>= next) before = (do
      let result ← compile selected source writer sign work before
      compile selected source writer sign (next result.1) result.2) := by
  simp only [compile, simulateQ_bind, StateT.run_bind]

private theorem query_allowed (role : Role) (choice : Choice n) (selected : Bool)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (Common n).Domain) (before : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (allowed : RegistrationNativePairedProvenance.Allowed role choice query) :
    AllQueriesSatisfy (compile (KemSK := KemSK) selected source writer sign
      (((Common n).query query) : OracleComp (Common n) ((Common n).Range query)) before)
      (Allowed (KemSK := KemSK) role choice) := by
  cases query with
  | inl publication =>
      apply RegistrationNativeSecretWordPairedSafe.free_allowed
      intro actual
      apply RegistrationNativeSecretWordAtomInstallPredicate.local_bound actual selected
      apply RegistrationNativeSecretWordAtomInstallCompiler.common_bound
      simp [RegistrationNativeSecretWordAtomInstallCaps.Install, isQueryBoundP_query_iff]
  | inr environment =>
      simp only [compile, simulateQ_spec_query, RegistrationNativeCommonCompiler.common,
        StateT.run_lift, bind_pure_comp, simulateQ_map, RegistrationNativeSecretWordInterface.effect, liftLocal]
      apply RegistrationNativeHiddenAllocationCore.mapped _ _ (Allowed role choice)
      exact (allQueriesSatisfy_query_iff _ _).mpr allowed

/-- The actual complete current-environment compiler retains the given literal paired continuation footprint. -/
theorem allowed (role : Role) (choice : Choice n) (selected : Bool)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (Common n) Value) (before : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (valid : AllQueriesSatisfy work (RegistrationNativePairedProvenance.Allowed role choice)) :
    AllQueriesSatisfy (compile (KemSK := KemSK) selected source writer sign work before)
      (Allowed (KemSK := KemSK) role choice) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [compile, simulateQ_pure, StateT.run_pure]; trivial
  | query_bind query next ih =>
      obtain ⟨head, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp valid
      rw [compile_bind]
      apply allQueriesSatisfy_bind (query_allowed role choice selected source writer sign query before head)
      intro reached
      exact ih reached.1 reached.2 (later reached.1)

/-- The exact compiled paired Server material suffix is clean from its own actual demanded descriptor and returned choice. -/
theorem server (selected : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded) (control : pqxdh.ServerState)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (choice : Choice n) (message : RegistrationNativeSecretWordMessage.Message)
    (before : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (trace : State n)
    (clean : trace.bad = false) (active : Active choice message trace)
    (result : (RustM (RegistrationNativePairedServerService.Result Encoded) × RegistrationWorldAgreementCompiler.EnvState Auxiliary) × State n)
    (supported : result ∈ support ((simulateQ handler (compile (KemSK := KemSK) selected source writer sign
      (RegistrationNativePairedServerService.publicBranch encode control initial choice) before)).run trace)) : result.2.bad = false := by
  apply RegistrationNativeSecretWordPairedSafe.suffix .server choice message _ 1 (by omega)
    (RegistrationNativeSecretWordAtomInstallPredicate.local_bound .server selected _ 1
      (RegistrationNativeSecretWordAtomInstallCompiler.common_bound .server source writer sign _ 1
        (RegistrationNativeSecretWordAtomInstallCaps.server_branch .server encode control initial choice) before))
    (RegistrationNativeSecretWordAtomCommonTrace.quiet selected source writer sign _ before)
    (allowed .server choice selected source writer sign _ before (RegistrationNativePairedProvenance.server_branch encode control initial choice))
    trace ⟨clean, Or.inr active⟩ result supported

end BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedCommon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedCommon.allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedCommon.allowed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedCommon.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedCommon.server
