-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallTrace

/-! Actual mutable Common callbacks cannot prepare or demand a new root descriptor. The concrete paired Server and Beacon suffixes therefore have their exact per-role atom-attempt bills under the chronological observer, including every publication and installation failure. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomCommonTrace
open PqxdhRecordLiftInterface (Role EnvEffects)
open RegistrationNativePairedServerService (Common)
open RegistrationNativeSecretWordInterface (LocalSpec liftLocal effect)
open RegistrationNativeSecretWordAtomInstallCaps (Install)
open RegistrationNativeSecretWordAtomInstallPredicate (GlobalInstall)
open RegistrationNativeSecretWordAtomInstallTrace (RootFree atom count)
open RegistrationNativeSecretWordFrontendTrace (State handler)
variable {n : Nat} {KemSK Value Encoded Auxiliary : Type}

def compile (selected : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (Common n) Value) (before : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) (Value × RegistrationWorldAgreementCompiler.EnvState Auxiliary) :=
  simulateQ (liftLocal selected)
    ((simulateQ (RegistrationNativeCommonCompiler.common effect source writer sign) work).run before)

private theorem effects_quiet (selected : Bool) (work : OracleComp (EnvEffects n) Value) :
    (simulateQ ((liftLocal selected) ∘ₛ (effect (KemSK := KemSK))) work).IsQueryBoundP
      (fun query => ¬ RootFree (KemSK := KemSK) query) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [QueryImpl.compose, effect, liftLocal, RootFree, isQueryBoundP_query_iff]

/-- The complete actual Common compiler emits no root prepare or demand query. -/
theorem quiet (selected : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (Common n) Value) (before : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    (compile (KemSK := KemSK) selected source writer sign work before).IsQueryBoundP
      (fun query => ¬ RootFree (KemSK := KemSK) query) 0 := by
  unfold compile
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  apply (isQueryBoundP_false work 0).simulateQ_run_of_step
  · intro query impossible state
    exact impossible.elim
  · intro query _ordinary state
    simp only [QueryImpl.mapStateTBase, StateT.run_mk]
    rw [RegistrationNativeCommonCompiler.common_map, ← QueryImpl.simulateQ_compose]
    exact effects_quiet selected _

/-- A bounded open Common program keeps its actual role bill when compiled on the current mutable environment. -/
theorem bound (role : Role) (selected : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (Common n) Value) (cap : Nat) (bounded : work.IsQueryBoundP (Install role) cap)
    (before : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (trace : State)
    (result : (Value × RegistrationWorldAgreementCompiler.EnvState Auxiliary) × State)
    (supported : result ∈ support ((simulateQ handler (compile (KemSK := KemSK) selected source writer sign work before)).run trace)) :
    atom result.2.current ≤ atom trace.current ∧ count role result.2 ≤ count role trace + cap * atom trace.current := by
  exact RegistrationNativeSecretWordAtomInstallTrace.program role _ cap
    (RegistrationNativeSecretWordAtomInstallPredicate.local_bound role selected _ cap
      (RegistrationNativeSecretWordAtomInstallCompiler.common_bound role source writer sign work cap bounded before))
    (quiet selected source writer sign work before) trace result supported

/-- The actual Server material suffix can record only its own one installation attempt for its current atom descriptor. -/
theorem server (role : Role) (selected : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded) (control : pqxdh.ServerState)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (choice : RegistrationNativePairedChoice.Choice n)
    (before : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (trace : State)
    (result : (RustM (RegistrationNativePairedServerService.Result Encoded) × RegistrationWorldAgreementCompiler.EnvState Auxiliary) × State)
    (supported : result ∈ support ((simulateQ handler (compile (KemSK := KemSK) selected source writer sign
      (RegistrationNativePairedServerService.publicBranch encode control initial choice) before)).run trace)) :
    atom result.2.current ≤ atom trace.current ∧ count role result.2 ≤ count role trace +
      (if role = .server then 1 else 0) * atom trace.current :=
  bound role selected source writer sign _ _ (RegistrationNativeSecretWordAtomInstallCaps.server_branch role encode control initial choice)
    before trace result supported

/-- The actual Beacon material suffix can record only its own one installation attempt for its current atom descriptor. -/
theorem beacon (role : Role) (selected : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (choice : RegistrationNativePairedChoice.Choice n)
    (before : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (trace : State)
    (result : (RustM RegistrationNativePairedBeaconService.Result × RegistrationWorldAgreementCompiler.EnvState Auxiliary) × State)
    (supported : result ∈ support ((simulateQ handler (compile (KemSK := KemSK) selected source writer sign
      (RegistrationNativePairedBeaconService.publicBranch source owner sender descriptor choice) before)).run trace)) :
    atom result.2.current ≤ atom trace.current ∧ count role result.2 ≤ count role trace +
      (if role = .beacon then 1 else 0) * atom trace.current :=
  bound role selected source writer sign _ _ (RegistrationNativeSecretWordAtomInstallCaps.beacon_branch role source owner sender descriptor choice)
    before trace result supported

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomCommonTrace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomCommonTrace.quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomCommonTrace.quiet
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomCommonTrace.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomCommonTrace.bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomCommonTrace.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomCommonTrace.server
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomCommonTrace.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomCommonTrace.beacon
