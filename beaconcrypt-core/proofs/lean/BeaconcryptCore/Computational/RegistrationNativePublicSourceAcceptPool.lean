-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicServerPool

/-! Full native accept pool preservation closes the private frame omitted by the SDK's Server-only result projection. Source authentication, root preparation and every replay/retention branch retain the entire owner KEM transcript. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceAcceptPool
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemReferenceEffects (Callbacks implementation)
open RegistrationNativeKemReferenceWorld (Private)
open RegistrationNativeRelatedFamily (Message)
open PqxdhSecretInputKdf (RootOutput)
open RegistrationServerOpenReferenceSourceStage (callbacks)
open RegistrationServerOpenReferenceSourceAccept (State close)
variable {n : Nat} {ι KemSK Extra Value : Type} {base : OracleSpec ι}
attribute [local irreducible] RegistrationAuthenticationCompiler.program

private theorem prepare_pool (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (remember : Extra → Message → Option RootOutput → Extra)
    (services : Callbacks n KemSK Extra) (work : OracleComp RegistrationServerReferenceRoot.PrepareSpec Value)
    (before : Private n KemSK Extra) (result : Value × Private n KemSK Extra)
    (supported : result ∈ support ((simulateQ (implementation setup (callbacks setup seed scalar remember services))
      (simulateQ RegistrationBeaconReferenceCompiler.prepare work)).run before)) : result.2.pool = before.pool := by
  rw [← QueryImpl.simulateQ_compose] at supported
  have same : implementation setup (callbacks setup seed scalar remember services) ∘ₛ
      RegistrationBeaconReferenceCompiler.prepare =
      RegistrationServerOpenReferenceSourceStage.prepare setup seed scalar remember := by
    funext message
    simp only [QueryImpl.compose, RegistrationBeaconReferenceCompiler.prepare,
      simulateQ_spec_query, implementation, RegistrationNativeKemReferenceWorld.handler, callbacks]
  rw [same] at supported
  induction work using OracleComp.inductionOn generalizing before result with
  | pure output =>
      rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      rfl
  | query_bind message next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨step, reached, tail⟩ := supported
      simp only [RegistrationServerOpenReferenceSourceStage.prepare, StateT.run, mem_support_pure_iff] at reached
      have last := ih step.1 step.2 result tail
      subst step
      exact last

/-- Actual successful or failed native agreement preparation leaves the complete owner KEM pool untouched. -/
theorem agreement_pool (setup : Setup base KemSK) (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (remember : Extra → Message → Option RootOutput → Extra)
    (services : Callbacks n KemSK Extra) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit)
    (before : RegistrationNativeKemReferenceBackend.State n KemSK Extra)
    (result : RustM (Option RegistrationServerReferenceRoot.Ready) × RegistrationNativeKemReferenceBackend.State n KemSK Extra)
    (supported : result ∈ support ((RegistrationServerOpenReferenceSourceStage.agreement setup checks seed scalar remember services packet authenticated).run before)) :
    result.2.2.pool = before.2.pool := by
  rw [RegistrationServerOpenReferenceSourceStage.agreement_run, mem_support_bind_iff] at supported
  obtain ⟨collected, reached, supported⟩ := supported
  have frame := RegistrationNativePublicServerPool.collect_frame setup checks
    (callbacks setup seed scalar remember services) packet authenticated before collected reached
  cases outcome : collected.1 with
  | none =>
      simp only [outcome, mem_support_pure_iff] at supported
      subst result
      exact frame.1
  | some input =>
      simp only [outcome, support_map] at supported
      obtain ⟨prepared, reached, rfl⟩ := supported
      exact (prepare_pool setup seed scalar remember services _ collected.2.2 prepared reached).trans frame.1

private theorem close_agreement_pool (setup : Setup base KemSK) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra) (services : Callbacks n KemSK Extra)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : State n KemSK Extra) (result : RustM (Option RegistrationServerReferenceRoot.Ready) × State n KemSK Extra)
    (supported : result ∈ support ((close setup seed scalar remember services
      (RegistrationServerOpenReferenceCompiler.agreement setup checks packet authenticated)).run before)) :
    result.2.2.2.pool = before.2.2.pool := by
  rw [RegistrationServerOpenReferenceSourceAccept.agreement_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact agreement_pool setup checks seed scalar remember services packet authenticated before.2 inner reached

private theorem retain_pool (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (remember : Extra → Message → Option RootOutput → Extra)
    (services : Callbacks n KemSK Extra) (ready : RegistrationServerReferenceRoot.Ready)
    (before : State n KemSK Extra) (result : RustM (Option Nat) × State n KemSK Extra)
    (supported : result ∈ support ((close setup seed scalar remember services
      (RegistrationServerOpenReferenceCompiler.retain ready)).run before)) :
    result.2.2.2.pool = before.2.2.pool := by
  rw [RegistrationServerOpenReferenceSourceAccept.retain_run, support_map] at supported
  obtain ⟨inner, _reached, rfl⟩ := supported
  rfl

/-- Replay refusal, registration allocation and owned one-use retention preserve the entire owner pool history. -/
theorem after_pool (setup : Setup base KemSK) (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (remember : Extra → Message → Option RootOutput → Extra)
    (services : Callbacks n KemSK Extra) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : State n KemSK Extra)
    (result : RustM (Option Nat) × State n KemSK Extra)
    (supported : result ∈ support ((close setup seed scalar remember services
      (RegistrationServerOpenReferenceCompiler.afterAuthentication setup checks packet authenticated)).run before)) :
    result.2.2.2.pool = before.2.2.pool := by
  rw [RegistrationServerOpenReferenceSourceAccept.after_run] at supported
  split at supported
  · rw [mem_support_pure_iff] at supported
    subst result
    rfl
  · split at supported
    · rw [mem_support_bind_iff] at supported
      obtain ⟨completed, reached, supported⟩ := supported
      have first := close_agreement_pool setup checks seed scalar remember services packet authenticated before completed reached
      cases outcome : completed.1 with
      | fail error =>
          simp only [outcome, mem_support_pure_iff] at supported
          subst result
          exact first
      | div =>
          simp only [outcome, mem_support_pure_iff] at supported
          subst result
          exact first
      | ok ready => cases ready with
        | none =>
            simp only [outcome, mem_support_pure_iff] at supported
            subst result
            exact first
        | some ready =>
            simp only [outcome] at supported
            exact (retain_pool setup seed scalar remember services ready completed.2 result supported).trans first
    · rw [mem_support_pure_iff] at supported
      subst result
      rfl

private theorem authentication_pool (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra) (services : Callbacks n KemSK Extra)
    (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value)
    (before : State n KemSK Extra) (result : Value × State n KemSK Extra)
    (supported : result ∈ support ((close setup seed scalar remember services
      (StateT.lift (StateT.lift (simulateQ RegistrationBeaconReferenceCompiler.effect work)))).run before)) :
    result.2.2.2.pool = before.2.2.pool := by
  rw [RegistrationServerOpenReferenceSourceEntry.close_effect, support_map] at supported
  obtain ⟨inner, _reached, rfl⟩ := supported
  rfl

/-- The entire native Server accept, including mandatory authentication and every failed poststate, preserves all owner keys and pool transcript entries. -/
theorem accept_pool (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra) (services : Callbacks n KemSK Extra)
    (packet : registration.InitPacket) (before : State n KemSK Extra) (result : RustM (Option Nat) × State n KemSK Extra)
    (supported : result ∈ support ((close setup seed scalar remember services
      (RegistrationServerOpenReferenceCompiler.accept setup checks verify packet)).run before)) :
    result.2.2.2.pool = before.2.2.pool := by
  rw [RegistrationServerOpenReferenceCompiler.accept, RegistrationServerOpenReferenceSourceAccept.close_bind,
    RegistrationServerOpenReferenceSourceAccept.close_get, pure_bind,
    RegistrationServerOpenReferenceSourceAccept.close_bind, mem_support_bind_iff] at supported
  obtain ⟨checked, reached, supported⟩ := supported
  have first := authentication_pool setup seed scalar remember services _ before checked reached
  cases outcome : checked.1 with
  | fail error =>
      simp only [outcome, RegistrationServerOpenReferenceSourceAccept.close_pure, mem_support_pure_iff] at supported
      subst result
      exact first
  | div =>
      simp only [outcome, RegistrationServerOpenReferenceSourceAccept.close_pure, mem_support_pure_iff] at supported
      subst result
      exact first
  | ok checkedReply =>
      rcases checkedReply with ⟨events, verdict⟩
      cases verdict <;> simp only [outcome] at supported
      all_goals try
        simp only [RegistrationServerOpenReferenceSourceAccept.close_pure, mem_support_pure_iff] at supported
        subst result
        exact first
      case Accepted authenticated =>
        exact (after_pool setup checks seed scalar remember services packet authenticated checked.2 result supported).trans first

end BeaconcryptCore.Computational.RegistrationNativePublicSourceAcceptPool
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceAcceptPool.agreement_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceAcceptPool.agreement_pool
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceAcceptPool.after_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceAcceptPool.after_pool
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceAcceptPool.accept_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceAcceptPool.accept_pool
