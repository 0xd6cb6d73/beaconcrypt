-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenMemo
/-! The actual corrected accept retains the Ready returned by its source agreement and the same private memo. Owned retention is a pure source step and cannot discard the agreement's root receipt or change the common platform state. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerAcceptMemo
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRelatedFamily (Message)
open PqxdhSecretInputKdf (RootOutput)
open RegistrationNativeKemReferenceWorld (Private)
open RegistrationServerReferenceMemoReceipt (MemoStore remember)
open RegistrationNativePlatformServerOpenControl (State close)
open RegistrationNativePlatformServerOpenKernel (handler agreement)
open RegistrationNativePlatformServerOpenSource (callbacks)
open RegistrationNativePlatformServerReferenceAccept (retain)
variable {n : Nat} {ι KemSK Extra Platform : Type} {base : OracleSpec ι}

private theorem map_apply {A B : Type} (observe : A → B) (work : StateT Platform ProbComp A) (before : Platform) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (StateT.pure value : StateT S m A) before = pure (value, before) := rfl

private theorem retain_run (ready : RegistrationServerReferenceRoot.Ready) (before : State n KemSK Extra) (previous : Platform) :
    ((close (m := StateT Platform ProbComp) (retain ready)).run before).run previous =
      match RegistrationServerMaterialFrontend.retain ready before.1 with
      | .fail error => pure ((.fail error, before), previous)
      | .div => pure ((.div, before), previous)
      | .ok (reply, front) => pure ((.ok reply, (front, before.2)), previous) := by
  unfold close
  cases retained : RegistrationServerMaterialFrontend.retain ready before.1 with
  | fail error | div =>
      simp only [retain, RegistrationNativePlatformServerOpenKernel.closeEnvironment,
        StateT.run, retained, StateT.monad_pure_def, map_apply, pure_apply, map_pure]
      rfl
  | ok result =>
      rcases result with ⟨reply, front⟩
      simp only [retain, RegistrationNativePlatformServerOpenKernel.closeEnvironment,
        StateT.run, retained, StateT.monad_pure_def, map_apply, pure_apply, map_pure]
      rfl


private theorem retained_entry (ready : RegistrationServerReferenceRoot.Ready) (handle : Nat)
    (before after : RegistrationServerMaterialFrontend.State)
    (retained : RegistrationServerMaterialFrontend.retain ready before = .ok (some handle, after)) :
    after.sessions[handle]? = some (some ready) := by
  unfold RegistrationServerMaterialFrontend.retain at retained
  cases consumed : RegistrationReplaySchedule.consume
    (RegistrationServerReferenceRoot.atRoot ready RegistrationBoundKeySchedule.zero) before.consumed with
  | fail error => simp only [consumed] at retained; cases retained
  | div => simp only [consumed] at retained; cases retained
  | ok result =>
      rcases result with ⟨optional, history⟩
      cases optional with
      | none => simp only [consumed] at retained; cases retained
      | some token =>
          simp only [consumed, RustM.ok.injEq, Prod.mk.injEq, Option.some.injEq] at retained
          rcases retained with ⟨rfl, rfl⟩
          simp only [List.getElem?_append, Nat.lt_irrefl, ite_false, Nat.sub_self, List.getElem?_cons_zero]

/-- Successful owned insertion retains that exact Ready and preserves the complete indexed private state and public platform poststate. -/
theorem retained (ready : RegistrationServerReferenceRoot.Ready) (handle : Nat)
    (before after : State n KemSK Extra) (previous next : Platform)
    (supported : ((.ok (some handle), after), next) ∈ support (((close (m := StateT Platform ProbComp) (retain ready)).run before).run previous)) :
    after.1.sessions[handle]? = some (some ready) ∧ after.2 = before.2 ∧ next = previous := by
  rw [retain_run] at supported
  cases actual : RegistrationServerMaterialFrontend.retain ready before.1 with
  | fail error => simp only [actual, support_pure, Set.mem_singleton_iff] at supported; cases supported
  | div => simp only [actual, support_pure, Set.mem_singleton_iff] at supported; cases supported
  | ok result =>
      rcases result with ⟨reply, front⟩
      simp only [actual, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, RustM.ok.injEq] at supported
      rcases before with ⟨initial, backendInitial⟩
      rcases after with ⟨final, after⟩
      dsimp only at supported
      rcases supported with ⟨⟨rfl, ⟨rfl, rfl⟩⟩, rfl⟩
      exact ⟨retained_entry ready handle initial front actual, rfl, rfl⟩

/-- Replay and the actual stateful reserve precede source agreement; any returned handle still has its same-run private preparation receipt after insertion. -/
theorem after_authentication [MemoStore Extra] (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (services : RegistrationNativeKemReferenceEffects.Callbacks n KemSK Extra)
    (demand : QueryImpl (Message →ₒ Option (RegistrationNativePairedChoice.Choice n))
      (StateT (Private n KemSK Extra) (StateT Platform ProbComp)))
    (publication : QueryImpl RegistrationBoundPublication.Spec (StateT (Private n KemSK Extra) (StateT Platform ProbComp)))
    (reserve : StateT Platform ProbComp Bool) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (handle : Nat)
    (before after : State n KemSK Extra) (previous next : Platform)
    (supported : ((.ok (some handle), after), next) ∈ support
      (((close (RegistrationNativePlatformServerOpenControl.afterAuthentication
        (handler coins setup (callbacks setup seed scalar remember services demand publication))
        (StateT.lift reserve) setup checks packet authenticated)).run before).run previous)) :
    ∃ ready root, after.1.sessions[handle]? = some (some ready) ∧
      MemoStore.read after.2.2.extra ready.reference = some root ∧
      RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar ready.reference = some root := by
  rw [RegistrationNativePlatformServerOpenControl.afterAuthentication,
    RegistrationNativePlatformServerOpenControl.close_bind, StateT.run_bind,
    RegistrationNativePlatformServerOpenControl.close_get, pure_bind] at supported
  split at supported
  · simp only [RegistrationNativePlatformServerOpenControl.close_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
  · rw [RegistrationNativePlatformServerOpenControl.close_bind, StateT.run_bind,
      RegistrationNativePlatformServerOpenControl.close_reserve] at supported
    simp only [StateT.run_bind, bind_map_left, mem_support_bind_iff] at supported
    obtain ⟨⟨admitted, atAgreement⟩, _reserved, continued⟩ := supported
    cases admitted with
    | false =>
        simp only [Bool.false_eq_true, ite_false, RegistrationNativePlatformServerOpenControl.close_pure,
          StateT.run_pure, mem_support_pure_iff] at continued
        cases continued
    | true =>
        simp only [ite_true, RegistrationNativePlatformServerOpenControl.close_bind,
          StateT.run_bind, mem_support_bind_iff] at continued
        obtain ⟨⟨⟨reply, current⟩, atRetention⟩, agreed, continued⟩ := continued
        cases reply with
        | fail error | div =>
            simp only [RegistrationNativePlatformServerOpenControl.close_pure, StateT.run_pure, mem_support_pure_iff] at continued
            cases continued
        | ok optional => cases optional with
          | none =>
              simp only [RegistrationNativePlatformServerOpenControl.close_pure, StateT.run_pure, mem_support_pure_iff] at continued
              cases continued
          | some ready =>
              have receipt := RegistrationNativePlatformServerOpenMemo.agreement_receipt coins setup checks seed scalar services
                demand publication packet authenticated ready before current atAgreement atRetention agreed
              have kept := retained ready handle current after atRetention next continued
              obtain ⟨root, stored, computed⟩ := receipt.2
              refine ⟨ready, root, kept.1, ?_, computed⟩
              rw [kept.2.1]
              exact stored

attribute [local irreducible] RegistrationNativePlatformServerOpenControl.afterAuthentication
  RegistrationNativePlatformServerOpenKernel.handler RegistrationNativePlatformServerOpenSource.callbacks
  RegistrationAuthenticationCompiler.program

private theorem after_pin [MemoStore Extra] (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (services : RegistrationNativeKemReferenceEffects.Callbacks n KemSK Extra)
    (demand : QueryImpl (Message →ₒ Option (RegistrationNativePairedChoice.Choice n))
      (StateT (Private n KemSK Extra) (StateT Platform ProbComp)))
    (publication : QueryImpl RegistrationBoundPublication.Spec (StateT (Private n KemSK Extra) (StateT Platform ProbComp)))
    (reserve : StateT Platform ProbComp Bool) (packet : registration.InitPacket)
    (result : RegistrationNativeServerPinRecompute.PinReply) (handle : Nat)
    (before after : State n KemSK Extra) (previous next : Platform)
    (supported : ((.ok (some handle), after), next) ∈ support
      (((close (RegistrationNativePlatformServerOpenControl.afterPin
        (handler coins setup (callbacks setup seed scalar remember services demand publication))
        (StateT.lift reserve) setup checks verify packet result)).run before).run previous)) :
    ∃ ready root, after.1.sessions[handle]? = some (some ready) ∧
      MemoStore.read after.2.2.extra ready.reference = some root ∧
      RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar ready.reference = some root := by
  cases result with
  | fail error | div =>
      simp only [RegistrationNativePlatformServerOpenControl.afterPin,
        RegistrationNativePlatformServerOpenControl.close_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
  | ok optional => cases optional with
    | none =>
        simp only [RegistrationNativePlatformServerOpenControl.afterPin,
          RegistrationNativePlatformServerOpenControl.close_pure, StateT.run_pure, mem_support_pure_iff] at supported
        cases supported
    | some pin =>
        rw [RegistrationNativePlatformServerOpenControl.afterPin,
          RegistrationNativePlatformServerOpenControl.close_bind, StateT.run_bind,
          RegistrationNativePlatformServerOpenControl.close_effect] at supported
        simp only [StateT.run_bind, bind_map_left, mem_support_bind_iff] at supported
        obtain ⟨⟨⟨checked, current⟩, atAfterAuthentication⟩, _authenticated, continued⟩ := supported
        cases checked with
        | fail error | div =>
            simp only [RegistrationNativePlatformServerOpenControl.close_pure, StateT.run_pure, mem_support_pure_iff] at continued
            cases continued
        | ok checked =>
            rcases checked with ⟨events, verdict⟩
            cases verdict with
            | Accepted authenticated =>
                exact after_authentication coins setup checks seed scalar services demand publication reserve packet authenticated
                  handle _ after atAfterAuthentication next continued
            | Rejected | HashRequested _ | MldsaVerificationRequested _ | Ed25519VerificationRequested _ | ServerFingerprintRequested _ | BeaconFingerprintRequested _ =>
                simp only [RegistrationNativePlatformServerOpenControl.close_pure, StateT.run_pure, mem_support_pure_iff] at continued
                cases continued

/-- The complete actual indexed accept entry returns only capabilities backed by a source root in its same final private memo, after the real pin, authentication, replay and allocation prefixes. -/
theorem accept [MemoStore Extra] (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (services : RegistrationNativeKemReferenceEffects.Callbacks n KemSK Extra)
    (demand : QueryImpl (Message →ₒ Option (RegistrationNativePairedChoice.Choice n))
      (StateT (Private n KemSK Extra) (StateT Platform ProbComp)))
    (publication : QueryImpl RegistrationBoundPublication.Spec (StateT (Private n KemSK Extra) (StateT Platform ProbComp)))
    (reserve : StateT Platform ProbComp Bool) (packet : registration.InitPacket) (handle : Nat)
    (before after : State n KemSK Extra) (previous next : Platform)
    (supported : ((.ok (some handle), after), next) ∈ support
      (((close (RegistrationNativePlatformServerOpenControl.accept
        (handler coins setup (callbacks setup seed scalar remember services demand publication))
        (StateT.lift reserve) setup checks verify packet)).run before).run previous)) :
    ∃ ready root, after.1.sessions[handle]? = some (some ready) ∧
      MemoStore.read after.2.2.extra ready.reference = some root ∧
      RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar ready.reference = some root := by
  rw [RegistrationNativePlatformServerOpenControl.accept,
    RegistrationNativePlatformServerOpenControl.close_bind, StateT.run_bind,
    RegistrationNativePlatformServerOpenControl.close_get, pure_bind,
    RegistrationNativePlatformServerOpenControl.close_bind, StateT.run_bind,
    RegistrationNativePlatformServerOpenControl.close_effect] at supported
  simp only [StateT.run_bind, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨pin, current⟩, atAfterPin⟩, _pinComputed, continued⟩ := supported
  exact after_pin coins setup checks verify seed scalar services demand publication reserve packet pin handle
    _ after atAfterPin next continued

end BeaconcryptCore.Computational.RegistrationNativePlatformServerAcceptMemo

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerAcceptMemo.retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerAcceptMemo.retained

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerAcceptMemo.after_authentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerAcceptMemo.after_authentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerAcceptMemo.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerAcceptMemo.accept
