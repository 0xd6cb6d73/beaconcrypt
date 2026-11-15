-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceServer
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSessionFrame
/-! Internal live-root and source-memo invariants of the complete corrected adaptive callback interpreter. Accept advances its actual parsed-attempt counter before the source-derived insertion controller; every other callback uses its derived token-subset frame. No public security event is restricted by these internal invariants. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceInvariant
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicSourceExecution (State execute)
open RegistrationNativePublicSourceState (Live MemoCorrect)
variable {n : Nat} {E Platform ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem accept_only (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (excluded : ¬ RegistrationNativePlatformPublicSessionFrame.NonAccept query) :
    ∃ packet, query = .inr (.accept packet) := by
  cases query with
  | inl coin => exact (excluded trivial).elim
  | inr command => cases command with
    | accept packet => exact ⟨packet, rfl⟩
    | create _ _ _ | bundle _ | build _ _ | finish _ _ | hmac _ _ | hash _ | serverSend _ _ | serverRaw _ | beaconSend _ _ | beaconRaw _ _ =>
        exact (excluded trivial).elim

def advance (before : State n KemSK Platform source) : State n KemSK Platform source :=
  (({ before.1.1 with parsedAccepts := before.1.1.parsedAccepts + 1 }, before.1.2), before.2)

private theorem bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

private theorem get_apply {S : Type} {m : Type → Type} [Monad m] (before : S) :
    (get : StateT S m S) before = pure (before, before) := rfl

private theorem modify_apply {S : Type} {m : Type → Type} [Monad m] (changeState : S → S) (before : S) :
    (modify changeState : StateT S m Unit) before = pure ((), changeState before) := rfl

/- The concrete corrected open-accept program now selects the Server pin purely (no fingerprint hash query), so elaboration-time `whnf` of its support types would evaluate the whole program; keep it opaque to the elaborator here. Proof terms are unchanged. -/
attribute [local irreducible] RegistrationNativePlatformServerOpenControl.accept

section Callbacks
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

noncomputable def callback : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT (State n KemSK Platform source) ProbComp) :=
  fun query => execute setup wire route sign seed scalar
    (RegistrationNativePlatformPublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query)


local notation "dispatch" => callback setup checks wire route sign seed scalar selectedOwner selectedAccept publicPrekey
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

/-- The actual parsed-attempt counter advances before indexed acceptance; private source state and external platform state are otherwise the same. -/
theorem accept_source (packet : registration.InitPacket) (before : State n KemSK Platform source) :
    ((dispatch (.inr (.accept packet))).run before) =
      (execute setup wire route sign seed scalar
        (RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.serverOpen
          (RegistrationNativePlatformServerOpenControl.accept
            (RegistrationNativePlatformPublicFrontend.localHandler (decide (before.1.1.parsedAccepts = selectedAccept)))
            (RegistrationNativePlatformPublicFrontend.platform reserveRegistration) setup checks source.verify packet)))).run (advance before) := by
  simp only [callback, RegistrationNativePlatformPublicSourceExecution.execute, RegistrationNativePlatformPublicFrontend.handler,
    RegistrationNativePlatformPublicFrontend.executeLocal, StateT.run, bind_apply, get_apply,
    modify_apply, pure_bind, advance]
  rfl

/-- Every corrected typed callback preserves actual live-root backing and functional memo correctness. -/
theorem handler (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK Platform source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK Platform source)
    (live : Live before.1.1 before.2) (correct : MemoCorrect setup seed scalar before.2.roots)
    (supported : result ∈ support ((dispatch query).run before)) :
    Live result.2.1.1 result.2.2 ∧ MemoCorrect setup seed scalar result.2.2.roots := by
  by_cases ordinary : RegistrationNativePlatformPublicSessionFrame.NonAccept query
  · exact RegistrationNativePlatformPublicSourceExecution.live_of_subset setup wire route sign seed scalar
      _ before result (fun output reached ready member =>
        RegistrationNativePlatformPublicSessionFrame.handler_nonaccept setup checks wire sign selectedOwner selectedAccept
          publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query ordinary
          before.1 output reached ready member) live correct supported
  · obtain ⟨packet, rfl⟩ := accept_only query ordinary
    rw [accept_source] at supported
    exact RegistrationNativePlatformPublicSourceServer.accept_live setup wire checks route sign seed scalar
      (decide (before.1.1.parsedAccepts = selectedAccept)) reserveRegistration source.verify packet (advance before) result live correct supported


/-- Arbitrary adaptive typed source programs preserve the actual internal root invariants, without adding an eligibility condition. -/
theorem program (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : State n KemSK Platform source) (result : Value × State n KemSK Platform source)
    (live : Live before.1.1 before.2) (correct : MemoCorrect setup seed scalar before.2.roots)
    (supported : result ∈ support ((simulateQ dispatch work).run before)) :
    Live result.2.1.1 result.2.2 ∧ MemoCorrect setup seed scalar result.2.2.roots := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact ⟨live, correct⟩
  | query_bind query continuation ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨step, called, continued⟩ := supported
      have first := handler setup checks wire route sign seed scalar selectedOwner selectedAccept publicPrekey view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query before step live correct called
      exact ih step.1 step.2 result first.1 first.2 continued

/-- Closing the new query tree once or sequencing its actual source callbacks retains the same whole value and state distribution. -/
theorem program_source (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : State n KemSK Platform source) :
    (simulateQ dispatch work).run before =
      (execute setup wire route sign seed scalar (simulateQ
        (RegistrationNativePlatformPublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) work)).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query continuation ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [RegistrationNativePlatformPublicSourceExecution.execute_bind]
      simp only [callback]
      apply bind_congr
      rintro ⟨value, current⟩
      exact ih value current

end Callbacks
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceInvariant

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceInvariant.accept_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceInvariant.accept_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceInvariant.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceInvariant.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceInvariant.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceInvariant.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceInvariant.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceInvariant.program_source
