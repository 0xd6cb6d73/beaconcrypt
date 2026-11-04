-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenPhase
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOwnerPhase
/-! Every actual current callback outside the selected parsed accept avoids the selected-getter channel. The proof covers dynamic source writers, mutable reserves, corrected assigned-ID finish and all raw record routes without constraining their replies. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPhaseSyntax
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformSecretWordOrdinary
open RegistrationNativeSecretWordTargetPhaseCore (Selected)

variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private theorem platform_zero (work : StateT Platform ProbComp A) (before : Platform) :
    ((RegistrationNativePlatformSecretWordOrdinary.platform (n := n) (KemSK := KemSK) work).run before).IsQueryBoundP
      (Selected (n := n) (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false (work.run before) 0)
  intro coin
  simp [RegistrationNativeSecretWordFrontend.effect, Selected, isQueryBoundP_query_iff]

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private theorem gate_free (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (size : A → Nat) (output : Option A) (before : Platform) :
    ((RegistrationNativePlatformOrdinaryGate.gate (fun amount => platform (n := n) (KemSK := KemSK) (reserve amount)) size output).run before).IsQueryBoundP
      (Selected (KemSK := KemSK)) 0 := by
  cases output with
  | none => trivial
  | some value =>
    simp only [RegistrationNativePlatformOrdinaryGate.gate, StateT.run]
    apply isQueryBoundP_bind (n := 0) (m := 0) (platform_zero _ before)
    rintro ⟨result, after⟩ _
    cases result <;> trivial

theorem record_free (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source Platform) :
    ((record (n := n) (KemSK := KemSK) reserve query).run before).IsQueryBoundP (Selected (KemSK := KemSK)) 0 := by
  rcases query with (send | raw) | ⟨owner, send | raw⟩
  · simp only [record, StateT.run]
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨by simp [Selected], ?_⟩
    intro output
    simpa only [StateT.run, bind_pure_comp, isQueryBoundP_map_iff, Selected, ite_false] using gate_free reserve _ output before.2
  · simp [record, StateT.run, isQueryBoundP_map_iff, Selected, isQueryBoundP_query_iff]
  · simp only [record, StateT.run]
    split
    · trivial
    · rw [isQueryBoundP_query_bind_iff]
      refine ⟨by simp [Selected], ?_⟩
      intro output
      simpa only [StateT.run, bind_pure_comp, isQueryBoundP_map_iff, Selected, ite_false] using gate_free reserve _ output before.2
  · simp only [record, StateT.run]
    split
    · trivial
    · simp [isQueryBoundP_map_iff, Selected, isQueryBoundP_query_iff]


private theorem finish_free (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket) (before : State source Platform) :
    ((RegistrationNativePlatformSecretWordFrontend.finish (n := n) setup wire source index packet).run before).IsQueryBoundP
      (Selected (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativePlatformSecretWordFrontend.finish, StateT.run]
  split
  · trivial
  · rw [isQueryBoundP_map_iff]
    exact RegistrationNativeSecretWordTargetPhaseCore.ordinary_free _

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "handler" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

attribute [local irreducible] RegistrationNativePlatformSecretWordOpen.accept

/-- Every current callback outside the one selected parsed accept excludes the exposed getter in its exact free syntax. -/
theorem handler_free (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source Platform)
    (quiet : ¬(RegistrationNativeSecretWordTargetCounter.isAccept query = true ∧ before.1.parsedAccepts = selectedAccept)) :
    ((handler query).run before).IsQueryBoundP (Selected (KemSK := KemSK)) 0 := by
  cases query with
  | inl coin =>
    simp [RegistrationNativePlatformSecretWordFrontend.handler, RegistrationNativePlatformSecretWordOrdinary.handler,
      StateT.run_lift, bind_pure_comp, RegistrationNativeSecretWordFrontend.effect, Selected,
      isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  | inr command => cases command with
    | create edPin mlPin keyId =>
      exact RegistrationNativePlatformSecretWordTargetOwnerPhase.create_zero setup selectedOwner publicPrekey reserveFrame writer edPin mlPin keyId before
    | bundle index =>
      exact RegistrationNativePlatformSecretWordTargetOwnerPhase.bundle_zero setup selectedOwner publicPrekey reserveFrame writer index before
    | accept packet =>
      have different : before.1.parsedAccepts ≠ selectedAccept := fun equal => quiet ⟨rfl,equal⟩
      simp only [RegistrationNativePlatformSecretWordFrontend.handler, RegistrationNativePlatformSecretWordFrontend.accept,
        StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind, different, decide_false]
      simp only [RegistrationNativePlatformSecretWordFrontend.serverOpen, StateT.run, isQueryBoundP_map_iff]
      exact RegistrationNativePlatformSecretWordTargetOpenPhase.accept_free reserveRegistration setup checks source.verify packet _ _ _
    | build handle application =>
      simp only [RegistrationNativePlatformSecretWordFrontend.handler, RegistrationNativePlatformSecretWordFrontend.build,
        StateT.run, isQueryBoundP_map_iff, QueryImpl.simulateQ_compose]
      exact RegistrationNativeSecretWordTargetPhaseCore.ordinary_free _
    | finish index packet => exact finish_free setup wire index packet before
    | hmac key bytes => trivial
    | hash bytes =>
      simp [RegistrationNativePlatformSecretWordFrontend.handler, RegistrationNativePlatformSecretWordOrdinary.handler,
        StateT.run_lift, bind_pure_comp, RegistrationNativeSecretWordFrontend.effect, Selected,
        isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    | serverSend keyId plaintext => exact record_free reserveFrame (.inl (.inl (plaintext,keyId))) before
    | serverRaw raw => exact record_free reserveFrame (.inl (.inr raw)) before
    | beaconSend index plaintext => exact record_free reserveFrame (.inr (index,.inl plaintext)) before
    | beaconRaw index raw => exact record_free reserveFrame (.inr (index,.inr raw)) before

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPhaseSyntax

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPhaseSyntax.record_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPhaseSyntax.record_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPhaseSyntax.handler_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPhaseSyntax.handler_free
