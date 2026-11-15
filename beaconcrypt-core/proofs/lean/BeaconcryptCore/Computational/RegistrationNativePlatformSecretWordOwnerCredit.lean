-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBundleCredit
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerRosterCredit
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerCredit
attribute [local irreducible] RegistrationNativePlatformSecretWordOpen.accept
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformSecretWordOrdinary (State M)
open RegistrationNativeSecretWordLifecycleOwnerPhase (Done Terminal)
open RegistrationNativeSecretWordOwnerCredit (credit cost)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
private theorem beacon_done (index : Nat)
    (work : RegistrationNativePlatformPublicOwners.M source RegistrationServerRoleBackend.State
      (RegistrationNativePlatformPublicFrontend.Base n KemSK Platform) A)
    (law : ∀ owners env previous result, Done index owners →
      result ∈ support (((work.run owners).run env).run previous) → Done index result.1.1.2)
    (before : State source Platform) (result : A × State source Platform) (valid : Done index before.1.beacons)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordOrdinary.beacon work).run before)) :
    Done index result.2.1.beacons := by
  simp only [RegistrationNativePlatformSecretWordOrdinary.beacon, StateT.run, support_map] at supported
  obtain ⟨middle, reached, equal⟩ := supported
  have kept := law before.1.beacons before.1.environment before.2 middle valid
    (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ reached)
  cases equal
  exact kept
private theorem record_beacons
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source Platform)
    (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordOrdinary.record (n := n) (KemSK := KemSK) reserve query).run before)) :
    result.2.1.beacons = before.1.beacons := by
  rcases query with (_ | _) | ⟨index, _ | _⟩
  all_goals simp only [RegistrationNativePlatformSecretWordOrdinary.record, StateT.run] at supported
  all_goals try split at supported
  all_goals first
    | rw [mem_support_pure_iff] at supported; cases supported; rfl
    | rw [support_map] at supported; obtain ⟨reached, _possible, equal⟩ := supported; exact (congrArg (fun output => output.2.1.beacons) equal).symm
    | rw [mem_support_bind_iff] at supported; obtain ⟨reply, _called, supported⟩ := supported
      rw [mem_support_bind_iff] at supported; obtain ⟨reached, _called, supported⟩ := supported
      rw [mem_support_pure_iff] at supported; cases supported; rfl
private theorem record_done (index : Nat)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source Platform)
    (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State source Platform) (valid : Done index before.1.beacons)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordOrdinary.record (n := n) (KemSK := KemSK) reserve query).run before)) :
    Done index result.2.1.beacons := by
  rw [record_beacons reserve query before result supported]
  exact valid
private theorem ordinary_done (setup : Setup base KemSK) (index selectedOwner : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source Platform)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source Platform) (valid : Done index before.1.beacons)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordOrdinary.handler (n := n) setup source selectedOwner publicPrekey reserve writer query).run before)) :
    Done index result.2.1.beacons := by
  cases query with
  | inl coin =>
      simp only [RegistrationNativePlatformSecretWordOrdinary.handler, StateT.run_lift, bind_pure_comp, support_map] at supported
      obtain ⟨reached, _possible, equal⟩ := supported
      cases equal
      exact valid
  | inr query => cases query with
    | create edPin mlPin keyId =>
        exact beacon_done index _ (RegistrationNativePlatformSecretWordBundleCredit.create_done index setup
          RegistrationNativePlatformPublicFrontend.trusted selectedOwner publicPrekey edPin mlPin keyId) before result valid supported
    | bundle target =>
        rw [RegistrationNativePlatformSecretWordOrdinary.handler, StateT.run_map, support_map] at supported
        obtain ⟨reached, possible, equal⟩ := supported
        cases equal
        exact beacon_done index _ (RegistrationNativePlatformSecretWordBundleCredit.bundle_done index setup
          RegistrationNativePlatformPublicFrontend.trusted (RegistrationNativePlatformPublicFrontend.writer writer)
          selectedOwner target publicPrekey) before reached valid possible
    | accept packet | build handle application | finish target packet | hmac key bytes =>
        simp only [RegistrationNativePlatformSecretWordOrdinary.handler, StateT.run_pure, mem_support_pure_iff] at supported
        cases supported
        exact valid
    | hash bytes =>
        simp only [RegistrationNativePlatformSecretWordOrdinary.handler, StateT.run_lift, bind_pure_comp, support_map] at supported
        obtain ⟨reached, _possible, equal⟩ := supported
        cases equal
        exact valid
    | serverSend keyId plaintext => exact record_done index reserve (.inl (.inl (plaintext, keyId))) before result valid supported
    | serverRaw raw => exact record_done index reserve (.inl (.inr raw)) before result valid supported
    | beaconSend target plaintext => exact record_done index reserve (.inr (target, .inl plaintext)) before result valid supported
    | beaconRaw target raw => exact record_done index reserve (.inr (target, .inr raw)) before result valid supported
private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (work before >>= fun reached => next reached.1 reached.2) := rfl
private theorem get_apply {S : Type} {m : Type → Type} [Monad m] (before : S) :
    (get : StateT S m S) before = pure (before, before) := rfl
private theorem modify_apply {S : Type} {m : Type → Type} [Monad m] (change : S → S) (before : S) :
    (modify change : StateT S m Unit) before = pure ((), change before) := rfl
private theorem accept_beacons (setup : Setup base KemSK) (checks : Checks) (selectedAccept : Nat)
    (reserve : StateT Platform ProbComp Bool) (packet : registration.InitPacket)
    (before : State source Platform) (result : RustM (Option Nat) × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordFrontend.accept (n := n) (KemSK := KemSK) setup checks source selectedAccept reserve packet).run before)) :
    result.2.1.beacons = before.1.beacons := by
  simp only [RegistrationNativePlatformSecretWordFrontend.accept, StateT.run, bind_apply, get_apply, modify_apply,
    pure_bind, RegistrationNativePlatformSecretWordFrontend.serverOpen, support_map] at supported
  obtain ⟨middle, _possible, equal⟩ := supported
  exact (congrArg (fun output => output.2.1.beacons) equal).symm
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "callback" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
attribute [local irreducible] RegistrationNativePlatformSecretWordBuild.body
private theorem build_beacons (handle : Nat) (application : Option (Slice U8))
    (before : State source Platform) (result : RustM (Option (U64 × Pqxdh.Bytes)) × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordFrontend.build (n := n) setup sign view failure allocation erased helper writer reservePeer handle application source).run before)) :
    result.2.1.beacons = before.1.beacons := by
  simp only [RegistrationNativePlatformSecretWordFrontend.build, StateT.run, support_map] at supported
  obtain ⟨middle, _possible, equal⟩ := supported
  exact (congrArg (fun output => output.2.1.beacons) equal).symm
/-- Every actual corrected typed callback retains a previously consumed local Beacon position through its full source/platform state. -/
theorem query_done (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source Platform)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source Platform) (valid : Done selectedOwner before.1.beacons)
    (supported : result ∈ support ((callback query).run before)) : Done selectedOwner result.2.1.beacons := by
  cases query with
  | inl coin => exact ordinary_done setup selectedOwner selectedOwner publicPrekey reserveFrame writer _ before result valid supported
  | inr query => cases query with
    | accept packet =>
        rw [accept_beacons setup checks selectedAccept reserveRegistration packet before result supported]
        exact valid
    | build handle application =>
        rw [build_beacons setup sign view failure allocation reservePeer erased helper writer handle application before result supported]
        exact valid
    | finish target packet => exact RegistrationNativePlatformSecretWordOwnerRosterCredit.finish_done setup wire selectedOwner target packet before result valid supported
    | _ => exact ordinary_done setup selectedOwner selectedOwner publicPrekey reserveFrame writer _ before result valid supported
/-- Any actual callback spending the sole pending-move attempt leaves its own selected position terminal, even on authentication or record failure. -/
theorem query_spent (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source Platform)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source Platform)
    (charged : cost selectedOwner query before.1 = 1) (supported : result ∈ support ((callback query).run before)) :
    Done selectedOwner result.2.1.beacons := by
  obtain ⟨packet, owner, pending, oneTime, aborted, selected, found, sent, moved⟩ :=
    RegistrationNativeSecretWordOwnerCredit.spent selectedOwner query before.1 charged
  subst query
  exact RegistrationNativePlatformSecretWordOwnerRosterCredit.finish_consumes setup wire selectedOwner packet before owner found
    pending oneTime aborted sent moved result supported
omit primitive in
private theorem cost_le (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source Platform) :
    cost selectedOwner query before.1 ≤ 1 := by
  cases query with
  | inl coin => exact Nat.zero_le _
  | inr query =>
      cases query <;> simp only [cost]
      all_goals repeat first | omega | split
/-- Literal pending consumption pays for at most one selected Beacon material attempt across every later corrected API callback. -/
theorem query_credit (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source Platform)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source Platform)
    (supported : result ∈ support ((callback query).run before)) :
    credit selectedOwner result.2.1 + cost selectedOwner query before.1 ≤ credit selectedOwner before.1 := by
  by_cases charged : cost selectedOwner query before.1 = 1
  · have afterDone := query_spent setup checks wire sign selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query before result charged supported
    have afterZero := (RegistrationNativeSecretWordOwnerCredit.credit_zero selectedOwner result.2.1).mpr afterDone
    obtain ⟨packet, owner, pending, oneTime, aborted, _selected, found, sent, _moved⟩ :=
      RegistrationNativeSecretWordOwnerCredit.spent selectedOwner query before.1 charged
    have beforeOne : credit selectedOwner before.1 = 1 := by simp only [credit, found, sent, Terminal, ite_false]
    omega
  · have costZero : cost selectedOwner query before.1 = 0 := by have small := cost_le selectedOwner query before; omega
    by_cases beforeZero : credit selectedOwner before.1 = 0
    · have beforeDone := (RegistrationNativeSecretWordOwnerCredit.credit_zero selectedOwner before.1).mp beforeZero
      have afterDone := query_done setup checks wire sign selectedOwner selectedAccept publicPrekey view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query before result beforeDone supported
      have afterZero := (RegistrationNativeSecretWordOwnerCredit.credit_zero selectedOwner result.2.1).mpr afterDone
      omega
    · have beforeSmall := RegistrationNativeSecretWordOwnerCredit.credit_le selectedOwner before.1
      have afterSmall := RegistrationNativeSecretWordOwnerCredit.credit_le selectedOwner result.2.1
      omega
end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerCredit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerCredit.query_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerCredit.query_done
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerCredit.query_spent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerCredit.query_spent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerCredit.query_credit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerCredit.query_credit
