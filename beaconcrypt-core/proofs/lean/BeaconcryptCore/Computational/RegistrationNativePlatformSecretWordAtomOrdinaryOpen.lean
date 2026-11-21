-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomSessionShape
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOrdinaryServer
/-! Every nonselected corrected OPEN accept keeps the total stored opaque-atom credit. Its real public encapsulation returns a literal, and its actual retention can append only that literal Ready. Repeated pin, authentication and mutable reservation retain their complete private/platform effects and failure states. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOrdinaryOpen
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message ServerReady)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordAtomSessionCredit (count)
open RegistrationNativePlatformSecretWordAtomOpenRun (State Base close)
open RegistrationNativePlatformSecretWordFrontendView (wordLocal)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "impl" => RegistrationNativeSecretWordTargetSource.implementation (n := n) setup wire route sign input inside provider outer

/-- The actual nonselected collector returns its own literal descriptor under the same early provider and outer replies. -/
theorem agreement_nonatom (checks : Checks) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : State n KemSK Platform) (result : RustM (Option ServerReady) × State n KemSK Platform)
    (supported : result ∈ support ((close impl
      (RegistrationNativePlatformSecretWordOpen.agreement (wordLocal false) setup checks packet authenticated)).run before))
    (ready : ServerReady) (returned : result.1 = .ok (some ready)) : ready.reference.kem ≠ Word.atom := by
  rw [RegistrationNativePlatformSecretWordAtomOpenRun.agreement_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  cases equal
  have replied : reached.1.1 = .ok (some ready) := returned
  have actual : ((.ok (some ready), reached.1.2), reached.2) ∈ support
      ((RegistrationNativeSecretWordTargetServerExecution.lower
        (RegistrationNativeSecretWordTargetServerExecution.localImpl setup wire route sign input inside provider outer false)
        ((RegistrationNativeSecretWordServerCompiler.agreement setup checks packet authenticated).run before.1)).run
          (before.2.1, before.2.2.2)) := by
    rw [← replied]
    exact called
  obtain ⟨collected, middle, collectedAt, _rooted, echo⟩ :=
    RegistrationNativeSecretWordLiveServerOriginOuter.agreement setup wire route sign input inside provider outer false
      checks packet authenticated before.1 reached.1.2 (before.2.1, before.2.2.2) reached.2 ready actual
  have literal := RegistrationNativeSecretWordAtomOrdinaryServer.collect_not_atom setup wire route sign input inside
    selected pairs publicKey challenge outer checks packet authenticated _ middle collected collectedAt
  rw [echo]
  exact literal

/-- Retaining a literal Ready creates no opaque-atom credit, even if replay insertion refuses. -/
theorem retain_count (ready : ServerReady) (literal : ready.reference.kem ≠ Word.atom)
    (before : State n KemSK Platform) (result : RustM (Option Nat) × State n KemSK Platform)
    (supported : result ∈ support ((close impl (RegistrationNativePlatformSecretWordOpen.retain ready)).run before)) :
    count result.2.1.sessions = count before.1.sessions := by
  rw [RegistrationNativePlatformSecretWordAtomOpenRun.retain_run] at supported
  cases consumed : RegistrationReplaySchedule.consume
      (RegistrationBoundGate.atRoot ready.agreement RegistrationBoundKeySchedule.zero) before.1.consumed with
  | fail error | div =>
    simp only [RegistrationNativeSecretWordServerMaterial.retain, consumed, mem_support_pure_iff] at supported
    cases supported
    rfl
  | ok pair =>
    rcases pair with ⟨entry, history⟩
    cases entry with
    | none =>
      simp only [RegistrationNativeSecretWordServerMaterial.retain, consumed, mem_support_pure_iff] at supported
      cases supported
      rfl
    | some token =>
      simp only [RegistrationNativeSecretWordServerMaterial.retain, consumed, mem_support_pure_iff] at supported
      cases supported
      rw [RegistrationNativeSecretWordAtomSessionCredit.append]
      simp only [count, RegistrationNativeSecretWordAtomSessionCredit.nonatom ready literal, Nat.add_zero]

/-- The real reservation precedes a nonselected collector and cannot manufacture stored atom credit. -/
theorem afterAuthentication_count (reserve : Base n KemSK Platform Bool) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : State n KemSK Platform) (result : RustM (Option Nat) × State n KemSK Platform)
    (supported : result ∈ support ((close impl
      (RegistrationNativePlatformSecretWordOpen.afterAuthentication (wordLocal false) reserve setup checks packet authenticated)).run before)) :
    count result.2.1.sessions = count before.1.sessions := by
  rw [RegistrationNativePlatformSecretWordOpen.afterAuthentication,
    RegistrationNativePlatformSecretWordAtomOpenRun.bind_run,
    RegistrationNativePlatformSecretWordAtomOpenRun.get_run, pure_bind] at supported
  split at supported
  · rw [RegistrationNativePlatformSecretWordAtomOpenRun.pure_run, mem_support_pure_iff] at supported
    cases supported
    rfl
  · rw [RegistrationNativePlatformSecretWordAtomOpenRun.bind_run, mem_support_bind_iff] at supported
    obtain ⟨reserved, called, supported⟩ := supported
    have same := RegistrationNativePlatformSecretWordAtomOpenRun.lifted_server impl reserve before reserved called
    cases allowed : reserved.1 with
    | false =>
      simp only [allowed, Bool.false_eq_true, ite_false,
        RegistrationNativePlatformSecretWordAtomOpenRun.pure_run, mem_support_pure_iff] at supported
      cases supported
      exact congrArg (fun current => count current.sessions) same
    | true =>
      simp only [allowed, ite_true, RegistrationNativePlatformSecretWordAtomOpenRun.bind_run,
        mem_support_bind_iff] at supported
      obtain ⟨accepted, reached, supported⟩ := supported
      have unchanged := RegistrationNativePlatformSecretWordAtomSessionShape.agreement_server impl setup checks false
        packet authenticated reserved.2 accepted reached
      have original : accepted.2.1 = before.1 := unchanged.trans same
      cases outcome : accepted.1 with
      | fail error | div =>
        simp only [outcome, RegistrationNativePlatformSecretWordAtomOpenRun.pure_run, mem_support_pure_iff] at supported
        cases supported
        exact congrArg (fun current => count current.sessions) original
      | ok value => cases value with
        | none =>
          simp only [outcome, RegistrationNativePlatformSecretWordAtomOpenRun.pure_run, mem_support_pure_iff] at supported
          cases supported
          exact congrArg (fun current => count current.sessions) original
        | some ready =>
          have literal := agreement_nonatom setup wire route sign input inside selected pairs publicKey challenge outer
            checks packet authenticated reserved.2 accepted reached ready outcome
          simp only [outcome] at supported
          have sameCount := retain_count setup wire route sign input inside selected pairs publicKey challenge outer ready literal accepted.2 result supported
          simpa only [original] using sameCount

attribute [local irreducible] RegistrationAuthenticationCompiler.program
  RegistrationNativePlatformServerReferenceAccept.pin

/-- Mandatory authentication and repeated-pin errors preserve the same complete stored atom count. -/
theorem afterPin_count (reserve : Base n KemSK Platform Bool) (checks : Checks)
    (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (current : RegistrationNativeServerPinRecompute.PinReply)
    (before : State n KemSK Platform) (result : RustM (Option Nat) × State n KemSK Platform)
    (supported : result ∈ support ((close impl
      (RegistrationNativePlatformSecretWordOpen.afterPin (wordLocal false) reserve setup checks verify packet current)).run before)) :
    count result.2.1.sessions = count before.1.sessions := by
  cases current with
  | fail error | div =>
    rw [RegistrationNativePlatformSecretWordOpen.afterPin,
      RegistrationNativePlatformSecretWordAtomOpenRun.pure_run, mem_support_pure_iff] at supported
    cases supported
    rfl
  | ok value => cases value with
    | none =>
      rw [RegistrationNativePlatformSecretWordOpen.afterPin,
        RegistrationNativePlatformSecretWordAtomOpenRun.pure_run, mem_support_pure_iff] at supported
      cases supported
      rfl
    | some pin =>
      rw [RegistrationNativePlatformSecretWordOpen.afterPin,
        RegistrationNativePlatformSecretWordAtomOpenRun.bind_run, mem_support_bind_iff] at supported
      obtain ⟨checked, called, supported⟩ := supported
      have same := RegistrationNativePlatformSecretWordAtomOpenRun.lifted_server impl _ before checked called
      cases checkedEq : checked.1 with
      | fail error | div =>
        simp only [checkedEq, RegistrationNativePlatformSecretWordAtomOpenRun.pure_run, mem_support_pure_iff] at supported
        cases supported
        exact congrArg (fun current => count current.sessions) same
      | ok checked =>
        rcases checked with ⟨events, verdict⟩
        cases verdict <;> simp only [checkedEq] at supported
        all_goals try {
          rw [RegistrationNativePlatformSecretWordAtomOpenRun.pure_run, mem_support_pure_iff] at supported
          cases supported
          exact congrArg (fun current => count current.sessions) same }
        case Accepted authenticated =>
          have sameCount := afterAuthentication_count setup wire route sign input inside selected pairs publicKey challenge outer
            reserve checks packet authenticated _ result supported
          simpa only [same] using sameCount

/-- Every supported ordinary corrected accept leaves the total stored opaque-atom credit unchanged. -/
theorem accept_count (reserve : Base n KemSK Platform Bool) (checks : Checks)
    (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (before : State n KemSK Platform) (result : RustM (Option Nat) × State n KemSK Platform)
    (supported : result ∈ support ((close impl
      (RegistrationNativePlatformSecretWordOpen.accept (wordLocal false) reserve setup checks verify packet)).run before)) :
    count result.2.1.sessions = count before.1.sessions := by
  rw [RegistrationNativePlatformSecretWordOpen.accept,
    RegistrationNativePlatformSecretWordAtomOpenRun.bind_run,
    RegistrationNativePlatformSecretWordAtomOpenRun.get_run, pure_bind,
    RegistrationNativePlatformSecretWordAtomOpenRun.bind_run, mem_support_bind_iff] at supported
  obtain ⟨pinned, called, supported⟩ := supported
  have same := RegistrationNativePlatformSecretWordAtomOpenRun.lifted_server impl _ before pinned called
  have sameCount := afterPin_count setup wire route sign input inside selected pairs publicKey challenge outer
    reserve checks verify packet pinned.1 pinned.2 result supported
  simpa only [same] using sameCount

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOrdinaryOpen

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOrdinaryOpen.agreement_nonatom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOrdinaryOpen.agreement_nonatom

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOrdinaryOpen.retain_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOrdinaryOpen.retain_count

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOrdinaryOpen.afterAuthentication_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOrdinaryOpen.afterAuthentication_count

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOrdinaryOpen.afterPin_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOrdinaryOpen.afterPin_count

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOrdinaryOpen.accept_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOrdinaryOpen.accept_count
