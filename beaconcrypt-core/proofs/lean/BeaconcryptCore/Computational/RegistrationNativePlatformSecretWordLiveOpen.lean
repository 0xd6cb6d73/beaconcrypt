-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpenRun
/-! Repeated pin hashing, authentication, effectful reservation and indexed root preparation establish the live-reference invariant for corrected acceptance in the same common platform state. Every retained capability carries its actual reached preparation flag. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpen
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message ServerReady)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked)
open RegistrationNativeSecretWordLiveFlags (Valid Keeps)
open RegistrationNativeSecretWordLiveSessions (Live)
open RegistrationNativePlatformSecretWordLiveOpenRun (State Work Base close)
open RegistrationNativePlatformSecretWordFrontendView (wordLocal)
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
local notation "impl" => handlerChecked setup wire route sign input inside provider

/-- Arbitrary corrected common-state source work preserves all earlier preparation receipts. -/
theorem receipts (work : Work n KemSK Platform A) (before : State n KemSK Platform)
    (result : A × State n KemSK Platform) (valid : Valid input before.2.2.2)
    (supported : result ∈ support ((close impl work).run before)) :
    Valid input result.2.2.2.2 ∧ Keeps before.2.2.2 result.2.2.2.2 := by
  simp only [close, StateT.run, support_map] at supported
  obtain ⟨reached, possible, equal⟩ := supported
  cases equal
  exact RegistrationNativeSecretWordLiveFlags.program_receipts setup wire route sign input inside provider _ _ valid reached possible

/-- The actual indexed collector and successful root preparation supply their precise retained reference. -/
theorem agreement (selected : Bool) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : State n KemSK Platform)
    (result : RustM (Option ServerReady) × State n KemSK Platform)
    (supported : result ∈ support ((close impl
      (RegistrationNativePlatformSecretWordOpen.agreement (wordLocal selected) setup checks packet authenticated)).run before)) :
    result.2.1 = before.1 ∧ ∀ ready, result.1 = .ok (some ready) → result.2.2.2.2.flags ready.reference = true := by
  rw [RegistrationNativePlatformSecretWordLiveOpenRun.agreement_run, support_map] at supported
  obtain ⟨reached, possible, equal⟩ := supported
  have shape := RegistrationNativeSecretWordLiveServer.agreement setup wire route sign input inside provider selected
    checks packet authenticated (before.1, (before.2.1, before.2.2.2)) reached possible
  cases equal
  exact shape

/-- Source replay insertion retains live flags already established by its reached preparation. -/
theorem retain (ready : ServerReady) (before : State n KemSK Platform)
    (result : RustM (Option Nat) × State n KemSK Platform)
    (live : Live before.1 before.2.2.2.flags) (prepared : before.2.2.2.flags ready.reference = true)
    (supported : result ∈ support ((close impl (RegistrationNativePlatformSecretWordOpen.retain ready)).run before)) :
    Live result.2.1 result.2.2.2.2.flags := by
  rw [RegistrationNativePlatformSecretWordLiveOpenRun.retain_run] at supported
  cases actual : RegistrationNativeSecretWordServerMaterial.retain ready before.1 with
  | fail error | div =>
      simp only [actual, mem_support_pure_iff] at supported
      cases supported
      exact live
  | ok pair =>
      rcases pair with ⟨reply, after⟩
      simp only [actual, mem_support_pure_iff] at supported
      cases supported
      exact RegistrationNativeSecretWordLiveSessions.retain_live ready before.1 after before.2.2.2.flags live prepared reply actual

/-- Corrected post-authentication admission retains the actual stateful reservation before agreement and replay insertion. -/
theorem afterAuthentication (selected : Bool) (reserve : Base n KemSK Platform Bool) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : State n KemSK Platform) (result : RustM (Option Nat) × State n KemSK Platform)
    (valid : Valid input before.2.2.2) (live : Live before.1 before.2.2.2.flags)
    (supported : result ∈ support ((close impl
      (RegistrationNativePlatformSecretWordOpen.afterAuthentication (wordLocal selected) reserve setup checks packet authenticated)).run before)) :
    Live result.2.1 result.2.2.2.2.flags := by
  rw [RegistrationNativePlatformSecretWordOpen.afterAuthentication,
    RegistrationNativePlatformSecretWordLiveOpenRun.bind_run,
    RegistrationNativePlatformSecretWordLiveOpenRun.get_run, pure_bind] at supported
  split at supported
  · rw [RegistrationNativePlatformSecretWordLiveOpenRun.pure_run, mem_support_pure_iff] at supported
    cases supported
    exact live
  · rw [RegistrationNativePlatformSecretWordLiveOpenRun.bind_run, mem_support_bind_iff] at supported
    obtain ⟨reserved, called, supported⟩ := supported
    have same := RegistrationNativePlatformSecretWordLiveOpenRun.lifted_server impl reserve before reserved called
    have kept := receipts setup wire route sign input inside provider _ before reserved valid called
    have liveReserved : Live reserved.2.1 reserved.2.2.2.2.flags := by
      rw [same]
      exact RegistrationNativeSecretWordLiveSessions.mono _ _ _ kept.2 live
    cases allowed : reserved.1 with
    | false =>
      simp only [allowed, Bool.false_eq_true, ite_false,
        RegistrationNativePlatformSecretWordLiveOpenRun.pure_run, mem_support_pure_iff] at supported
      cases supported
      exact liveReserved
    | true =>
      simp only [allowed, ite_true, RegistrationNativePlatformSecretWordLiveOpenRun.bind_run,
        mem_support_bind_iff] at supported
      obtain ⟨accepted, reached, supported⟩ := supported
      have shape := agreement setup wire route sign input inside provider selected checks packet authenticated reserved.2 accepted reached
      have flags := receipts setup wire route sign input inside provider _ reserved.2 accepted kept.1 reached
      have liveAccepted : Live accepted.2.1 accepted.2.2.2.2.flags := by
        rw [shape.1]
        exact RegistrationNativeSecretWordLiveSessions.mono _ _ _ flags.2 liveReserved
      cases outcome : accepted.1 with
      | fail error | div =>
        simp only [outcome, RegistrationNativePlatformSecretWordLiveOpenRun.pure_run, mem_support_pure_iff] at supported
        cases supported
        exact liveAccepted
      | ok value => cases value with
        | none =>
          simp only [outcome, RegistrationNativePlatformSecretWordLiveOpenRun.pure_run, mem_support_pure_iff] at supported
          cases supported
          exact liveAccepted
        | some ready =>
          simp only [outcome] at supported
          exact retain setup wire route sign input inside provider ready accepted.2 result liveAccepted (shape.2 ready outcome) supported

attribute [local irreducible] RegistrationAuthenticationCompiler.program
  RegistrationNativePlatformServerReferenceAccept.pin

/-- Mandatory authentication preserves earlier references before the corrected admission branch. -/
theorem afterPin (selected : Bool) (reserve : Base n KemSK Platform Bool) (checks : Checks)
    (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (current : RegistrationNativeServerPinRecompute.PinReply)
    (before : State n KemSK Platform) (result : RustM (Option Nat) × State n KemSK Platform)
    (valid : Valid input before.2.2.2) (live : Live before.1 before.2.2.2.flags)
    (supported : result ∈ support ((close impl
      (RegistrationNativePlatformSecretWordOpen.afterPin (wordLocal selected) reserve setup checks verify packet current)).run before)) :
    Live result.2.1 result.2.2.2.2.flags := by
  cases current with
  | fail error | div =>
      simp only [RegistrationNativePlatformSecretWordOpen.afterPin,
        RegistrationNativePlatformSecretWordLiveOpenRun.pure_run, mem_support_pure_iff] at supported
      cases supported
      exact live
  | ok current => cases current with
    | none =>
      simp only [RegistrationNativePlatformSecretWordOpen.afterPin,
        RegistrationNativePlatformSecretWordLiveOpenRun.pure_run, mem_support_pure_iff] at supported
      cases supported
      exact live
    | some pin =>
      rw [RegistrationNativePlatformSecretWordOpen.afterPin,
        RegistrationNativePlatformSecretWordLiveOpenRun.bind_run, mem_support_bind_iff] at supported
      obtain ⟨checked, called, supported⟩ := supported
      have same := RegistrationNativePlatformSecretWordLiveOpenRun.lifted_server impl _ before checked called
      have kept := receipts setup wire route sign input inside provider _ before checked valid called
      have liveChecked : Live checked.2.1 checked.2.2.2.2.flags := by
        rw [same]
        exact RegistrationNativeSecretWordLiveSessions.mono _ _ _ kept.2 live
      cases checkedEq : checked.1 with
      | fail error | div =>
        simp only [checkedEq, RegistrationNativePlatformSecretWordLiveOpenRun.pure_run, mem_support_pure_iff] at supported
        cases supported
        exact liveChecked
      | ok checked =>
        rcases checked with ⟨events, verdict⟩
        cases verdict <;> simp only [checkedEq] at supported
        all_goals try {
          rw [RegistrationNativePlatformSecretWordLiveOpenRun.pure_run, mem_support_pure_iff] at supported
          cases supported
          exact liveChecked }
        case Accepted authenticated =>
          exact afterAuthentication setup wire route sign input inside provider selected reserve checks packet authenticated _ result kept.1 liveChecked supported

/-- Actual corrected acceptance establishes live preparation for every returned retained capability. -/
theorem accept (selected : Bool) (reserve : Base n KemSK Platform Bool) (checks : Checks)
    (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (before : State n KemSK Platform) (result : RustM (Option Nat) × State n KemSK Platform)
    (valid : Valid input before.2.2.2) (live : Live before.1 before.2.2.2.flags)
    (supported : result ∈ support ((close impl
      (RegistrationNativePlatformSecretWordOpen.accept (wordLocal selected) reserve setup checks verify packet)).run before)) :
    Live result.2.1 result.2.2.2.2.flags := by
  rw [RegistrationNativePlatformSecretWordOpen.accept,
    RegistrationNativePlatformSecretWordLiveOpenRun.bind_run,
    RegistrationNativePlatformSecretWordLiveOpenRun.get_run, pure_bind,
    RegistrationNativePlatformSecretWordLiveOpenRun.bind_run, mem_support_bind_iff] at supported
  obtain ⟨pinned, called, supported⟩ := supported
  have same := RegistrationNativePlatformSecretWordLiveOpenRun.lifted_server impl _ before pinned called
  have kept := receipts setup wire route sign input inside provider _ before pinned valid called
  have livePinned : Live pinned.2.1 pinned.2.2.2.2.flags := by
    rw [same]
    exact RegistrationNativeSecretWordLiveSessions.mono _ _ _ kept.2 live
  exact afterPin setup wire route sign input inside provider selected reserve checks verify packet pinned.1 pinned.2 result kept.1 livePinned supported

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpen

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpen.receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpen.receipts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpen.agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpen.agreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpen.retain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpen.retain

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpen.afterAuthentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpen.afterAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpen.afterPin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpen.afterPin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpen.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpen.accept
