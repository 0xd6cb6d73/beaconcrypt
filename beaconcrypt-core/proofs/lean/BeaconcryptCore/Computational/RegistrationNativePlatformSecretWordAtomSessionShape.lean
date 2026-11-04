-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOpenRun
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionShape
/-! Corrected OPEN acceptance preserves its complete old capability table or appends exactly its returned Ready. This follows from the actual repeated-pin/authentication/reserve/collector/retain source, under arbitrary concrete private interpretation and all failures. No successful-admission or source-controller law is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomSessionShape
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (ServerState ServerReady)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativeSecretWordAtomSessionShape (Shape)
open RegistrationNativePlatformSecretWordAtomOpenRun (State Base close)
open RegistrationNativePlatformSecretWordFrontendView (wordLocal)
variable {n : Nat} {I KemSK Platform : Type} {base : OracleSpec I}
variable (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK)
  (StateT (RegistrationNativeSecretWordInterpreter.State n KemSK) ProbComp))

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map _ _ _
private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) : (StateT.lift work : StateT S m X) before = (fun value => (value, before)) <$> work :=
  bind_pure_comp _ _

private theorem source_agreement_server (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : ServerState) (env : Environment)
    (result : (RustM (Option ServerReady) × ServerState) × Environment)
    (supported : result ∈ support (((RegistrationNativeSecretWordServerCompiler.agreement (n := n) setup checks packet authenticated).run before).run env)) :
    result.1.2 = before := by
  simp only [RegistrationNativeSecretWordServerCompiler.agreement, StateT.run_bind, StateT.run_lift,
    bind_assoc, pure_bind, mem_support_bind_iff] at supported
  obtain ⟨collected, _possible, supported⟩ := supported
  cases formed : collected.1 with
  | none =>
    simp only [formed, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    rfl
  | some pending =>
    simp only [formed, StateT.run, lift_apply, map_apply, Functor.map_map, support_map] at supported
    obtain ⟨returned, _possible, equal⟩ := supported
    exact (congrArg (fun result => result.1.2) equal).symm

/-- The actual ordered collector and root preparation change no retained Server capability. -/
theorem agreement_server (setup : Setup base KemSK) (checks : Checks) (selected : Bool)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : State n KemSK Platform) (result : RustM (Option ServerReady) × State n KemSK Platform)
    (supported : result ∈ support ((close implementation
      (RegistrationNativePlatformSecretWordOpen.agreement (wordLocal selected) setup checks packet authenticated)).run before)) :
    result.2.1 = before.1 := by
  rw [RegistrationNativePlatformSecretWordAtomOpenRun.agreement_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  rw [RegistrationNativeSecretWordTargetServerExecution.lower_run, support_map] at called
  obtain ⟨raw, actual, returned⟩ := called
  have possible : raw.1 ∈ support (((RegistrationNativeSecretWordServerCompiler.agreement (n := n) setup checks packet authenticated).run before.1).run before.2.1) := by
    apply OracleComp.support_simulateQ_run'_subset
      (implementation ∘ₛ RegistrationNativeSecretWordInterface.liftLocal selected) _ before.2.2.2
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst actual
  have retained := source_agreement_server setup checks packet authenticated before.1 before.2.1 raw.1 possible
  cases equal
  cases returned
  exact retained

/-- One-use retention adds exactly its actual returned capability and leaves every older slot intact. -/
theorem retain_shape (ready : ServerReady) (before : State n KemSK Platform)
    (result : RustM (Option Nat) × State n KemSK Platform)
    (supported : result ∈ support ((close implementation (RegistrationNativePlatformSecretWordOpen.retain ready)).run before)) :
    Shape before.1.sessions result.1 result.2.1.sessions := by
  rw [RegistrationNativePlatformSecretWordAtomOpenRun.retain_run] at supported
  cases consumed : RegistrationReplaySchedule.consume
      (RegistrationBoundGate.atRoot ready.agreement RegistrationBoundKeySchedule.zero) before.1.consumed with
  | fail error | div =>
    simp only [RegistrationNativeSecretWordServerMaterial.retain, consumed, mem_support_pure_iff] at supported
    cases supported
    exact Or.inl rfl
  | ok pair =>
    rcases pair with ⟨entry, history⟩
    cases entry with
    | none =>
      simp only [RegistrationNativeSecretWordServerMaterial.retain, consumed, mem_support_pure_iff] at supported
      cases supported
      exact Or.inl rfl
    | some token =>
      simp only [RegistrationNativeSecretWordServerMaterial.retain, consumed, mem_support_pure_iff] at supported
      cases supported
      exact Or.inr ⟨ready, rfl, rfl⟩

/-- Effectful reservation still precedes collection and the only possible capability append. -/
theorem afterAuthentication (setup : Setup base KemSK) (checks : Checks) (selected : Bool)
    (reserve : Base n KemSK Platform Bool) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : State n KemSK Platform) (result : RustM (Option Nat) × State n KemSK Platform)
    (supported : result ∈ support ((close implementation
      (RegistrationNativePlatformSecretWordOpen.afterAuthentication (wordLocal selected) reserve setup checks packet authenticated)).run before)) :
    Shape before.1.sessions result.1 result.2.1.sessions := by
  rw [RegistrationNativePlatformSecretWordOpen.afterAuthentication,
    RegistrationNativePlatformSecretWordAtomOpenRun.bind_run,
    RegistrationNativePlatformSecretWordAtomOpenRun.get_run, pure_bind] at supported
  split at supported
  · rw [RegistrationNativePlatformSecretWordAtomOpenRun.pure_run, mem_support_pure_iff] at supported
    cases supported
    exact Or.inl rfl
  · rw [RegistrationNativePlatformSecretWordAtomOpenRun.bind_run, mem_support_bind_iff] at supported
    obtain ⟨reserved, called, supported⟩ := supported
    have same := RegistrationNativePlatformSecretWordAtomOpenRun.lifted_server implementation reserve before reserved called
    cases allowed : reserved.1 with
    | false =>
      simp only [allowed, Bool.false_eq_true, ite_false,
        RegistrationNativePlatformSecretWordAtomOpenRun.pure_run, mem_support_pure_iff] at supported
      cases supported
      exact Or.inl (congrArg (fun current => current.sessions) same)
    | true =>
      simp only [allowed, ite_true, RegistrationNativePlatformSecretWordAtomOpenRun.bind_run,
        mem_support_bind_iff] at supported
      obtain ⟨accepted, reached, supported⟩ := supported
      have unchanged := agreement_server implementation setup checks selected packet authenticated reserved.2 accepted reached
      have original : accepted.2.1 = before.1 := unchanged.trans same
      cases outcome : accepted.1 with
      | fail error | div =>
        simp only [outcome, RegistrationNativePlatformSecretWordAtomOpenRun.pure_run, mem_support_pure_iff] at supported
        cases supported
        exact Or.inl (congrArg (fun current => current.sessions) original)
      | ok value => cases value with
        | none =>
          simp only [outcome, RegistrationNativePlatformSecretWordAtomOpenRun.pure_run, mem_support_pure_iff] at supported
          cases supported
          exact Or.inl (congrArg (fun current => current.sessions) original)
        | some ready =>
          simp only [outcome] at supported
          have appended := retain_shape implementation ready accepted.2 result supported
          simpa only [original] using appended

attribute [local irreducible] RegistrationAuthenticationCompiler.program
  RegistrationNativePlatformServerReferenceAccept.pin

/-- Mandatory authentication and repeated-pin failure preserve the same append-only shape. -/
theorem afterPin (setup : Setup base KemSK) (checks : Checks) (selected : Bool)
    (reserve : Base n KemSK Platform Bool) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (current : RegistrationNativeServerPinRecompute.PinReply)
    (before : State n KemSK Platform) (result : RustM (Option Nat) × State n KemSK Platform)
    (supported : result ∈ support ((close implementation
      (RegistrationNativePlatformSecretWordOpen.afterPin (wordLocal selected) reserve setup checks verify packet current)).run before)) :
    Shape before.1.sessions result.1 result.2.1.sessions := by
  cases current with
  | fail error | div =>
    rw [RegistrationNativePlatformSecretWordOpen.afterPin,
      RegistrationNativePlatformSecretWordAtomOpenRun.pure_run, mem_support_pure_iff] at supported
    cases supported
    exact Or.inl rfl
  | ok value => cases value with
    | none =>
      rw [RegistrationNativePlatformSecretWordOpen.afterPin,
        RegistrationNativePlatformSecretWordAtomOpenRun.pure_run, mem_support_pure_iff] at supported
      cases supported
      exact Or.inl rfl
    | some pin =>
      rw [RegistrationNativePlatformSecretWordOpen.afterPin,
        RegistrationNativePlatformSecretWordAtomOpenRun.bind_run, mem_support_bind_iff] at supported
      obtain ⟨checked, called, supported⟩ := supported
      have same := RegistrationNativePlatformSecretWordAtomOpenRun.lifted_server implementation _ before checked called
      cases checkedEq : checked.1 with
      | fail error | div =>
        simp only [checkedEq, RegistrationNativePlatformSecretWordAtomOpenRun.pure_run, mem_support_pure_iff] at supported
        cases supported
        exact Or.inl (congrArg (fun current => current.sessions) same)
      | ok checked =>
        rcases checked with ⟨events, verdict⟩
        cases verdict <;> simp only [checkedEq] at supported
        all_goals try {
          rw [RegistrationNativePlatformSecretWordAtomOpenRun.pure_run, mem_support_pure_iff] at supported
          cases supported
          exact Or.inl (congrArg (fun current => current.sessions) same) }
        case Accepted authenticated =>
          have shape := afterAuthentication implementation setup checks selected reserve packet authenticated _ result supported
          simpa only [same] using shape

/-- Every supported corrected accept preserves the old table or appends its exact returned Ready. -/
theorem accept (setup : Setup base KemSK) (checks : Checks) (selected : Bool)
    (reserve : Base n KemSK Platform Bool) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (before : State n KemSK Platform) (result : RustM (Option Nat) × State n KemSK Platform)
    (supported : result ∈ support ((close implementation
      (RegistrationNativePlatformSecretWordOpen.accept (wordLocal selected) reserve setup checks verify packet)).run before)) :
    Shape before.1.sessions result.1 result.2.1.sessions := by
  rw [RegistrationNativePlatformSecretWordOpen.accept,
    RegistrationNativePlatformSecretWordAtomOpenRun.bind_run,
    RegistrationNativePlatformSecretWordAtomOpenRun.get_run, pure_bind,
    RegistrationNativePlatformSecretWordAtomOpenRun.bind_run, mem_support_bind_iff] at supported
  obtain ⟨pinned, called, supported⟩ := supported
  have same := RegistrationNativePlatformSecretWordAtomOpenRun.lifted_server implementation _ before pinned called
  have shape := afterPin implementation setup checks selected reserve verify packet pinned.1 pinned.2 result supported
  simpa only [same] using shape

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomSessionShape

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomSessionShape.agreement_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomSessionShape.agreement_server

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomSessionShape.retain_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomSessionShape.retain_shape

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomSessionShape.afterAuthentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomSessionShape.afterAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomSessionShape.afterPin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomSessionShape.afterPin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomSessionShape.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomSessionShape.accept
