-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasRepeatBound
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordOpaqueInitialized
import BeaconcryptCore.Computational.RegistrationNativeG3NativeRepeatUniformBound
import BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupFields
import BeaconcryptCore.Computational.RegistrationNativeG3NativeUniformAuditBound
/-! One executable recovery client includes the actual warm startup, the independent material table, the genuine reserved KEM family/challenge and the complete corrected stateful frontend. The mathematical candidate is used only by the final observation and its oracle interpretation. The same persistent platform state and original mode/ledger remain in the returned client value. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInitializedAlias
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordServiceCaps (Kind Counted)
open RegistrationNativeSuffixKeyPrf (Secret)
open RegistrationNativePlatformPublicRecordOpaqueInitialized (Context prior)
variable {I KemSK Platform E Value : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)

abbrev Result (source : RegistrationNativeMldsa.Source) (cap : Nat) (KemSK Value Platform : Type) :=
  Context source cap × Option (RegistrationNativePlatformSecretWordAliasClient.Result source cap KemSK Value Platform)

noncomputable def after (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1))
    (previous : Platform) (context : Context source (budget.cap 4 + budget.cap 5)) :
    OracleComp Combined (Result source (budget.cap 4 + budget.cap 5) KemSK Value Platform) :=
  match context.2.2.2.1 with
  | none => pure (context, none)
  | some started =>
    RegistrationNativeSecretWordAliasPrior.client
      (RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected)
      (fun profile => (fun result => (context, some result)) <$>
        RegistrationNativePlatformSecretWordAliasClient.client setup checks wire source
          (RegistrationNativeMldsa.owned source started.credential) selected.val selectedAccept (setup.dh.publicKey context.2.1)
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route
          (RegistrationNativeSecretWordMessage.input setup.joint setup.dh context.1 context.2.1)
          (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh context.1 (setup.dh.publicKey context.2.1)))
          (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected.val profile.pairs profile.publicKey profile.challenge)
          serverKeyId bounds mode (adversary ⟨setup.joint.publicKeys context.1, started.credential.publicKey, serverKeyId⟩)
          (RegistrationNativeG3NativeStartupFields.word started.frontend, previous)
          (RegistrationNativeG3NativeUniformAuditBound.ordinary context.2.2.2.2)
          (RegistrationNativeSecretWordKemPool.empty, none))

noncomputable def actual (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform) :=
  RegistrationNativeSecretWordAliasPrior.client (prior setup source ensureInit identityIndex serverKeyId budget)
    (after setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected previous)

/-- Actual startup, private material and KEM sampling consume only ordinary coins; the original material budget bounds both recovery query classes. -/
theorem actual_bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (previous : Platform) (kind : Kind) :
    (actual setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected previous).IsQueryBoundP (Counted kind) (budget.cap 4 + budget.cap 5) := by
  apply RegistrationNativeSecretWordAliasPrior.client_bound
  intro context
  unfold after
  split
  · trivial
  · apply RegistrationNativeSecretWordAliasPrior.client_bound
    intro profile
    simp only [isQueryBoundP_map_iff]
    exact RegistrationNativePlatformSecretWordAliasClient.client_bound setup checks wire source _ selected.val selectedAccept _
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route _ _ _ serverKeyId bounds mode _ _ _ _
      budget (bounded _) kind

omit primitive in
def Event {cap : Nat} (setup : Setup base KemSK) (candidate : Secret)
    (result : Result source cap KemSK Value Platform) : Prop :=
  match result.2 with
  | none => False
  | some observed => RegistrationNativePlatformSecretWordAliasRepeatBound.Event source setup result.1.1 result.1.2.1 candidate observed

/-- Every repeated-role event in the same initialized execution yields its literal in that execution's own recovery log. -/
theorem logged_hit (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform)
    (candidate : Secret) (result : Result source (budget.cap 4 + budget.cap 5) KemSK Value Platform × RegistrationNativeSecretWordRecoveryCompiler.State)
    (supported : result ∈ support (RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate
      (actual setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected previous)))
    (repeated : Event source setup candidate result.1) : candidate ∈ result.2.2 := by
  rw [actual, RegistrationNativeSecretWordAliasPrior.logged_source, mem_support_bind_iff] at supported
  obtain ⟨context, drawn, reached⟩ := supported
  cases success : context.2.2.2.1 with
  | none =>
    simp only [after, success, RegistrationNativeSecretWordRecoveryBound.logged, simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff] at reached
    cases reached
    exact repeated.elim
  | some started =>
    simp only [after, success, RegistrationNativeSecretWordAliasPrior.logged_source, mem_support_bind_iff] at reached
    obtain ⟨profile, _sampled, reached⟩ := reached
    simp only [RegistrationNativeSecretWordRecoveryBound.logged, simulateQ_map, StateT.run_map, support_map] at reached
    obtain ⟨observed, possible, equal⟩ := reached
    cases equal
    obtain ⟨sessions, owners, parsed, _unused, _seeds⟩ :=
      RegistrationNativePlatformPublicRecordOpaqueInitialized.prior_fields setup source ensureInit identityIndex serverKeyId budget context started drawn success
    exact RegistrationNativePlatformSecretWordAliasRepeatBound.logged_hit setup checks wire source _ selected.val selectedAccept _
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route context.1 context.2.1
      profile.pairs profile.publicKey profile.challenge serverKeyId bounds mode _
      (RegistrationNativeG3NativeStartupFields.word started.frontend, previous) _ (RegistrationNativeSecretWordKemPool.empty, none)
      (by simp only [RegistrationNativeG3NativeStartupFields.word, sessions, List.map_nil])
      parsed (by simp only [RegistrationNativeG3NativeStartupFields.word, owners]) rfl candidate observed possible repeated

/-- The complete initialized byte alias event pays twice one explicit startup/KEM-inclusive recovery advantage, with no owner union or cache reset. -/
theorem bytes_bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (previous : Platform) :
    Pr{let pair ← (RegistrationNativeSecretWordRecoveryBound.bytesView setup.source
      (fun candidate result => (candidate, result.1))
      (actual setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected previous))}[Event source setup pair.1 pair.2] ≤
      2 * (ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage setup.source
        (RegistrationNativeSuffixKeyRecovery.adversary setup.source (RegistrationNativeSecretWordRecoveryCompiler.guesses
          (actual setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
            erased helper writer bounds mode adversary budget selected previous)))) +
        (budget.cap 4 + budget.cap 5) * (256 ^ 160 : ℝ≥0∞)⁻¹ + (budget.cap 4 + budget.cap 5) * (256 ^ 32 : ℝ≥0∞)⁻¹) := by
  simpa only [Nat.cast_add] using RegistrationNativeSecretWordAliasPriorBound.bytes_bound setup.source _ _
    (actual_bound setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget bounded selected previous .suffix)
    (actual_bound setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget bounded selected previous .key)
    (Event source setup)
    (logged_hit setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected previous)

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInitializedAlias

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInitializedAlias.actual_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInitializedAlias.actual_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInitializedAlias.logged_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInitializedAlias.logged_hit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInitializedAlias.bytes_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInitializedAlias.bytes_bound
