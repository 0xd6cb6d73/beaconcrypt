-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInitializedAlias
import BeaconcryptCore.Computational.RegistrationNativePlatformG3CheckedUniformSource
/-! The actual initialized corrected open-retained tree, genuine private KEM family/challenge and persistent platform state have the same byte alias observation. The warm startup and all private draws stay inside one executable recovery client; final repetition is charged on that same native chronology. The separate ordinary KEM real/uniform comparison is not identified with this uniform-candidate experiment. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInitializedSource
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

abbrev Result (source : RegistrationNativeMldsa.Source) (cap : Nat) (Value Platform : Type) :=
  Context source cap × Option (RegistrationNativePlatformG3CheckedUniformSource.Result source Value Platform)

omit primitive in
def observe {cap : Nat} (candidate : Secret)
    (result : RegistrationNativePlatformSecretWordInitializedAlias.Result source cap KemSK Value Platform) : Result source cap Value Platform :=
  (result.1, result.2.map (RegistrationNativePlatformG3CheckedUniformSource.observe source candidate))

noncomputable def after (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform)
    (candidate : Secret) (context : Context source (budget.cap 4 + budget.cap 5)) : ProbComp (Result source (budget.cap 4 + budget.cap 5) Value Platform) :=
  match context.2.2.2.1 with
  | none => pure (context, none)
  | some started => do
    let profile ← RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected
    let result ← (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected.val
      profile.pairs profile.publicKey profile.challenge candidate)
      (RegistrationNativePlatformG3CheckedUniformSource.openProgram setup checks wire source
        (RegistrationNativeMldsa.owned source started.credential) selected.val selectedAccept (setup.dh.publicKey context.2.1)
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route context.1 context.2.1
        (setup.joint.staticDh context.1 (setup.dh.publicKey context.2.1)) serverKeyId bounds mode
        (adversary ⟨setup.joint.publicKeys context.1, started.credential.publicKey, serverKeyId⟩)
        (RegistrationNativeG3NativeStartupFields.word started.frontend, previous)
        (RegistrationNativeG3NativeUniformAuditBound.ordinary context.2.2.2.2))).run'
      ((PqxdhLiveKemBirth.empty, none), ∅)
    pure (context, some result)

noncomputable def game (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform) := do
  let context ← prior setup source ensureInit identityIndex serverKeyId budget
  let candidate ← $ᵗ Secret
  let result ← after setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds mode adversary budget selected previous candidate context
  pure (candidate, result)

private theorem context_source (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform)
    (context : Context source (budget.cap 4 + budget.cap 5)) (candidate : Secret)
    (cold : ∀ started, context.2.2.2.1 = some started → started.frontend.server.sessions = []) :
    after setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected previous candidate context =
      observe source candidate <$> (simulateQ (RegistrationNativeSecretWordRecoveryBound.bytes setup.source candidate)
        (RegistrationNativePlatformSecretWordInitializedAlias.after setup checks wire route source serverKeyId selectedAccept view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous context)).run' ∅ := by
  cases success : context.2.2.2.1 with
  | none =>
    simp only [after, RegistrationNativePlatformSecretWordInitializedAlias.after, success, simulateQ_pure,
      StateT.run'_eq, StateT.run_pure, map_pure, observe, Option.map_none]
  | some started =>
    simp only [after, RegistrationNativePlatformSecretWordInitializedAlias.after, success, StateT.run'_eq,
      RegistrationNativeSecretWordAliasPrior.bytes_source, map_bind, bind_pure_comp]
    apply bind_congr
    intro profile
    have fixed := RegistrationNativePlatformG3CheckedUniformSource.fixed_source setup checks wire source
      (RegistrationNativeMldsa.owned source started.credential) selected.val selectedAccept (setup.dh.publicKey context.2.1)
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route context.1 context.2.1
      (setup.joint.staticDh context.1 (setup.dh.publicKey context.2.1)) serverKeyId bounds mode
      (adversary ⟨setup.joint.publicKeys context.1, started.credential.publicKey, serverKeyId⟩)
      (RegistrationNativeG3NativeStartupFields.word started.frontend, previous)
      (RegistrationNativeG3NativeUniformAuditBound.ordinary context.2.2.2.2)
      (by simp only [RegistrationNativeG3NativeStartupFields.word, cold started success, List.map_nil]) selected.val
      profile.pairs profile.publicKey profile.challenge candidate
    rw [StateT.run'_eq] at fixed
    rw [fixed]
    simp only [simulateQ_map, StateT.run_map, StateT.run'_eq, Functor.map_map, observe, Option.map_some]

/-- The literal actual warm open-retained/early-KEM execution has the byte observation of ONE startup-inclusive alias client. -/
theorem bytes_source (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform) :
    game setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected previous =ᵈ
      RegistrationNativeSecretWordRecoveryBound.bytesView setup.source (fun candidate result => (candidate, observe source candidate result.1))
        (RegistrationNativePlatformSecretWordInitializedAlias.actual setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous) := by
  have prefixed := RegistrationNativeSecretWordAliasPrior.bytesView_source setup.source
    (prior setup source ensureInit identityIndex serverKeyId budget)
    (RegistrationNativePlatformSecretWordInitializedAlias.after setup checks wire route source serverKeyId selectedAccept view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous)
    (fun candidate result => (candidate, observe source candidate result.1))
  refine _root_.EvalDistEq.trans ?_ prefixed.symm
  unfold game
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro context supported
  unfold RegistrationNativeSecretWordRecoveryBound.bytesView
  apply _root_.EvalDistEq.bind_right
  intro candidate
  have cold := fun started success => (RegistrationNativePlatformPublicRecordOpaqueInitialized.prior_fields setup source ensureInit identityIndex serverKeyId
    budget context started supported success).1
  rw [context_source setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds mode adversary budget selected previous context candidate cold]
  simp only [bind_pure_comp, Functor.map_map, StateT.run'_eq]
  exact .rfl

omit primitive in
def Event {cap : Nat} (setup : Setup base KemSK) (candidate : Secret) (result : Result source cap Value Platform) : Prop :=
  match result.2 with
  | none => False
  | some observed => RegistrationNativeG2Trace.RepeatedRoleAttempt
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh result.1.1 result.1.2.1)
    (RegistrationNativeSelectiveHiddenService.selected
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh result.1.1 (setup.dh.publicKey result.1.2.1))) candidate)
    observed.2.events

/-- The same actual initialized native repeated-role event is bounded by the one whole-prefix recovery advantage, with the original ledger and P retained. -/
theorem repeat_bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (previous : Platform) :
    Pr{let pair ← (game setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected previous)}[Event source setup pair.1 pair.2] ≤
      2 * (ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage setup.source
        (RegistrationNativeSuffixKeyRecovery.adversary setup.source (RegistrationNativeSecretWordRecoveryCompiler.guesses
          (RegistrationNativePlatformSecretWordInitializedAlias.actual setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation
            reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous)))) +
        (budget.cap 4 + budget.cap 5) * (256 ^ 160 : ℝ≥0∞)⁻¹ + (budget.cap 4 + budget.cap 5) * (256 ^ 32 : ℝ≥0∞)⁻¹) := by
  rw [(bytes_source setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds mode adversary budget selected previous).prEvent_eq]
  have same : ∀ candidate (result : RegistrationNativePlatformSecretWordInitializedAlias.Result source (budget.cap 4 + budget.cap 5) KemSK Value Platform),
      Event source setup candidate (observe source candidate result) = RegistrationNativePlatformSecretWordInitializedAlias.Event source setup candidate result := by
    intro candidate result
    rcases result with ⟨context, optional⟩
    cases optional <;> rfl
  simp only [RegistrationNativeSecretWordRecoveryBound.bytesView, OracleComp.prEvent_bind_eq_tsum, prEvent_map, same] at ⊢
  have original := RegistrationNativePlatformSecretWordInitializedAlias.bytes_bound setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget bounded selected previous
  simpa only [RegistrationNativeSecretWordRecoveryBound.bytesView, OracleComp.prEvent_bind_eq_tsum, prEvent_map] using original

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInitializedSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInitializedSource.bytes_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInitializedSource.bytes_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInitializedSource.repeat_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInitializedSource.repeat_bound
