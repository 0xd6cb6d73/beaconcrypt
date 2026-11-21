-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3InitializedKem
import BeaconcryptCore.Computational.RegistrationNativePlatformG3AuditOpenKey
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemCaps
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedReal
/-! The genuine real reserved provider audit is bounded on the actual corrected warm source tree, with its original ledger, returned frontend and persistent platform state. Both the source chronology and the actual unused-role receipt are derived internally. This is an explicit reserved-provider game; it is not identified with a candidate-observed on-demand-provider audit. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformAudit
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


omit primitive in
private theorem reference_values {A P : Type}
    (provider : RegistrationNativeSecretWordNativePlain.NativeProvider KemSK P)
    (work : OracleComp (RegistrationNativeOpenKey.Spec KemSK) A) (state : P)
    (table : RegistrationNativeOpenKeyKemGame.Table) :
    (simulateQ ((PqxdhRegistrationJointKemSecondEntry.lazyImpl.mapStateTBase
        (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider)).flattenStateT) work).run' (state, table) =
      (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl
        ((simulateQ (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider) work).run' state)).run' table := by
  have actual := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT PqxdhRegistrationJointKemSecondEntry.lazyImpl
    (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider) work state table
  have observed := congrArg (Functor.map (fun result => result.1.1)) actual
  simpa only [StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map] using observed.symm

noncomputable def audit (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform) : ProbComp Bool := do
  let context ← prior setup source ensureInit identityIndex serverKeyId budget
  let profile ← RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected
  let candidate ← $ᵗ PqxdhKemIndCca.MlKemSharedSecret
  match context.2.2.2.1 with
  | none => pure false
  | some started => do
    let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)
    let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable (budget.cap 4 + budget.cap 5)
    let result ← RegistrationNativePlatformG3RepeatRun.original setup
      (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route seeds wire
      (RegistrationNativeMldsa.owned source started.credential) context.1 context.2.1 candidate
      (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val profile.pairs profile.publicKey profile.challenge candidate) checks source selected.val selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode
      (adversary ⟨setup.joint.publicKeys context.1, started.credential.publicKey, serverKeyId⟩)
      (started.frontend, previous) (RegistrationNativeHiddenInterpreter.initial none, ∅)
      (RegistrationNativeG3LocalMaterialCompletedSource.cache materials) context.2.2.2.2
    pure result.2.2

/-- The actual uniform-provider audit is bounded by repetition in the same complete initialized native experiment. -/
theorem audit_le_conditional (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (previous : Platform) :
    Pr{let flag ← (audit setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected previous)}[flag = true] ≤
      Pr{let flag ← (RegistrationNativePlatformG3InitializedKem.conditional setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected previous (RegistrationNativePlatformG3InitializedKem.repeatObservation source setup))}[flag = true] := by
  classical
  unfold audit RegistrationNativePlatformG3InitializedKem.conditional
  simp only [map_bind]
  apply OracleComp.prEvent_bind_mono_of_support
  intro context reached
  apply OracleComp.prEvent_bind_mono_of_support
  intro profile _profile
  apply OracleComp.prEvent_bind_mono_of_support
  intro candidate _candidate
  cases success : context.2.2.2.1 with
  | none =>
    simp only [RegistrationNativePlatformG3InitializedKem.after, success, simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure,
      RegistrationNativePlatformG3InitializedKem.repeatObservation, RegistrationNativePlatformSecretWordInitializedSource.Event, decide_false]
    exact le_refl (prEvent (pure (false = true) : ProbComp Prop))
  | some started =>
    have fields := RegistrationNativePlatformPublicRecordOpaqueInitialized.prior_fields setup source ensureInit identityIndex serverKeyId budget context started reached success
    have point := RegistrationNativePlatformG3AuditOpenKey.bound setup wire route (RegistrationNativeMldsa.owned source started.credential)
      context.1 context.2.1 candidate view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer checks source
      selected.val selectedAccept serverKeyId bounds mode
      (adversary ⟨setup.joint.publicKeys context.1, started.credential.publicKey, serverKeyId⟩) (started.frontend, previous)
      budget (bounded _) (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val profile.pairs profile.publicKey profile.challenge candidate)
      (RegistrationNativeHiddenInterpreter.initial none) context.2.2.2.2 fields.2.2.2.1
    simp only [RegistrationNativePlatformG3InitializedKem.after, success, simulateQ_map, StateT.run'_map', Functor.map_map,
      RegistrationNativePlatformG3InitializedKem.repeatObservation, RegistrationNativePlatformSecretWordInitializedSource.Event, decide_eq_true_eq]
    rw [RegistrationNativeOpenKeyKemEarlySource.reference, reference_values]
    simp only [RegistrationNativePlatformG3CheckedUniformSource.openProgram, RegistrationNativeG3MaterializedRetainedLazy.client,
      RegistrationNativeG3MaterializedRetainedSource.ordinary, RegistrationNativeG3NativeUniformAuditBound.ordinary,
      RegistrationNativeHiddenInterpreter.initial,
      RegistrationNativePlatformSecretWordOrdinary.evaluate, Prod.map_def, id_eq,
      RegistrationNativeG3NativeStartupFields.word_eval] at point ⊢
    exact point

/-- The uniform-provider warm audit pays twice ONE whole-prefix recovery advantage and the two original material byte-guess losses, without a further KEM charge. -/
theorem bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (previous : Platform) :
    Pr{let flag ← (audit setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected previous)}[flag = true] ≤
      2 * (ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage setup.source
        (RegistrationNativeSuffixKeyRecovery.adversary setup.source (RegistrationNativeSecretWordRecoveryCompiler.guesses
          (RegistrationNativePlatformSecretWordInitializedAlias.actual setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation
            reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous)))) +
        (budget.cap 4 + budget.cap 5) * (256 ^ 160 : ℝ≥0∞)⁻¹ + (budget.cap 4 + budget.cap 5) * (256 ^ 32 : ℝ≥0∞)⁻¹) :=
  (audit_le_conditional setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds mode adversary budget bounded selected previous).trans
    (RegistrationNativePlatformG3InitializedKem.conditional_bound setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget bounded selected previous)
end BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformAudit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformAudit.audit_le_conditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformAudit.audit_le_conditional

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformAudit.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformAudit.bound
