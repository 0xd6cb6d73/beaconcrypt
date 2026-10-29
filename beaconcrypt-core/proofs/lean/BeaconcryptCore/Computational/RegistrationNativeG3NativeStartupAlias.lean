-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasPriorBound
import BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAuditSource

/-! A single executable alias client samples the original Server seed, prekey scalar and effectful native startup, followed by its actual KEM profile and full original frontend. The mathematical candidate appears only in the final event. Its one recovery adversary therefore owns all startup and KEM sampling, including the reached shared cache. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAlias
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordServiceCaps (Kind Counted)
open RegistrationNativeSuffixKeyPrf (Secret)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

structure Context (source : RegistrationNativeMldsa.Source) (n : Nat) where
  seed : PqxdhJointIdentity.IdentitySeed
  scalar : PqxdhJointGapDh.ScalarBytes
  initialized : Option (RegistrationNativeHiddenStartup.Started source) × PqxdhRecordLiftWorld.State n

abbrev Result (source : RegistrationNativeMldsa.Source) (n : Nat) (KemSK Value : Type) :=
  Context source n × Option (RegistrationNativeSecretWordAliasClient.Result source n KemSK Value)

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)

noncomputable def prior : ProbComp (Context source n) := do
  let seed ← PqxdhJointIdentity.sampleSeed
  let scalar ← PqxdhJointGapDh.sampleScalar
  let initialized ← RegistrationNativeG3MaterializedStartup.startup setup wire route source ensureInit identityIndex serverKeyId seed
  pure ⟨seed, scalar, initialized⟩

noncomputable def after (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1))
    (context : Context source n) : OracleComp RegistrationNativeSecretWordService.Combined (Result source n KemSK Value) :=
  match context.initialized.1 with
  | none => pure (context, none)
  | some born =>
      (fun result => (context, some result)) <$>
        RegistrationNativeG3NativeRepeatUniformBound.actual setup checks wire source route
          (RegistrationNativeMldsa.owned source born.native.credential) selectedAccept (setup.dh.publicKey context.scalar) serverKeyId bounds mode
          context.seed context.scalar
          (adversary ⟨setup.joint.publicKeys context.seed, born.native.credential.publicKey, serverKeyId⟩)
          (RegistrationNativeG3NativeStartupFields.word born.native.frontend)
          (RegistrationNativeG3NativeUniformAuditBound.ordinary context.initialized.2) budget selected

noncomputable def actual (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) :=
  RegistrationNativeSecretWordAliasPrior.client
    (prior (n := n) setup wire source route ensureInit identityIndex serverKeyId)
    (after setup checks wire source route serverKeyId selectedAccept bounds mode adversary budget selected)

/-- Original Respects bounds the whole actual startup client; all startup and KEM prior draws are ordinary coins. -/
theorem actual_bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (kind : Kind) :
    (actual (n := n) setup checks wire source route ensureInit identityIndex serverKeyId selectedAccept bounds mode adversary budget selected).IsQueryBoundP
      (Counted kind) (budget.cap 4 + budget.cap 5) := by
  apply RegistrationNativeSecretWordAliasPrior.client_bound
  intro context
  unfold after
  split
  · trivial
  · simp only [isQueryBoundP_map_iff]
    exact RegistrationNativeSecretWordAliasOuter.client_bound setup checks wire source route _ context.seed context.scalar selected.val selectedAccept
      (setup.dh.publicKey context.scalar) serverKeyId bounds mode _ _ _ (RegistrationNativeSecretWordKemPool.empty, none)
      (RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected) budget (bounded _) kind

/-- Every successful context is the same actually reached cold startup result. -/
theorem prior_fields (context : Context source n) (born : RegistrationNativeHiddenStartup.Started source)
    (supported : context ∈ support (prior setup wire source route ensureInit identityIndex serverKeyId))
    (success : context.initialized.1 = some born) :
    born.native.frontend.server.sessions = [] ∧ born.native.frontend.beacons = [] ∧ born.native.frontend.parsedAccepts = 0 ∧
      (∀ slot role, context.initialized.2.used slot role = false) ∧ context.initialized.2.seeds = PqxdhRecordLiftLazyTable.initial := by
  simp only [prior, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨seed, _seed, scalar, _scalar, initialized, reached, rfl⟩ := supported
  have reached' : (some born, initialized.2) ∈ support
      (RegistrationNativeG3MaterializedStartup.startup setup wire route source ensureInit identityIndex serverKeyId seed) := by
    simpa only [← success] using reached
  exact RegistrationNativeG3NativeStartupFields.initialized setup wire route source ensureInit identityIndex serverKeyId seed born initialized.2 reached'

noncomputable def Event (candidate : Secret) (result : Result source n KemSK Value) : Prop :=
  match result.2 with
  | none => False
  | some observed =>
      RegistrationNativeG2Trace.RepeatedRoleAttempt (RegistrationNativeRelatedFamily.input setup.joint setup.dh result.1.seed result.1.scalar)
        (RegistrationNativeSelectiveHiddenService.selected
          (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh result.1.seed (setup.dh.publicKey result.1.scalar))) candidate)
        (observed.1.2.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate))

/-- Repetition in this same complete startup execution implies a literal in this same execution's actual recovery log. -/
theorem logged_hit (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1))
    (candidate : Secret)
    (result : Result source n KemSK Value × (RegistrationNativeSecretWord.Cache × List Secret))
    (supported : result ∈ support (RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate
      (actual setup checks wire source route ensureInit identityIndex serverKeyId selectedAccept bounds mode adversary budget selected)))
    (repeated : Event setup source candidate result.1) : candidate ∈ result.2.2 := by
  rw [actual, RegistrationNativeSecretWordAliasPrior.logged_source, mem_support_bind_iff] at supported
  obtain ⟨context, drawn, reached⟩ := supported
  cases success : context.initialized.1 with
  | none =>
      simp only [after, success, RegistrationNativeSecretWordRecoveryBound.logged, simulateQ_pure, StateT.run_pure,
        mem_support_pure_iff] at reached
      cases reached
      exact repeated.elim
  | some born =>
      simp only [after, success, RegistrationNativeSecretWordRecoveryBound.logged, simulateQ_map, StateT.run_map,
        support_map] at reached
      obtain ⟨observed, possible, rfl⟩ := reached
      obtain ⟨sessions, owners, parsed, _unused, _seeds⟩ := prior_fields setup wire source route ensureInit identityIndex serverKeyId context born drawn success
      exact RegistrationNativeSecretWordAliasOuterRepeatBound.logged_hit setup checks wire source route
        (RegistrationNativeMldsa.owned source born.native.credential) context.seed context.scalar selected.val selectedAccept
        (setup.dh.publicKey context.scalar) serverKeyId bounds mode _
        (RegistrationNativeG3NativeStartupFields.word born.native.frontend)
        (RegistrationNativeG3NativeUniformAuditBound.ordinary context.initialized.2)
        (RegistrationNativeSecretWordKemPool.empty, none)
        (RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected)
        (by simp only [RegistrationNativeG3NativeStartupFields.word, sessions, List.map_nil]) parsed owners rfl candidate observed possible repeated

/-- The complete actual startup byte event pays twice one explicit whole-execution recovery advantage. -/
theorem bytes_bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) :
    Pr{let pair ← (RegistrationNativeSecretWordRecoveryBound.bytesView setup.source
      (fun candidate result => (candidate, result.1))
      (actual (n := n) setup checks wire source route ensureInit identityIndex serverKeyId selectedAccept bounds mode adversary budget selected))}[
      Event setup source pair.1 pair.2] ≤
      2 * (ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage setup.source
        (RegistrationNativeSuffixKeyRecovery.adversary setup.source
          (RegistrationNativeSecretWordRecoveryCompiler.guesses
            (actual (n := n) setup checks wire source route ensureInit identityIndex serverKeyId selectedAccept bounds mode adversary budget selected)))) +
        (budget.cap 4 + budget.cap 5) * (256 ^ 160 : ℝ≥0∞)⁻¹ + (budget.cap 4 + budget.cap 5) * (256 ^ 32 : ℝ≥0∞)⁻¹) := by
  simpa only [Nat.cast_add] using RegistrationNativeSecretWordAliasPriorBound.bytes_bound setup.source _ _
    (actual_bound setup checks wire source route ensureInit identityIndex serverKeyId selectedAccept bounds mode adversary budget bounded selected .suffix)
    (actual_bound setup checks wire source route ensureInit identityIndex serverKeyId selectedAccept bounds mode adversary budget bounded selected .key)
    (Event setup source) (logged_hit setup checks wire source route ensureInit identityIndex serverKeyId selectedAccept bounds mode adversary budget selected)

end BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAlias
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAlias.actual_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAlias.actual_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAlias.prior_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAlias.prior_fields
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAlias.logged_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAlias.logged_hit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAlias.bytes_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAlias.bytes_bound
