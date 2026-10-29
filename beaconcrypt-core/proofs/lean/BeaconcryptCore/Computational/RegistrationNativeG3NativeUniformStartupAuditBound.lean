-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAliasSource
import BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAuditReference

/-! The actual cold G3 audit is averaged over the original effectful startup and uniform KEM prior. Its complete recovery adversary samples that entire context itself, so the bound uses one explicit advantage rather than an average of absolute advantages. The same reached World and startup hash cache enter every actual continuation. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeUniformStartupAuditBound
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhKemIndCca
open RegistrationNativeG3NativeStartupAlias (Context prior)
variable {ι KemSK Value : Type} {base : OracleSpec ι}
attribute [local irreducible] uniformSample RegistrationNativeSuffixKeyPrf.value
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)

noncomputable def Event {n : Nat} (candidate : MlKemSharedSecret)
    (result : RegistrationNativeG3NativeStartupUniformValue.Result source n Value) : Prop :=
  match result.2 with
  | none => False
  | some observed => RegistrationNativeG3AuditRepeatOpenKey.Event setup result.1.seed result.1.scalar candidate observed

noncomputable def observe {n : Nat} (candidate : MlKemSharedSecret)
    (result : RegistrationNativeG3NativeStartupUniformValue.Result source n Value) : Bool := by
  classical
  exact decide (Event setup source candidate result)

noncomputable def audit (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) : ProbComp Bool := do
  let context ← prior (n := budget.cap 4 + budget.cap 5) setup wire source route ensureInit identityIndex serverKeyId
  let profile ← RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected
  let candidate ← $ᵗ MlKemSharedSecret
  RegistrationNativeG3MaterializedStartup.auditAfter setup checks wire route source serverKeyId context.seed context.scalar candidate
    (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val profile.pairs profile.publicKey profile.challenge candidate)
    none selected.val selectedAccept bounds mode adversary context.initialized

noncomputable def uniform (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) : ProbComp Bool :=
  RegistrationNativeKemEarlyObservedGame.branch setup.baseImpl setup.kem
    (RegistrationNativeOpenKeyKemGame.other setup.baseImpl setup.kem) (pure ∅)
    (simulateQ RegistrationNativeOpenKey.native
      (RegistrationNativeG3NativeStartupUniformValue.program (n := budget.cap 4 + budget.cap 5) setup checks wire source route ensureInit identityIndex serverKeyId
        selected.val selectedAccept bounds mode adversary))
    (observe setup source) budget.create selected false

noncomputable def loss (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) : ℝ≥0∞ :=
  2 * (ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage setup.source
    (RegistrationNativeSuffixKeyRecovery.adversary setup.source
      (RegistrationNativeSecretWordRecoveryCompiler.guesses
        (RegistrationNativeG3NativeStartupAlias.actual (n := budget.cap 4 + budget.cap 5) setup checks wire source route ensureInit identityIndex serverKeyId
          selectedAccept bounds mode adversary budget selected)))) +
    (budget.cap 4 + budget.cap 5) * (256 ^ 160 : ℝ≥0∞)⁻¹ + (budget.cap 4 + budget.cap 5) * (256 ^ 32 : ℝ≥0∞)⁻¹)

/-- The actual startup-averaged marked audit implies repetition in the same whole uniform-side original native trace. -/
theorem audit_le_uniform (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) :
    Pr{let marked ← audit setup checks wire source route ensureInit identityIndex serverKeyId selectedAccept bounds mode adversary budget selected}[marked = true] ≤
      Pr{let repeated ← uniform setup checks wire source route ensureInit identityIndex serverKeyId selectedAccept bounds mode adversary budget selected}[repeated = true] := by
  have sourceEq := RegistrationNativeG3NativeStartupUniformSource.uniform_source (n := budget.cap 4 + budget.cap 5) setup checks wire source route ensureInit identityIndex serverKeyId
    selectedAccept bounds mode adversary budget bounded selected (observe setup source)
  unfold uniform
  rw [sourceEq.prEvent_eq (fun repeated => repeated = true)]
  unfold audit RegistrationNativeG3NativeStartupUniformSource.conditional
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun context reached => ?_
  obtain ⟨seed, scalar, initialized⟩ := context
  cases success : initialized.1 with
  | none =>
      simp only [RegistrationNativeG3MaterializedStartup.auditAfter, RegistrationNativeG3NativeStartupUniformValue.after,
        success, simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure, observe, Event, decide_false]
      exact le_rfl
  | some born =>
      obtain ⟨_sessions, _owners, _parsed, unused, seedcache⟩ :=
        RegistrationNativeG3NativeStartupAlias.prior_fields setup wire source route ensureInit identityIndex serverKeyId
          ⟨seed, scalar, initialized⟩ born reached success
      refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun profile => ?_
      refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun candidate => ?_
      have afterEq := RegistrationNativeG3NativeStartupAuditSource.after_source setup checks wire source route serverKeyId seed scalar candidate
        (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val profile.pairs profile.publicKey profile.challenge candidate)
        none selected.val selectedAccept bounds mode adversary born initialized.2 seedcache
      have normalized : initialized = (some born, initialized.2) := by exact Prod.ext success rfl
      rw [normalized, afterEq]
      have point := RegistrationNativeG3NativeStartupAuditReference.after_bound setup checks wire source route serverKeyId seed scalar
        budget selected profile candidate selectedAccept bounds mode adversary born (bounded _) initialized.2 unused
      simpa only [RegistrationNativeG3NativeStartupUniformValue.after, success, simulateQ_map,
        StateT.run'_eq, StateT.run_map, Functor.map_map, prEvent_map, observe, Event, decide_eq_true_eq] using point

private theorem event_view {n : Nat} (candidate : MlKemSharedSecret)
    (result : RegistrationNativeG3NativeStartupAlias.Result source n KemSK Value) :
    Event setup source candidate (RegistrationNativeG3NativeStartupAliasSource.view candidate result) =
      RegistrationNativeG3NativeStartupAlias.Event setup source candidate result := by
  rcases result with ⟨context, _ | result⟩ <;> rfl

/-- One complete explicit recovery adversary bounds the actual startup-averaged audit, entirely on the uniform KEM side. -/
theorem bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) :
    Pr{let marked ← audit setup checks wire source route ensureInit identityIndex serverKeyId selectedAccept bounds mode adversary budget selected}[marked = true] ≤
      loss setup checks wire source route ensureInit identityIndex serverKeyId selectedAccept bounds mode adversary budget selected := by
  apply (audit_le_uniform setup checks wire source route ensureInit identityIndex serverKeyId selectedAccept bounds mode adversary budget bounded selected).trans
  have sourceEq := RegistrationNativeG3NativeStartupAliasSource.bytes_source (n := budget.cap 4 + budget.cap 5) setup checks wire source route ensureInit identityIndex serverKeyId
    selectedAccept bounds mode adversary budget bounded selected (observe setup source)
  unfold uniform
  rw [sourceEq.prEvent_eq (fun repeated => repeated = true)]
  have recovery := RegistrationNativeG3NativeStartupAlias.bytes_bound (n := budget.cap 4 + budget.cap 5) setup checks wire source route ensureInit identityIndex serverKeyId
    selectedAccept bounds mode adversary budget bounded selected
  simpa only [RegistrationNativeSecretWordRecoveryBound.bytesView, map_bind, bind_pure_comp, Functor.map_map,
    prEvent_map, loss, observe, event_view, decide_eq_true_eq] using recovery

end BeaconcryptCore.Computational.RegistrationNativeG3NativeUniformStartupAuditBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeUniformStartupAuditBound.audit_le_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeUniformStartupAuditBound.audit_le_uniform
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeUniformStartupAuditBound.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeUniformStartupAuditBound.bound
