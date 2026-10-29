-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupUniformSource

/-! The complete ordinary uniform KEM client and actual whole-startup byte alias client retain the same full result and actual context. Exact fixed-candidate closure is applied only after the same supported startup context supplies cold original sessions. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAliasSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhKemIndCca
open RegistrationNativeG3NativeStartupAlias (Context prior)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

noncomputable def view {source : RegistrationNativeMldsa.Source} (candidate : MlKemSharedSecret)
    (result : RegistrationNativeG3NativeStartupAlias.Result source n KemSK Value) :
    RegistrationNativeG3NativeStartupUniformValue.Result source n Value :=
  (result.1, result.2.map (RegistrationNativeG3NativeCheckedAliasSource.view candidate))

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)

private theorem context_source (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1))
    (context : Context source n)
    (cold : ∀ born, context.initialized.1 = some born → born.native.frontend.server.sessions = [])
    (candidate : MlKemSharedSecret) :
    (do let profile ← RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected
        (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected.val
          profile.pairs profile.publicKey profile.challenge candidate)
          (RegistrationNativeG3NativeStartupUniformValue.after setup checks wire source route serverKeyId selected.val selectedAccept bounds mode adversary context)).run'
            ((PqxdhLiveKemBirth.empty, none), ∅)) =ᵈ
      view candidate <$> (simulateQ (RegistrationNativeSecretWordRecoveryBound.bytes setup.source candidate)
        (RegistrationNativeG3NativeStartupAlias.after setup checks wire source route serverKeyId selectedAccept bounds mode adversary budget selected context)).run' ∅ := by
  cases success : context.initialized.1 with
  | none =>
      simp only [RegistrationNativeG3NativeStartupUniformValue.after, RegistrationNativeG3NativeStartupAlias.after, success,
        simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure, view, Option.map_none]
      exact OracleComp.EvalDistEq.bind_const _ _
  | some born =>
      simp only [RegistrationNativeG3NativeStartupUniformValue.after, RegistrationNativeG3NativeStartupAlias.after, success,
        RegistrationNativeG3NativeRepeatUniformBound.actual, StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map]
      rw [RegistrationNativeSecretWordAliasOuter.bytes_source]
      simp only [map_bind]
      apply _root_.EvalDistEq.bind_right
      intro profile
      have fixed := RegistrationNativeG3NativeCheckedUniformSource.fixed_source setup checks wire source route
        (RegistrationNativeMldsa.owned source born.native.credential) selected.val selectedAccept (setup.dh.publicKey context.scalar) serverKeyId
        bounds mode context.seed context.scalar (setup.joint.staticDh context.seed (setup.dh.publicKey context.scalar))
        (adversary ⟨setup.joint.publicKeys context.seed, born.native.credential.publicKey, serverKeyId⟩)
        (RegistrationNativeG3NativeStartupFields.word born.native.frontend)
        (RegistrationNativeG3NativeUniformAuditBound.ordinary context.initialized.2)
        (by simp only [RegistrationNativeG3NativeStartupFields.word, cold born success, List.map_nil])
        selected.val profile.pairs profile.publicKey profile.challenge candidate
      have mapped := congrArg (Functor.map (fun result => (context, some result))) fixed
      simp only [StateT.run'_eq, Functor.map_map, RegistrationNativeSecretWordAliasOuter.inner,
        RegistrationNativeG3NativeCheckedAliasSource.aliasClient, view, Option.map_some,
        ] at mapped ⊢
      rw [mapped]

/-- The entire actual uniform KEM observation is the byte execution of one startup-inclusive alias client. -/
theorem bytes_source (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1))
    (observe : MlKemSharedSecret → RegistrationNativeG3NativeStartupUniformValue.Result source n Value → Bool) :
    RegistrationNativeKemEarlyObservedGame.branch setup.baseImpl setup.kem
      (RegistrationNativeOpenKeyKemGame.other setup.baseImpl setup.kem) (pure ∅)
      (simulateQ RegistrationNativeOpenKey.native
        (RegistrationNativeG3NativeStartupUniformValue.program setup checks wire source route ensureInit identityIndex serverKeyId selected.val selectedAccept bounds mode adversary))
      observe budget.create selected false =ᵈ
      RegistrationNativeSecretWordRecoveryBound.bytesView setup.source
        (fun candidate result => observe candidate (view candidate result.1))
        (RegistrationNativeG3NativeStartupAlias.actual setup checks wire source route ensureInit identityIndex serverKeyId selectedAccept bounds mode adversary budget selected) := by
  have uniform := RegistrationNativeG3NativeStartupUniformSource.uniform_source setup checks wire source route ensureInit identityIndex serverKeyId
    selectedAccept bounds mode adversary budget bounded selected observe
  have prefixed := RegistrationNativeSecretWordAliasPrior.bytesView_source setup.source
    (prior (n := n) setup wire source route ensureInit identityIndex serverKeyId)
    (RegistrationNativeG3NativeStartupAlias.after setup checks wire source route serverKeyId selectedAccept bounds mode adversary budget selected)
    (fun candidate result => observe candidate (view candidate result.1))
  refine uniform.trans ?_
  refine _root_.EvalDistEq.trans ?_ prefixed.symm
  unfold RegistrationNativeG3NativeStartupUniformSource.conditional
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro context supported
  have swapped := OracleComp.EvalDistEq.bind_bind_swap
    (RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected) ($ᵗ MlKemSharedSecret)
    (fun profile candidate => observe candidate <$> (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected.val
      profile.pairs profile.publicKey profile.challenge candidate)
        (RegistrationNativeG3NativeStartupUniformValue.after setup checks wire source route serverKeyId selected.val selectedAccept bounds mode adversary context)).run'
          ((PqxdhLiveKemBirth.empty, none), ∅))
  refine swapped.trans ?_
  unfold RegistrationNativeSecretWordRecoveryBound.bytesView
  apply _root_.EvalDistEq.bind_right
  intro candidate
  have cold := fun born success => (RegistrationNativeG3NativeStartupAlias.prior_fields setup wire source route ensureInit identityIndex serverKeyId context born supported success).1
  have actual := context_source setup checks wire source route serverKeyId selectedAccept bounds mode adversary budget selected context cold candidate
  have observed := actual.map (observe candidate)
  simpa only [map_bind, StateT.run'_eq, Functor.map_map] using observed

end BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAliasSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAliasSource.bytes_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAliasSource.bytes_source
