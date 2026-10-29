-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupUniformValue

/-! The ordinary uniform KEM game for the unchanged whole native client is reassociated with its actual startup probability prefix. All sampled context and full ledger/frontend/G2 trace remain available to the pure final candidate observer. The independent prefix is sampled before the mathematical candidate without granting that candidate to executable client code. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupUniformSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhKemIndCca
open RegistrationNativeG3NativeStartupUniformValue (Result program after)
open RegistrationNativeG3NativeStartupAlias (Context prior)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)

noncomputable def conditional (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1))
    (observe : MlKemSharedSecret → Result source n Value → Bool) : ProbComp Bool := do
  let context ← prior setup wire source route ensureInit identityIndex serverKeyId
  let profile ← RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected
  let candidate ← $ᵗ MlKemSharedSecret
  observe candidate <$> (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected.val
    profile.pairs profile.publicKey profile.challenge candidate)
      (after setup checks wire source route serverKeyId selected.val selectedAccept bounds mode adversary context)).run'
        ((PqxdhLiveKemBirth.empty, none), ∅)

/-- One ordinary KEM uniform challenge for the entire unchanged client has the same complete actual startup and result law. -/
theorem uniform_source (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (observe : MlKemSharedSecret → Result source n Value → Bool) :
    RegistrationNativeKemEarlyObservedGame.branch setup.baseImpl setup.kem
      (RegistrationNativeOpenKeyKemGame.other setup.baseImpl setup.kem) (pure ∅)
      (simulateQ RegistrationNativeOpenKey.native
        (program setup checks wire source route ensureInit identityIndex serverKeyId selected.val selectedAccept bounds mode adversary))
      observe budget.create selected false =ᵈ
      conditional setup checks wire source route ensureInit identityIndex serverKeyId selectedAccept bounds mode adversary budget selected observe := by
  have bills := RegistrationNativeG3NativeStartupUniformValue.resource_bounds (n := n) setup checks wire source route ensureInit identityIndex serverKeyId
    selected.val selectedAccept bounds mode adversary budget bounded
  have closed := RegistrationNativeOpenKeyKemEarlyObservedUniform.uniform_source setup.baseImpl setup.kem
    (program setup checks wire source route ensureInit identityIndex serverKeyId selected.val selectedAccept bounds mode adversary)
    observe budget.create selected bills.1 bills.2
  refine closed.trans ?_
  have exactPrefix : RegistrationNativeOpenKeyKemEarlyObservedUniform.source setup.baseImpl setup.kem
      (program setup checks wire source route ensureInit identityIndex serverKeyId selected.val selectedAccept bounds mode adversary)
      observe budget.create selected =
      (do let profile ← RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected
          let candidate ← $ᵗ MlKemSharedSecret
          let context ← prior setup wire source route ensureInit identityIndex serverKeyId
          observe candidate <$> (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected.val
            profile.pairs profile.publicKey profile.challenge candidate)
            (after setup checks wire source route serverKeyId selected.val selectedAccept bounds mode adversary context)).run'
              ((PqxdhLiveKemBirth.empty, none), ∅)) := by
    unfold RegistrationNativeOpenKeyKemEarlyObservedUniform.source RegistrationNativeG3NativeRepeatUniformBound.prior
    simp only [bind_assoc, pure_bind]
    apply bind_congr
    intro chosen
    apply bind_congr
    intro others
    apply bind_congr
    intro pair
    apply bind_congr
    intro candidate
    rw [RegistrationNativeG3NativeStartupUniformValue.reference_source]
    simp only [map_bind]
  rw [exactPrefix]
  have swapped :
      (do let profile ← RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected
          let candidate ← $ᵗ MlKemSharedSecret
          let context ← prior setup wire source route ensureInit identityIndex serverKeyId
          observe candidate <$> (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected.val
            profile.pairs profile.publicKey profile.challenge candidate)
            (after setup checks wire source route serverKeyId selected.val selectedAccept bounds mode adversary context)).run'
              ((PqxdhLiveKemBirth.empty, none), ∅)) =ᵈ
      (do let profile ← RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected
          let context ← prior setup wire source route ensureInit identityIndex serverKeyId
          let candidate ← $ᵗ MlKemSharedSecret
          observe candidate <$> (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected.val
            profile.pairs profile.publicKey profile.challenge candidate)
            (after setup checks wire source route serverKeyId selected.val selectedAccept bounds mode adversary context)).run'
              ((PqxdhLiveKemBirth.empty, none), ∅)) := by
    apply _root_.EvalDistEq.bind_right
    intro profile
    exact OracleComp.EvalDistEq.bind_bind_swap ($ᵗ MlKemSharedSecret)
      (prior setup wire source route ensureInit identityIndex serverKeyId) _
  exact swapped.trans (OracleComp.EvalDistEq.bind_bind_swap
    (RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected)
    (prior setup wire source route ensureInit identityIndex serverKeyId) _)

end BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupUniformSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupUniformSource.uniform_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupUniformSource.uniform_source
