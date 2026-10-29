-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAlias

/-! The entire unchanged native client includes its actual seed/scalar/startup probability prefix and retains the complete original ledger, frontend and G2 trace. One ordinary KEM challenge value is supplied only to the pure final observer. Whole-client KEM bills follow from original Respects and the coin-only startup prefix. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupUniformValue
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhKemIndCca
open RegistrationNativeG3NativeStartupAlias (Context prior)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

abbrev Result (source : RegistrationNativeMldsa.Source) (n : Nat) (Value : Type) :=
  Context source n × Option (RegistrationNativeG3NativeCheckedUniformSource.Result source Value)

def coins : QueryImpl unifSpec (OracleComp (RegistrationNativeOpenKey.Spec KemSK)) :=
  RegistrationNativeOpenKey.keyLift ∘ₛ RegistrationNativeKeyCompiler.coins

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)

noncomputable def after (context : Context source n) : OracleComp (RegistrationNativeOpenKey.Spec KemSK) (Result source n Value) :=
  match context.initialized.1 with
  | none => pure (context, none)
  | some born =>
      (fun result => (context, some result)) <$>
        RegistrationNativeG3NativeCheckedUniformSource.openProgram setup checks wire source route
          (RegistrationNativeMldsa.owned source born.native.credential) selectedOwner selectedAccept (setup.dh.publicKey context.scalar)
          serverKeyId bounds mode context.seed context.scalar (setup.joint.staticDh context.seed (setup.dh.publicKey context.scalar))
          (adversary ⟨setup.joint.publicKeys context.seed, born.native.credential.publicKey, serverKeyId⟩)
          (RegistrationNativeG3NativeStartupFields.word born.native.frontend)
          (RegistrationNativeG3NativeUniformAuditBound.ordinary context.initialized.2)

noncomputable def program : OracleComp (RegistrationNativeOpenKey.Spec KemSK) (Result source n Value) := do
  let context ← simulateQ coins (prior setup wire source route ensureInit identityIndex serverKeyId)
  after setup checks wire source route serverKeyId selectedOwner selectedAccept bounds mode adversary context

private theorem coin_bound (predicate : (RegistrationNativeOpenKey.NativeSpec KemSK).Domain → Prop)
    [DecidablePred predicate]
    (free : ∀ query, ¬ predicate (.inl (.inl (.inl query)))) (work : ProbComp (Context source n)) :
    (simulateQ (RegistrationNativeOpenKey.native (KemSK := KemSK)) (simulateQ coins work)).IsQueryBoundP predicate 0 := by
  rw [← QueryImpl.simulateQ_compose]
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ work 0 (isQueryBoundP_false work 0)
  intro query
  simp only [QueryImpl.compose, coins, simulateQ_spec_query, RegistrationNativeOpenKey.keyLift,
    RegistrationNativeKeyCompiler.coins, RegistrationNativeOpenKey.native, isQueryBoundP_query_iff]
  intro counted
  exact False.elim (free query counted)

/-- The unchanged whole startup client satisfies both ordinary KEM resource bounds internally. -/
theorem resource_bounds (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication)) :
    (simulateQ RegistrationNativeOpenKey.native
      (program (n := n) setup checks wire source route ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary)).IsQueryBoundP
        (RegistrationNativeKemReservation.IsCreate (ambient := RegistrationNativeOpenKey.Ambient) (KemSK := KemSK)) budget.create ∧
    (simulateQ RegistrationNativeOpenKey.native
      (program (n := n) setup checks wire source route ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary)).IsQueryBoundP
        (RegistrationNativeKemPoolSource.IsReveal (ambient := RegistrationNativeOpenKey.Ambient) (KemSK := KemSK)) 0 := by
  constructor
  · unfold program
    rw [simulateQ_bind]
    apply (OracleComp.isQueryBoundP_bind (n := 0) (m := budget.create) ?_ ?_).mono (by omega)
    · exact coin_bound source _ (fun _ => id) _
    · intro context _possible
      unfold after
      split
      · trivial
      · simp only [simulateQ_map, isQueryBoundP_map_iff]
        exact (RegistrationNativeG3NativeCheckedUniformSource.resource_bounds setup checks wire source route _ selectedOwner selectedAccept _ serverKeyId
          bounds mode context.seed context.scalar _ _ _ _ budget (bounded _)).1
  · unfold program
    rw [simulateQ_bind]
    apply (OracleComp.isQueryBoundP_bind (n := 0) (m := 0) ?_ ?_).mono (by omega)
    · exact coin_bound source _ (fun _ => id) _
    · intro context _possible
      unfold after
      split
      · trivial
      · simp only [simulateQ_map, isQueryBoundP_map_iff]
        exact (RegistrationNativeG3NativeCheckedUniformSource.resource_bounds setup checks wire source route _ selectedOwner selectedAccept _ serverKeyId
          bounds mode context.seed context.scalar _ _ _ _ budget (bounded _)).2

private theorem reference_coins (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    {A : Type} (work : ProbComp A)
    (before : (PqxdhLiveKemBirth.Pool KemSK × RegistrationNativeKemSwitchSource.Phase) × RegistrationNativeOpenKeyKemGame.Table) :
    (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected pairs publicKey challenge candidate)
      (simulateQ coins work)).run before = (fun reply => (reply, before)) <$> work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected pairs publicKey challenge candidate ∘ₛ coins =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT _ ProbComp) := by
    funext query
    apply StateT.ext
    rintro ⟨external, table⟩
    simp only [QueryImpl.compose, coins, RegistrationNativeOpenKey.keyLift,
      RegistrationNativeKeyCompiler.coins, simulateQ_spec_query, RegistrationNativeOpenKeyKemEarlySource.reference,
      QueryImpl.liftTarget_apply, QueryImpl.ofLift, StateT.run, PqxdhRegistrationJointKemSecondEntry.lazyImpl, ]
    rfl
  rw [same, simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  change (work >>= fun value => pure (value, before)) = _
  exact bind_pure_comp _ _

/-- For every fixed actual challenge, closing the whole client preserves its actual probability prefix and full reached output. -/
theorem reference_source (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected pairs publicKey challenge candidate)
      (program (n := n) setup checks wire source route ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary)).run'
        ((PqxdhLiveKemBirth.empty, none), ∅) =
      (do let context ← prior setup wire source route ensureInit identityIndex serverKeyId
          (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected pairs publicKey challenge candidate)
            (after setup checks wire source route serverKeyId selectedOwner selectedAccept bounds mode adversary context)).run'
              ((PqxdhLiveKemBirth.empty, none), ∅)) := by
  unfold program
  simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_bind]
  rw [reference_coins]
  simp only [bind_map_left]

end BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupUniformValue
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupUniformValue.resource_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupUniformValue.resource_bounds
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupUniformValue.reference_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupUniformValue.reference_source
