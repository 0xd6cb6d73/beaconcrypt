-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3SelectiveServiceSource
import BeaconcryptCore.Computational.RegistrationNativeG3MetricCoins
import BeaconcryptCore.Computational.RegistrationNativeOpenRetained

/-! The actual selective direct108-byte service forwards original compiler coin programs without changing its descriptor flags, allocator, material cache or nonselected cache. Root-free ordinary World callbacks of the original retained compiler therefore retain their literal World/receipt outcomes under this service closure. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3RetainedCallbacks
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeSelectiveHiddenService (State)
variable {n : Nat} {KemSK Value : Type}
variable (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (materials : Slot n → Material) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)

noncomputable def keys : QueryImpl RegistrationNativeRetainedService.Spec (StateT (State n) ProbComp) := fun query before =>
  simulateQ RegistrationNativeG3MetricCoins.localCoins
    ((RegistrationNativeG3SelectiveService.direct source input inside candidate materials seeds query).run before)

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (map : A → B) (work : StateT S m A) (before : S) :
    (map <$> work) before = Prod.map map id <$> work before := StateT.run_map map work before

private theorem state_lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := by
  change (work >>= fun value => pure (value, before)) = _
  exact bind_pure_comp _ _

/-- The actual direct selective service forwards one original uniform query while preserving every private state field. -/
theorem coin (query : unifSpec.Domain) (before : State n) :
    (keys source input inside candidate materials seeds (.inl query)).run before =
      (fun reply => (reply, before)) <$> (unifSpec.query query : ProbComp _) := by
  simp only [keys, StateT.run, RegistrationNativeG3SelectiveService.direct, RegistrationNativeG3SelectiveService.count,
    RegistrationNativeG3KeyService.direct, StateT.lift, simulateQ_map, simulateQ_spec_query, RegistrationNativeKeyCompiler.coins,
    RegistrationNativeG3SelectiveService.fixedKeys, RegistrationNativeHiddenService.coins,
    bind_pure_comp]
  simp only [state_map_apply, state_lift_apply, simulateQ_map, simulateQ_spec_query,
    RegistrationNativeG3MetricCoins.localCoins, Functor.map_map]
  rfl

/-- Every actual ordinary probability program closes through the original retained coin surface with the full same selective private state. -/
theorem coins_source (work : ProbComp Value) (before : State n) :
    (simulateQ (keys source input inside candidate materials seeds)
      (simulateQ RegistrationNativePublicRetained.coins work)).run before =
      (fun value => (value, before)) <$> work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : keys source input inside candidate materials seeds ∘ₛ RegistrationNativePublicRetained.coins =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (State n) ProbComp) := by
    funext query current
    change keys source input inside candidate materials seeds (.inl query) current =
      ((unifSpec.query query : ProbComp _) >>= fun value => pure (value, current))
    rw [bind_pure_comp]
    exact coin source input inside candidate materials seeds query current
  rw [same, simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  change (work >>= fun value => pure (value, before)) = _
  exact bind_pure_comp _ _

private theorem ordinary_world (hmac : PqxdhSecretInputKdf.HmacSha512)
    (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value)
    (before : RegistrationNativePublicInterpreter.State n KemSK) :
    (RegistrationNativePublicRetained.ordinary hmac (RegistrationNativePublicInterpreter.world work)).run before =
      (fun result => (result.1, { before with world := result.2 })) <$>
        simulateQ RegistrationNativePublicRetained.coins (work.run before.world) := by
  change simulateQ RegistrationNativePublicRetained.coins
    (simulateQ (RegistrationNativePublicRootCoins.localImpl hmac)
      ((fun result => (result.1, { before with world := result.2 })) <$>
        simulateQ RegistrationNativePublicInterpreter.coins (work.run before.world))) = _
  simp only [simulateQ_map]
  rw [← QueryImpl.simulateQ_compose (RegistrationNativePublicRootCoins.localImpl hmac)
    RegistrationNativePublicInterpreter.coins]
  have same : RegistrationNativePublicRootCoins.localImpl hmac ∘ₛ RegistrationNativePublicInterpreter.coins =
      QueryImpl.ofLift unifSpec ProbComp := rfl
  rw [same, simulateQ_ofLift_eq_self]

/-- The original retained World callback closes under this actual direct108-byte service with exactly its original World result and unchanged private key state. -/
theorem world_source (hmac : PqxdhSecretInputKdf.HmacSha512)
    (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value)
    (before : RegistrationNativePublicInterpreter.State n KemSK) (keyState : State n) :
    (simulateQ (keys source input inside candidate materials seeds)
      ((RegistrationNativePublicRetained.ordinary hmac (RegistrationNativePublicInterpreter.world work)).run before)).run keyState =
      (fun result => ((result.1, { before with world := result.2 }), keyState)) <$> work.run before.world := by
  rw [ordinary_world, simulateQ_map, StateT.run_map, coins_source]
  simp only [Functor.map_map, ]

 /-- The complete original ordinary retained callback keeps its actual evaluated result and every selective private field under the concrete service closure. -/
theorem ordinary_source (hmac : PqxdhSecretInputKdf.HmacSha512)
    (work : RegistrationNativePublicInterpreter.M n KemSK Value)
    (before : RegistrationNativePublicInterpreter.State n KemSK) (keyState : State n) :
    (simulateQ (keys source input inside candidate materials seeds)
      ((RegistrationNativePublicRetained.ordinary hmac work).run before)).run keyState =
      (fun result => (result, keyState)) <$>
        simulateQ (RegistrationNativePublicRootCoins.localImpl hmac) (work.run before) := by
  change (simulateQ (keys source input inside candidate materials seeds)
    (simulateQ RegistrationNativePublicRetained.coins
      (simulateQ (RegistrationNativePublicRootCoins.localImpl hmac) (work.run before)))).run keyState = _
  exact coins_source source input inside candidate materials seeds _ keyState

end BeaconcryptCore.Computational.RegistrationNativeG3RetainedCallbacks
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedCallbacks.coin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedCallbacks.coin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedCallbacks.coins_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedCallbacks.coins_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedCallbacks.world_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedCallbacks.world_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedCallbacks.ordinary_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedCallbacks.ordinary_source
