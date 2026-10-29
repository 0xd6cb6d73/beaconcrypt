-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3RetainedCallbacks
import BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialService

/-! The finite known108-byte material service is the actual original native descriptor-flag service under the same selective fixed-key table. Both retain the same flags, allocator, demand counter, material-cache field and nonselected byte cache. Only a genuinely fresh selected address needs room; the original complete-frontend demand cap supplies it at runtime. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectService
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeSelectiveHiddenService (State selected)
open RegistrationNativePairedChoice (Choice)
variable {n : Nat} {Value : Type}
attribute [local irreducible] uniformSample PqxdhServerAuthKeySchedule.fromRoot RegistrationNativeRelatedRoot.nativeRoot

private theorem state_pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (map : A → B) (work : StateT S m A) (before : S) :
    (map <$> work) before = Prod.map map id <$> work before := StateT.run_map map work before

private theorem state_bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = work before >>= fun result => next result.1 result.2 := rfl

private theorem state_lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := by
  change (work >>= fun value => pure (value, before)) = _
  exact bind_pure_comp _ _

private theorem material_coins (materials : Slot n → Material) (work : ProbComp Value) :
    simulateQ (RegistrationNativeG3CellEager.fixed materials)
      (simulateQ RegistrationNativeG3LocalMaterialService.coins work) = work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : RegistrationNativeG3CellEager.fixed materials ∘ₛ RegistrationNativeG3LocalMaterialService.coins =
      QueryImpl.ofLift unifSpec ProbComp := by funext query; rfl
  rw [same, simulateQ_ofLift_eq_self]

private theorem direct_coins (work : ProbComp Value) :
    simulateQ (RegistrationNativeG3MetricCoins.localCoins (n := n))
      (simulateQ RegistrationNativeHiddenService.coins work) = work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : RegistrationNativeG3MetricCoins.localCoins (n := n) ∘ₛ RegistrationNativeHiddenService.coins =
      QueryImpl.ofLift unifSpec ProbComp := by funext query; rfl
  rw [same, simulateQ_ofLift_eq_self]

/-- The fixed material table forwards the original ordinary probability program exactly. -/
theorem coins_source (materials : Slot n → Material) (work : ProbComp Value) :
    simulateQ (RegistrationNativeG3CellEager.fixed materials)
      (simulateQ RegistrationNativeG3LocalMaterialService.coins work) = work := material_coins materials work

/-- Successful and failed preparation update the same actual native descriptor flag in both finite services. -/
theorem prepare_source (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (materials : Slot n → Material) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (message : Message) (before : State n) :
    (RegistrationNativeG3RetainedCallbacks.keys source input inside candidate materials seeds (.inr (.prepare message))).run before =
      simulateQ (RegistrationNativeG3CellEager.fixed materials)
        ((RegistrationNativeG3LocalMaterialService.prepare input message).run before) := by
  simp only [RegistrationNativeG3RetainedCallbacks.keys, RegistrationNativeG3SelectiveService.direct,
    RegistrationNativeG3SelectiveService.count, RegistrationNativeG3KeyService.direct,
    RegistrationNativeG3LocalMaterialService.prepare, StateT.run, simulateQ_pure]
  rfl

/-- Every actual native material demand has the same full known108-byte reply and complete reached selective service state, with capacity required only at a genuinely fresh selected input. -/
theorem demand_source (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (materials : Slot n → Material) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (message : Message) (before : State n)
    (room : ∀ bytes, input message = some bytes → selected inside candidate bytes = true →
      before.1.slots bytes = none → before.1.next < n) :
    (fun result => (result.1.map Choice.known, result.2)) <$>
      (RegistrationNativeG3RetainedCallbacks.keys source input inside candidate materials seeds (.inr (.demand message))).run before =
      simulateQ (RegistrationNativeG3CellEager.fixed materials)
        ((Option.map (RegistrationNativeG3MaterializedFrontend.materialize seeds) <$>
          RegistrationNativeG3LocalMaterialService.demand source input inside candidate message).run before) := by
  simp only [StateT.run_map, simulateQ_map]
  cases prepared : before.1.prepared message with
  | false =>
      simp only [RegistrationNativeG3RetainedCallbacks.keys, RegistrationNativeG3SelectiveService.direct,
        RegistrationNativeG3SelectiveService.count, RegistrationNativeG3KeyService.direct,
        RegistrationNativeG3LocalMaterialService.demand, RegistrationNativeG3LocalMaterialService.hiddenDemand,
        prepared, Bool.false_eq_true, ite_false, StateT.run, simulateQ_pure, map_pure,
        state_pure_apply]
      rfl
  | true =>
      cases formed : input message with
      | none =>
          simp only [RegistrationNativeG3RetainedCallbacks.keys, RegistrationNativeG3SelectiveService.direct,
            RegistrationNativeG3SelectiveService.count, RegistrationNativeG3KeyService.direct,
            RegistrationNativeG3LocalMaterialService.demand, RegistrationNativeG3LocalMaterialService.hiddenDemand,
            prepared, formed, ite_true, StateT.run, simulateQ_pure, map_pure,
            state_pure_apply]
          rfl
      | some bytes =>
          cases protectedInput : inside bytes
          all_goals simp only [RegistrationNativeG3RetainedCallbacks.keys, RegistrationNativeG3SelectiveService.direct,
            RegistrationNativeG3SelectiveService.count, RegistrationNativeG3KeyService.direct,
            RegistrationNativeG3LocalMaterialService.demand, RegistrationNativeG3LocalMaterialService.hiddenDemand,
            prepared, formed, protectedInput, Bool.false_eq_true, Bool.false_and, Bool.true_and,
            ite_true, ite_false, StateT.run, state_map_apply, state_pure_apply, simulateQ_map, simulateQ_pure, simulateQ_spec_query,
            Functor.map_map, RegistrationNativeG3SelectiveService.fixedKeys]
          case false =>
            simp only [selected, protectedInput, Bool.false_and, Bool.false_eq_true, ite_false,
              simulateQ_pure, map_pure]
            rfl
          case true =>
            cases chosen : selected inside candidate bytes with
            | false =>
                cases found : before.2 bytes
                all_goals simp only [Bool.false_eq_true, Bool.not_false, ite_false, ite_true,
                  RegistrationNativeSelectiveHiddenService.known, RegistrationNativeG3LocalMaterialService.known,
                  found, simulateQ_pure, simulateQ_map, map_pure,
                  material_coins, direct_coins, Functor.map_map,
                  Prod.map_def, id_eq]
                all_goals rfl
            | true =>
                cases found : before.1.slots bytes with
                | some slot =>
                    simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true,
                      RegistrationNativeHiddenService.reserve, found,
                      RegistrationNativeG3LocalMaterialService.material, state_lift_apply,
                      simulateQ_pure, simulateQ_map, simulateQ_spec_query, map_pure,
                      RegistrationNativeG3CellEager.fixed, Functor.map_map, Prod.map_def, id_eq]
                    rfl
                | none =>
                    have available := room bytes formed chosen found
                    simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true,
                      RegistrationNativeHiddenService.reserve, found, available, dite_true,
                      RegistrationNativeG3LocalMaterialService.material, state_lift_apply,
                      simulateQ_pure, simulateQ_map, simulateQ_spec_query, map_pure,
                      RegistrationNativeG3CellEager.fixed, Functor.map_map, Prod.map_def, id_eq]
                    rfl

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectService
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectService.prepare_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectService.prepare_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectService.demand_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectService.demand_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectService.coins_source' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectService.coins_source
