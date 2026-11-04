-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaMainView

/-! A free-program transformation erases only the private Nat accounting receipt of each named ML leaf. Primitive queries, complete optional replies and their order remain literal. The transformation is not assumed invisible: its local World call law and closed-source input laws below are checked explicitly, and complete controller composition is a separate step. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCountMap
open RegistrationNativeMldsaProgram (Spec)
variable {source : RegistrationNativeMldsa.Source} {State Value Next : Type} {n : Nat}

def translation : QueryImpl (Spec source) (OracleComp (Spec source))
  | .inl query => (Spec source).query (.inl query)
  | .inr query => (fun reply => (reply.1, 0)) <$> (Spec source).query (.inr query)

def transform (work : OracleComp (Spec source) Value) : OracleComp (Spec source) Value :=
  simulateQ translation work

def transformState (work : StateT State (OracleComp (Spec source)) Value) : StateT State (OracleComp (Spec source)) Value :=
  fun before => transform (work.run before)

/-- Ordinary source randomness is unchanged by private ML accounting erasure. -/
theorem lift (work : ProbComp Value) : transform (RegistrationNativeMldsaProgram.lift (source := source) work) =
    RegistrationNativeMldsaProgram.lift work := by
  have restriction : translation (source := source) ∘ₛ RegistrationNativeMldsaProgram.ordinary =
      RegistrationNativeMldsaProgram.ordinary (source := source) := by
    funext query
    simp only [QueryImpl.apply_compose, RegistrationNativeMldsaProgram.ordinary, simulateQ_spec_query, translation]
  rw [transform, RegistrationNativeMldsaProgram.lift, ← QueryImpl.simulateQ_compose, restriction]

/-- Source-state lifting preserves its literal ordinary computation under count normalization. -/
theorem liftState (work : StateT State ProbComp Value) :
    transformState (RegistrationNativeMldsaProgram.liftState (source := source) work) = RegistrationNativeMldsaProgram.liftState work :=
  funext (fun before => lift (work.run before))

/-- Normalization preserves complete stateful sequencing and every failure continuation. -/
theorem bindState (work : StateT State (OracleComp (Spec source)) Value)
    (next : Value → StateT State (OracleComp (Spec source)) Next) :
    transformState (work >>= next) = (transformState work >>= fun value => transformState (next value)) := by
  funext before
  simp only [transformState, transform, StateT.run_bind, simulateQ_bind]
  rfl

/-- Complete adaptive oracle programs normalize in their original callback order. -/
theorem simulateState {Query : Type} {queries : OracleSpec Query}
    (implementation : QueryImpl queries (StateT State (OracleComp (Spec source)))) (work : OracleComp queries Value) :
    transformState (simulateQ implementation work) = simulateQ (fun query => transformState (implementation query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure]
      funext before
      simp only [transformState, StateT.run_pure, transform, simulateQ_pure]
      rfl
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, bindState, ih]

/-- The literal named generate or sign query retains its complete optional reply and uses zero private count in its continuation. -/
theorem query (request : RegistrationNativeMldsaCapability.Request source) :
    transform (liftM ((Spec source).query (.inr request)) : OracleComp (Spec source) (RegistrationNativeMldsaCapability.Reply request × Nat)) =
      (fun reply => (reply.1, 0)) <$> (liftM ((Spec source).query (.inr request)) : OracleComp (Spec source) (RegistrationNativeMldsaCapability.Reply request × Nat)) := by
  simp only [transform, simulateQ_spec_query, translation]
  rfl

/-- A normalized named ML call and the original call have the same complete operational World result under the explicit count view. -/
theorem call (accounting : RegistrationNativeMldsaCapability.Accounting)
    (request : RegistrationNativeMldsaCapability.Request source) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id RegistrationNativeMldsaWorldView.project <$>
        transform ((RegistrationNativeMldsaProgram.call accounting request).run before) =
      Prod.map id RegistrationNativeMldsaWorldView.project <$>
        (RegistrationNativeMldsaProgram.call accounting request).run (RegistrationNativeMldsaWorldView.project before) := by
  simp only [RegistrationNativeMldsaProgram.call, StateT.run, bind_pure_comp, transform,
    simulateQ_map, simulateQ_spec_query, translation, Functor.map_map, Prod.map, id_eq,
    RegistrationNativeMldsaWorldView.advance, RegistrationNativeMldsaWorldView.idempotent]

def Natural (projection : State → State) (work : StateT State (OracleComp (Spec source)) Value) : Prop :=
  ∀ before, Prod.map id projection <$> transform (work.run before) =
    Prod.map id projection <$> work.run (projection before)

/-- Every already-proved closed-source input independence law lifts to the free ML language without replacing ordinary randomness. -/
theorem closed (projection : State → State) (work : StateT State ProbComp Value)
    (stable : RegistrationNativeKemCounterIndependence.Stable projection work) :
    Natural projection (RegistrationNativeMldsaProgram.liftState (source := source) work) := by
  intro before
  have same := congrArg (RegistrationNativeMldsaProgram.lift (source := source)) (stable before)
  simp only [RegistrationNativeMldsaProgram.lift, simulateQ_map] at same
  simp only [RegistrationNativeMldsaProgram.liftState, StateT.run, lift]
  exact same

/-- Every actual complete closed native callback supplies the ordinary component of free count-parametric execution. -/
theorem native {ι KemSK : Type} {base : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (request : RegistrationNativeRawAdapter.TypedSpec.Domain) :
    Natural (source := source) (RegistrationNativeMldsaMainView.project (n := n))
      (RegistrationNativeMldsaProgram.liftState (source := source) (RegistrationNativeExperiment.handler
        setup checks wire route representation created source credential request)) :=
  closed (source := source) _ _ (RegistrationNativeMldsaMainView.handler setup checks wire route representation created credential request)
end BeaconcryptCore.Computational.RegistrationNativeMldsaCountMap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountMap.lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountMap.lift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountMap.liftState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountMap.liftState

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountMap.bindState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountMap.bindState

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountMap.simulateState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountMap.simulateState

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountMap.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountMap.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountMap.call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountMap.call

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountMap.closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountMap.closed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountMap.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountMap.native
