-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCountedCapability

/-! Ordinary source randomness and actual private indexed KEM capabilities form one additive free program. Its interpreter retains the complete source state, private key pool and exact primitive draw accounting across every continuation. This is the true-cost leaf boundary for the corrected profile; no masked legacy experiment is identified with that profile. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCountedProgram
open PqxdhKemIndCca (MlKemScheme)
open PqxdhLiveKemBirth (Pool)
open RegistrationNativeKemCountedCapability (LeafSpec)
open RegistrationNativeMldsaCapability (advance)
variable {ι KemSK State Value Next : Type} {base : OracleSpec ι} {n : Nat}

abbrev Spec (KemSK : Type) := unifSpec + RegistrationNativeKemCountedCapability.Spec KemSK

def ordinary : QueryImpl unifSpec (OracleComp (Spec KemSK)) := fun query => (Spec KemSK).query (.inl query)
def lift (work : ProbComp Value) : OracleComp (Spec KemSK) Value := simulateQ ordinary work
def liftState (work : StateT State ProbComp Value) : StateT State (OracleComp (Spec KemSK)) Value := fun before => lift (work.run before)

noncomputable def handler (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) :
    QueryImpl (Spec KemSK) (StateT (Pool KemSK) ProbComp)
  | .inl query => StateT.lift (unifSpec.query query)
  | .inr query => RegistrationNativeKemCountedCapability.actual baseImpl kem query

noncomputable def evaluate (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (work : OracleComp (Spec KemSK) Value) (pool : Pool KemSK) : ProbComp (Value × Pool KemSK) :=
  (simulateQ (handler baseImpl kem) work).run pool

noncomputable def runState (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (work : StateT State (OracleComp (Spec KemSK)) Value) (before : State) (pool : Pool KemSK) : ProbComp ((Value × State) × Pool KemSK) :=
  evaluate baseImpl kem (work.run before) pool

/-- Ordinary source randomness retains the literal complete private pool. -/
theorem ordinary_source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (work : ProbComp Value) (before : Pool KemSK) :
    evaluate baseImpl kem (lift work) before = (fun value => (value, before)) <$> work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [evaluate, lift, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [evaluate, lift, simulateQ_bind, simulateQ_spec_query, ordinary, handler, StateT.run_bind, StateT.run_lift]
      simp only [bind_assoc, pure_bind, map_bind]
      apply bind_congr
      intro reply
      exact ih reply before

/-- A pure source return keeps all source and private-table state. -/
theorem run_pure (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (value : Value) (current : State) (before : Pool KemSK) :
    runState baseImpl kem (pure value) current before = pure ((value, current), before) := by
  simp only [runState, evaluate, StateT.run_pure, simulateQ_pure]

/-- Every adaptive continuation receives the literal reached source state and private pool. -/
theorem run_bind (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (work : StateT State (OracleComp (Spec KemSK)) Value)
    (next : Value → StateT State (OracleComp (Spec KemSK)) Next) (current : State) (before : Pool KemSK) :
    runState baseImpl kem (work >>= next) current before = (do
      let result ← runState baseImpl kem work current before
      runState baseImpl kem (next result.1.1) result.1.2 result.2) := by
  simp only [runState, evaluate, StateT.run_bind, simulateQ_bind]

/-- Ordinary stateful source work retains all source coordinates and leaves the private KEM pool untouched. -/
theorem run_liftState (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (work : StateT State ProbComp Value) (current : State) (before : Pool KemSK) :
    runState baseImpl kem (liftState work) current before = (fun result => (result, before)) <$> work.run current :=
  ordinary_source baseImpl kem _ before

def call (query : (LeafSpec KemSK).Domain) :
    StateT (PqxdhRecordLiftWorld.State n) (OracleComp (Spec KemSK)) ((LeafSpec KemSK).Range query) := fun before => do
  let result ← (Spec KemSK).query (.inr query)
  pure (result.1, advance .native before result.2)

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : A → B) (work : StateT S m A) (before : S) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before

/-- Every actual named KEM leaf restores its full source World, private pool and precise uniform accounting. -/
theorem call_source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (query : (LeafSpec KemSK).Domain) (world : PqxdhRecordLiftWorld.State n) (pool : Pool KemSK) :
    runState baseImpl kem (call query) world pool =
      (fun result => ((result.1.1, result.2), result.1.2)) <$>
        (PqxdhRecordLiftWorld.sampled ((RegistrationNativeKemCountedCapability.draw baseImpl kem query).run pool)).run world := by
  have law := congrArg (fun distribution => (fun result => ((result.1, result.2.1), result.2.2)) <$> distribution)
    (RegistrationNativeKemCountedCapability.actual_native baseImpl kem query pool world)
  simp only [runState, evaluate, call, StateT.run, bind_pure_comp, simulateQ_map, simulateQ_spec_query, handler]
  rw [map_apply]
  simp only [StateT.run, Functor.map_map] at law ⊢
  exact law

end BeaconcryptCore.Computational.RegistrationNativeKemCountedProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedProgram.ordinary_source' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedProgram.ordinary_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedProgram.run_pure' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedProgram.run_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedProgram.run_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedProgram.run_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedProgram.run_liftState' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedProgram.run_liftState

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedProgram.call_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedProgram.call_source
