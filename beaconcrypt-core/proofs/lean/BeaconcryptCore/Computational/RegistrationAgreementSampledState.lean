-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationWorldAgreement
open CoreModels Aeneas OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
/-! The original uniform-query counter is a monad interpretation, so sampling an entire actual request tree equals sampling each reached callback in sequence. Complete auxiliary and World states remain explicit. -/
namespace BeaconcryptCore.Computational.RegistrationAgreementSampledState
variable {n : Nat} {A B Auxiliary : Type}

private theorem state_pure_apply {S A : Type} {m : Type → Type} [Monad m]
    (value : A) (before : S) : (pure value : StateT S m A) before = pure (value, before) := rfl
private theorem state_bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

theorem sampled_pure (value : A) (world : PqxdhRecordLiftWorld.State n) :
    (PqxdhRecordLiftWorld.sampled (pure value)).run world = pure (value, world) := by
  simp only [PqxdhRecordLiftWorld.sampled, StateT.run, simulateQ_pure, state_pure_apply, pure_bind]

theorem sampled_bind (work : ProbComp A) (next : A → ProbComp B) (world : PqxdhRecordLiftWorld.State n) :
    (PqxdhRecordLiftWorld.sampled (work >>= next)).run world = (do
      let (value, current) ← (PqxdhRecordLiftWorld.sampled work).run world
      (PqxdhRecordLiftWorld.sampled (next value)).run current) := by
  simp only [PqxdhRecordLiftWorld.sampled, StateT.run, simulateQ_bind, state_bind_apply,
    bind_assoc, pure_bind]

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : A → B) (work : StateT S m A) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := by
  change (work before >>= fun result => pure (observe result.1, result.2)) = _
  rw [bind_pure_comp]
  rfl

theorem sampled_map (observe : A → B) (work : ProbComp A) (world : PqxdhRecordLiftWorld.State n) :
    (PqxdhRecordLiftWorld.sampled (observe <$> work)).run world =
      Prod.map observe id <$> (PqxdhRecordLiftWorld.sampled work).run world := by
  simp only [PqxdhRecordLiftWorld.sampled, StateT.run, simulateQ_map,
    state_map_apply, bind_pure_comp, Functor.map_map]
  rfl

variable {ι : Type} {spec : OracleSpec ι}
def implementation (backend : QueryImpl spec (StateT Auxiliary ProbComp)) :
    QueryImpl spec (StateT (Auxiliary × PqxdhRecordLiftWorld.State n) ProbComp) := fun request before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (PqxdhRecordLiftWorld.sampled ((backend request).run before.1)).run before.2

theorem program (backend : QueryImpl spec (StateT Auxiliary ProbComp)) (work : OracleComp spec A)
    (auxiliary : Auxiliary) (world : PqxdhRecordLiftWorld.State n) :
    (simulateQ (implementation backend) work).run (auxiliary, world) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (PqxdhRecordLiftWorld.sampled ((simulateQ backend work).run auxiliary)).run world := by
  induction work using OracleComp.inductionOn generalizing auxiliary world with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, sampled_pure, map_pure]
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [sampled_bind]
    simp only [implementation, StateT.run, bind_map_left, map_bind]
    apply bind_congr
    rintro ⟨⟨reply, after⟩, current⟩
    exact ih reply after current
end BeaconcryptCore.Computational.RegistrationAgreementSampledState

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementSampledState.sampled_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementSampledState.sampled_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementSampledState.sampled_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementSampledState.sampled_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementSampledState.sampled_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementSampledState.sampled_map

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementSampledState.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementSampledState.program
