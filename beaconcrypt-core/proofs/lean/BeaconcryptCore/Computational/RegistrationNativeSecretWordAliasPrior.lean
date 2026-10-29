-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasOuterRepeatBound

/-! A complete candidate-independent probability prefix is executed inside one actual alias client. Its continuation may choose the original frontend, signing credential and reached World from the actual prefix result. The prefix preserves both the symbolic literal log and byte cache, and its one concrete recovery adversary includes all prefix sampling. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasPrior
open RegistrationNativeSecretWordService (Combined coins)
open RegistrationNativeSecretWordServiceCaps (Kind Counted)
open RegistrationNativeSuffixKeyPrf (Secret)
variable {P Result : Type}
private theorem probability_source {S A : Type}
    (handler : QueryImpl Combined (StateT S ProbComp))
    (coin : ∀ query before, (handler (.inl (.inl query))).run before =
      (fun reply => (reply, before)) <$> (unifSpec.query query : ProbComp _))
    (work : ProbComp A) (before : S) :
    (simulateQ handler (simulateQ coins work)).run before = (fun value => (value, before)) <$> work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : handler ∘ₛ coins =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT S ProbComp) := by
    funext query
    apply StateT.ext
    intro current
    simp only [QueryImpl.compose, coins, simulateQ_spec_query, QueryImpl.liftTarget_apply]
    change handler (.inl (.inl query)) current =
      ((unifSpec.query query : ProbComp _) >>= fun reply => pure (reply, current))
    rw [bind_pure_comp]
    exact coin query current
  rw [same, simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  change (work >>= fun value => pure (value, before)) = _
  exact bind_pure_comp _ _

private theorem logged_coins (keySource : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (candidate : Secret)
    (query : unifSpec.Domain) (before : RegistrationNativeSecretWord.Cache × List Secret) :
    (RawCtxSelectedQueryTrace.recorded (RegistrationNativeSecretWordRecoveryCompiler.closed keySource candidate)
      RegistrationNativeSecretWordRecoveryCompiler.literals (.inl (.inl query))).run before =
      (fun reply => (reply, before)) <$> (unifSpec.query query : ProbComp _) := by
  simp only [RawCtxSelectedQueryTrace.recorded, RegistrationNativeSecretWordRecoveryCompiler.closed,
    RegistrationNativeSecretWordRecoveryCompiler.literals, RegistrationNativeSecretWord.literals,
    RegistrationNativeSecretWord.symbolic, RegistrationNativeG3CellEager.lazy,
    StateT.run, List.append_nil, bind_pure_comp,
    QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift, ]
  change (fun result => (result.1, (result.2, before.2))) <$>
    ((unifSpec.query query : ProbComp _) >>= fun reply => pure (reply, before.1)) = _
  rw [bind_pure_comp, Functor.map_map]


noncomputable def client (prior : ProbComp P) (next : P → OracleComp Combined Result) := do
  let context ← simulateQ coins prior
  next context

/-- Actual prefix sampling consumes no key or suffix queries. -/
theorem client_bound (prior : ProbComp P) (next : P → OracleComp Combined Result)
    (kind : Kind) (q : Nat) (bounded : ∀ context, (next context).IsQueryBoundP (Counted kind) q) :
    (client prior next).IsQueryBoundP (Counted kind) q := by
  apply (OracleComp.isQueryBoundP_bind (n := 0) (m := q) ?_ ?_).mono (by omega)
  · apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ prior 0 (isQueryBoundP_false prior 0)
    intro query
    cases kind <;> simp [coins, Counted, RegistrationNativeSecretWordRecoveryCompiler.IsKey,
      RegistrationNativeSecretWordRecoveryCompiler.IsSuffix, RegistrationNativeSecretWord.IsKey, isQueryBoundP_query_iff]
  · intro context _possible
    exact bounded context

/-- The actual probability prefix leaves the symbolic cache and literal log unchanged. -/
theorem logged_source (keySource : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (prior : ProbComp P) (next : P → OracleComp Combined Result) (candidate : Secret) :
    RegistrationNativeSecretWordRecoveryBound.logged keySource candidate (client prior next) =
      (prior >>= fun context => RegistrationNativeSecretWordRecoveryBound.logged keySource candidate (next context)) := by
  unfold RegistrationNativeSecretWordRecoveryBound.logged client
  simp only [simulateQ_bind, StateT.run_bind]
  rw [probability_source _ (logged_coins keySource candidate)]
  simp only [bind_map_left]

/-- The actual probability prefix also leaves the complete byte cache unchanged. -/
theorem bytes_source (keySource : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (prior : ProbComp P) (next : P → OracleComp Combined Result) (candidate : Secret) :
    (simulateQ (RegistrationNativeSecretWordRecoveryBound.bytes keySource candidate) (client prior next)).run ∅ =
      (prior >>= fun context => (simulateQ (RegistrationNativeSecretWordRecoveryBound.bytes keySource candidate) (next context)).run ∅) := by
  unfold client
  simp only [simulateQ_bind, StateT.run_bind]
  rw [probability_source]
  · simp only [bind_map_left]
  · intro query before
    rfl

/-- A mathematical candidate may be sampled after the entire independent actual prefix without changing its observed byte law. -/
theorem bytesView_source {Observation : Type} (keySource : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (prior : ProbComp P) (next : P → OracleComp Combined Result)
    (observe : Secret → (Result × RegistrationNativeSecretWordSource.ByteCache) → Observation) :
    RegistrationNativeSecretWordRecoveryBound.bytesView keySource observe (client prior next) =ᵈ
      (prior >>= fun context => RegistrationNativeSecretWordRecoveryBound.bytesView keySource observe (next context)) := by
  simp only [RegistrationNativeSecretWordRecoveryBound.bytesView, bytes_source, map_bind]
  exact OracleComp.EvalDistEq.bind_bind_swap ($ᵗ Secret) prior _

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasPrior
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasPrior.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasPrior.client_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasPrior.logged_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasPrior.logged_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasPrior.bytes_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasPrior.bytes_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasPrior.bytesView_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasPrior.bytesView_source
