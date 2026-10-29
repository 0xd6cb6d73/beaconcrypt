-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTrace

/-! Actual checked audit callbacks and the residual common/KEM queries reproduce the complete symbolic frontend trace after literal evaluation. In particular, optional preparation or material refusal still records the original callback before its check. The adaptive equation retains the complete current trace and the full original result rather than reconstructing events from successful replies alone. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTraceSource
open RegistrationNativeSecretWordCheckedFrontend (Spec PlainSpec erase implementation localLift)
open RegistrationNativeSecretWordCheckedTrace (handler state)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open PqxdhKemIndCca (MlKemSharedSecret)
variable {n : Nat} {KemSK Value : Type}

private theorem state_bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (first : StateT S m A) (next : A → StateT S m B) (before : S) :
    (first >>= next) before = (first before >>= fun reached => next reached.1 reached.2) := rfl

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (map : A → B) (work : StateT S m A) (before : S) :
    (map <$> work) before = Prod.map map id <$> work before := StateT.run_map map work before

def keys : QueryImpl RegistrationNativeKeyCompiler.KeySpec (OracleComp (Spec n KemSK)) := fun query =>
  (Spec n KemSK).query (.inl query)

def plainKeys : QueryImpl RegistrationNativeKeyCompiler.KeySpec (OracleComp (PlainSpec n KemSK)) := fun query =>
  (PlainSpec n KemSK).query (.inl query)

private theorem local_keys (selected : Bool) : localLift (n := n) (KemSK := KemSK) selected ∘ₛ
    RegistrationNativeSecretWordChecked.keys = keys := by
  funext query
  simp only [QueryImpl.compose, RegistrationNativeSecretWordChecked.keys, simulateQ_spec_query, localLift, keys]

private theorem erase_keys : erase (n := n) (KemSK := KemSK) ∘ₛ keys = plainKeys := by
  funext query
  rfl

private theorem local_key_program (selected : Bool) (work : OracleComp RegistrationNativeKeyCompiler.KeySpec Value) :
    simulateQ (localLift (n := n) (KemSK := KemSK) selected)
      (simulateQ RegistrationNativeSecretWordChecked.keys work) = simulateQ keys work := by
  rw [← QueryImpl.simulateQ_compose, local_keys]

private theorem erase_key_program (work : OracleComp RegistrationNativeKeyCompiler.KeySpec Value) :
    simulateQ (erase (n := n) (KemSK := KemSK)) (simulateQ keys work) = simulateQ plainKeys work := by
  rw [← QueryImpl.simulateQ_compose, erase_keys]

/-- The actual evaluated material-table program cannot change any chronological preparation, demand, installation or encapsulation trace. -/
theorem key_program (candidate : MlKemSharedSecret) (work : OracleComp RegistrationNativeKeyCompiler.KeySpec Value)
    (before : RegistrationNativeG2Trace.State) :
    (simulateQ (handler candidate) (simulateQ (keys (n := n) (KemSK := KemSK)) work)).run before =
      (fun value => (value, before)) <$> simulateQ plainKeys work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, keys, handler,
        StateT.run, erase, RegistrationNativeSecretWordCheckedTrace.begin,
        RegistrationNativeSecretWordCheckedTrace.finish, state_bind_apply,
        bind_map_left, map_bind]
      apply bind_congr
      intro reply
      exact ih reply before

/-- The actual checked material operation records its demand before optional input checks and keeps that trace throughout its key-table computation. -/
theorem material_source (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : MlKemSharedSecret)
    (input : RegistrationNativeSecretWordMessage.Message → Option RegistrationNativeSecretWord.Key)
    (message : RegistrationNativeSecretWordMessage.Message) (before : RegistrationNativeG2Trace.State) :
    (simulateQ (handler candidate)
      (simulateQ (localLift (n := n) (KemSK := KemSK) false)
        (RegistrationNativeSecretWordChecked.material source inside candidate input message))).run before =
      (fun reply => (reply, RegistrationNativeSecretWordCheckedTrace.begin
        (n := n) (KemSK := KemSK) (.inr (.inr (.demand (RegistrationNativeSecretWordMessage.eval candidate message)))) before)) <$>
        simulateQ erase (simulateQ (localLift false)
          (RegistrationNativeSecretWordChecked.material source inside candidate input message)) := by
  simp only [RegistrationNativeSecretWordChecked.material, RegistrationNativeSecretWordChecked.audit,
    simulateQ_bind, simulateQ_spec_query, localLift, StateT.run_bind,
    pure_bind, erase]
  cases found : input message with
  | none =>
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      rfl
  | some key =>
      simp only [simulateQ_map, local_key_program, erase_key_program, StateT.run_map,
        key_program, Functor.map_map]
      rfl

/-- Each actual symbolic callback has precisely its evaluated native trace under the concrete checked source, including all failed root and installation replies. -/
theorem word_query (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : MlKemSharedSecret)
    (input : RegistrationNativeSecretWordMessage.Message → Option RegistrationNativeSecretWord.Key)
    (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (before : RegistrationNativeSecretWordFrontendTrace.State) :
    Prod.map id (state candidate) <$>
      simulateQ (erase ∘ₛ implementation source inside candidate input)
        ((RegistrationNativeSecretWordFrontendTrace.handler query).run before) =
      (simulateQ (handler candidate) (implementation source inside candidate input query)).run (state candidate before) := by
  rcases query with (message | (message | common) | kem) | record
  · simp only [RegistrationNativeSecretWordFrontendTrace.handler, StateT.run,
      RegistrationNativeSecretWordFrontendTrace.begin, RegistrationNativeSecretWordFrontendTrace.finish,
      simulateQ_map, simulateQ_spec_query, QueryImpl.compose, implementation,
      RegistrationNativeSecretWordChecked.preparation, RegistrationNativeSecretWordChecked.audit,
      simulateQ_bind, simulateQ_pure, localLift,
      state_bind_apply,
      pure_bind,
      erase, map_pure, state, Prod.map_def, id_eq,
      List.map_append, List.map_cons, List.map_nil,
      RegistrationNativeSecretWordCheckedTrace.event, Option.map_none]
    rfl
  · rw [implementation, material_source]
    simp only [RegistrationNativeSecretWordFrontendTrace.handler, StateT.run,
      RegistrationNativeSecretWordFrontendTrace.begin, RegistrationNativeSecretWordFrontendTrace.finish,
      simulateQ_map, simulateQ_spec_query, QueryImpl.compose, implementation,
      Functor.map_map, Prod.map_def, id_eq, state, RegistrationNativeSecretWordCheckedTrace.begin,
      List.map_append, List.map_cons, List.map_nil, RegistrationNativeSecretWordCheckedTrace.event, Option.map_some]
    rfl
  · rcases common with publication | environment
    · rfl
    · rcases environment with coin | capability
      · rfl
      · cases capability <;>
          simp only [RegistrationNativeSecretWordFrontendTrace.handler, StateT.run,
            RegistrationNativeSecretWordFrontendTrace.begin, RegistrationNativeSecretWordFrontendTrace.finish,
            simulateQ_map, simulateQ_spec_query, QueryImpl.compose, implementation, handler, erase,
            RegistrationNativeSecretWordCheckedTrace.begin, RegistrationNativeSecretWordCheckedTrace.finish,
            RegistrationNativeG2Trace.begin, RegistrationNativeG2Trace.finish,
            Functor.map_map, Prod.map_def, id_eq, state]
        all_goals try rfl
        all_goals
          congr 1
          funext reply
          cases reply <;> cases found : before.current <;>
            simp only [RegistrationNativeSecretWordFrontendTrace.installed, RegistrationNativeSecretWordFrontendTrace.attempt,
              RegistrationNativeG2Trace.installed, RegistrationNativeG2Trace.attempt, found,
              Option.map_none, Option.map_some, List.map_append, List.map_cons, List.map_nil,
              RegistrationNativeSecretWordCheckedTrace.event]
  · rcases kem with (other | key) | (pool | key)
    · rfl
    · simp only [RegistrationNativeSecretWordFrontendTrace.handler, StateT.run,
        RegistrationNativeSecretWordFrontendTrace.begin, RegistrationNativeSecretWordFrontendTrace.finish,
        simulateQ_map, simulateQ_spec_query, QueryImpl.compose, implementation, handler, erase,
        RegistrationNativeSecretWordCheckedTrace.begin, RegistrationNativeSecretWordCheckedTrace.finish,
        Functor.map_map, Prod.map_def, id_eq, state, List.map_append, List.map_cons, List.map_nil,
        RegistrationNativeSecretWordCheckedTrace.event]
      rfl
    · cases pool <;> rfl
    · simp only [RegistrationNativeSecretWordFrontendTrace.handler, StateT.run,
        RegistrationNativeSecretWordFrontendTrace.begin, RegistrationNativeSecretWordFrontendTrace.finish,
        simulateQ_map, simulateQ_spec_query, QueryImpl.compose, implementation, handler, erase,
        RegistrationNativeSecretWordCheckedTrace.begin, RegistrationNativeSecretWordCheckedTrace.finish,
        Functor.map_map, Prod.map_def, id_eq, state, List.map_append, List.map_cons, List.map_nil,
        RegistrationNativeSecretWordCheckedTrace.event]
      rfl
  · rfl

/-- Complete symbolic checked execution retains the exact evaluated native trace through all adaptive raw frontend continuations. -/
theorem word_program (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : MlKemSharedSecret)
    (input : RegistrationNativeSecretWordMessage.Message → Option RegistrationNativeSecretWord.Key)
    (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) Value)
    (before : RegistrationNativeSecretWordFrontendTrace.State) :
    Prod.map id (state candidate) <$>
      simulateQ (erase ∘ₛ implementation source inside candidate input)
        ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler work).run before) =
      (simulateQ (handler candidate) (simulateQ (implementation source inside candidate input) work)).run (state candidate before) := by
  rw [QueryImpl.simulateQ_mapStateTBase_run, ← QueryImpl.simulateQ_compose]
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (state candidate) _ work before
  intro query current
  exact word_query source inside candidate input query current

end BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTraceSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTraceSource.key_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTraceSource.key_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTraceSource.material_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTraceSource.material_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTraceSource.word_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTraceSource.word_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTraceSource.word_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTraceSource.word_program
