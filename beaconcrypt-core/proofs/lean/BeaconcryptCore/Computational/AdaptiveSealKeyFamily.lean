import BeaconcryptCore.Computational.CtxNonceAeadIndDollarValidation
import BeaconcryptCore.Computational.RawKeyPartition
import BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity

/-!
The indexed ordinary real/random encryption family preserves every nonce and successful-seal history. The constructed reduction forwards the selected key exclusively to the ordinary challenger and runs other-key work locally. Full stateful interpretation and arbitrary continuation equality precede the security hop.

This independent-key component does not establish the production evolving-material distribution, native reveal/restore freshness or the common computational-symbolic experiment. No primitive implementation is proved. The exact experiments, assumptions, statement explanations and complete query/byte ledgers are maintained in `doc/impl/adaptive-shared-ctx-privacy.md`.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveSealKeyFamily
open CtxRomAuth CtxNonceAeadIntCtxt CtxNonceAeadIndDollar CtxNonceAeadIndDollarValidation RawKeyPartition

abbrev Spec (count : Nat) := RawCtxRoleFamily.FamilySpec ModifiedNonceAeadAdversarySpec count
abbrev State (count : Nat) := Fin count → ModifiedNonceAeadHandlerState

def initialState (count : Nat) : State count := fun _ => emptyModifiedNonceAeadHandlerState

noncomputable def localImpl (real : Bool) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl ModifiedNonceAeadAdversarySpec (StateT ModifiedNonceAeadHandlerState ProbComp) :=
  if real then modifiedNonceAeadINTCTXTImpl c key else modifiedNonceAeadINDDollarRandomImpl

noncomputable def familyImpl {count : Nat} (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (real : Fin count → Bool) : QueryImpl (Spec count) (StateT (State count) ProbComp) :=
  fun query state => do
    let result ← (localImpl (real query.1) c (keys query.1) query.2).run (state query.1)
    pure (result.1, Function.update state query.1 result.2)

abbrev SplitSpec (count : Nat) := ModifiedNonceAeadAdversarySpec + Spec count
abbrev SplitState (count : Nat) := State count × ModifiedNonceAeadHandlerState

/-- Arbitrary local uniform work preserves the complete target challenger state. -/
theorem targetUniform (real : Bool) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (work : ProbComp Result) (state : ModifiedNonceAeadHandlerState) :
    (simulateQ (localImpl real c key)
      (OracleComp.liftComp work ModifiedNonceAeadAdversarySpec)).run state =
        (fun answer => (answer, state)) <$> work := by
  apply QueryImpl.Stateful.simulateQ_liftComp_run_of_query
  intro coin before
  change (simulateQ (localImpl real c key)
    (ModifiedNonceAeadAdversarySpec.query (.inl coin))).run before = _
  cases real <;> change (do let answer ← unifSpec.query coin; pure (answer, before) : ProbComp _) = _
  all_goals simp only [bind_pure_comp]

noncomputable def reductionImpl {count : Nat} (real : Fin count → Bool)
    (c : Pqxdh.Crypto) (keys : Fin count → CtxKey) :
    QueryImpl (SplitSpec count) (StateT (State count) (OracleComp ModifiedNonceAeadAdversarySpec)) :=
  fun query state => match query with
  | .inl target => do
      let answer ← ModifiedNonceAeadAdversarySpec.query target
      pure (answer, state)
  | .inr other => do
      let result ← OracleComp.liftComp
        ((localImpl (real other.1) c (keys other.1) other.2).run (state other.1)) ModifiedNonceAeadAdversarySpec
      pure (result.1, Function.update state other.1 result.2)

noncomputable def splitImpl {count : Nat} (targetReal : Bool) (real : Fin count → Bool)
    (c : Pqxdh.Crypto) (targetKey : CtxKey) (keys : Fin count → CtxKey) :
    QueryImpl (SplitSpec count) (StateT (SplitState count) ProbComp) :=
  fun query state => match query with
  | .inl target => do
      let result ← (localImpl targetReal c targetKey target).run state.2
      pure (result.1, (state.1, result.2))
  | .inr other => do
      let result ← (localImpl (real other.1) c (keys other.1) other.2).run (state.1 other.1)
      pure (result.1, (Function.update state.1 other.1 result.2, state.2))

/-- Ordinary interpretation preserves the complete selected and other-key nonce and seal histories. -/
theorem interpretation {count : Nat} (targetReal : Bool) (real : Fin count → Bool)
    (c : Pqxdh.Crypto) (targetKey : CtxKey) (keys : Fin count → CtxKey) :
    ((localImpl targetReal c targetKey).mapStateTBase
      (reductionImpl real c keys)).flattenStateT =
        splitImpl targetReal real c targetKey keys := by
  funext query state
  cases query with
  | inl target =>
      simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, reductionImpl, splitImpl,
        StateT.run, StateT.mk, bind_pure_comp, simulateQ_map, simulateQ_query, OracleQuery.input_query]
      change (fun x => (x.1.1, x.1.2, x.2)) <$>
        (((fun a => (a, state.1)) <$> ((OracleSpec.query target).cont <$>
          localImpl targetReal c targetKey (OracleSpec.query target).input)).run state.2) = _
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
      rw [StateT.run_map]
      simp only [Functor.map_map, StateT.run]
  | inr other =>
      simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, reductionImpl, splitImpl,
        StateT.run, StateT.mk, bind_pure_comp, simulateQ_map]
      change (fun x => (x.1.1, x.1.2, x.2)) <$>
        (((fun a => (a.1, Function.update state.1 other.1 a.2)) <$>
          simulateQ (localImpl targetReal c targetKey)
            (OracleComp.liftComp ((localImpl (real other.1) c (keys other.1) other.2).run (state.1 other.1)) ModifiedNonceAeadAdversarySpec)).run state.2) = _
      rw [StateT.run_map, targetUniform]
      simp only [Functor.map_map, StateT.run]
      rfl

noncomputable def wrapped {count : Nat} (real : Fin count → Bool)
    (c : Pqxdh.Crypto) (keys : Fin count → CtxKey) {Result : Type}
    (client : OracleComp (SplitSpec count) Result) (state : State count) :
    OracleComp ModifiedNonceAeadAdversarySpec (Result × State count) :=
  (simulateQ (reductionImpl real c keys) client).run state

def reassociate {count : Nat} {Result : Type}
    (result : (Result × State count) × ModifiedNonceAeadHandlerState) : Result × SplitState count :=
  (result.1.1, result.1.2, result.2)

theorem schedule_interpretation {count : Nat} (targetReal : Bool) (real : Fin count → Bool)
    (c : Pqxdh.Crypto) (targetKey : CtxKey) (keys : Fin count → CtxKey) {Result : Type}
    (client : OracleComp (SplitSpec count) Result) (state : SplitState count) :
    (simulateQ (splitImpl targetReal real c targetKey keys) client).run state =
      reassociate <$> (simulateQ (localImpl targetReal c targetKey)
        (wrapped real c keys client state.1)).run state.2 := by
  rw [wrapped, simulateQ_mapStateTBase_run_eq_map_flattenStateT, interpretation]
  simp [reassociate, Functor.map_map]

end BeaconcryptCore.Computational.AdaptiveSealKeyFamily

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeyFamily.targetUniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeyFamily.targetUniform

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeyFamily.interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeyFamily.interpretation

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeyFamily.schedule_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeyFamily.schedule_interpretation
