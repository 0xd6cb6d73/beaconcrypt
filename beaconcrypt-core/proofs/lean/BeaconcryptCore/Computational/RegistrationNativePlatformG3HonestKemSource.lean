-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedMarginal
import BeaconcryptCore.Computational.RegistrationNativeOpenRetainedReal
/-! The honest on-demand KEM pool and public encapsulation provider close the same open-key tree as the literal indexed native KEM interface. The proof is a state bijection at each query and retains complete pool histories and the lazy byte table, including unreached or failed routes. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3HonestKemSource
open PqxdhKemIndCca
variable {I KemSK Value : Type} {base : OracleSpec I}
open RegistrationNativeOpenKeyKemGame (Table)
open PqxdhServerAuthExperiment (Setup)

def embed (before : Table × PqxdhLiveKemBirth.Pool KemSK) : (PqxdhLiveKemBirth.Pool KemSK × Unit) × Table :=
  ((before.2, ()), before.1)

noncomputable def honest (setup : Setup base KemSK) : QueryImpl (RegistrationNativeOpenKey.Spec KemSK)
    (StateT ((PqxdhLiveKemBirth.Pool KemSK × Unit) × Table) ProbComp) :=
  (PqxdhRegistrationJointKemSecondEntry.lazyImpl.mapStateTBase
    (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins (RegistrationNativeOpenRetainedReal.provider setup))).flattenStateT

noncomputable def native (setup : Setup base KemSK) : QueryImpl (RegistrationNativeOpenKey.Spec KemSK)
    (StateT (Table × PqxdhLiveKemBirth.Pool KemSK) ProbComp) :=
  RegistrationNativeKemInterface.source setup.baseImpl setup.kem RegistrationNativeOpenKey.Ambient
    (RegistrationNativeOpenKeyKemGame.other setup.baseImpl setup.kem) ∘ₛ RegistrationNativeOpenKey.native

private theorem coin_program (work : ProbComp Value) (table : Table) :
    (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl
      (simulateQ RegistrationNativeKeyCompiler.coins work)).run table =
      (fun value => (value, table)) <$> work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : PqxdhRegistrationJointKemSecondEntry.lazyImpl ∘ₛ RegistrationNativeKeyCompiler.coins =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT Table ProbComp) := by
    funext query
    rfl
  rw [same, simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  change (work >>= fun value => pure (value, table)) = _
  exact bind_pure_comp _ _

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- Every literal on-demand reply and complete post-pool agrees under the exact state reassociation. -/
theorem query_source (setup : Setup base KemSK) (query : (RegistrationNativeOpenKey.Spec KemSK).Domain)
    (before : Table × PqxdhLiveKemBirth.Pool KemSK) :
    Prod.map id embed <$> (native setup query).run before = (honest setup query).run (embed before) := by
  rcases before with ⟨table, pool⟩
  simp only [native, honest, QueryImpl.apply_compose, QueryImpl.flattenStateT_mapStateTBase_apply_run, embed]
  cases query with
  | inl query =>
      simp only [RegistrationNativeOpenKey.native, simulateQ_spec_query, RegistrationNativeKemInterface.source,
        RegistrationNativeOpenKeyKemGame.other, RegistrationNativeOpenCompile.close,
        StateT.run, StateT.lift, bind_pure_comp, simulateQ_map, simulateQ_spec_query, state_map_apply, Functor.map_map, Prod.map_def, id_eq, embed]
      rfl
  | inr query =>
      change _ = (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl
          (simulateQ RegistrationNativeKeyCompiler.coins
            ((RegistrationNativeOpenRetainedReal.provider setup query).run (pool, ())))).run table
      rw [coin_program]
      rcases query with (query | key) | query | key
      all_goals try cases query
      all_goals simp only [RegistrationNativeOpenKey.native, simulateQ_spec_query, RegistrationNativeKemInterface.source,
        RegistrationNativeOpenKeyKemGame.other, RegistrationNativeOpenRetainedReal.provider,
        StateT.run, StateT.lift, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq, embed]
      all_goals rfl

/-- The literal source/native state equation holds for any adaptive open-key tree and every actual KEM outcome. -/
theorem program_source (setup : Setup base KemSK) (work : OracleComp (RegistrationNativeOpenKey.Spec KemSK) Value)
    (before : Table × PqxdhLiveKemBirth.Pool KemSK) :
    Prod.map id embed <$> (simulateQ (native setup) work).run before =
      (simulateQ (honest setup) work).run (embed before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ embed (query_source setup) work before

/-- Erasing only compiler poststate gives the same literal on-demand client result. -/
theorem values_source (setup : Setup base KemSK) (work : OracleComp (RegistrationNativeOpenKey.Spec KemSK) Value)
    (before : Table × PqxdhLiveKemBirth.Pool KemSK) :
    (simulateQ (native setup) work).run' before = (simulateQ (honest setup) work).run' (embed before) := by
  have actual := congrArg (Functor.map Prod.fst) (program_source setup work before)
  simpa only [StateT.run'_eq, Functor.map_map, Prod.map_def, id_eq] using actual
end BeaconcryptCore.Computational.RegistrationNativePlatformG3HonestKemSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3HonestKemSource.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3HonestKemSource.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3HonestKemSource.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3HonestKemSource.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3HonestKemSource.values_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3HonestKemSource.values_source
