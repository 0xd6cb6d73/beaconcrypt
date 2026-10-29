-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemGame
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyClosure

/-! The real external indexed pool and lazy uniform108 table are the same service before and after native KEM sum reassociation. This operational equality keeps both complete private states; it does not replace a randomized candidate provider by real encapsulation. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemSource
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeOpenKeyKemGame (Table other normal)
open RegistrationNativeOpenKey (Spec Ambient)
variable {ι KemSK Value : Type} {base : OracleSpec ι}

def embed (before : Table × PqxdhLiveKemBirth.Pool KemSK) :
    (PqxdhLiveKemBirth.Pool KemSK × Unit) × Table := ((before.2, ()), before.1)

noncomputable def implementation (setup : Setup base KemSK) :
    QueryImpl (Spec KemSK) (StateT (Table × PqxdhLiveKemBirth.Pool KemSK) ProbComp) :=
  RegistrationNativeKemInterface.source setup.baseImpl setup.kem Ambient (other setup.baseImpl setup.kem) ∘ₛ
    RegistrationNativeOpenKey.native

noncomputable def reference (setup : Setup base KemSK) :
    QueryImpl (Spec KemSK) (StateT ((PqxdhLiveKemBirth.Pool KemSK × Unit) × Table) ProbComp) :=
  (PqxdhRegistrationJointKemSecondEntry.lazyImpl.mapStateTBase
    (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins
      (RegistrationNativeOpenRetainedReal.provider setup))).flattenStateT

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

/-- Each real callback retains the exact indexed pool history and uniform108 table under the explicit state reassociation. -/
theorem query_source (setup : Setup base KemSK) (query : (Spec KemSK).Domain)
    (before : Table × PqxdhLiveKemBirth.Pool KemSK) :
    Prod.map id embed <$> (implementation setup query).run before =
      (reference setup query).run (embed before) := by
  rcases before with ⟨table, pool⟩
  simp only [implementation, QueryImpl.apply_compose, reference,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, embed]
  cases query with
  | inl query =>
      simp only [RegistrationNativeOpenKey.native, simulateQ_spec_query, RegistrationNativeKemInterface.source,
        other, RegistrationNativeOpenCompile.close, StateT.run_lift, bind_pure_comp,
        simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map, Prod.map_def, id_eq]
      simp only [StateT.run, Functor.map_map, embed]
      rfl
  | inr query =>
      change _ = (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl
          (simulateQ RegistrationNativeKeyCompiler.coins
            ((RegistrationNativeOpenRetainedReal.provider setup query).run (pool, ())))).run table
      rw [coin_program]
      rcases query with (query | key) | query | key
      all_goals simp only [RegistrationNativeOpenKey.native, simulateQ_spec_query, RegistrationNativeKemInterface.source,
        other, RegistrationNativeOpenRetainedReal.provider, StateT.lift, bind_pure_comp,
        StateT.run, Functor.map_map, Prod.map_def, id_eq, embed]
      all_goals rfl

/-- The whole adaptive real open client preserves every private table/pool coordinate, including unsuccessful operations. -/
theorem program_source (setup : Setup base KemSK) (work : OracleComp (Spec KemSK) Value)
    (before : Table × PqxdhLiveKemBirth.Pool KemSK) :
    Prod.map id embed <$> (simulateQ (implementation setup) work).run before =
      (simulateQ (reference setup) work).run (embed before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ embed (query_source setup) work before

/-- Closing the same real provider after key compilation and interpreting the actual lazy uniform table gives exactly the normal native KEM game. -/
theorem normal_source (setup : Setup base KemSK) (work : OracleComp (Spec KemSK) Bool) :
    normal setup.baseImpl setup.kem (simulateQ RegistrationNativeOpenKey.native work) =
      (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl
        ((simulateQ (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins
          (RegistrationNativeOpenRetainedReal.provider setup)) work).run'
          (PqxdhLiveKemBirth.empty, ()))).run' ∅ := by
  have whole := congrArg (fun distribution => Prod.fst <$> distribution)
    (program_source setup work (∅, PqxdhLiveKemBirth.empty))
  simp only [Functor.map_map, Prod.map_def, id_eq] at whole
  unfold normal
  rw [StateT.run'_eq, ← QueryImpl.simulateQ_compose]
  change Prod.fst <$> (simulateQ (implementation setup) work).run (∅, PqxdhLiveKemBirth.empty) = _
  rw [whole]
  simp only [reference, embed, OracleComp.simulateQ_flattenStateT_run,
    QueryImpl.simulateQ_mapStateTBase_run, StateT.run'_eq, simulateQ_map, StateT.run_map,
    bind_pure_comp, Functor.map_map]

end BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemSource.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemSource.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemSource.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemSource.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemSource.normal_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemSource.normal_source
