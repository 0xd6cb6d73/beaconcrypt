-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope
import BeaconcryptCore.Computational.PqxdhRecordLiftChildRelay

/-! Factor the actual directional seed-mask continuation of `PqxdhRecordLiftGlobalSeedCut` through one persistent full76 initial child. Only an unselected real lookup of the exact initial coordinate that reads the unavailable seed half requests the child; every other uniform query, the complete original source client and every private field stay literal. Adapted from Codex WIP `a274839204ccf2a7825ff8f42b107c41ba7d7541cacb76927c9f7ed23d3bb908` (the stub `PqxdhRecordLiftSeedRelay`), restarted: the interpreter now carries the seed-mask filling input, and the relay theorems follow the published `PqxdhRecordLiftChildRelay`. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftSeedRelay
open PqxdhRecordLiftInterface PqxdhRecordLiftProtocol PqxdhFullSecretInputKdf
variable {n : Nat}

/-- Only an unselected real initial-coordinate lookup reads the unavailable selected seed half. -/
def Needs (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (state : PqxdhRecordLiftGlobalSeedCut.Mask n) : Service n → Prop
  | .lookup coordinate => ideal coordinate = false ∧ PqxdhRecordLiftGlobalSeedCut.Reads state coordinate
  | _ => False

open Classical in
/-- The actual seed-mask interpreter asks for the persistent full76 child only at its exact structural use. Its complete native and private continuation remains unchanged, and every other uniform query is forwarded literally. -/
noncomputable def interpreter {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool) (filling : PqxdhSecretInputKdf.RootOutput)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    QueryImpl (ServiceSpec n) (StateT (PqxdhRecordLiftGlobalSeedCut.Mask n)
      (OracleComp PqxdhRecordLiftDeferredChild.Spec)) := fun query state => do
  let child ← if Needs ideal state query then
      PqxdhRecordLiftDeferredChild.Spec.query (.inl ()) else pure PqxdhRecordLiftChildRelay.unusedChild
  simulateQ PqxdhRecordLiftChildRelay.coinLift
    ((PqxdhRecordLiftGlobalSeedCut.interpreter source ideal filling child setup codec query).run state)

/-- A service that does not read the selected seed half ignores the supplied child through its complete native and private result. -/
theorem unused_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool) (filling : PqxdhSecretInputKdf.RootOutput)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : Service n) (state : PqxdhRecordLiftGlobalSeedCut.Mask n)
    (left right : FullOutput) (unused : ¬ Needs ideal state query) :
    (PqxdhRecordLiftGlobalSeedCut.interpreter source ideal filling left setup codec query).run state =
      (PqxdhRecordLiftGlobalSeedCut.interpreter source ideal filling right setup codec query).run state := by
  cases query with
  | lookup coordinate =>
      simp only [PqxdhRecordLiftGlobalSeedCut.interpreter, StateT.run, PqxdhRecordLiftGlobalSeedCut.lookup]
      split_ifs <;> simp_all [Needs]
  | _ => rfl

/-- Supplying the fixed child recovers the original seed-mask service after erasing only the extra lazy-cell instrumentation. -/
theorem query_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool) (filling : PqxdhSecretInputKdf.RootOutput)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : Service n) (state : PqxdhRecordLiftGlobalSeedCut.Mask n)
    (child : FullOutput) (cell : Option FullOutput) :
    Prod.fst <$> (simulateQ (PqxdhRecordLiftDeferredChild.supplied child)
      ((interpreter source ideal filling setup codec query).run state)).run cell =
      (PqxdhRecordLiftGlobalSeedCut.interpreter source ideal filling child setup codec query).run state := by
  by_cases used : Needs ideal state query
  · simp only [interpreter, StateT.run, used, ite_true, simulateQ_bind, simulateQ_spec_query,
      PqxdhRecordLiftDeferredChild.supplied, pure_bind]
    change Prod.fst <$> (simulateQ (PqxdhRecordLiftDeferredChild.supplied child)
      (simulateQ PqxdhRecordLiftChildRelay.coinLift
        ((PqxdhRecordLiftGlobalSeedCut.interpreter source ideal filling child setup codec query).run state))).run
          (some child) = _
    simp only [PqxdhRecordLiftChildRelay.coin_source, Functor.map_map]
    exact id_map _
  · simp only [interpreter, StateT.run, used, ite_false, pure_bind]
    change Prod.fst <$> (simulateQ (PqxdhRecordLiftDeferredChild.supplied child)
      (simulateQ PqxdhRecordLiftChildRelay.coinLift
        ((PqxdhRecordLiftGlobalSeedCut.interpreter source ideal filling PqxdhRecordLiftChildRelay.unusedChild
          setup codec query).run state))).run cell = _
    simp only [PqxdhRecordLiftChildRelay.coin_source, Functor.map_map]
    exact (id_map _).trans
      (unused_source source ideal filling setup codec query state PqxdhRecordLiftChildRelay.unusedChild child used)

/-- Erasing only the additional cell recovers the complete adaptive seed-mask run, including its entire original private state. -/
theorem schedule_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool) (filling : PqxdhSecretInputKdf.RootOutput)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (client : OracleComp (ServiceSpec n) Result) (state : PqxdhRecordLiftGlobalSeedCut.Mask n)
    (child : FullOutput) (cell : Option FullOutput) :
    Prod.fst <$> (simulateQ (PqxdhRecordLiftDeferredChild.supplied child)
      ((simulateQ (interpreter source ideal filling setup codec) client).run state)).run cell =
      (simulateQ (PqxdhRecordLiftGlobalSeedCut.interpreter source ideal filling child setup codec) client).run state := by
  induction client using OracleComp.inductionOn generalizing state cell with
  | pure result => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      simp_rw [ih]
      rw [← query_source source ideal filling setup codec query state child cell, bind_map_left]

/-- A persistent initial child drawn at its first structural read has the same evaluated complete seed-mask continuation as one drawn independently before the run, under every subsequent observation. -/
theorem deferred_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool) (filling : PqxdhSecretInputKdf.RootOutput)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (draw : ProbComp FullOutput) (client : OracleComp (ServiceSpec n) Result)
    (state : PqxdhRecordLiftGlobalSeedCut.Mask n) :
    LazyOracleDiscard.LawEq
      (Prod.fst <$> (simulateQ (PqxdhRecordLiftDeferredChild.lazyImpl draw)
        ((simulateQ (interpreter source ideal filling setup codec) client).run state)).run none)
      (draw >>= fun child =>
        (simulateQ (PqxdhRecordLiftGlobalSeedCut.interpreter source ideal filling child setup codec) client).run
          state) := by
  have same := LazyOracleDiscard.LawEq.map Prod.fst
    (PqxdhRecordLiftDeferredChild.initial_law draw
      ((simulateQ (interpreter source ideal filling setup codec) client).run state))
  simpa only [map_bind, schedule_source] using same

end BeaconcryptCore.Computational.PqxdhRecordLiftSeedRelay

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedRelay.unused_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedRelay.unused_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedRelay.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedRelay.query_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedRelay.schedule_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedRelay.schedule_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedRelay.deferred_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedRelay.deferred_source
