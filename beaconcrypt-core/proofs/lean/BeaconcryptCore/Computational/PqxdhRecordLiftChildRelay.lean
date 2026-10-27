-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut
import BeaconcryptCore.Computational.PqxdhRecordLiftDeferredChild

/-! Factor the literal global masked continuation through one persistent child response. All other random queries and complete source state remain explicit. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftChildRelay
open PqxdhRecordLiftInterface PqxdhRecordLiftProtocol PqxdhFullSecretInputKdf
variable {n : Nat}

/-- The only use of the unavailable parent's child is an unselected real lookup that reads that parent. -/
def Needs (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (state : PqxdhRecordLiftGlobalMask.State n) : Service n → Prop
  | .lookup coordinate => coordinate ≠ state.masked.coordinate ∧ ideal coordinate = false ∧
      PqxdhRecordLiftMaskedReads.Reads coordinate state.masked.coordinate
  | _ => False

/-- Every other uniform request is forwarded literally; it is not replaced by a sampled table. -/
def coinLift : QueryImpl unifSpec (OracleComp PqxdhRecordLiftDeferredChild.Spec) :=
  fun query => PqxdhRecordLiftDeferredChild.Spec.query (.inr query)

def unusedChild : FullOutput := List.Vector.replicate 76 0

open Classical in
/-- The actual masked interpreter requests the persistent child only at its structural use. Its entire native/private continuation remains unchanged. -/
noncomputable def interpreter {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    QueryImpl (ServiceSpec n) (StateT (PqxdhRecordLiftGlobalMask.State n)
      (OracleComp PqxdhRecordLiftDeferredChild.Spec)) := fun query state => do
  let child ← if Needs ideal state query then
      PqxdhRecordLiftDeferredChild.Spec.query (.inl ()) else pure unusedChild
  simulateQ coinLift ((PqxdhRecordLiftGlobalMask.interpreter source ideal child setup codec query).run state)

/-- A source service that does not read the selected parent ignores the supplied child through its complete native/private result. -/
theorem unused_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : Service n) (state : PqxdhRecordLiftGlobalMask.State n)
    (left right : FullOutput) (unused : ¬ Needs ideal state query) :
    (PqxdhRecordLiftGlobalMask.interpreter source ideal left setup codec query).run state =
      (PqxdhRecordLiftGlobalMask.interpreter source ideal right setup codec query).run state := by
  cases query with
  | lookup coordinate =>
      simp only [PqxdhRecordLiftGlobalMask.interpreter, PqxdhRecordLiftGlobalMask.withRecords,
        PqxdhRecordLiftGlobalMask.localInterpreter, PqxdhRecordLiftMaskedOracle.interpreter,
        PqxdhRecordLiftGlobalMask.records, StateT.run, PqxdhRecordLiftMaskedOracle.lookup]
      split_ifs <;> simp_all [Needs]
  | _ => rfl

/-- Forwarded coins preserve the optional child cell and every sampled reply through the entire continuation. -/
theorem coin_source {Result : Type} (child : FullOutput) (work : ProbComp Result)
    (cell : Option FullOutput) :
    (simulateQ (PqxdhRecordLiftDeferredChild.supplied child) (simulateQ coinLift work)).run cell =
      (fun result => (result, cell)) <$> work := by
  induction work using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, coinLift,
        PqxdhRecordLiftDeferredChild.supplied, StateT.run, map_bind]
      change ((unifSpec.query query : ProbComp _) >>= fun reply =>
        (simulateQ (PqxdhRecordLiftDeferredChild.supplied child) (simulateQ coinLift (next reply))).run cell) = _
      exact bind_congr ih

/-- Supplying the fixed child recovers the original full masked source service after erasing only the extra lazy-cell instrumentation. -/
theorem query_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : Service n) (state : PqxdhRecordLiftGlobalMask.State n)
    (child : FullOutput) (cell : Option FullOutput) :
    Prod.fst <$> (simulateQ (PqxdhRecordLiftDeferredChild.supplied child)
      ((interpreter source ideal setup codec query).run state)).run cell =
      (PqxdhRecordLiftGlobalMask.interpreter source ideal child setup codec query).run state := by
  by_cases used : Needs ideal state query
  · simp only [interpreter, StateT.run, used, ite_true, simulateQ_bind, simulateQ_spec_query,
      PqxdhRecordLiftDeferredChild.supplied, pure_bind]
    change Prod.fst <$> (simulateQ (PqxdhRecordLiftDeferredChild.supplied child)
      (simulateQ coinLift ((PqxdhRecordLiftGlobalMask.interpreter source ideal child setup codec query).run state))).run (some child) = _
    simp only [coin_source, Functor.map_map]
    exact id_map _
  · simp only [interpreter, StateT.run, used, ite_false, pure_bind]
    change Prod.fst <$> (simulateQ (PqxdhRecordLiftDeferredChild.supplied child)
      (simulateQ coinLift ((PqxdhRecordLiftGlobalMask.interpreter source ideal unusedChild setup codec query).run state))).run cell = _
    simp only [coin_source, Functor.map_map]
    exact (id_map _).trans (unused_source source ideal setup codec query state unusedChild child used)

/-- Erasing only the additional cell recovers the complete adaptive source run, including its entire original private state. -/
theorem schedule_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (client : OracleComp (ServiceSpec n) Result) (state : PqxdhRecordLiftGlobalMask.State n)
    (child : FullOutput) (cell : Option FullOutput) :
    Prod.fst <$> (simulateQ (PqxdhRecordLiftDeferredChild.supplied child)
      ((simulateQ (interpreter source ideal setup codec) client).run state)).run cell =
      (simulateQ (PqxdhRecordLiftGlobalMask.interpreter source ideal child setup codec) client).run state := by
  induction client using OracleComp.inductionOn generalizing state cell with
  | pure result => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      simp_rw [ih]
      rw [← query_source source ideal setup codec query state child cell, bind_map_left]

/-- A persistent child drawn at its first structural read has the same evaluated full source continuation as one independently drawn before the run. This statement retains every original private field and quantifies over all subsequent observations. -/
theorem deferred_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (draw : ProbComp FullOutput) (client : OracleComp (ServiceSpec n) Result)
    (state : PqxdhRecordLiftGlobalMask.State n) :
    LazyOracleDiscard.LawEq
      (Prod.fst <$> (simulateQ (PqxdhRecordLiftDeferredChild.lazyImpl draw)
        ((simulateQ (interpreter source ideal setup codec) client).run state)).run none)
      (draw >>= fun child =>
        (simulateQ (PqxdhRecordLiftGlobalMask.interpreter source ideal child setup codec) client).run state) := by
  have same := LazyOracleDiscard.LawEq.map Prod.fst
    (PqxdhRecordLiftDeferredChild.initial_law draw
      ((simulateQ (interpreter source ideal setup codec) client).run state))
  simpa only [map_bind, schedule_source] using same

end BeaconcryptCore.Computational.PqxdhRecordLiftChildRelay

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChildRelay.unused_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChildRelay.unused_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChildRelay.coin_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChildRelay.coin_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChildRelay.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChildRelay.query_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChildRelay.schedule_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChildRelay.schedule_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChildRelay.deferred_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChildRelay.deferred_source
