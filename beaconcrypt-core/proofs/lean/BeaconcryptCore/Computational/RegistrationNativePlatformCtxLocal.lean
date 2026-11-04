-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryWorld
import BeaconcryptCore.Computational.RegistrationNativePlatformServerCompletion
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram
/-! The complete native Local retains auxiliary state, request markers and raw signing receipts while its World and record callbacks route through the explicit shared CTX backend. This is an exact operational lens, before any private receipt erasure. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxLocal
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationWorldAgreement (State)
open RegistrationNativePlatformCtxBackend (Spec)
open RegistrationNativePlatformCtxRunner (M Full interpret privateWork)
open RegistrationNativePlatformCtxCacheFrame (replace)
variable {n : Nat} {I KemSK Reader Response Auxiliary Platform A : Type} {base : OracleSpec I}

def attach (before : State n Auxiliary) (world : PqxdhRecordLiftWorld.State n) : State n Auxiliary :=
  {before with world := (world, before.world.2)}

def realize (before : Full (State n Auxiliary) Platform) : State n Auxiliary × Platform :=
  (attach before.1.1 (replace before.2.1 before.1.1.world.1), before.1.2)

noncomputable def effects (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    StateT (State n Auxiliary) (OracleComp Spec) ((PqxdhRecordLiftInterface.EnvEffects n).Range query) := fun before =>
  (fun result => (result.1, attach before result.2)) <$>
    (RegistrationNativePlatformCtxEffects.program query).run before.world.1

noncomputable def record (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) :
    StateT (State n Auxiliary) (OracleComp Spec) (RawCtxMixedOwner.NativeSpec.Range query) := fun before =>
  (fun result => (result.1, attach before {before.world.1 with primitive := result.2})) <$>
    (RegistrationNativePlatformCtxPrimitives.program setup codec query).run before.world.1.primitive

noncomputable def shared (setup : Setup base KemSK) (codec : Codec Reader Response) :
    QueryImpl MldsaSharedNative.Spec (StateT (State n Auxiliary) (OracleComp Spec))
  | .inl query => effects (.inr (.hash query.2))
  | .inr query => record setup codec query

noncomputable def records (setup : Setup base KemSK) (codec : Codec Reader Response) :
    QueryImpl RegistrationRecordPrimitives.Spec (StateT (State n Auxiliary) (OracleComp Spec)) := fun query before =>
  (fun result => (result.1, {result.2 with recordRequests := before.recordRequests ++ [RegistrationWorldAgreement.recordCall query]})) <$>
    (simulateQ (shared setup codec) (RegistrationRecordPrimitives.callbacks setup.source query)).run before

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (do let value ← work; pure (value, before)) := rfl

theorem effects_source (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain)
    (before : Full (State n Auxiliary) Platform) :
    Prod.map id realize <$> (interpret (privateWork (effects query))).run before =
      (fun result => (result.1, (attach (realize before).1 result.2, before.1.2))) <$>
        (PqxdhRecordLiftWorld.effects query).run (realize before).1.world.1 := by
  rw [RegistrationNativePlatformCtxRunner.private_run]
  have source := RegistrationNativePlatformCtxEffects.query query (before.1.1.world.1, before.2)
  have mapped := congrArg (fun action => (fun result => (result.1, (attach (realize before).1 result.2, before.1.2))) <$> action) source
  simpa only [effects, RegistrationNativePlatformCtxEffects.implementation, StateT.run,
    simulateQ_map, state_map_apply, Functor.map_map, realize, attach,
    RegistrationNativePlatformCtxEffects.realize, replace, Prod.map_def, id_eq] using mapped

theorem record_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (before : Full (State n Auxiliary) Platform) :
    Prod.map id realize <$> (interpret (privateWork (record setup codec query))).run before =
      (fun result => (result.1, (result.2, before.1.2))) <$>
        (RegistrationWorldRecords.record setup codec query).run (realize before).1 := by
  rw [RegistrationNativePlatformCtxRunner.private_run]
  have source := RegistrationNativePlatformCtxPrimitives.query setup codec query (before.1.1.world.1.primitive, before.2)
  have mapped := congrArg (fun action => (fun result => (result.1,
    (attach (realize before).1 {(realize before).1.world.1 with primitive := result.2}, before.1.2))) <$> action) source
  simpa only [record, RegistrationWorldRecords.record, RegistrationNativePlatformCtxPrimitives.implementation,
    StateT.run, simulateQ_map, state_map_apply, Functor.map_map, realize, attach,
    RegistrationNativePlatformCtxPrimitives.realize, replace, Prod.map_def, id_eq] using mapped

theorem shared_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : MldsaSharedNative.Spec.Domain) (before : Full (State n Auxiliary) Platform) :
    Prod.map id realize <$> (interpret (privateWork (shared setup codec query))).run before =
      (fun result => (result.1, (result.2, before.1.2))) <$>
        (RegistrationWorldRecords.shared setup codec query).run (realize before).1 := by
  cases query with
  | inl query =>
    simpa only [shared, RegistrationWorldRecords.shared, StateT.run, Functor.map_map, attach] using
      effects_source (.inr (.hash query.2)) before
  | inr query => exact record_source setup codec query before
private theorem private_pure (value : A) :
    privateWork (pure value : StateT (State n Auxiliary) (OracleComp Spec) A) =
      (pure value : M (State n Auxiliary) Platform A) := rfl

private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let reply ← work before; next reply.1 reply.2) := rfl

private theorem private_bind {B : Type}
    (work : StateT (State n Auxiliary) (OracleComp Spec) A)
    (next : A → StateT (State n Auxiliary) (OracleComp Spec) B) :
    privateWork (work >>= next) =
      (privateWork work >>= fun value => privateWork (next value) : M (State n Auxiliary) Platform B) := by
  funext current previous
  simp only [privateWork, StateT.run, state_bind_apply, state_lift_apply, bind_assoc, pure_bind]

theorem private_program {K : Type} {queries : OracleSpec K}
    (handler : QueryImpl queries (StateT (State n Auxiliary) (OracleComp Spec)))
    (work : OracleComp queries A) :
    privateWork (simulateQ handler work) =
      (simulateQ (fun query => privateWork (handler query)) work : M (State n Auxiliary) Platform A) := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, private_pure]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, private_bind, ih]
noncomputable def native {K : Type} {queries : OracleSpec K}
    (handler : QueryImpl queries (StateT (State n Auxiliary) ProbComp)) :
    QueryImpl queries (StateT (State n Auxiliary × Platform) ProbComp) :=
  (RegistrationNativePlatformMldsaProgram.coins.mapStateTBase handler).flattenStateT

theorem native_program {K : Type} {queries : OracleSpec K}
    (handler : QueryImpl queries (StateT (State n Auxiliary) ProbComp))
    (work : OracleComp queries A) (before : State n Auxiliary × Platform) :
    (simulateQ (native handler) work).run before =
      (fun result => (result.1, (result.2, before.2))) <$> (simulateQ handler work).run before.1 := by
  unfold native
  rw [OracleComp.simulateQ_flattenStateT_run, ← QueryImpl.simulateQ_mapStateTBase_run,
    RegistrationNativePlatformMldsaProgram.lift_coins]
  simp only [StateT.run_lift, bind_pure_comp, Functor.map_map]

theorem shared_program (setup : Setup base KemSK) (codec : Codec Reader Response)
    (work : OracleComp MldsaSharedNative.Spec A) (before : Full (State n Auxiliary) Platform) :
    Prod.map id realize <$> (interpret (privateWork (simulateQ (shared setup codec) work))).run before =
      (fun result => (result.1, (result.2, before.1.2))) <$>
        (simulateQ (RegistrationWorldRecords.shared setup codec) work).run (realize before).1 := by
  rw [private_program, RegistrationNativePlatformCtxRunner.simulate]
  have leaf (query : MldsaSharedNative.Spec.Domain) (current : Full (State n Auxiliary) Platform) :
      Prod.map id realize <$> (interpret (privateWork (shared setup codec query))).run current =
        (native (RegistrationWorldRecords.shared setup codec) query).run (realize current) := by
    have transport := native_program (RegistrationWorldRecords.shared setup codec)
      (MldsaSharedNative.Spec.query query : OracleComp MldsaSharedNative.Spec _) (realize current)
    simp only [simulateQ_spec_query] at transport
    exact (shared_source setup codec query current).trans transport.symm
  have whole := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (fun query => interpret (privateWork (shared setup codec query)))
    (native (RegistrationWorldRecords.shared setup codec)) realize leaf work before
  rw [native_program] at whole
  exact whole
theorem records_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RegistrationRecordPrimitives.Spec.Domain) (before : Full (State n Auxiliary) Platform) :
    Prod.map id realize <$> (interpret (privateWork (records setup codec query))).run before =
      (fun result => (result.1, (result.2, before.1.2))) <$>
        (RegistrationWorldRecords.handler setup codec query).run (realize before).1 := by
  have source := shared_program setup codec (RegistrationRecordPrimitives.callbacks setup.source query) before
  rw [RegistrationNativePlatformCtxRunner.private_run] at source ⊢
  have mapped := congrArg (fun action => (fun result =>
    (result.1, ({result.2.1 with recordRequests := before.1.1.recordRequests ++ [RegistrationWorldAgreement.recordCall query]}, result.2.2))) <$> action) source
  simpa only [records, RegistrationWorldRecords.handler,
    StateT.run, simulateQ_map, state_map_apply, Functor.map_map, realize, attach, replace, Prod.map_def, id_eq] using mapped
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxLocal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxLocal.effects_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxLocal.effects_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxLocal.record_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxLocal.record_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxLocal.shared_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxLocal.shared_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxLocal.private_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxLocal.private_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxLocal.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxLocal.native_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxLocal.shared_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxLocal.shared_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxLocal.records_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxLocal.records_source
