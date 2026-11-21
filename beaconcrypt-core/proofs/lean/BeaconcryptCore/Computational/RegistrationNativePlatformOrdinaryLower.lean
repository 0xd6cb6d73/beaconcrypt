-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldReceive
/-! A deterministic public capacity service, including an arbitrary stateful retry tape, lowers the actual adaptive World into the established World oracle without changing private counters. The gate runs before every original continuation and keeps the full advanced private state and external state on rejection. This normal-result World theorem does not erase source Rust failures or establish a whole registration/private-material compiler; randomized external allocation needs its own uncounted public base oracle. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLower
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (WorldSpec)
open RegistrationNativePlatformOrdinaryGate (gate)
variable {n : Nat} {I KemSK Reader Response Platform E A : Type} {base : OracleSpec I}
variable {m : Type → Type} [Monad m]

def terminal (native : QueryImpl (WorldSpec n) m) (reserve : Nat → m (core.result.Result Unit E)) :
    QueryImpl (WorldSpec n) m
  | .inr (.inr (.inl (.inl (plaintext, keyId)))) => do
      let result ← native (.inr (.inr (.inl (.inl (plaintext, keyId)))))
      gate reserve (fun output : RawCtxSourceSend.Encrypted => output.ciphertext.length) result
  | .inr (.inr (.inr (owner, .inl plaintext))) => do
      let result ← native (.inr (.inr (.inr (owner, .inl plaintext))))
      gate reserve (fun output : RawCtxSourceSend.Encrypted => output.ciphertext.length) result
  | query => native query

def deterministic (reserve : Nat → Platform → core.result.Result Unit E × Platform) (size : Nat) :
    StateT Platform m (core.result.Result Unit E) := fun before => pure (reserve size before)

def query (reserve : Nat → Platform → core.result.Result Unit E × Platform) :
    QueryImpl (WorldSpec n) (StateT Platform (OracleComp (WorldSpec n))) :=
  terminal (fun request => StateT.lift ((WorldSpec n).query request : OracleComp (WorldSpec n) _))
    (deterministic reserve)


private theorem gate_lift {S V : Type} [LawfulMonad m]
    (reserve : Nat → m (core.result.Result Unit E)) (size : V → Nat) (output : Option V) :
    gate (fun amount => StateT.lift (reserve amount) : Nat → StateT S m (core.result.Result Unit E)) size output =
      StateT.lift (gate reserve size output) := by
  funext before
  change (gate (fun amount => StateT.lift (reserve amount) : Nat → StateT S m (core.result.Result Unit E)) size output).run before =
    (StateT.lift (gate reserve size output) : StateT S m (Option V)).run before
  cases output with
  | none => simp only [gate, StateT.run_pure, StateT.run_lift, pure_bind]
  | some value =>
      simp only [gate, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
      apply bind_congr
      intro result
      cases result <;> simp only [StateT.run_pure, pure_bind]

private theorem outer_pure {V : Type} (value : V) :
    (StateT.lift (pure value : ProbComp V) : StateT Platform ProbComp V) = pure value := by
  funext previous
  change (pure value >>= fun result => pure (result, previous) : ProbComp _) = pure (value, previous)
  exact pure_bind _ _

omit [Monad m] in
theorem actual_query (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (request : (WorldSpec n).Domain) :
    RegistrationNativePlatformOrdinaryWorld.guarded setup codec reserve route request =
      terminal (fun request => RegistrationNativePlatformOrdinaryWorld.liftWorld
        (CborRecordWorldSimulation.guarded setup (CborRawCanonicalBuild.canonical codec) route request))
        (fun size => StateT.lift (reserve size)) request := by
  rcases request with created | (effect | ((send | raw) | ⟨owner, send | raw⟩))
  · rfl
  · rfl
  · rcases send with ⟨plaintext, keyId⟩
    convert RegistrationNativePlatformOrdinaryWorldGuarded.server setup codec reserve route keyId plaintext using 1
    simp only [terminal, RegistrationNativePlatformOrdinaryWorldRouting.after, gate_lift]
    rfl
  · funext before
    cases refused : CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inl (.inr raw))))
        (CborRecordWorldCursor.worldShell before) with
    | some reply =>
      simp only [RegistrationNativePlatformOrdinaryWorld.guarded, CborRecordWorldSimulation.guarded,
        terminal, RegistrationNativePlatformOrdinaryWorld.liftWorld, StateT.run, refused, outer_pure]
    | none =>
      have same := congrFun (RegistrationNativePlatformOrdinaryWorldReceive.server setup codec reserve route raw) before
      simpa only [RegistrationNativePlatformOrdinaryWorld.guarded, CborRecordWorldSimulation.guarded,
        terminal, RegistrationNativePlatformOrdinaryWorld.liftWorld, StateT.run, refused,
        RegistrationNativePlatformOrdinaryWorld.handler, PqxdhRecordLiftWorld.handler] using same
  · convert RegistrationNativePlatformOrdinaryWorldGuarded.beacon setup codec reserve route owner send using 1
    simp only [terminal, RegistrationNativePlatformOrdinaryWorldRouting.after, gate_lift]
    rfl
  · funext before
    cases refused : CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inr (owner, .inr raw))))
        (CborRecordWorldCursor.worldShell before) with
    | some reply =>
      simp only [RegistrationNativePlatformOrdinaryWorld.guarded, CborRecordWorldSimulation.guarded,
        terminal, RegistrationNativePlatformOrdinaryWorld.liftWorld, StateT.run, refused, outer_pure]
    | none =>
      have same := congrFun (RegistrationNativePlatformOrdinaryWorldReceive.beacon setup codec reserve owner raw) before
      simpa only [RegistrationNativePlatformOrdinaryWorld.guarded, CborRecordWorldSimulation.guarded,
        terminal, RegistrationNativePlatformOrdinaryWorld.liftWorld, StateT.run, refused,
        RegistrationNativePlatformOrdinaryWorld.handler, PqxdhRecordLiftWorld.handler] using same

private theorem lift_apply {T V : Type} (work : m V) (before : T) :
    (StateT.lift work : StateT T m V) before = (work >>= fun value => pure (value, before)) := rfl
private theorem bind_apply {T V W : Type} (work : StateT T m V) (next : V → StateT T m W) (before : T) :
    (work >>= next) before = (work before >>= fun result => next result.1 result.2) := rfl
private theorem pure_apply {T V : Type} (value : V) (before : T) :
    (pure value : StateT T m V) before = pure (value, before) := rfl

omit [Monad m] in
private theorem query_commutes (native : QueryImpl (WorldSpec n) (StateT (PqxdhRecordLiftWorld.State n) ProbComp))
    (reserve : Nat → Platform → core.result.Result Unit E × Platform)
    (request : (WorldSpec n).Domain) (previous : Platform) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id Prod.swap <$>
      (((native.mapStateTBase (query reserve)).flattenStateT request).run (previous, before)) =
        ((terminal (fun request => RegistrationNativePlatformOrdinaryWorld.liftWorld (native request))
          (fun amount => StateT.lift (deterministic reserve amount))).flattenStateT request).run (before, previous) := by
  rcases request with created | (effect | ((send | raw) | ⟨owner, send | raw⟩))
  all_goals simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, query, terminal,
    StateT.run, StateT.mk, lift_apply, bind_apply, pure_apply,
    simulateQ_bind, simulateQ_pure, simulateQ_spec_query,
    RegistrationNativePlatformOrdinaryWorld.liftWorld,
    bind_assoc, pure_bind, map_bind, map_pure, Functor.map_map, Prod.map_def, id_eq]
  all_goals try rfl
  all_goals apply bind_congr
  all_goals rintro ⟨reply, after⟩
  all_goals cases reply with
  | none => rfl
  | some value =>
      simp only [gate, bind_apply, lift_apply, pure_apply,
        deterministic, pure_bind]
      cases reserved : reserve value.ciphertext.length previous with
      | mk outcome next => cases outcome <;> simp only [pure_apply, simulateQ_pure, map_pure] <;> rfl


omit [Monad m] in
/-- Public retry-tape allocation lowers below every adaptive continuation while retaining the complete private World and external state. -/
theorem program (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → Platform → core.result.Result Unit E × Platform)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) A)
    (previous : Platform) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id Prod.swap <$>
      (simulateQ ((CborRecordWorldSimulation.guarded setup (CborRawCanonicalBuild.canonical codec) route).mapStateTBase
        (query reserve)).flattenStateT work).run (previous, before) =
      (simulateQ (RegistrationNativePlatformOrdinaryWorld.guarded setup codec (deterministic reserve) route).flattenStateT work).run (before, previous) := by
  apply map_run_simulateQ_eq_of_query_map_eq
  intro request state
  rcases state with ⟨prior, current⟩
  have callbacks : terminal (n := n)
      (fun request => RegistrationNativePlatformOrdinaryWorld.liftWorld
        (CborRecordWorldSimulation.guarded setup (CborRawCanonicalBuild.canonical codec) route request))
      (fun amount => StateT.lift (deterministic reserve amount)) =
        RegistrationNativePlatformOrdinaryWorld.guarded setup codec (deterministic reserve) route := by
    funext request
    exact (actual_query setup codec (deterministic reserve) route request).symm
  rw [← callbacks]
  exact query_commutes _ reserve request prior current


omit [Monad m] in
/-- The source execution is the same lower client with only state-pair reassociation, including every failed publication and its advanced private state. -/
theorem joint (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → Platform → core.result.Result Unit E × Platform)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) A)
    (previous : Platform) (before : PqxdhRecordLiftWorld.State n) :
    (fun result : (A × Platform) × PqxdhRecordLiftWorld.State n => ((result.1.1, result.2), result.1.2)) <$>
      (simulateQ (CborRecordWorldSimulation.guarded setup (CborRawCanonicalBuild.canonical codec) route)
        ((simulateQ (query reserve) work).run previous)).run before =
      ((simulateQ (RegistrationNativePlatformOrdinaryWorld.guarded setup codec (deterministic reserve) route) work).run before).run previous := by
  have same := congrArg (Functor.map (fun result : A × (PqxdhRecordLiftWorld.State n × Platform) =>
    ((result.1, result.2.1), result.2.2))) (program setup codec reserve route work previous before)
  rw [simulateQ_flattenStateT_run
    (RegistrationNativePlatformOrdinaryWorld.guarded setup codec (deterministic reserve) route) work before previous] at same
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  simpa only [map_bind, map_pure, bind_pure_comp, Functor.map_map, Prod.map_def, Function.comp_def, id_eq, Prod.swap, Prod.mk.eta, id_map', StateT.run] using same


private def publish {V : Type} (reserve : Nat → Platform → core.result.Result Unit E × Platform)
    (size : V → Nat) (output : Option V) (previous : Platform) : Option V × Platform :=
  match output with
  | none => (none, previous)
  | some value =>
      let result := reserve (size value) previous
      match result.1 with
      | .Err _ => (none, result.2)
      | .Ok _ => (some value, result.2)

omit [Monad m] in
private theorem gate_deterministic {V : Type}
    (reserve : Nat → Platform → core.result.Result Unit E × Platform) (size : V → Nat)
    (output : Option V) (previous : Platform) :
    (gate (deterministic (m := OracleComp (WorldSpec n)) reserve) size output).run previous =
      pure (publish reserve size output previous) := by
  cases output with
  | none => rfl
  | some value =>
      simp only [gate, StateT.run_bind]
      rw [show (deterministic (m := OracleComp (WorldSpec n)) reserve (size value)).run previous =
        pure (reserve (size value) previous) from rfl, pure_bind]
      cases reached : reserve (size value) previous with
      | mk result next => cases result <;> simp only [publish, reached] <;> rfl

private def continuation (reserve : Nat → Platform → core.result.Result Unit E × Platform)
    (request : (WorldSpec n).Domain) (reply : (WorldSpec n).Range request) (previous : Platform) :
    (WorldSpec n).Range request × Platform :=
  match request with
  | .inr (.inr (.inl (.inl _))) => publish reserve (fun output : RawCtxSourceSend.Encrypted => output.ciphertext.length) reply previous
  | .inr (.inr (.inr (_, .inl _))) => publish reserve (fun output : RawCtxSourceSend.Encrypted => output.ciphertext.length) reply previous
  | _ => (reply, previous)

omit [Monad m] in
private theorem query_exact (reserve : Nat → Platform → core.result.Result Unit E × Platform)
    (request : (WorldSpec n).Domain) (previous : Platform) :
    (query reserve request).run previous =
      (fun reply => continuation reserve request reply previous) <$>
        ((WorldSpec n).query request : OracleComp (WorldSpec n) _) := by
  rcases request with created | (effect | ((send | raw) | ⟨owner, send | raw⟩))
  all_goals simp only [query, terminal, StateT.run_bind, StateT.run_lift, bind_map_left,
    continuation, bind_pure_comp]
  all_goals rw [← bind_pure_comp]
  all_goals apply bind_congr
  all_goals intro output
  all_goals exact gate_deterministic (n := n) reserve _ output previous

omit [Monad m] in
/-- The public allocator adds no private World query and forwards each reached original query exactly once. -/
theorem query_bound (reserve : Nat → Platform → core.result.Result Unit E × Platform)
    (predicate : (WorldSpec n).Domain → Prop) [DecidablePred predicate]
    (request : (WorldSpec n).Domain) (previous : Platform) :
    ((query reserve request).run previous).IsQueryBoundP predicate (if predicate request then 1 else 0) := by
  rw [query_exact, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  intro selected
  rw [ite_eq_left selected]
  decide

omit [Monad m] in
/-- Every original predicated source budget is retained through arbitrary adaptive public retry-tape allocation. -/
theorem program_bound (reserve : Nat → Platform → core.result.Result Unit E × Platform)
    (predicate : (WorldSpec n).Domain → Prop) [DecidablePred predicate]
    (work : OracleComp (WorldSpec n) A) (cap : Nat) (bounded : work.IsQueryBoundP predicate cap)
    (previous : Platform) :
    ((simulateQ (query reserve) work).run previous).IsQueryBoundP predicate cap := by
  exact bounded.simulateQ_run_of_step
    (fun request selected state => by simpa only [ite_eq_left selected] using query_bound reserve predicate request state)
    (fun request unselected state => by simpa only [ite_eq_right unselected] using query_bound reserve predicate request state)
    previous

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLower

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLower.actual_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLower.actual_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLower.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLower.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLower.joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLower.joint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLower.query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLower.query_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLower.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLower.program_bound
