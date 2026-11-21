-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLower
/-! The lower source interface combines private World operations with capacity/site-only public allocation requests. Every registration and ordinary-frame request uses one shared external state. The target oracle has a separate external uniform branch, so arbitrary allocator randomness does not alter private native counters. Trusted serialization, private material compilation and individual source primitive contracts remain outside this interface theorem. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRandomizedLower
open PqxdhRecordLiftInterface (WorldSpec)
variable {n : Nat} {Platform E S A : Type}

/-- The public coin service has its own oracle branch and never enters native World counters. -/
abbrev Spec (n : Nat) := WorldSpec n + unifSpec

def world : QueryImpl (WorldSpec n) (OracleComp (Spec n)) :=
  fun request => (Spec n).query (.inl request)
def publicCoin : QueryImpl unifSpec (OracleComp (Spec n)) :=
  fun request => (Spec n).query (.inr request)

def implementation (native : QueryImpl (WorldSpec n) (StateT S ProbComp)) :
    QueryImpl (Spec n) (StateT S ProbComp)
  | .inl request => native request
  | .inr coin => StateT.lift (unifSpec.query coin : ProbComp _)

def allocation (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (size : Nat) : StateT Platform (OracleComp (Spec n)) (core.result.Result Unit E) :=
  fun previous => simulateQ publicCoin ((reserve size).run previous)

def query (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) :
    QueryImpl (WorldSpec n) (StateT Platform (OracleComp (Spec n))) :=
  RegistrationNativePlatformOrdinaryLower.terminal (fun request => StateT.lift (world request))
    (allocation reserve)

/-- Arbitrary external random execution preserves the complete private state exactly. -/
theorem external_program (native : QueryImpl (WorldSpec n) (StateT S ProbComp)) (work : ProbComp A) :
    simulateQ (implementation native) (simulateQ publicCoin work) = StateT.lift work := by
  rw [← QueryImpl.simulateQ_compose]
  have leaves : implementation native ∘ₛ publicCoin =
      (fun coin => StateT.lift (unifSpec.query coin : ProbComp _)) := by
    funext coin
    simp only [QueryImpl.compose, publicCoin, simulateQ_spec_query, implementation]
  rw [leaves]
  induction work using OracleComp.inductionOn with
  | pure value =>
      funext before
      change pure (value, before) = (pure value >>= fun result => pure (result, before) : ProbComp _)
      exact (pure_bind _ _).symm
  | query_bind coin next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, ih]
      funext before
      change ((StateT.lift (unifSpec.query coin : ProbComp _) >>= fun reply => StateT.lift (next reply)) : StateT S ProbComp A).run before =
        (StateT.lift ((unifSpec.query coin : ProbComp _) >>= next) : StateT S ProbComp A).run before
      simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]

private theorem lift_apply {T V : Type} {m : Type → Type} [Monad m] (work : m V) (before : T) :
    (StateT.lift work : StateT T m V) before = (work >>= fun value => pure (value, before)) := rfl
private theorem bind_apply {T V W : Type} {m : Type → Type} [Monad m]
    (work : StateT T m V) (next : V → StateT T m W) (before : T) :
    (work >>= next) before = (work before >>= fun result => next result.1 result.2) := rfl
private theorem pure_apply {T V : Type} {m : Type → Type} [Monad m] (value : V) (before : T) :
    (pure value : StateT T m V) before = pure (value, before) := rfl

private theorem query_commutes (native : QueryImpl (WorldSpec n) (StateT S ProbComp))
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (request : (WorldSpec n).Domain) (previous : Platform) (before : S) :
    Prod.map id Prod.swap <$>
      ((((implementation native).mapStateTBase (query reserve)).flattenStateT request).run (previous, before)) =
        ((RegistrationNativePlatformOrdinaryLower.terminal
          (fun request => RegistrationNativePlatformOrdinarySendGate.liftState (native request))
          (fun amount => StateT.lift (reserve amount))).flattenStateT request).run (before, previous) := by
  rcases request with created | (effect | ((send | raw) | ⟨owner, send | raw⟩))
  all_goals simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, query,
    RegistrationNativePlatformOrdinaryLower.terminal, world, simulateQ_spec_query, implementation,
    StateT.run, StateT.mk, lift_apply, bind_apply, pure_apply,
    simulateQ_bind, simulateQ_pure, RegistrationNativePlatformOrdinarySendGate.liftState,
    bind_assoc, pure_bind, map_bind, map_pure, Functor.map_map, Prod.map_def, id_eq]
  all_goals try rfl
  all_goals apply bind_congr
  all_goals rintro ⟨reply, after⟩
  all_goals cases reply with
  | none => rfl
  | some value =>
      simp only [RegistrationNativePlatformOrdinaryGate.gate, bind_apply, lift_apply, pure_apply,
        allocation, simulateQ_bind, external_program,
        bind_assoc, pure_bind, map_bind]
      apply bind_congr
      rintro ⟨result, next⟩
      cases result <;> rfl


/-- No request contains packet bytes, plaintext, a private key or a private map. -/
inductive Site where
  | ordinaryFrame
  | firstRecordJoin
  | firstRecordRaw
  | registrationInit
  | registrationResponse
  | registrationMap
  | peerMap
  deriving DecidableEq

abbrev PlatformSpec (E : Type) := (Site × Nat) →ₒ core.result.Result Unit E
abbrev SourceSpec (n : Nat) (E : Type) := WorldSpec n + PlatformSpec E

def compile (external : QueryImpl (PlatformSpec E) (StateT Platform ProbComp)) :
    QueryImpl (SourceSpec n E) (StateT Platform (OracleComp (Spec n)))
  | .inl request => query (fun amount => external (.ordinaryFrame, amount)) request
  | .inr request => fun previous => simulateQ publicCoin ((external request).run previous)

def runtime (native : QueryImpl (WorldSpec n) (StateT S ProbComp))
    (external : QueryImpl (PlatformSpec E) (StateT Platform ProbComp)) :
    QueryImpl (SourceSpec n E) (StateT S (StateT Platform ProbComp))
  | .inl request => RegistrationNativePlatformOrdinaryLower.terminal
      (fun request => RegistrationNativePlatformOrdinarySendGate.liftState (native request))
      (fun amount => StateT.lift (external (.ordinaryFrame, amount))) request
  | .inr request => StateT.lift (external request)


private theorem map_apply {T V W : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : V → W) (work : StateT T m V) (before : T) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem mixed_query (native : QueryImpl (WorldSpec n) (StateT S ProbComp))
    (external : QueryImpl (PlatformSpec E) (StateT Platform ProbComp))
    (request : (SourceSpec n E).Domain) (previous : Platform) (before : S) :
    Prod.map id Prod.swap <$>
      ((((implementation native).mapStateTBase (compile external)).flattenStateT request).run (previous, before)) =
        ((runtime native external).flattenStateT request).run (before, previous) := by
  cases request with
  | inl request => exact query_commutes native (fun amount => external (.ordinaryFrame, amount)) request previous before
  | inr request =>
      simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, compile, runtime,
        StateT.run, StateT.mk, external_program, lift_apply, bind_pure_comp,
        map_apply, Functor.map_map, Prod.map_def, id_eq, Prod.swap]


/-- All source public requests and all ordinary frame reservations share exactly one mutable platform state, with public draws outside private counters. -/
theorem program (native : QueryImpl (WorldSpec n) (StateT S ProbComp))
    (external : QueryImpl (PlatformSpec E) (StateT Platform ProbComp))
    (work : OracleComp (SourceSpec n E) A) (previous : Platform) (before : S) :
    Prod.map id Prod.swap <$>
      (simulateQ (((implementation native).mapStateTBase (compile external)).flattenStateT) work).run (previous, before) =
        (simulateQ (runtime native external).flattenStateT work).run (before, previous) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ Prod.swap
    (fun request state => mixed_query native external request state.1 state.2) work (previous, before)


/-- The complete randomized public-runtime source run and its free lower client have identical values, private state and one shared platform state. -/
theorem joint (native : QueryImpl (WorldSpec n) (StateT S ProbComp))
    (external : QueryImpl (PlatformSpec E) (StateT Platform ProbComp))
    (work : OracleComp (SourceSpec n E) A) (previous : Platform) (before : S) :
    (fun result : (A × Platform) × S => ((result.1.1, result.2), result.1.2)) <$>
      (simulateQ (implementation native) ((simulateQ (compile external) work).run previous)).run before =
      ((simulateQ (runtime native external) work).run before).run previous := by
  have same := congrArg (Functor.map (fun result : A × (S × Platform) =>
    ((result.1, result.2.1), result.2.2))) (program native external work previous before)
  rw [simulateQ_flattenStateT_run (runtime native external) work before previous] at same
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  simpa only [map_bind, map_pure, bind_pure_comp, Functor.map_map, Prod.map_def, Function.comp_def,
    id_eq, Prod.swap, Prod.mk.eta, id_map', StateT.run] using same


open PqxdhServerAuthExperiment (Setup Codec)
variable {I KemSK Reader Response : Type} {base : OracleSpec I}

noncomputable def actual (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (external : QueryImpl (PlatformSpec E) (StateT Platform ProbComp)) :
    QueryImpl (SourceSpec n E) (RegistrationNativePlatformOrdinaryWorld.M n Platform)
  | .inl request => RegistrationNativePlatformOrdinaryWorld.guarded setup codec
      (fun amount => external (.ordinaryFrame, amount)) route request
  | .inr request => StateT.lift (external request)

/-- The source runtime expands the actual dynamic ordinary World body and the common public platform handler. -/
theorem runtime_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (external : QueryImpl (PlatformSpec E) (StateT Platform ProbComp)) :
    runtime (CborRecordWorldSimulation.guarded (n := n) setup (CborRawCanonicalBuild.canonical codec) route) external =
      actual setup codec route external := by
  funext request
  cases request with
  | inl request =>
      exact (RegistrationNativePlatformOrdinaryLower.actual_query setup codec
        (fun amount => external (.ordinaryFrame, amount)) route request).symm
  | inr request => rfl


/-- Concrete adaptive record execution and every interleaved public allocation retain exact native and external poststates; external coin costs stay on their own oracle branch. -/
theorem actual_joint (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (external : QueryImpl (PlatformSpec E) (StateT Platform ProbComp))
    (work : OracleComp (SourceSpec n E) A) (previous : Platform) (before : PqxdhRecordLiftWorld.State n) :
    (fun result : (A × Platform) × PqxdhRecordLiftWorld.State n => ((result.1.1, result.2), result.1.2)) <$>
      (simulateQ (implementation (CborRecordWorldSimulation.guarded setup (CborRawCanonicalBuild.canonical codec) route))
        ((simulateQ (compile external) work).run previous)).run before =
      ((simulateQ (actual setup codec route external) work).run before).run previous := by
  rw [← runtime_source]
  exact joint _ external work previous before

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRandomizedLower

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRandomizedLower.external_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRandomizedLower.external_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRandomizedLower.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRandomizedLower.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRandomizedLower.joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRandomizedLower.joint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRandomizedLower.runtime_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRandomizedLower.runtime_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRandomizedLower.actual_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRandomizedLower.actual_joint
