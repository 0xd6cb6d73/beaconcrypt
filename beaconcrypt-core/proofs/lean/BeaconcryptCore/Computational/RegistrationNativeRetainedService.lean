-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRetainedRoots

/-! A private memo of the actual prepare-time roots can be erased through an entire adaptive client. Its executable replacement keeps only successful descriptor flags, while the phase interpreter retains the protected PRK. The equality follows from the reached cached-root invariant; arbitrary malformed or unprepared descriptor requests remain refused. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRetainedService
open RegistrationNativeRelatedFamily (Message)
open PqxdhSecretInputKdf (HmacSha512)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open RegistrationNativeRetainedRoots (Good)
variable {Value : Type}

inductive Request where
  | prepare : Message → Request
  | demand : Message → Request

abbrev CommandSpec : OracleSpec Request
  | .prepare _ => Option Message
  | .demand _ => Option PqxdhServerAuthKeySchedule.Output
abbrev Spec := unifSpec + CommandSpec
abbrev Flags := Message → Bool
abbrev PublicState := Flags × RegistrationNativeKeyPhases.State

def flags (memo : RegistrationNativeRetainedRoots.Memo) : Flags := fun message => (memo message).isSome

def project (before : RegistrationNativeRetainedRoots.State) : PublicState := (flags before.1, before.2)

noncomputable def retained (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) :
    QueryImpl Spec (StateT RegistrationNativeRetainedRoots.State ProbComp)
  | .inl coin => StateT.lift (unifSpec.query coin)
  | .inr (.prepare message) => RegistrationNativeRetainedRoots.remember source hmac input inside message
  | .inr (.demand message) => RegistrationNativeRetainedRoots.demand source message

/-- This compiler has no selected scalar, root, PRK, full private input or protection bit. -/
def compiler : QueryImpl Spec (StateT Flags (OracleComp RegistrationNativeKeyPhases.Spec))
  | .inl coin => StateT.lift (RegistrationNativeKeyPhases.Spec.query (.inl coin))
  | .inr (.prepare message) => fun before => do
      let prepared ← (RegistrationNativeKeyPhases.Spec.query (.inr (.prepare message)) : OracleComp RegistrationNativeKeyPhases.Spec _)
      pure (prepared, Function.update before message prepared.isSome)
  | .inr (.demand message) => fun before =>
      if before message then
        (fun reply => (reply.map RegistrationNativeRetainedRoots.output, before)) <$>
          (RegistrationNativeKeyPhases.Spec.query (.inr (.demand message)) : OracleComp RegistrationNativeKeyPhases.Spec _)
      else pure (none, before)

def client (work : OracleComp Spec Value) : OracleComp RegistrationNativeKeyPhases.Spec Value :=
  (simulateQ compiler work).run' (fun _ => false)

noncomputable def phase (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) :
    QueryImpl Spec (StateT PublicState ProbComp)
  | .inl coin => StateT.lift (unifSpec.query coin)
  | .inr (.prepare message) => fun before =>
      (fun result => (result.1,
        (Function.update before.1 message result.1.isSome, result.2))) <$>
          (RegistrationNativeKeyServiceBound.native source hmac input inside (.inr (.prepare message))).run before.2
  | .inr (.demand message) => fun before =>
      if before.1 message then
        (fun result => (result.1.map RegistrationNativeRetainedRoots.output, (before.1, result.2))) <$>
          (RegistrationNativeKeyServiceBound.native source hmac input inside (.inr (.demand message))).run before.2
      else pure (none, before)

private theorem flags_update (memo : RegistrationNativeRetainedRoots.Memo) (message : Message)
    (root : Option PqxdhSecretInputKdf.RootOutput) :
    flags (Function.update memo message root) = Function.update (flags memo) message root.isSome := by
  funext other
  by_cases same : other = message
  · subst other
    simp only [flags, Function.update_self]
  · simp only [flags, Function.update_of_ne same]

private theorem native_prepare_run (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (message : Message) (before : RegistrationNativeKeyPhases.State) :
    (RegistrationNativeKeyServiceBound.native source hmac input inside (.inr (.prepare message))).run before =
      (fun result => (result.1.map Prod.fst, result.2)) <$>
        (RegistrationNativeKeyPreparation.prepare source hmac input inside message).run before := by
  simp only [RegistrationNativeKeyServiceBound.native, StateT.run_map]

/-- Each actual private service step preserves its reached root/cache invariant. -/
theorem retained_good (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (query : Spec.Domain) (before : RegistrationNativeRetainedRoots.State)
    (good : Good source hmac input inside before)
    (result : Spec.Range query × RegistrationNativeRetainedRoots.State)
    (reached : result ∈ support ((retained source hmac input inside query).run before)) :
    Good source hmac input inside result.2 := by
  cases query with
  | inl coin =>
      simp only [retained, StateT.run, StateT.lift, bind_pure_comp, support_map] at reached
      obtain ⟨reply, _sampled, equal⟩ := reached
      cases equal
      exact good
  | inr request => cases request with
    | prepare message => exact RegistrationNativeRetainedRoots.remember_good source hmac input inside message before result.2 result.1 good reached
    | demand message => exact RegistrationNativeRetainedRoots.demand_good source hmac input inside message before result.2 result.1 good reached

/-- Private root erasure preserves every service reply and complete phase state. -/
theorem query_project (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (query : Spec.Domain) (before : RegistrationNativeRetainedRoots.State)
    (good : Good source hmac input inside before) :
    Prod.map id project <$> (retained source hmac input inside query).run before =
      (phase source hmac input inside query).run (project before) := by
  cases query with
  | inl coin =>
      simp only [retained, phase, StateT.run, StateT.lift, bind_pure_comp, Functor.map_map]
      rfl
  | inr request => cases request with
    | prepare message =>
      change Prod.map id project <$>
          (RegistrationNativeRetainedRoots.remember source hmac input inside message).run before =
        (fun result => (result.1, (Function.update (flags before.1) message result.1.isSome, result.2))) <$>
          (RegistrationNativeKeyServiceBound.native source hmac input inside (.inr (.prepare message))).run before.2
      rw [native_prepare_run]
      simp only [RegistrationNativeRetainedRoots.remember, StateT.run, Functor.map_map,
        project, Prod.map, id_eq]
      congr 1
      funext result
      rcases result with ⟨reply, after⟩
      cases reply <;> simp only [Option.map_none, Option.map_some, Option.isSome_none,
        Option.isSome_some, flags_update]
    | demand message =>
      have base := RegistrationNativeRetainedRoots.demand_project source hmac input inside message before good
      have augmented := congrArg (fun work => (fun result => (result.1, (flags before.1, result.2))) <$> work) base
      cases stored : before.1 message
      all_goals simp only [retained, phase, project, flags, StateT.run, stored, Option.isSome_none,
        Option.isSome_some, Bool.false_eq_true, ite_false, ite_true,
        RegistrationNativeRetainedRoots.demand, Functor.map_map, map_pure, Prod.map, id_eq] at augmented ⊢
      all_goals exact augmented

/-- The actual invariant establishes complete adaptive private-root erasure, including failed and repeated preparation/demand requests. -/
theorem program_project (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (work : OracleComp Spec Value) (before : RegistrationNativeRetainedRoots.State)
    (good : Good source hmac input inside before) :
    Prod.map id project <$> (simulateQ (retained source hmac input inside) work).run before =
      (simulateQ (phase source hmac input inside) work).run (project before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv' _ _ (Good source hmac input inside) project
    (retained_good source hmac input inside) (query_project source hmac input inside) work before good

private theorem map_apply {S X Y : Type} (f : X → Y) (work : StateT S ProbComp X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

/-- The public phase implementation is the actual interpretation of the root-free compiler, with both local flags and private phase state threaded. -/
theorem phase_compiler (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) :
    ((RegistrationNativeKeyServiceBound.native source hmac input inside).mapStateTBase compiler).flattenStateT =
      phase source hmac input inside := by
  funext query before
  change (((RegistrationNativeKeyServiceBound.native source hmac input inside).mapStateTBase compiler).flattenStateT query).run before =
    (phase source hmac input inside query).run before
  rcases before with ⟨before, privateState⟩
  cases query with
  | inl coin =>
      simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.mk, compiler, phase,
        StateT.run, StateT.lift, simulateQ_map, simulateQ_spec_query, bind_pure_comp]
      rfl
  | inr request => cases request with
    | prepare message =>
      simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.mk, compiler, phase,
        StateT.run, simulateQ_map, simulateQ_spec_query, map_apply,
        bind_pure_comp, Functor.map_map]
      rfl
    | demand message =>
      simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.mk, compiler, phase, StateT.run]
      split
      · simp only [simulateQ_map, simulateQ_spec_query, map_apply, Functor.map_map]
        rfl
      · simp only [simulateQ_pure, ]
        rfl

noncomputable def initial : RegistrationNativeRetainedRoots.State :=
  ((fun _ => none), RegistrationNativeKeyPhases.initial)

/-- The required cache/root invariant follows from fresh actual initialization. -/
theorem initial_good (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) :
    Good source hmac input inside initial := by
  intro message root present
  cases present

/-- Complete adaptive retained-root execution is the actual before-prepare phase game of the constructed PRK-free client. -/
theorem source_phase (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (work : OracleComp Spec Bool) :
    (simulateQ (retained source hmac input inside) work).run' initial =
      RegistrationNativeKeyServiceBound.g1 source hmac input inside (client work) := by
  have projected := congrArg (fun experiment => Prod.fst <$> experiment)
    (program_project source hmac input inside work initial (initial_good source hmac input inside))
  have compiled := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (RegistrationNativeKeyServiceBound.native source hmac input inside) compiler work
    (fun _ => false) RegistrationNativeKeyPhases.initial
  rw [phase_compiler] at compiled
  simp only [RegistrationNativeKeyServiceBound.g1, client, StateT.run'_eq, simulateQ_map,
    StateT.run_map, Functor.map_map] at projected compiled ⊢
  have initialEq : project initial = ((fun _ => false), RegistrationNativeKeyPhases.initial) := rfl
  rw [initialEq] at projected
  rw [compiled]
  simpa only [Functor.map_map, Prod.map, id_eq] using projected

def IsDemand : Spec.Domain → Prop
  | .inr (.demand _) => True
  | _ => False

instance : DecidablePred IsDemand := fun query => by
  cases query with
  | inl _ => exact isFalse id
  | inr query => cases query with
    | prepare _ => exact isFalse id
    | demand _ => exact isTrue trivial

/-- The public compiler issues at most one phase material query per original material demand and none during preparation or ordinary draws. -/
theorem compiler_bound (query : Spec.Domain) (before : Flags) :
    ((compiler query).run before).IsQueryBoundP RegistrationNativeKeyBounds.IsDemand
      (if IsDemand query then 1 else 0) := by
  cases query with
  | inl coin => simp [compiler, StateT.run, StateT.lift, bind_pure_comp,
      isQueryBoundP_map_iff, isQueryBoundP_query_iff, RegistrationNativeKeyBounds.IsDemand, IsDemand]
  | inr query => cases query with
    | prepare message => simp [compiler, StateT.run, RegistrationNativeKeyBounds.IsDemand, IsDemand]
    | demand message =>
        simp only [compiler, StateT.run]
        split
        · simp [isQueryBoundP_map_iff, isQueryBoundP_query_iff, RegistrationNativeKeyBounds.IsDemand, IsDemand]
        · trivial

/-- Complete adaptive native scheduling retains its actual demand allowance through private-root erasure. -/
theorem client_bound (work : OracleComp Spec Value) (count : Nat) (bounded : work.IsQueryBoundP IsDemand count) :
    (client work).IsQueryBoundP RegistrationNativeKeyBounds.IsDemand count := by
  unfold client
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  apply bounded.simulateQ_run_of_step
  · intro query counted before
    simpa only [ite_eq_left counted] using compiler_bound query before
  · intro query free before
    simpa only [ite_eq_right free] using compiler_bound query before

/-- Actual retained prepare-time roots have the before-prepare five-loss uniform108 bound for the whole constructed PRK-free client. -/
theorem key_bound (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect source hmac)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (work : OracleComp Spec Bool) (count : Nat) (bounded : work.IsQueryBoundP IsDemand count) :
    ((simulateQ (retained source hmac input inside) work).run' initial).boolDistance
      (RegistrationNativeKeyServiceBound.g2 source input inside (client work)) ≤
      ∑ index ∈ Finset.range count, RegistrationBoundKeySchedule.keyLoss source hmac
        (RegistrationNativeKeyHybrid.reduction source hmac
          (RegistrationNativeKeyCompiler.client source input inside (client work)
            RegistrationNativeKeyPhases.emptyMeta) index) := by
  rw [source_phase]
  exact RegistrationNativeKeyServiceBound.bound source hmac correct input inside (client work) count
    (client_bound work count bounded)

end BeaconcryptCore.Computational.RegistrationNativeRetainedService

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedService.retained_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedService.retained_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedService.query_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedService.query_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedService.program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedService.program_project

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedService.phase_compiler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedService.phase_compiler
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedService.initial_good' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedService.initial_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedService.source_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedService.source_phase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedService.compiler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedService.compiler_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedService.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedService.client_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedService.key_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedService.key_bound
