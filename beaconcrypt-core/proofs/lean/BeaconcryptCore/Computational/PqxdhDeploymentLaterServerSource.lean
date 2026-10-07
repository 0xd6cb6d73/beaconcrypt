-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedSchedule
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemCollected

/-! LQ-F: a logged source for the exact later-quantum profile. The source is source14 (`PqxdhRegistrationJointServerSchedule.source`, the initialized annotated source of the accept/KEM join) with two changes. First, every raw accept is a logged accept (`acceptSource`): the literal Server accept, whose collector is the logged collector `collectLogged`, also returns the secret of the Server ephemeral it generated whenever its generation step was reached and returned one (`beforeLogged`, the steps before encapsulation split after generation), including an accept whose PQ-key parse then rejects, and the handler appends that entry (`some` scalar, or `none` when verification or a step before generation rejected) to a log kept beside the source state, one entry per raw accept in raw-accept order. Second, a Server read (the only query of `LaterRead`, issued as `.inr ()`) returns the Server identity seed, read from the Server's slot of the private identity pool by the ordinary pool reveal request, together with the log; the compiled later-quantum program issues it after its run, and the statements here allow it anywhere. The log is ghost state of the analysis: no source14 command reads it. Forgetting the log gives back source14 exactly, for every source14 program (`query_projection`, `program_projection`) and for the initialized execution (`initialized_projection`), and the logged collector forgets to the actual collector (`beforeLogged_fst`, `collectLogged_fst`). A successful collection records exactly the ephemeral scalar its DH steps used (`collectLogged_some`, `beforeLogged_some`). Under the Server-slot invariant the read returns the Server's actual seed and the current log, changes no seed, key, owner or shared state and only appends its reveal observation to the identity-pool transcript (`later_read`), and every logged step keeps that invariant (`query_owned`, `program_owned`). An entry is `none` only when no ephemeral was generated. This module proves no security statement and adds no assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhServerRootPreparation (Inputs Verified Ephemeral verifyInput collect)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhRegistrationJointFinish (onNative onPool)
open PqxdhRegistrationJointServerSchedule (onBackend Owned)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result : Type}

/-- The Server ephemeral log: one entry per raw accept in raw-accept order, the scalar of the ephemeral the accept generated when its generation step was reached and returned one, and `none` otherwise. -/
abbrev Log := List (Option ScalarBytes)

/-- The Server read: the Server identity seed read from its private identity-pool slot, and the ephemeral log. -/
abbrev Reveal := Option IdentitySeed × Log

/-- The single later-quantum Server read. -/
abbrev LaterRead : OracleSpec Unit := fun _ => Reveal

/-- source14 extended by the Server read. -/
abbrev Spec (KemSK : Type) := PqxdhRegistrationJointRevealSchedule.Spec KemSK + LaterRead

/-- The steps before encapsulation (freshness, reservation, both point parsers, ephemeral generation and KEM parsing), which also return the secret of the generated ephemeral whenever the generation step was reached and returned one, including when the following PQ-key parse rejects. The callbacks, their order and every optional exit are those of `KemCollected.beforeEncapsulation`. -/
def beforeLogged {E Shared : Type} (verified : Verified Reader) :
    OracleComp (PqxdhServerRootPreparation.Spec Reader E Shared) (Option (Ephemeral E) × Option E) := do
  let status ← (PqxdhServerRootPreparation.Spec Reader E Shared).query
    (.registrationStatus (PqxdhServerRootPreparation.registrationId verified))
  match status with
  | .Consumed => pure (none, none)
  | .Fresh => do
    let reserved ← (PqxdhServerRootPreparation.Spec Reader E Shared).query .reserveRegistration
    if !reserved then pure (none, none) else do
      let validPrekey ← (PqxdhServerRootPreparation.Spec Reader E Shared).query
        (.parseDh (PqxdhRootTableInitialization.rootArray verified.keys.prekey))
      if !validPrekey then pure (none, none) else do
        let validOneTime ← (PqxdhServerRootPreparation.Spec Reader E Shared).query
          (.parseDh (PqxdhRootTableInitialization.rootArray verified.keys.oneTime))
        if !validOneTime then pure (none, none) else do
          let generated ← (PqxdhServerRootPreparation.Spec Reader E Shared).query .generate
          match generated with
          | none => pure (none, none)
          | some ephemeral => do
            let validKem ← (PqxdhServerRootPreparation.Spec Reader E Shared).query (.parseKem verified.keys.pqKey)
            if !validKem then pure (none, some ephemeral.secret) else pure (some ephemeral, some ephemeral.secret)

/-- Forgetting the logged scalar gives the actual steps before encapsulation as an oracle program, before any interpretation. -/
theorem beforeLogged_fst {E Shared : Type} (verified : Verified Reader) :
    Prod.fst <$> beforeLogged (E := E) (Shared := Shared) verified =
      PqxdhRegistrationJointKemCollected.beforeEncapsulation verified := by
  unfold beforeLogged PqxdhRegistrationJointKemCollected.beforeEncapsulation
  repeat
    first
    | rfl
    | (fail_if_no_progress simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_monadLift, Option.elimM,
        Option.elim_some, bind_map_left, map_bind, Bool.not_true, Bool.false_eq_true, ite_false])
    | (apply bind_congr; intro answer; cases answer)

/-- When the steps before encapsulation succeed with an ephemeral, the logged scalar is that ephemeral's secret. -/
theorem beforeLogged_some {E Shared : Type} (verified : Verified Reader) (result : Option (Ephemeral E) × Option E)
    (ephemeral : Ephemeral E) (reached : result ∈ support (beforeLogged (Shared := Shared) verified))
    (found : result.1 = some ephemeral) : result.2 = some ephemeral.secret := by
  unfold beforeLogged at reached
  repeat' (first
    | (rw [mem_support_bind_iff] at reached; obtain ⟨answer, _, reached⟩ := reached; cases answer <;>
        try simp only [Bool.not_true, Bool.not_false, ite_true, ite_false, Bool.false_eq_true] at reached)
    | (simp only [support_pure, Set.mem_singleton_iff] at reached; subst reached; simp_all))

/-- The actual raw-accept collector, with the secret of the ephemeral it generated whenever its generation step was reached and returned one: on a rejection before encapsulation the entry of `beforeLogged`, and once the encapsulation is reached the secret of the ephemeral fixed before it. The callbacks, their order and every optional exit are those of `collect`. -/
def collectLogged {E Shared : Type} (raw : Pqxdh.Bytes) :
    OracleComp (PqxdhServerRootPreparation.Spec Reader E Shared) (Option (Inputs Reader E Shared) × Option E) := do
  let verified ← verifyInput raw
  match verified with
  | none => pure (none, none)
  | some verified => do
      let before ← beforeLogged verified
      match before.1 with
      | none => pure (none, before.2)
      | some ephemeral => do
          let reply ← (PqxdhServerRootPreparation.Spec Reader E Shared).query (.encapsulate verified.keys.pqKey)
          let input ← PqxdhRegistrationJointKemCollected.afterEncapsulation verified ephemeral reply
          pure (input, some ephemeral.secret)

/-- Forgetting the logged scalar gives the actual collector as an oracle program, before any interpretation. -/
theorem collectLogged_fst {E Shared : Type} (raw : Pqxdh.Bytes) :
    Prod.fst <$> collectLogged (Reader := Reader) (E := E) (Shared := Shared) raw = collect raw := by
  simp only [collectLogged, collect, map_bind]
  apply bind_congr
  intro verified
  cases verified with
  | none => simp
  | some verified =>
    dsimp only
    rw [PqxdhRegistrationJointKemCollected.collect_split, ← beforeLogged_fst, bind_map_left, map_bind]
    apply bind_congr
    rintro ⟨_ | ephemeral, logged⟩
    · simp
    · simp [map_bind]

/-- Under every stateful interpretation, a successful collection logs exactly the ephemeral secret recorded in its collected input, which is the scalar of its DH2 to DH4 steps. -/
theorem collectLogged_some {E Shared State : Type} {κ : Type} {target : OracleSpec κ}
    (impl : QueryImpl (PqxdhServerRootPreparation.Spec Reader E Shared) (StateT State (OracleComp target)))
    (raw : Pqxdh.Bytes) (before after : State) (input : Inputs Reader E Shared) (logged : Option E)
    (reached : ((some input, logged), after) ∈ support ((simulateQ impl (collectLogged raw)).run before)) :
    logged = some input.ephemeral.secret := by
  have program : (some input, logged) ∈ support (collectLogged (Reader := Reader) (Shared := Shared) raw) := by
    apply support_simulateQ_run'_subset impl _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ reached
  simp only [collectLogged, mem_support_bind_iff] at program
  obtain ⟨verified, _, program⟩ := program
  cases verified with
  | none => simp at program
  | some verified =>
    simp only [mem_support_bind_iff] at program
    obtain ⟨prepared, _, program⟩ := program
    rcases prepared with ⟨_ | ephemeral, entry⟩
    · simp at program
    · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at program
      obtain ⟨reply, _, collected, collectedReached, rfl, rfl⟩ := program
      obtain ⟨_, same, _⟩ := PqxdhRegistrationJointKemCollected.after_fields verified ephemeral reply input
        collectedReached
      rw [same]

/-- The annotated source preparation of a logged accept: `ServerAccept.sourcePrepare` with the logged collector. -/
def sourcePrepare (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes) :
    StateT (PqxdhRegistrationJointFinish.State KemSK) ProbComp
      ((Option (Inputs Reader ScalarBytes Word32) × List Pqxdh.Bytes) × Option ScalarBytes) := fun state =>
  (fun result => (((result.1.1, result.2.2), result.1.2), (result.2.1, state.2))) <$>
    (simulateQ (PqxdhRegistrationJointServerPrefix.annotated setup.joint seed identityIndex (serverAux setup codec checks))
      (collectLogged raw)).run (state.1, state.2.2.server.consumed)

/-- Forgetting the logged scalar gives the actual annotated preparation with its complete state. -/
theorem sourcePrepare_fst (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes) (state : PqxdhRegistrationJointFinish.State KemSK) :
    (fun result => (result.1.1, result.2)) <$> (sourcePrepare setup codec checks seed identityIndex raw).run state =
      (PqxdhRegistrationJointServerAccept.sourcePrepare setup codec checks seed identityIndex raw).run state := by
  have logged := congrArg (fun work => StateT.run work (state.1, state.2.2.server.consumed))
    (congrArg (simulateQ (PqxdhRegistrationJointServerPrefix.annotated setup.joint seed identityIndex
      (serverAux setup codec checks))) (collectLogged_fst (Reader := Reader) raw))
  simp only [simulateQ_map, StateT.run_map] at logged
  simp only [StateT.run] at logged
  simp only [sourcePrepare, PqxdhRegistrationJointServerAccept.sourcePrepare, StateT.run, Functor.map_map]
  rw [← logged, Functor.map_map]

/-- The logged raw accept: the literal annotated Server accept (allocation, preparation, root, clearing, consumption and pending publication), which also returns the logged ephemeral scalar. -/
noncomputable def acceptSource (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes) :
    StateT (PqxdhRegistrationJointFinish.State KemSK) ProbComp (Option Nat × Option ScalarBytes) := do
  let state ← onNative nativeGet
  let collected ← sourcePrepare setup codec checks seed identityIndex raw
  let reply ← onNative (PqxdhRegistrationJointServerAccept.tail setup (setup.joint.publicKeys seed) state collected.1)
  pure (reply, collected.2)

/-- Forgetting the logged scalar gives the actual annotated accept with its complete state. -/
theorem acceptSource_fst (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes) (state : PqxdhRegistrationJointFinish.State KemSK) :
    (fun result => (result.1.1, result.2)) <$> (acceptSource setup codec checks seed identityIndex raw).run state =
      (PqxdhRegistrationJointServerAccept.source setup codec checks seed identityIndex raw).run state := by
  simp only [acceptSource, PqxdhRegistrationJointServerAccept.source, PqxdhRegistrationJointServerAccept.run,
    StateT.run_bind, map_bind]
  apply bind_congr
  intro before
  rw [← sourcePrepare_fst, bind_map_left]
  apply bind_congr
  intro collected
  simp only [StateT.run_pure, map_pure, Prod.mk.eta, bind_pure]

/-- The logged source handler. A raw accept runs the logged accept and appends its entry to the log; every other source14 request runs the unchanged source14 handler and keeps the log; the Server read reveals the Server's identity-pool slot by the ordinary pool reveal request and returns it with the log. -/
noncomputable def source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) :
    QueryImpl (Spec KemSK) (StateT (PqxdhRegistrationJointSchedule.State KemSK × Log) ProbComp)
  | .inl (.inl (.inr (.accept raw))) => fun state =>
      (fun result => (result.1.1, (result.2, state.2 ++ [result.1.2]))) <$>
        (onBackend (acceptSource setup codec checks seed identityIndex raw)).run state.1
  | .inl query => fun state => (fun result => (result.1, (result.2, state.2))) <$>
      (PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex query).run state.1
  | .inr _ => fun state => (fun result => ((result.1, state.2), (result.2, state.2))) <$>
      (onBackend (onPool (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem
        (.inl (.inr (.reveal identityIndex)))))).run state.1

/-- source14 programs as programs of the logged source. -/
def embed : QueryImpl (PqxdhRegistrationJointRevealSchedule.Spec KemSK) (OracleComp (Spec KemSK)) :=
  fun query => (Spec KemSK).query (.inl query)

/-- Every source14 request of the logged source projects to the same reply and source state as source14, whatever the log. -/
theorem query_projection (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (log : Log) :
    (fun result => (result.1, result.2.1)) <$> (source setup codec checks seed identityIndex (.inl query)).run (state, log) =
      (PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex query).run state := by
  rcases query with (coin | request) | read
  case inl.inr =>
    cases request
    case accept raw =>
      have logged := acceptSource_fst setup codec checks seed identityIndex raw (state.pool, state.shared)
      simp only [StateT.run] at logged
      simp only [source, PqxdhRegistrationJointServerSchedule.source, onBackend, StateT.run, Functor.map_map, ← logged]
    all_goals simp only [source, StateT.run, Functor.map_map]; exact id_map _
  all_goals simp only [source, StateT.run, Functor.map_map]; exact id_map _

/-- Every source14 program, run by the logged source from any log, projects to its source14 execution with the same result and complete source state. -/
theorem program_projection (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (log : Log) :
    (fun result => (result.1, result.2.1)) <$>
      (simulateQ (source setup codec checks seed identityIndex) (simulateQ embed program)).run (state, log) =
      (simulateQ (PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex) program).run state := by
  induction program using OracleComp.inductionOn generalizing state log with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, embed, StateT.run_bind, map_bind]
    rw [← query_projection setup codec checks seed identityIndex query state log, bind_map_left]
    apply bind_congr
    intro result
    exact ih result.1 result.2.1 result.2.2

/-- The logged initialized source: the actual Server constructor followed by the logged source from the empty log, at the constructed Server's seed and identity index. The final log is returned beside the source outcome. -/
noncomputable def initialized (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (program : OracleComp (Spec KemSK) Result) :
    StateT (PqxdhRegistrationJointServerPrefix.State KemSK A) ProbComp
      (Option (PqxdhRegistrationJointInitializedSchedule.SourceOutcome KemSK Result × Log)) := fun state => do
  let born ← (PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId supplied).run state
  match born.1 with
  | none => pure (none, born.2)
  | some created =>
    (fun result => (some ((PqxdhRegistrationJointServerBirth.encode created, result.1, result.2.1), result.2.2),
      (result.2.1.pool, born.2.2))) <$>
      (simulateQ (source setup codec checks created.seed created.server.server.metadata.identityIndex) program).run
        (PqxdhRegistrationJointSchedule.initial born.2.1 (PqxdhRegistrationSchedule.initial created).shared, [])

/-- Forgetting the log, the logged initialized execution of a source14 program is the initialized source14 execution, with the same constructor, outcome and final state. -/
theorem initialized_projection (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A) :
    (fun result => (result.1.map Prod.fst, result.2)) <$>
      (initialized setup codec checks ensureInit supplied (simulateQ embed program)).run state =
      (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied program).run state := by
  simp only [initialized, PqxdhRegistrationJointInitializedSchedule.source, StateT.run, map_bind]
  apply bind_congr
  rintro ⟨(_ | created), after⟩
  · simp
  · have logged := program_projection setup codec checks created.seed created.server.server.metadata.identityIndex
      program (PqxdhRegistrationJointSchedule.initial after.1 (PqxdhRegistrationSchedule.initial created).shared) []
    simp only [StateT.run] at logged
    simp only [← logged, Functor.map_map, Option.map_some]

/-- The Server read at a state whose Server slot holds `seed` returns that seed and the current log, keeps the log, changes no seed, KEM key, owner or shared state, and only appends the reveal observation of the Server's slot to the identity-pool transcript. -/
theorem later_read (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (state : PqxdhRegistrationJointSchedule.State KemSK) (log : Log)
    (slot : state.pool.1.seeds[identityIndex]? = some seed)
    (result : Reveal × (PqxdhRegistrationJointSchedule.State KemSK × Log))
    (reached : result ∈ support ((source setup codec checks seed identityIndex (.inr ())).run (state, log))) :
    result.1 = (some seed, log) ∧ result.2.2 = log ∧ result.2.1.pool.1.seeds = state.pool.1.seeds ∧
      result.2.1.pool.2 = state.pool.2 ∧ result.2.1.owners = state.owners ∧ result.2.1.shared = state.shared ∧
      result.2.1.pool.1.transcript = state.pool.1.transcript ++ [⟨.inr (.reveal identityIndex), some seed⟩] := by
  simp only [source, onBackend, onPool, PqxdhLiveKemBirth.impl, PqxdhDynamicIdentityPool.lazyImpl,
    PqxdhDynamicIdentityPool.poolImpl, StateT.run, support_map, Set.mem_image] at reached
  obtain ⟨_, ⟨_, ⟨_, ⟨_, reached, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := reached
  simp only [support_pure, Set.mem_singleton_iff] at reached
  subst reached
  simp [slot, PqxdhDynamicIdentityPool.record]

/-- Every logged step keeps the Server-slot and owner invariant of source14. -/
theorem query_owned (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (query : (Spec KemSK).Domain)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (log : Log)
    (result : (Spec KemSK).Range query × (PqxdhRegistrationJointSchedule.State KemSK × Log))
    (owned : Owned seed identityIndex state)
    (reached : result ∈ support ((source setup codec checks seed identityIndex query).run (state, log))) :
    Owned seed identityIndex result.2.1 := by
  cases query with
  | inl query =>
    have projected : (result.1, result.2.1) ∈ support
        ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex query).run state) := by
      rw [← query_projection setup codec checks seed identityIndex query state log, support_map]
      exact Set.mem_image_of_mem _ reached
    exact PqxdhRegistrationJointServerSchedule.query_invariant setup codec checks seed identityIndex query state
      (result.1, result.2.1) owned projected
  | inr read =>
    obtain ⟨_, _, seeds, keys, owners, _, _⟩ := later_read setup codec checks seed identityIndex state log owned.2
      result reached
    refine ⟨?_, by rw [seeds]; exact owned.2⟩
    intro entry member
    rw [owners] at member
    exact PqxdhRegistrationJointOwnership.owned_slots state.pool result.2.1.pool entry seeds
      (by rw [keys]) (owned.1 entry member)

/-- Every logged program keeps the Server-slot and owner invariant on every reached state, so every Server read of a reached state returns the Server's actual seed. -/
theorem program_owned (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (program : OracleComp (Spec KemSK) Result)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (log : Log)
    (result : Result × (PqxdhRegistrationJointSchedule.State KemSK × Log))
    (owned : Owned seed identityIndex state)
    (reached : result ∈ support ((simulateQ (source setup codec checks seed identityIndex) program).run (state, log))) :
    Owned seed identityIndex result.2.1 := by
  induction program using OracleComp.inductionOn generalizing state log with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
    subst reached
    exact owned
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
    obtain ⟨middle, middleReached, reached⟩ := reached
    exact ih middle.1 middle.2.1 middle.2.2
      (query_owned setup codec checks seed identityIndex query state log middle owned middleReached) reached

end BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource.beforeLogged_fst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource.beforeLogged_fst

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource.beforeLogged_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource.beforeLogged_some

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource.collectLogged_fst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource.collectLogged_fst

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource.collectLogged_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource.collectLogged_some

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource.sourcePrepare_fst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource.sourcePrepare_fst

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource.acceptSource_fst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource.acceptSource_fst

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource.query_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource.query_projection

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource.program_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource.program_projection

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource.initialized_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource.initialized_projection

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource.later_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource.later_read

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource.query_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource.query_owned

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource.program_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource.program_owned
