-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource
import BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace

/-! LQ-F: the native logged source, the counterpart of the logged annotated source at the native level of the deployment experiment. The native logged raw accept `acceptLogged` is the literal native Server accept `nativeAccept` with the logged collector in its native prefix (`prefixLogged`); forgetting the logged entry gives `nativeAccept` back exactly, with its complete shared state (`acceptLogged_fst`). The native logged handler `native` keeps the ephemeral log beside the native source14 state: a raw accept runs `acceptLogged` and appends its entry, every other source14 request runs the unchanged native handler `RevealSchedule.native`, and the Server read returns the Server seed of the handler with the current log and changes nothing. Forgetting the log gives source14's native execution back for every source14 program (`query_projection`, `program_projection`), a source14 program that issues no raw accept keeps the log (`program_quiet`), and along every execution the log grows exactly as the Server's session counter does: a step appends one entry and advances the counter by one (a raw accept) or keeps both (`step_log`), so over a run the log length and the counter advance by the same amount (`program_log`). That from the initial state entry `j` belongs to the accept that allocated session index `j` is an informal consequence of these two lemmas, not a stated theorem. Erasing the private service annotations of the logged annotated source gives the native logged handler (`acceptSource_native`, `query_native`, `program_native`), under the Server-slot invariant for the read, and the logged initialized source is the native logged initialized execution with the same constructor, outcome and final log (`initialized_native`). No security statement and no assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhServerRootPreparation (Inputs)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhRegistrationJointRevealCosts (sourceKind)
open PqxdhDeploymentLaterServerSource (Log Reveal Spec embed collectLogged collectLogged_fst)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result : Type}

/-- The native logged prefix: the logged collector under the native Server callbacks, on the consumed set. -/
noncomputable def prefixLogged (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (raw : Pqxdh.Bytes) :
    StateT (List Pqxdh.Bytes) ProbComp (Option (Inputs Reader ScalarBytes Word32) × Option ScalarBytes) :=
  simulateQ (PqxdhServerStaticDhSource.nativeImpl setup.joint seed (serverAux setup codec checks)
    (fun _ => pure ())) (collectLogged raw)

/-- The native logged raw accept: the literal native accept (allocation, native logged prefix, core acceptance, root, clearing, consumption and pending publication), which also returns the logged entry of its collector. -/
noncomputable def acceptLogged (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (raw : Pqxdh.Bytes) : NativeGame KemSK (Option Nat × Option ScalarBytes) := do
  let state ← nativeGet
  let collected ← nativeCoins ((prefixLogged setup codec checks seed raw).run state.server.consumed)
  let reply ← PqxdhRegistrationJointServerAccept.tail setup (setup.joint.publicKeys seed) state
    (collected.1.1, collected.2)
  pure (reply, collected.1.2)

/-- Forgetting the logged entry of the native logged prefix gives the actual native prefix with its consumed set. -/
theorem prefixLogged_fst (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (raw : Pqxdh.Bytes) (consumed : List Pqxdh.Bytes) :
    (fun result => (result.1.1, result.2)) <$> (prefixLogged setup codec checks seed raw).run consumed =
      (nativePrefix setup codec checks seed raw).run consumed := by
  rw [nativePrefix, ← collectLogged_fst, simulateQ_map, StateT.run_map, prefixLogged]

/-- Forgetting the logged entry of the native logged accept gives the actual native accept with its complete shared state. -/
theorem acceptLogged_fst (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (raw : Pqxdh.Bytes) (shared : NativeState KemSK) :
    (fun result => (result.1.1, result.2)) <$> (acceptLogged setup codec checks seed raw).run shared =
      (nativeAccept setup codec checks seed PqxdhRegistrationSchedule.observationScalar raw).run shared := by
  rw [PqxdhRegistrationJointServerAccept.native_run, ← prefixLogged_fst, bind_map_left]
  change (fun result => (result.1.1, result.2)) <$> ((nativeCoins ((prefixLogged setup codec checks seed raw).run
      shared.2.server.consumed) >>= fun collected => PqxdhRegistrationJointServerAccept.tail setup
        (setup.joint.publicKeys seed) shared.2 (collected.1.1, collected.2) >>= fun reply =>
          (pure (reply, collected.1.2) : NativeGame KemSK _)).run shared) = _
  have coins : ∀ {Value : Type} (work : ProbComp Value) (state : NativeState KemSK),
      (nativeCoins work).run state = (fun value => (value, state)) <$> work := fun _ _ => rfl
  rw [StateT.run_bind, coins]
  simp only [bind_map_left, map_bind, StateT.run_bind, StateT.run_pure, map_pure, Prod.mk.eta, bind_pure]

/-- The native logged accept, unfolded: the native logged prefix on the current consumed set, then the accept tail on its collected input, with the logged entry returned beside the reply. -/
theorem acceptLogged_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (raw : Pqxdh.Bytes) (shared : NativeState KemSK) :
    (acceptLogged setup codec checks seed raw).run shared = (do
      let collected ← (prefixLogged setup codec checks seed raw).run shared.2.server.consumed
      let answer ← (PqxdhRegistrationJointServerAccept.tail setup (setup.joint.publicKeys seed) shared.2
        (collected.1.1, collected.2)).run shared
      pure ((answer.1, collected.1.2), answer.2)) := by
  have coins : ∀ {Value : Type} (work : ProbComp Value) (state : NativeState KemSK),
      (nativeCoins work).run state = (fun value => (value, state)) <$> work := fun _ _ => rfl
  change ((nativeCoins ((prefixLogged setup codec checks seed raw).run shared.2.server.consumed) >>= fun collected =>
      PqxdhRegistrationJointServerAccept.tail setup (setup.joint.publicKeys seed) shared.2 (collected.1.1, collected.2) >>=
        fun reply => (pure (reply, collected.1.2) : NativeGame KemSK _)).run shared) = _
  rw [StateT.run_bind, coins]
  simp only [bind_map_left, StateT.run_bind, StateT.run_pure]

/-- Erasing the private service annotations of the logged annotated accept gives the native logged accept, with the same reply, logged entry and complete shared state. -/
theorem acceptSource_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes) (state : PqxdhRegistrationJointFinish.State KemSK) :
    (fun result => (result.1, result.2.2)) <$>
      (PqxdhDeploymentLaterServerSource.acceptSource setup codec checks seed identityIndex raw).run state =
      (acceptLogged setup codec checks seed raw).run state.2 := by
  rw [acceptLogged_run]
  have projected := PqxdhRegistrationJointServerPrefix.program_projection setup.joint seed identityIndex
    (serverAux setup codec checks) (collectLogged raw) (state.1, state.2.2.server.consumed)
  rw [prefixLogged, ← projected, bind_map_left]
  have onNative : ∀ {Value : Type} (work : NativeGame KemSK Value) (current : PqxdhRegistrationJointFinish.State KemSK),
      (PqxdhRegistrationJointFinish.onNative work).run current =
        (fun result => (result.1, (current.1, result.2))) <$> work.run current.2 := fun _ _ => rfl
  have get : ∀ current : NativeState KemSK, (nativeGet (KemSK := KemSK)).run current = pure (current.2, current) :=
    fun _ => rfl
  have prepare : (PqxdhDeploymentLaterServerSource.sourcePrepare setup codec checks seed identityIndex raw).run state =
      (fun result => (((result.1.1, result.2.2), result.1.2), (result.2.1, state.2))) <$>
        (simulateQ (PqxdhRegistrationJointServerPrefix.annotated setup.joint seed identityIndex
          (serverAux setup codec checks)) (collectLogged raw)).run (state.1, state.2.2.server.consumed) := rfl
  simp only [PqxdhDeploymentLaterServerSource.acceptSource, StateT.run_bind, onNative, get, map_pure, pure_bind,
    prepare, bind_map_left, map_bind, StateT.run_pure]

/-- The native logged handler. A raw accept runs the native logged accept and appends its entry to the log; every other source14 request runs the unchanged native source14 handler and keeps the log; the Server read returns the handler's Server seed with the current log and changes nothing. -/
noncomputable def native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) :
    QueryImpl (Spec KemSK) (StateT (PqxdhRegistrationSchedule.State KemSK × Log) ProbComp)
  | .inl (.inl (.inr (.accept raw))) => fun state =>
      (fun result => (result.1.1, (result.2, state.2 ++ [result.1.2]))) <$>
        (PqxdhRegistrationSchedule.onShared (acceptLogged setup codec checks serverSeed raw)).run state.1
  | .inl query => fun state => (fun result => (result.1, (result.2, state.2))) <$>
      (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed query).run state.1
  | .inr _ => fun state => pure ((some serverSeed, state.2), state)

/-- Every source14 request of the native logged handler projects to the native source14 handler, whatever the log. -/
theorem query_projection (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : PqxdhRegistrationSchedule.State KemSK) (log : Log) :
    (fun result => (result.1, result.2.1)) <$> (native setup codec checks serverSeed (.inl query)).run (state, log) =
      (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed query).run state := by
  rcases query with (coin | request) | read
  case inl.inr =>
    cases request
    case accept raw =>
      change (fun result => (result.1, result.2.1)) <$> ((fun result => (result.1.1, (result.2, log ++ [result.1.2]))) <$>
        (PqxdhRegistrationSchedule.onShared (acceptLogged setup codec checks serverSeed raw)).run state) =
          (PqxdhRegistrationSchedule.onShared (nativeAccept setup codec checks serverSeed
            PqxdhRegistrationSchedule.observationScalar raw)).run state
      rw [Functor.map_map, PqxdhRegistrationSchedule.onShared_run, PqxdhRegistrationSchedule.onShared_run,
        show nativeAccept setup codec checks serverSeed PqxdhRegistrationSchedule.observationScalar raw state.shared =
          (nativeAccept setup codec checks serverSeed PqxdhRegistrationSchedule.observationScalar raw).run state.shared
          from rfl, ← acceptLogged_fst, Functor.map_map, Functor.map_map]
      rfl
    all_goals simp only [native, StateT.run, Functor.map_map]; exact id_map _
  all_goals simp only [native, StateT.run, Functor.map_map]; exact id_map _

/-- Every source14 program, run by the native logged handler from any log, projects to its native source14 execution with the same result and complete native state. -/
theorem program_projection (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (state : PqxdhRegistrationSchedule.State KemSK) (log : Log) :
    (fun result => (result.1, result.2.1)) <$>
      (simulateQ (native setup codec checks serverSeed) (simulateQ embed program)).run (state, log) =
      (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed) program).run state := by
  induction program using OracleComp.inductionOn generalizing state log with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, embed, StateT.run_bind, map_bind]
    rw [← query_projection setup codec checks serverSeed query state log, bind_map_left]
    apply bind_congr
    intro result
    exact ih result.1 result.2.1 result.2.2

/-- A source14 request other than a raw accept runs the native source14 handler and keeps the log. -/
theorem query_quiet (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (notAccept : sourceKind (KemSK := KemSK) query ≠ .inl 3) (state : PqxdhRegistrationSchedule.State KemSK)
    (log : Log) :
    (native setup codec checks serverSeed (.inl query)).run (state, log) =
      (fun result => (result.1, (result.2, log))) <$>
        (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed query).run state := by
  rcases query with (coin | request) | read
  case inl.inr =>
    cases request
    case accept raw => exact absurd rfl notAccept
    all_goals rfl
  all_goals rfl

/-- A source14 program that issues no raw accept runs, under the native logged handler, as its native source14 execution and keeps the log. -/
theorem program_quiet (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (noAccept : program.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = .inl 3) 0)
    (state : PqxdhRegistrationSchedule.State KemSK) (log : Log) :
    (simulateQ (native setup codec checks serverSeed) (simulateQ embed program)).run (state, log) =
      (fun result => (result.1, (result.2, log))) <$>
        (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed) program).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at noAccept
    obtain ⟨allowed, rest⟩ := noAccept
    have notAccept : sourceKind (KemSK := KemSK) query ≠ .inl 3 := by
      rcases allowed with free | impossible
      · exact free
      · omega
    simp only [simulateQ_bind, simulateQ_spec_query, embed, StateT.run_bind, map_bind]
    rw [query_quiet setup codec checks serverSeed query notAccept state log, bind_map_left]
    apply bind_congr
    intro result
    have next := rest result.1
    simp only [notAccept, ite_false] at next
    exact ih result.1 next result.2

/-- A source14 request of source kind `.inl 3` is a raw accept. -/
theorem kind_accept (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (kind : sourceKind (KemSK := KemSK) query = .inl 3) : ∃ raw, query = .inl (.inr (.accept raw)) := by
  rcases query with (coin | request) | read
  · simp [sourceKind, PqxdhRegistrationSchedule.sourceKind] at kind
  · cases request <;> simp_all [sourceKind, PqxdhRegistrationSchedule.sourceKind]
  · simp [sourceKind] at kind

/-- A source14 request other than a raw accept runs the unchanged annotated source14 step in the logged annotated source and keeps the log. -/
theorem source_quiet (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (notAccept : sourceKind (KemSK := KemSK) query ≠ .inl 3) (state : PqxdhRegistrationJointSchedule.State KemSK)
    (log : Log) :
    (PqxdhDeploymentLaterServerSource.source setup codec checks seed identityIndex (.inl query)).run (state, log) =
      (fun result => (result.1, (result.2, log))) <$>
        (PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex query).run state := by
  rcases query with (coin | request) | read
  case inl.inr =>
    cases request
    case accept raw => exact absurd rfl notAccept
    all_goals rfl
  all_goals rfl

/-- Erasing the private service annotations of one logged annotated step gives the native logged step with the same reply and log; for the Server read this needs the Server-slot invariant, under which both return the Server's actual seed. -/
theorem query_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (query : (Spec KemSK).Domain)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (log : Log)
    (owned : PqxdhRegistrationJointServerSchedule.Owned seed identityIndex state) :
    (fun result => (result.1, (PqxdhRegistrationJointSchedule.source result.2.1, result.2.2))) <$>
      (PqxdhDeploymentLaterServerSource.source setup codec checks seed identityIndex query).run (state, log) =
      (native setup codec checks seed query).run (PqxdhRegistrationJointSchedule.source state, log) := by
  rcases query with query | later
  · by_cases accept : ∃ raw, query = .inl (.inr (.accept raw))
    · obtain ⟨raw, rfl⟩ := accept
      change (fun result => (result.1, (PqxdhRegistrationJointSchedule.source result.2.1, result.2.2))) <$>
          ((fun result => (result.1.1, (result.2, log ++ [result.1.2]))) <$>
            (PqxdhRegistrationJointServerSchedule.onBackend (PqxdhDeploymentLaterServerSource.acceptSource setup codec
              checks seed identityIndex raw)).run state) =
        (fun result => (result.1.1, (result.2, log ++ [result.1.2]))) <$>
          (PqxdhRegistrationSchedule.onShared (acceptLogged setup codec checks seed raw)).run
            (PqxdhRegistrationJointSchedule.source state)
      rw [PqxdhRegistrationSchedule.onShared_run,
        show acceptLogged setup codec checks seed raw (PqxdhRegistrationJointSchedule.source state).shared =
          (acceptLogged setup codec checks seed raw).run state.shared from rfl,
        ← acceptSource_native setup codec checks seed identityIndex raw (state.pool, state.shared)]
      simp only [PqxdhRegistrationJointServerSchedule.onBackend, StateT.run, Functor.map_map]
      rfl
    · have notAccept : sourceKind (KemSK := KemSK) query ≠ .inl 3 := fun kind => by
        obtain ⟨raw, same⟩ := kind_accept query kind
        exact accept ⟨raw, by simpa using same⟩
      rw [source_quiet setup codec checks seed identityIndex query notAccept state log,
        query_quiet setup codec checks seed query notAccept, Functor.map_map,
        ← PqxdhRegistrationJointServerSchedule.query_native setup codec checks seed identityIndex query state,
        Functor.map_map]
  · simp only [PqxdhDeploymentLaterServerSource.source, native, PqxdhRegistrationJointServerSchedule.onBackend,
      PqxdhRegistrationJointFinish.onPool, PqxdhLiveKemBirth.impl, PqxdhDynamicIdentityPool.lazyImpl,
      PqxdhDynamicIdentityPool.poolImpl, StateT.run, map_pure, owned.2]
    rfl

/-- Erasing the private service annotations of the logged annotated execution of any logged program, from a state with the Server-slot invariant, gives its native logged execution with the same result and log. -/
theorem program_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (program : OracleComp (Spec KemSK) Result)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (log : Log)
    (owned : PqxdhRegistrationJointServerSchedule.Owned seed identityIndex state) :
    (fun result => (result.1, (PqxdhRegistrationJointSchedule.source result.2.1, result.2.2))) <$>
      (simulateQ (PqxdhDeploymentLaterServerSource.source setup codec checks seed identityIndex) program).run
        (state, log) =
      (simulateQ (native setup codec checks seed) program).run (PqxdhRegistrationJointSchedule.source state, log) := by
  induction program using OracleComp.inductionOn generalizing state log with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [← query_native setup codec checks seed identityIndex query state log owned, bind_map_left]
    apply bind_congr_of_forall_mem_support
    intro result member
    exact ih result.1 result.2.1 result.2.2
      (PqxdhDeploymentLaterServerSource.query_owned setup codec checks seed identityIndex query state log result owned
        member)

/-- The native logged initialized execution: the actual Server constructor at the given identity index, then the native logged handler at the constructed Server's seed from the initial native state and the empty log. The final log is returned beside the native outcome. -/
noncomputable def initialized (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (Spec KemSK) Result) :
    StateT A ProbComp (Option (PqxdhRegistrationJointInitializedSchedule.NativeOutcome KemSK Result × Log)) :=
  fun runtime => do
  let born ← (PqxdhLiveServerConstruction.construct setup.joint ensureInit identityIndex setup.serverKeyId
    supplied).run runtime
  match born.1 with
  | none => pure (none, born.2)
  | some created =>
    (fun result => (some ((PqxdhRegistrationJointServerBirth.encode created, result.1, result.2.1), result.2.2),
      born.2)) <$>
      (simulateQ (native setup codec checks created.seed) program).run (PqxdhRegistrationSchedule.initial created, [])

/-- Erasing the private service annotations of the logged initialized source gives the native logged initialized execution at the identity index of the starting pool, with the same constructor, outcome, final native state and final log. -/
theorem initialized_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (program : OracleComp (Spec KemSK) Result)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A) :
    (fun result => (result.1.map fun outcome =>
        (PqxdhRegistrationJointInitializedSchedule.eraseOutcome outcome.1, outcome.2), result.2.2)) <$>
      (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit supplied program).run state =
      (initialized setup codec checks ensureInit state.1.1.seeds.length supplied program).run state.2 := by
  simp only [PqxdhDeploymentLaterServerSource.initialized, initialized, PqxdhRegistrationJointServerBirth.source,
    StateT.run, map_bind, bind_map_left]
  apply bind_congr_of_forall_mem_support
  rintro ⟨(_ | created), runtime⟩ member
  · rfl
  · have born : (some created, (PqxdhRegistrationJointServerBirth.install created state.1, runtime)) ∈
        support ((PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId supplied).run
          state) := by
      simp only [PqxdhRegistrationJointServerBirth.source, StateT.run, support_map]
      exact ⟨_, member, rfl⟩
    have owned : PqxdhRegistrationJointServerSchedule.Owned created.seed created.server.server.metadata.identityIndex
        (PqxdhRegistrationJointSchedule.initial (PqxdhRegistrationJointServerBirth.install created state.1)
          (PqxdhRegistrationSchedule.initial created).shared) :=
      ⟨by simp [PqxdhRegistrationJointSchedule.Invariant, PqxdhRegistrationJointSchedule.initial],
        PqxdhRegistrationJointServerBirth.source_owned setup.joint ensureInit setup.serverKeyId supplied state _ created
          born⟩
    have erased := program_native setup codec checks created.seed created.server.server.metadata.identityIndex program
      (PqxdhRegistrationJointSchedule.initial (PqxdhRegistrationJointServerBirth.install created state.1)
        (PqxdhRegistrationSchedule.initial created).shared) [] owned
    have start : PqxdhRegistrationJointSchedule.source (PqxdhRegistrationJointSchedule.initial
        (PqxdhRegistrationJointServerBirth.install created state.1) (PqxdhRegistrationSchedule.initial created).shared) =
        PqxdhRegistrationSchedule.initial (KemSK := KemSK) created := rfl
    rw [start] at erased
    simp only [StateT.run] at erased
    simp only [Option.map_some, Functor.map_map]
    rw [← erased, Functor.map_map]
    rfl

/-- One step of the native logged handler grows the log by as many entries as it advances the Server's session counter (the first conjunct, which `program_log` sums along a run). More precisely, either the step appends exactly one entry and advances the counter by one, which is the case of a raw accept (by CE-9's `nativeAccept_session`), or it keeps both the log and the counter, which is the case of every other request, the Server read included (by CE-9's `native_sessions`). -/
theorem step_log (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (query : (Spec KemSK).Domain) (state : PqxdhRegistrationSchedule.State KemSK)
    (log : Log) (result : (Spec KemSK).Range query × (PqxdhRegistrationSchedule.State KemSK × Log))
    (supported : result ∈ support ((native setup codec checks serverSeed query).run (state, log))) :
    result.2.2.length + state.shared.2.sessions = log.length + result.2.1.shared.2.sessions ∧
      ((∃ entry, result.2.2 = log ++ [entry] ∧ result.2.1.shared.2.sessions = state.shared.2.sessions + 1) ∨
        (result.2.2 = log ∧ result.2.1.shared.2.sessions = state.shared.2.sessions)) := by
  rcases query with query | later
  · by_cases accept : ∃ raw, query = .inl (.inr (.accept raw))
    · obtain ⟨raw, rfl⟩ := accept
      change result ∈ support ((fun result => (result.1.1, (result.2, log ++ [result.1.2]))) <$>
        (PqxdhRegistrationSchedule.onShared (acceptLogged setup codec checks serverSeed raw)).run state) at supported
      rw [support_map, PqxdhRegistrationSchedule.onShared_run, support_map] at supported
      obtain ⟨_, ⟨inner, member, rfl⟩, rfl⟩ := supported
      have native : (inner.1.1, inner.2) ∈ support ((nativeAccept setup codec checks serverSeed
          PqxdhRegistrationSchedule.observationScalar raw).run state.shared) := by
        rw [← acceptLogged_fst, support_map]
        exact ⟨inner, member, rfl⟩
      have sessions := (PqxdhDeploymentRegistrationTrace.nativeAccept_session setup codec checks serverSeed raw
        state.shared _ native).1
      change inner.2.2.sessions = state.shared.2.sessions + 1 at sessions
      refine ⟨?_, Or.inl ⟨inner.1.2, rfl, sessions⟩⟩
      change (log ++ [inner.1.2]).length + state.shared.2.sessions = log.length + inner.2.2.sessions
      rw [List.length_append, List.length_singleton]
      omega
    · have notAccept : sourceKind (KemSK := KemSK) query ≠ .inl 3 := fun kind => by
        obtain ⟨raw, same⟩ := kind_accept query kind
        exact accept ⟨raw, same⟩
      rw [query_quiet setup codec checks serverSeed query notAccept, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      have sessions := PqxdhDeploymentRegistrationTrace.native_sessions setup codec checks serverSeed query
        (fun raw same => accept ⟨raw, same⟩) state inner member
      refine ⟨?_, Or.inr ⟨rfl, sessions⟩⟩
      change log.length + state.shared.2.sessions = log.length + inner.2.shared.2.sessions
      rw [sessions]
  · simp only [native, StateT.run, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩

/-- Along every execution of the native logged handler, the log grows by exactly as many entries as the Server's session counter advances. With `step_log`, by which a step appends an entry exactly when it advances the counter by one (a raw accept) and otherwise keeps both, it follows informally, by induction along the execution, that from the initial state and the empty log entry `j` of the final log is the one appended by the raw accept that advanced the counter from `j` to `j + 1`, that is, the accept that allocated session index `j`; that positional correspondence is not itself stated as a theorem. -/
theorem program_log (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (program : OracleComp (Spec KemSK) Result)
    (state : PqxdhRegistrationSchedule.State KemSK) (log : Log)
    (result : Result × (PqxdhRegistrationSchedule.State KemSK × Log))
    (supported : result ∈ support ((simulateQ (native setup codec checks serverSeed) program).run (state, log))) :
    result.2.2.length + state.shared.2.sessions = log.length + result.2.1.shared.2.sessions := by
  induction program using OracleComp.inductionOn generalizing state log with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, first, second⟩ := supported
    have step := (step_log setup codec checks serverSeed query state log middle first).1
    have rest := ih middle.1 middle.2.1 middle.2.2 second
    omega

end BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.prefixLogged_fst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.prefixLogged_fst

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.acceptLogged_fst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.acceptLogged_fst

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.acceptLogged_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.acceptLogged_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.acceptSource_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.acceptSource_native

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.query_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.query_projection

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.program_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.program_projection

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.query_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.query_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.program_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.program_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.kind_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.kind_accept

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.source_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.source_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.query_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.query_native

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.program_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.program_native

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.initialized_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.initialized_native

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.step_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.step_log

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.program_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative.program_log
