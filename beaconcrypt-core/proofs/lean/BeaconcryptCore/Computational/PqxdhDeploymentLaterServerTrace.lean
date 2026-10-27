-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompileBudget
import BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBridge

/-! LQ-F: the bundle-to-pool invariant of CE-9 and GoodKem over the logged run. Two facts of the annotated execution that the per-target KEM transfer needs are carried from source14 programs to programs of the logged source. First, GoodKem: every annotated source14 step other than a KEM-field read keeps the private KEM pool free of disclosures, whatever the identity pool holds (`kem_step`, with `prefix_kem` and `accept_kem` for the raw accept), the Server read keeps the KEM pool (`later_kem`), so a logged program with no KEM-field read, such as the compiled LQ-F program (`LaterServerCompileBudget.compile_server_no_kem`), ends its logged initialized execution, and that of its tagged form, with no KEM creation index disclosed (`kem_run`, `kem_initialized`, `goodKem_later`), although the Server read discloses the Server's identity seed. Second, the registration trace: the logging interpreter of CE-9 is extended to the logged source, where the Server read logs nothing (`recordLater`, `logImpl`, `traceFrom`, with `traceFrom_erase`, `traceFrom_embed` and `traceFrom_prefix`), the raw-accept tag of the logged source records the selected logged accept (`tag_traced`, with `tag_map` and the scan facts), and the run invariant `RegistrationTrace.Traced` holds at the end of every logged initialized execution of a traced program from an empty KEM pool (`traced_source`): source14 steps keep it by CE-9's `traced_step` through the projection of the logged source, and the Server read keeps it because it changes no seed, KEM key, owner or shared state (`later_frame`, `traced_frame`). Finally the log of the traced compiled LQ-F program is the registrations of its final transcript (`compiled_server_trace`): its run part is traced by `snap_compiled_traceFrom` (CE-9's `compiled_traceFrom` for the compiler with the finish pre-read), and the terminal reads, the Server read and the post part log nothing. Only native semantics are used: no codec law, no assumption and no advantage term. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity PqxdhJointGapDh
open PqxdhDeploymentQuiet (kemReveal)
open PqxdhDeploymentLaterServerSource (Log Spec embed)
open PqxdhDeploymentLaterServerReserve (laterKind)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
open PqxdhDeploymentRegistrationTrace (Logged record acceptsOf Traced)
open PqxdhDeploymentLaterServerCommands (Cut scan tag tagFinish)
open PqxdhRegistrationJointAcceptCutTag (Tag)
open PqxdhDeploymentInterface (FullSpec ModeSpec Mode FreshBounds asModeO queryClass)
open PqxdhDeploymentSecrecy (Ledger ledgerImpl wrap)
open PqxdhDeploymentCompile (Local compileImpl)
open PqxdhDeploymentCompileBudget (commandKind cost unit)
open PqxdhDeploymentCompileSecrecy (wrapCost)
open PqxdhDeploymentLater (Snap PostSpec postEmbed finishOwner)
open PqxdhDeploymentLaterCompile (compileSnapImpl terminal laterCost)
open PqxdhDeploymentKemTransfer (regOf registrations)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Result Next : Type}

/-- The private KEM pool has recorded no disclosure. -/
def KemQuiet (pool : PqxdhRegistrationJointPreparation.Pool KemSK) : Prop :=
  pool.2.transcript.any kemReveal = false

/-- The Server's raw-accept prefix keeps the private KEM pool. -/
theorem prefix_kem (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes)
    (start : PqxdhRegistrationJointServerPrefix.State KemSK (List Pqxdh.Bytes))
    (reached : Option (PqxdhServerRootPreparation.Inputs Reader ScalarBytes PqxdhBeaconPhase2Preparation.Word32) ×
      PqxdhRegistrationJointServerPrefix.State KemSK (List Pqxdh.Bytes))
    (member : reached ∈ support ((simulateQ (PqxdhRegistrationJointServerPrefix.annotated setup.joint seed identityIndex
      (serverAux setup codec checks)) (PqxdhServerRootPreparation.collect raw)).run start)) :
    reached.2.1.2 = start.1.2 := by
  refine OracleComp.simulateQ_run_preserves_inv_of_query (spec' := unifSpec) _
    (fun current => current.1.2 = start.1.2) ?_ _ start rfl reached member
  intro query current same after step
  cases query with
  | staticDh input =>
      simp only [PqxdhRegistrationJointServerPrefix.annotated, PqxdhServerStaticDhSource.nativeImpl, StateT.run_bind,
        mem_support_bind_iff] at step
      obtain ⟨_, visited, rfl⟩ := step
      change _ ∈ support (pure _ : ProbComp _) at visited
      rw [support_pure, Set.mem_singleton_iff] at visited
      subst visited
      exact same
  | _ =>
      rw [PqxdhDeploymentQuiet.onAux_pool _ current after step]
      exact same

/-- The Server's annotated raw accept keeps the private KEM pool free of disclosures. -/
theorem accept_kem (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes)
    (state : PqxdhRegistrationJointFinish.State KemSK) (quiet : KemQuiet state.1) (result : Option Nat ×
      PqxdhRegistrationJointFinish.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationJointServerAccept.source setup codec checks seed identityIndex
      raw).run state)) :
    KemQuiet result.2.1 := by
  simp only [PqxdhRegistrationJointServerAccept.source, PqxdhRegistrationJointServerAccept.run, StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨⟨_, afterGet⟩, getMember, ⟨collected, afterPrepare⟩, prepareMember, tailMember⟩ := supported
  simp only [PqxdhRegistrationJointFinish.onNative, StateT.run, support_map, Set.mem_image] at getMember tailMember
  obtain ⟨_, _, getEq⟩ := getMember
  obtain ⟨_, _, rfl⟩ := tailMember
  simp only [Prod.mk.injEq] at getEq
  obtain ⟨_, rfl⟩ := getEq
  simp only [PqxdhRegistrationJointServerAccept.sourcePrepare, StateT.run, support_map, Set.mem_image] at prepareMember
  obtain ⟨reached, reachedMember, same⟩ := prepareMember
  simp only [Prod.mk.injEq] at same
  obtain ⟨_, rfl⟩ := same
  unfold KemQuiet
  rw [prefix_kem setup codec checks seed identityIndex raw _ reached reachedMember]
  exact quiet

/-- Every annotated source14 step other than a KEM-field read keeps the private KEM pool free of disclosures, whatever the identity pool holds. -/
theorem kem_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (notKem : sourceKind (KemSK := KemSK) query ≠ .inr 1) (state : PqxdhRegistrationJointSchedule.State KemSK)
    (quiet : KemQuiet state.pool)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex
      query).run state)) :
    KemQuiet result.2.pool := by
  have sharedQuiet : ∀ {Value : Type} (work : NativeGame KemSK Value)
      (reached : Value × PqxdhRegistrationJointSchedule.State KemSK),
      reached ∈ support ((PqxdhRegistrationJointSchedule.onShared work).run state) → KemQuiet reached.2.pool := by
    intro Value work reached member
    simp only [PqxdhRegistrationJointSchedule.onShared, StateT.run, support_map, Set.mem_image] at member
    obtain ⟨_, _, rfl⟩ := member
    exact quiet
  rcases query with request | ⟨index, field⟩
  · rcases request with coin | command
    · simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
        PqxdhRegistrationJointSchedule.handler, StateT.run_lift, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at supported
      obtain ⟨_, _, rfl⟩ := supported
      exact quiet
    · cases command with
      | create pin keyId =>
          simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
            PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.create, StateT.run, support_map,
            Set.mem_image] at supported
          obtain ⟨material, _, rfl⟩ := supported
          unfold KemQuiet at quiet ⊢
          simp [PqxdhRegistrationJointSchedule.created, PqxdhRegistrationJointCreation.serviceView,
            PqxdhLiveKemBirth.created, PqxdhLiveKemBirth.record, kemReveal, quiet]
      | bundle address =>
          simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
            PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.bundle, StateT.run] at supported
          split at supported
          · simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            exact quiet
          · simp only [support_map, Set.mem_image] at supported
            obtain ⟨_, _, rfl⟩ := supported
            exact quiet
      | accept raw =>
          simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointServerSchedule.onBackend,
            StateT.run, support_map, Set.mem_image] at supported
          obtain ⟨accepted, acceptedMember, rfl⟩ := supported
          exact accept_kem setup codec checks seed identityIndex raw (state.pool, state.shared) quiet accepted
            acceptedMember
      | build session payload => exact sharedQuiet _ result supported
      | finish address raw =>
          simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
            PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.finish, StateT.run] at supported
          split at supported
          · simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            exact quiet
          · rename_i entry _
            simp only [support_map, Set.mem_image] at supported
            obtain ⟨finished, finishedMember, rfl⟩ := supported
            refine OracleComp.simulateQ_run_preserves_inv_of_query (spec' := unifSpec) _
              (fun current => KemQuiet current.1) ?_ _ (state.pool, state.shared) quiet finished finishedMember
            intro query current currentQuiet reached member
            rcases query with query | query
            · simp only [PqxdhRegistrationJointFinish.annotated, PqxdhRegistrationJointFinish.onPool, StateT.run,
                support_map, Set.mem_image] at member
              obtain ⟨inner, innerMember, rfl⟩ := member
              cases query with
              | decapsulate ciphertext key =>
                  simp only [PqxdhRegistrationJointPreparation.annotated, support_map, Set.mem_image] at innerMember
                  obtain ⟨_, _, rfl⟩ := innerMember
                  unfold KemQuiet at currentQuiet ⊢
                  simp [PqxdhLiveKemBirth.record, kemReveal, currentQuiet]
              | dhIdentity seed point =>
                  simp only [PqxdhRegistrationJointPreparation.annotated, support_pure, Set.mem_singleton_iff]
                    at innerMember
                  subst innerMember
                  exact currentQuiet
              | _ =>
                  simp only [PqxdhRegistrationJointPreparation.annotated, support_map, Set.mem_image] at innerMember
                  obtain ⟨_, _, rfl⟩ := innerMember
                  exact currentQuiet
            · simp only [PqxdhRegistrationJointFinish.annotated, PqxdhRegistrationJointFinish.onNative, StateT.run,
                support_map, Set.mem_image] at member
              obtain ⟨_, _, rfl⟩ := member
              exact currentQuiet
      | hmac key message => exact sharedQuiet _ result supported
      | hash bytes => exact sharedQuiet _ result supported
      | reveal keyId => exact sharedQuiet _ result supported
  · simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source, StateT.run,
      support_pure, Set.mem_singleton_iff] at supported
    subst supported
    simp only [PqxdhRegistrationJointLiveRead.sourceStep]
    split
    · exact quiet
    · cases field with
      | identity => exact quiet
      | kem => exact absurd rfl notKem
      | prekey => exact quiet
      | oneTime => exact quiet
      | kernel => exact quiet

/-- The Server read records only its identity-pool observation: the private KEM pool is kept, in every state. -/
theorem later_kem (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (state : PqxdhRegistrationJointSchedule.State KemSK) (log : Log)
    (result : PqxdhDeploymentLaterServerSource.Reveal × (PqxdhRegistrationJointSchedule.State KemSK × Log))
    (reached : result ∈ support ((PqxdhDeploymentLaterServerSource.source setup codec checks seed identityIndex
      (.inr ())).run (state, log))) :
    result.2.1.pool.2 = state.pool.2 := by
  simp only [PqxdhDeploymentLaterServerSource.source, PqxdhRegistrationJointServerSchedule.onBackend,
    PqxdhRegistrationJointFinish.onPool, PqxdhLiveKemBirth.impl, PqxdhDynamicIdentityPool.lazyImpl,
    PqxdhDynamicIdentityPool.poolImpl, StateT.run, support_map, Set.mem_image] at reached
  obtain ⟨_, ⟨_, ⟨_, ⟨_, reached, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := reached
  simp only [support_pure, Set.mem_singleton_iff] at reached
  subst reached
  rfl

/-- Every logged step other than a KEM-field read keeps the private KEM pool free of disclosures. -/
theorem kem_later_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (query : (Spec KemSK).Domain)
    (notKem : laterKind (KemSK := KemSK) query ≠ some (.inr 1)) (state : PqxdhRegistrationJointSchedule.State KemSK)
    (log : Log) (quiet : KemQuiet state.pool)
    (result : (Spec KemSK).Range query × (PqxdhRegistrationJointSchedule.State KemSK × Log))
    (supported : result ∈ support ((PqxdhDeploymentLaterServerSource.source setup codec checks seed identityIndex
      query).run (state, log))) :
    KemQuiet result.2.1.pool := by
  cases query with
  | inl query =>
    have projected : (result.1, result.2.1) ∈ support
        ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex query).run state) := by
      rw [← PqxdhDeploymentLaterServerSource.query_projection setup codec checks seed identityIndex query state log,
        support_map]
      exact Set.mem_image_of_mem _ supported
    exact kem_step setup codec checks seed identityIndex query (fun same => notKem (by simp [laterKind, same])) state
      quiet _ projected
  | inr read =>
    unfold KemQuiet
    rw [later_kem setup codec checks seed identityIndex state log result supported]
    exact quiet

/-- A logged program with no KEM-field read keeps the private KEM pool free of disclosures along its whole logged annotated execution. -/
theorem kem_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (program : OracleComp (Spec KemSK) Result)
    (noKem : program.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = some (.inr 1)) 0)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (log : Log) (quiet : KemQuiet state.pool)
    (result : Result × (PqxdhRegistrationJointSchedule.State KemSK × Log))
    (supported : result ∈ support ((simulateQ (PqxdhDeploymentLaterServerSource.source setup codec checks seed
      identityIndex) program).run (state, log))) :
    KemQuiet result.2.1.pool := by
  induction program using OracleComp.inductionOn generalizing state log with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact quiet
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at noKem
    obtain ⟨allowed, rest⟩ := noKem
    have notKem : laterKind (KemSK := KemSK) query ≠ some (.inr 1) := by
      rcases allowed with free | impossible
      · exact free
      · omega
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, first, second⟩ := supported
    have next := rest middle.1
    rw [ite_eq_right notKem] at next
    exact ih middle.1 next middle.2.1 middle.2.2
      (kem_later_step setup codec checks seed identityIndex query notKem state log quiet middle first) second

/-- In every completed logged initialized execution from a KEM pool with no disclosure, of a logged program with no KEM-field read, the final KEM pool has no disclosure. -/
theorem kem_initialized (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (program : OracleComp (Spec KemSK) Result)
    (noKem : program.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = some (.inr 1)) 0)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A) (quiet : KemQuiet state.1)
    (result : Option (PqxdhRegistrationJointInitializedSchedule.SourceOutcome KemSK Result × Log) ×
      PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : result ∈ support ((PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit supplied
      program).run state)) :
    KemQuiet result.2.1 := by
  simp only [PqxdhDeploymentLaterServerSource.initialized, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨born, bornMember, supported⟩ := supported
  have bornQuiet : KemQuiet born.2.1 := by
    simp only [PqxdhRegistrationJointServerBirth.source, StateT.run, support_map, Set.mem_image] at bornMember
    obtain ⟨constructed, _, rfl⟩ := bornMember
    rcases constructed with ⟨_ | created, runtime⟩
    · exact quiet
    · exact quiet
  rcases born with ⟨_ | created, after⟩
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact bornQuiet
  · simp only [support_map, Set.mem_image] at supported
    obtain ⟨executed, executedMember, rfl⟩ := supported
    exact kem_run setup codec checks created.seed _ program noKem _ [] bornQuiet executed executedMember

/-- A KEM pool with no disclosure has disclosed no creation index. -/
theorem goodKem_of_kem {count : Nat} (kemIndex : Fin count)
    (final : PqxdhRegistrationJointKemRawBridge.Final KemSK A X) (quiet : KemQuiet final.2.1) :
    PqxdhRegistrationJointKemRawBridge.GoodKem kemIndex final := by
  unfold PqxdhRegistrationJointKemRawBridge.GoodKem
  rw [List.any_eq_false]
  intro observation member disclosed
  have revealed : kemReveal observation = true := by
    rcases observation with ⟨query, answer⟩
    cases query <;> simp_all [PqxdhDynamicKemStopping.disclosed, kemReveal]
  have none := List.any_eq_false.mp quiet observation member
  exact none revealed

/-- GoodKem for the logged source: in the logged initialized execution of the tagged form of any logged program with no KEM-field read, from the empty pools and with the log forgotten and the outcome encoded, no KEM creation index is ever disclosed. The Server read discloses the Server's identity seed but no KEM key. -/
theorem goodKem_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (work : OracleComp (Spec KemSK) X)
    (noKem : work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = some (.inr 1)) 0) (index : Nat)
    (runtime : A) {count : Nat} (kemIndex : Fin count)
    (final : PqxdhRegistrationJointKemRawBridge.Final KemSK A X)
    (supported : final ∈ support ((fun result => (result.1.map fun outcome =>
        PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup outcome.1, result.2)) <$>
      (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit supplied
        (PqxdhDeploymentLaterServerCommands.tag work index)).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))) :
    PqxdhRegistrationJointKemRawBridge.GoodKem kemIndex final := by
  rw [support_map] at supported
  obtain ⟨result, member, rfl⟩ := supported
  apply goodKem_of_kem
  exact kem_initialized setup codec checks ensureInit supplied _
    (PqxdhDeploymentLaterServerBridge.tag_bound work index _ 0 noKem) _
    (by unfold KemQuiet; rfl) result member

/-- Append the registration reply of one logged-source request to a log: a source14 request as in the registration trace of CE-9, and the Server read nothing. -/
def recordLater : (query : (Spec KemSK).Domain) → (Spec KemSK).Range query → List Logged → List Logged
  | .inl query, reply, log => record query reply log
  | .inr _, _, log => log

/-- The logging interpreter for logged-source programs: every request is forwarded once and unchanged, and its registration reply is appended to the log. -/
def logImpl : QueryImpl (Spec KemSK) (StateT (List Logged) (OracleComp (Spec KemSK))) := fun query log =>
  (fun reply => (reply, recordLater query reply log)) <$> ((Spec KemSK).query query : OracleComp (Spec KemSK) _)

/-- A logged-source program run under the logging interpreter from a starting log. It issues exactly the program's requests. -/
def traceFrom (program : OracleComp (Spec KemSK) Result) (log : List Logged) :
    OracleComp (Spec KemSK) (Result × List Logged) :=
  (simulateQ logImpl program).run log

/-- A traced request is the request itself followed by the traced continuation from the extended log. -/
theorem traceFrom_query_bind (query : (Spec KemSK).Domain)
    (next : (Spec KemSK).Range query → OracleComp (Spec KemSK) Result) (log : List Logged) :
    traceFrom (((Spec KemSK).query query : OracleComp (Spec KemSK) _) >>= next) log =
      ((Spec KemSK).query query : OracleComp (Spec KemSK) _) >>= fun reply =>
        traceFrom (next reply) (recordLater query reply log) := by
  simp only [traceFrom, simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
    StateT.run]
  rfl

/-- Forgetting the log gives back the program. -/
theorem traceFrom_erase (program : OracleComp (Spec KemSK) Result) (log : List Logged) :
    Prod.fst <$> traceFrom program log = program := by
  induction program using OracleComp.inductionOn generalizing log with
  | pure value => simp [traceFrom]
  | query_bind query next ih =>
    rw [traceFrom_query_bind, map_bind]
    simp only [ih]

/-- A traced bind is the traced first program followed by the traced continuation from the reached log. -/
theorem traceFrom_bind (program : OracleComp (Spec KemSK) Result) (next : Result → OracleComp (Spec KemSK) Next)
    (log : List Logged) :
    traceFrom (program >>= next) log = traceFrom program log >>= fun reached => traceFrom (next reached.1) reached.2 := by
  simp only [traceFrom, simulateQ_bind, StateT.run_bind]

/-- Tracing an embedded source14 program is embedding its registration trace. -/
theorem traceFrom_embed (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (log : List Logged) :
    traceFrom (simulateQ embed program) log =
      simulateQ embed (PqxdhDeploymentRegistrationTrace.traceFrom program log) := by
  induction program using OracleComp.inductionOn generalizing log with
  | pure value => simp [traceFrom, PqxdhDeploymentRegistrationTrace.traceFrom]
  | query_bind query next ih =>
    rw [PqxdhDeploymentRegistrationTrace.traceFrom_query_bind, simulateQ_bind, simulateQ_spec_query]
    simp only [simulateQ_bind, simulateQ_spec_query, embed]
    rw [traceFrom_query_bind]
    exact bind_congr fun reply => ih reply _

/-- A result of a traced program, without its log, is a result of the program. -/
theorem traceFrom_support (program : OracleComp (Spec KemSK) Result) (log : List Logged)
    (outcome : Result × List Logged) (reached : outcome ∈ support (traceFrom program log)) :
    outcome.1 ∈ support program := by
  rw [← traceFrom_erase program log, support_map]
  exact ⟨outcome, reached, rfl⟩

/-- The log of a traced run extends its starting log. -/
theorem traceFrom_prefix (program : OracleComp (Spec KemSK) Result) (log : List Logged)
    (outcome : Result × List Logged) (reached : outcome ∈ support (traceFrom program log)) : log <+: outcome.2 := by
  induction program using OracleComp.inductionOn generalizing log with
  | pure value =>
    simp only [traceFrom, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
    subst reached
    exact List.prefix_refl _
  | query_bind query next ih =>
    rw [traceFrom_query_bind, mem_support_bind_iff] at reached
    obtain ⟨reply, _, reached⟩ := reached
    refine List.IsPrefix.trans ?_ (ih reply (recordLater query reply log) reached)
    rcases query with ((coin | request) | read) | later
    · exact List.prefix_refl _
    · cases request with
      | accept raw => exact List.prefix_append _ _
      | bundle owner => exact List.prefix_append _ _
      | _ => exact List.prefix_refl _
    · exact List.prefix_refl _
    · exact List.prefix_refl _

/-- A request other than a raw accept adds no accept to the log. -/
theorem acceptsOf_other (query : (Spec KemSK).Domain) (other : ∀ raw, query ≠ .inl (.inl (.inr (.accept raw))))
    (reply : (Spec KemSK).Range query) (log : List Logged) : acceptsOf (recordLater query reply log) = acceptsOf log := by
  rcases query with query | later
  · exact PqxdhDeploymentRegistrationTrace.acceptsOf_record_other query (fun raw same => other raw (by rw [same]))
      reply log
  · rfl

/-- The tag of a finished logged program records nothing. -/
theorem tag_pure (value : Result) (index : Nat) :
    tag (pure value : OracleComp (Spec KemSK) Result) index = pure (value, none) := rfl

/-- At the selected ordinal the tag issues the accept and records its bytes and reply. -/
theorem tag_accept_zero (raw : Pqxdh.Bytes) (next : Option Nat → OracleComp (Spec KemSK) Result) :
    tag (((Spec KemSK).query (.inl (.inl (.inr (.accept raw)))) : OracleComp (Spec KemSK) _) >>= next) 0 =
      ((Spec KemSK).query (.inl (.inl (.inr (.accept raw)))) : OracleComp (Spec KemSK) _) >>= fun answer =>
        (fun result => (result, some (raw, answer))) <$> next answer := by
  simp only [tag]
  rfl

/-- Before the selected ordinal an accept is forwarded and the ordinal decreases. -/
theorem tag_accept_succ (raw : Pqxdh.Bytes) (next : Option Nat → OracleComp (Spec KemSK) Result) (index : Nat) :
    tag (((Spec KemSK).query (.inl (.inl (.inr (.accept raw)))) : OracleComp (Spec KemSK) _) >>= next) (index + 1) =
      ((Spec KemSK).query (.inl (.inl (.inr (.accept raw)))) : OracleComp (Spec KemSK) _) >>= fun answer =>
        tag (next answer) index := by
  simp only [tag]
  rfl

/-- A request other than a raw accept is forwarded by the tag without moving the ordinal. -/
theorem tag_other (query : (Spec KemSK).Domain) (other : ∀ raw, query ≠ .inl (.inl (.inr (.accept raw))))
    (next : (Spec KemSK).Range query → OracleComp (Spec KemSK) Result) (index : Nat) :
    tag (((Spec KemSK).query query : OracleComp (Spec KemSK) _) >>= next) index =
      ((Spec KemSK).query query : OracleComp (Spec KemSK) _) >>= fun answer => tag (next answer) index := by
  have scanned : scan (((Spec KemSK).query query : OracleComp (Spec KemSK) _) >>= next) index =
      ((Spec KemSK).query query : OracleComp (Spec KemSK) _) >>= fun answer => scan (next answer) index := by
    rcases query with ((coin | request) | read) | later
    · rfl
    · cases request with
      | accept raw => exact absurd rfl (other raw)
      | _ => rfl
    · rfl
    · rfl
  simp only [tag, scanned, bind_assoc]

/-- Tagging commutes with a map of the program's result. -/
theorem tag_map (f : Result → Next) (program : OracleComp (Spec KemSK) Result) (index : Nat) :
    tag (f <$> program) index = (fun outcome => (f outcome.1, outcome.2)) <$> tag program index := by
  induction program using OracleComp.inductionOn generalizing index with
  | pure value => simp only [map_pure, tag_pure]
  | query_bind query next ih =>
    rw [map_bind]
    by_cases accept : ∃ raw, query = .inl (.inl (.inr (.accept raw)))
    · obtain ⟨raw, rfl⟩ := accept
      cases index with
      | zero => simp only [tag_accept_zero, map_bind, Functor.map_map]
      | succ index => simp only [tag_accept_succ, map_bind, ih]
    · have other : ∀ raw, query ≠ .inl (.inl (.inr (.accept raw))) := fun raw same => accept ⟨raw, same⟩
      simp only [tag_other query other, map_bind, ih]

/-- The tag of a traced run records the accept at the selected raw-accept ordinal of the log. -/
theorem tag_traceFrom (program : OracleComp (Spec KemSK) Result) (log : List Logged) (index : Nat)
    (outcome : (Result × List Logged) × Tag) (reached : outcome ∈ support (tag (traceFrom program log) index)) :
    outcome.2 = (acceptsOf outcome.1.2)[(acceptsOf log).length + index]? := by
  induction program using OracleComp.inductionOn generalizing log index with
  | pure value =>
    simp only [traceFrom, simulateQ_pure, StateT.run_pure, tag_pure, support_pure, Set.mem_singleton_iff] at reached
    subst reached
    simp
  | query_bind query next ih =>
    rw [traceFrom_query_bind] at reached
    by_cases accept : ∃ raw, query = .inl (.inl (.inr (.accept raw)))
    · obtain ⟨raw, rfl⟩ := accept
      cases index with
      | zero =>
        rw [tag_accept_zero, mem_support_bind_iff] at reached
        obtain ⟨answer, _, reached⟩ := reached
        rw [support_map] at reached
        obtain ⟨result, member, rfl⟩ := reached
        obtain ⟨rest, same⟩ := traceFrom_prefix _ _ result member
        simp only [recordLater, record] at same
        simp only [← same, acceptsOf, List.filterMap_append, List.append_assoc, Nat.add_zero]
        simp
      | succ index =>
        rw [tag_accept_succ, mem_support_bind_iff] at reached
        obtain ⟨answer, _, reached⟩ := reached
        rw [ih answer _ index reached]
        congr 1
        simp only [recordLater, record, acceptsOf, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
          List.length_append, List.length_singleton]
        omega
    · have other : ∀ raw, query ≠ .inl (.inl (.inr (.accept raw))) := fun raw same => accept ⟨raw, same⟩
      rw [tag_other query other, mem_support_bind_iff] at reached
      obtain ⟨answer, _, reached⟩ := reached
      rw [ih answer (recordLater query answer log) index reached, acceptsOf_other query other]

/-- The tag of a logged program traced from the empty log records its logged accept at the selected raw-accept ordinal. -/
theorem tag_traced (program : OracleComp (Spec KemSK) Result) (index : Nat) (outcome : (Result × List Logged) × Tag)
    (reached : outcome ∈ support (tag (traceFrom program []) index)) :
    outcome.2 = (acceptsOf outcome.1.2)[index]? := by
  simpa [acceptsOf] using tag_traceFrom program [] index outcome reached

/-- The Server read, in every state, keeps every seed, KEM key, owner and shared state. -/
theorem later_frame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (state : PqxdhRegistrationJointSchedule.State KemSK) (log : Log)
    (result : PqxdhDeploymentLaterServerSource.Reveal × (PqxdhRegistrationJointSchedule.State KemSK × Log))
    (reached : result ∈ support ((PqxdhDeploymentLaterServerSource.source setup codec checks seed identityIndex
      (.inr ())).run (state, log))) :
    result.2.1.pool.1.seeds = state.pool.1.seeds ∧ result.2.1.pool.2 = state.pool.2 ∧
      result.2.1.owners = state.owners ∧ result.2.1.shared = state.shared := by
  simp only [PqxdhDeploymentLaterServerSource.source, PqxdhRegistrationJointServerSchedule.onBackend,
    PqxdhRegistrationJointFinish.onPool, PqxdhLiveKemBirth.impl, PqxdhDynamicIdentityPool.lazyImpl,
    PqxdhDynamicIdentityPool.poolImpl, StateT.run, support_map, Set.mem_image] at reached
  obtain ⟨_, ⟨_, ⟨_, ⟨_, reached, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := reached
  simp only [support_pure, Set.mem_singleton_iff] at reached
  subst reached
  simp [PqxdhDynamicIdentityPool.record]

/-- The bundle-to-pool run invariant of CE-9 depends only on the Server's session counter, the seeds, the KEM pool and the owners: it survives any change that keeps them (the identity-pool transcript and the rest of the shared state may change). -/
theorem traced_frame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (log : List Logged) (state after : PqxdhRegistrationJointSchedule.State KemSK)
    (traced : Traced setup codec checks log state) (seeds : after.pool.1.seeds = state.pool.1.seeds)
    (keys : after.pool.2 = state.pool.2) (owners : after.owners = state.owners)
    (counter : after.shared.2.sessions = state.shared.2.sessions) :
    Traced setup codec checks log after := by
  obtain ⟨sessions, positional, verified, bundles, kem, owned⟩ := traced
  refine ⟨by rw [counter]; exact sessions, positional, verified, fun k bytes member => ?_, ?_, ?_⟩
  · obtain ⟨identity, tuple, s1, s2, s3, written, pooled⟩ := bundles k bytes member
    exact ⟨identity, tuple, s1, s2, s3, written, by rw [keys]; exact pooled⟩
  · obtain ⟨length, index⟩ := kem
    exact ⟨by rw [keys, owners]; exact length, by rw [owners]; exact index⟩
  · intro entry member
    rw [owners] at member
    exact PqxdhRegistrationJointOwnership.owned_slots state.pool after.pool entry seeds (by rw [keys])
      (owned entry member)

/-- One logged annotated step keeps the invariant, with its registration reply appended to the log. -/
theorem traced_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (query : (Spec KemSK).Domain) (log : List Logged)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (ephemerals : Log) (traced : Traced setup codec checks log state)
    (result : (Spec KemSK).Range query × (PqxdhRegistrationJointSchedule.State KemSK × Log))
    (supported : result ∈ support ((PqxdhDeploymentLaterServerSource.source setup codec checks seed identityIndex
      query).run (state, ephemerals))) :
    Traced setup codec checks (recordLater query result.1 log) result.2.1 := by
  cases query with
  | inl query =>
    have projected : (result.1, result.2.1) ∈ support
        ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex query).run state) := by
      rw [← PqxdhDeploymentLaterServerSource.query_projection setup codec checks seed identityIndex query state
        ephemerals, support_map]
      exact Set.mem_image_of_mem _ supported
    exact PqxdhDeploymentRegistrationTrace.traced_step setup codec checks seed identityIndex query log state traced
      (result.1, result.2.1) projected
  | inr read =>
    obtain ⟨seeds, keys, owners, shared⟩ := later_frame setup codec checks seed identityIndex state ephemerals result
      supported
    exact traced_frame setup codec checks log state result.2.1 traced seeds keys owners (by rw [shared])

/-- The logged annotated execution of a traced logged program keeps the invariant from any start. -/
theorem traced_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (program : OracleComp (Spec KemSK) Result) (log : List Logged)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (ephemerals : Log) (traced : Traced setup codec checks log state)
    (result : (Result × List Logged) × (PqxdhRegistrationJointSchedule.State KemSK × Log))
    (supported : result ∈ support ((simulateQ (PqxdhDeploymentLaterServerSource.source setup codec checks seed
      identityIndex) (traceFrom program log)).run (state, ephemerals))) :
    Traced setup codec checks result.1.2 result.2.1 := by
  induction program using OracleComp.inductionOn generalizing log state ephemerals with
  | pure value =>
    simp only [traceFrom, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact traced
  | query_bind query next ih =>
    rw [traceFrom_query_bind] at supported
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨reply, middle⟩, first, second⟩ := supported
    exact ih reply (recordLater query reply log) middle.1 middle.2
      (traced_step setup codec checks seed identityIndex query log state ephemerals traced (reply, middle) first) second

/-- Every completed logged initialized execution of a traced logged program from an empty KEM pool ends with the invariant on its final log and final source state, whose pool is the execution's final pool. -/
theorem traced_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (program : OracleComp (Spec KemSK) Result)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A) (empty : state.1.2.keys = [])
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (outcome : PqxdhRegistrationJointInitializedSchedule.SourceOutcome KemSK (Result × List Logged) × Log)
    (supported : (some outcome, after) ∈ support ((PqxdhDeploymentLaterServerSource.initialized setup codec checks
      ensureInit supplied (traceFrom program [])).run state)) :
    Traced setup codec checks outcome.1.2.1.2 outcome.1.2.2 ∧ after.1 = outcome.1.2.2.pool := by
  simp only [PqxdhDeploymentLaterServerSource.initialized, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨⟨_ | created, bornState⟩, born, reached⟩ := supported
  · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at reached
  · simp only [support_map, Set.mem_image, Prod.mk.injEq, Option.some.injEq] at reached
    obtain ⟨finished, member, rfl, rfl⟩ := reached
    have bornKeys : bornState.1.2.keys = [] := by
      simp only [PqxdhRegistrationJointServerBirth.source, StateT.run, support_map, Set.mem_image] at born
      obtain ⟨constructed, _, same⟩ := born
      simp only [Prod.mk.injEq] at same
      obtain ⟨wasCreated, rfl⟩ := same
      rw [wasCreated]
      simp only [PqxdhRegistrationJointServerBirth.install]
      exact empty
    have start : Traced setup codec checks [] (PqxdhRegistrationJointSchedule.initial bornState.1
        (PqxdhRegistrationSchedule.initial created).shared) :=
      ⟨rfl, fun _ _ _ found => by simp [acceptsOf] at found, fun _ _ member => by simp [acceptsOf] at member,
        fun _ _ member => by simp at member,
        ⟨by simp [PqxdhRegistrationJointSchedule.initial, bornKeys], fun _ _ found => by
          simp [PqxdhRegistrationJointSchedule.initial] at found⟩,
        PqxdhRegistrationJointSchedule.initial_owned _ _⟩
    exact ⟨traced_run setup codec checks created.seed _ program [] _ [] start finished member, rfl⟩

/-- The logged initialized execution of a mapped program is the execution of the program with its result mapped. -/
theorem source_map (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (f : Result → Next)
    (program : OracleComp (Spec KemSK) Result) (state : PqxdhRegistrationJointServerPrefix.State KemSK A) :
    (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit supplied (f <$> program)).run state =
      (fun result => (result.1.map fun outcome => ((outcome.1.1, f outcome.1.2.1, outcome.1.2.2), outcome.2),
        result.2)) <$>
        (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit supplied program).run state := by
  simp only [PqxdhDeploymentLaterServerSource.initialized, StateT.run, map_bind]
  apply bind_congr
  rintro ⟨_ | created, after⟩
  · simp
  · simp only [simulateQ_map]
    change _ <$> (f <$> _ : StateT _ ProbComp _).run _ = _
    rw [StateT.run_map, Functor.map_map, Functor.map_map]
    rfl

/-- The result of a completed logged initialized execution is a result of the program. -/
theorem source_support (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (program : OracleComp (Spec KemSK) Result)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A) (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (outcome : PqxdhRegistrationJointInitializedSchedule.SourceOutcome KemSK Result × Log)
    (supported : (some outcome, after) ∈ support ((PqxdhDeploymentLaterServerSource.initialized setup codec checks
      ensureInit supplied program).run state)) :
    outcome.1.2.1 ∈ support program := by
  simp only [PqxdhDeploymentLaterServerSource.initialized, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨⟨_ | created, born⟩, _, reached⟩ := supported
  · simp at reached
  · simp only [support_map, Set.mem_image, Prod.mk.injEq, Option.some.injEq] at reached
    obtain ⟨finished, member, rfl, _⟩ := reached
    apply support_simulateQ_run'_subset (PqxdhDeploymentLaterServerSource.source setup codec checks created.seed
      created.server.server.metadata.identityIndex) program _
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ member

/-- Source bundle calls of the compiled secrecy-layer step of a query with the finish pre-read: none unless the query is a bundle command. -/
theorem snap_bundle_cost (bounds : FreshBounds) (kind : Fin 14) (other : kind ≠ 2) :
    (∑ core, laterCost (.inl 2) core * wrapCost bounds core kind) = 0 := by
  fin_cases kind <;> simp_all [Fin.sum_univ_succ, laterCost, cost, unit, wrapCost]

/-- Source raw accepts of the compiled secrecy-layer step of a query with the finish pre-read: none unless the query is an accept command. -/
theorem snap_accept_cost (bounds : FreshBounds) (kind : Fin 14) (other : kind ≠ 3) :
    (∑ core, laterCost (.inl 3) core * wrapCost bounds core kind) = 0 := by
  fin_cases kind <;> simp_all [Fin.sum_univ_succ, laterCost, cost, unit, wrapCost]

/-- One complete-interface query through the secrecy layer and the compiler with the finish pre-read, traced: the transcript gains exactly the query with its reply, and the log gains exactly that entry's registration reply. -/
theorem snap_step_trace (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (query : PqxdhDeploymentInterface.Query)
    (ledger : Ledger) (held : Snap × Local) (log : List Logged)
    (outcome : ((FullSpec.Range query × Ledger) × (Snap × Local)) × List Logged)
    (reached : outcome ∈ support (PqxdhDeploymentRegistrationTrace.traceFrom ((simulateQ (compileSnapImpl setup codec route)
      ((ledgerImpl setup.source.crypto codec setup.serverKeyId bounds query).run ledger)).run held) log)) :
    outcome.1.1.2.transcript = ledger.transcript ++ [⟨query, outcome.1.1.1⟩] ∧
      outcome.2 = log ++ (regOf ⟨query, outcome.1.1.1⟩).toList := by
  have compiled := PqxdhDeploymentRegistrationTrace.traceFrom_support _ log outcome reached
  have layered : outcome.1.1 ∈ support ((ledgerImpl setup.source.crypto codec setup.serverKeyId bounds query).run
      ledger) := by
    apply support_simulateQ_run'_subset (compileSnapImpl setup codec route) _ held
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ compiled
  have transcript : outcome.1.1.2.transcript = ledger.transcript ++ [⟨query, outcome.1.1.1⟩] := by
    rcases query with request | secrecy
    · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, support_map] at layered
      obtain ⟨reply, _, same⟩ := layered
      rw [← same]
      rfl
    · exact PqxdhDeploymentEligibility.ledger_secrecy setup.source.crypto codec setup.serverKeyId bounds secrecy ledger
        outcome.1.1 layered
  refine ⟨transcript, ?_⟩
  have quietBundle := FinitePartitionQueryBounds.weighted_bound commandKind (laterCost (.inl 2))
    (fun core => wrapCost bounds core (queryClass query)) (compileSnapImpl setup codec route)
    (fun request => sourceKind (KemSK := KemSK) request = .inl 2)
    ((ledgerImpl setup.source.crypto codec setup.serverKeyId bounds query).run ledger)
    (fun core => PqxdhDeploymentCompileSecrecy.wrap_step setup.source.crypto codec setup.serverKeyId bounds core query
      ledger)
    (fun request state => PqxdhDeploymentLaterCompile.snap_step_bound setup codec route (.inl 2) request state) held
  have quietAccept := FinitePartitionQueryBounds.weighted_bound commandKind (laterCost (.inl 3))
    (fun core => wrapCost bounds core (queryClass query)) (compileSnapImpl setup codec route)
    (fun request => sourceKind (KemSK := KemSK) request = .inl 3)
    ((ledgerImpl setup.source.crypto codec setup.serverKeyId bounds query).run ledger)
    (fun core => PqxdhDeploymentCompileSecrecy.wrap_step setup.source.crypto codec setup.serverKeyId bounds core query
      ledger)
    (fun request state => PqxdhDeploymentLaterCompile.snap_step_bound setup codec route (.inl 3) request state) held
  by_cases accept : ∃ raw, query = .inl (.inr (.accept raw))
  · obtain ⟨raw, rfl⟩ := accept
    have program : (compileSnapImpl setup codec route (.inr (.accept raw))).run held =
        (fun answer => (answer, (held.1, { held.2 with log := (PqxdhDeploymentCompile.logReply held.2.log (.accept raw)
          answer) }))) <$> ((PqxdhRegistrationJointRevealSchedule.Spec KemSK).query (.inl (.inr (.accept raw))) :
            OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) _) := by
      simp only [compileSnapImpl, finishOwner, PqxdhDeploymentLaterCompile.preRead, compileImpl,
        PqxdhDeploymentCompile.forwardLogged, PqxdhDeploymentCompile.forward, StateT.run, pure_bind, bind_assoc,
        map_eq_bind_pure_comp]
      rfl
    rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map, program,
      Functor.map_map, PqxdhDeploymentKemTransfer.traceFrom_map, PqxdhDeploymentKemTransfer.traceFrom_query,
      Functor.map_map, support_map] at reached
    obtain ⟨reply, _, rfl⟩ := reached
    rfl
  · by_cases bundle : ∃ owner, query = .inl (.inr (.bundle owner))
    · obtain ⟨owner, rfl⟩ := bundle
      have program : (compileSnapImpl setup codec route (.inr (.bundle owner))).run held =
          (fun answer => (answer, (held.1, { held.2 with log := (PqxdhDeploymentCompile.logReply held.2.log
            (.bundle owner) answer) }))) <$> ((PqxdhRegistrationJointRevealSchedule.Spec KemSK).query
              (.inl (.inr (.bundle owner))) : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) _) := by
        simp only [compileSnapImpl, finishOwner, PqxdhDeploymentLaterCompile.preRead, compileImpl,
          PqxdhDeploymentCompile.forwardLogged, PqxdhDeploymentCompile.forward, StateT.run, pure_bind, bind_assoc,
          map_eq_bind_pure_comp]
        rfl
      rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map, program,
        Functor.map_map, PqxdhDeploymentKemTransfer.traceFrom_map, PqxdhDeploymentKemTransfer.traceFrom_query,
        Functor.map_map, support_map] at reached
      obtain ⟨reply, _, rfl⟩ := reached
      rfl
    · have notAccept : queryClass query ≠ 3 := by
        intro same
        rcases query with ((coin | command) | secrecy)
        · cases same
        · cases command <;> first | exact accept ⟨_, rfl⟩ | cases same
        · rcases secrecy with ⟨_, _, _⟩ | ⟨_, _⟩ <;> cases same
      have notBundle : queryClass query ≠ 2 := by
        intro same
        rcases query with ((coin | command) | secrecy)
        · cases same
        · cases command <;> first | exact bundle ⟨_, rfl⟩ | cases same
        · rcases secrecy with ⟨_, _, _⟩ | ⟨_, _⟩ <;> cases same
      rw [snap_bundle_cost bounds _ notBundle] at quietBundle
      rw [snap_accept_cost bounds _ notAccept] at quietAccept
      have kept := PqxdhDeploymentKemTransfer.traceFrom_quiet _ quietBundle quietAccept log outcome reached
      have none : regOf ⟨query, outcome.1.1.1⟩ = none := by
        rcases query with ((coin | command) | secrecy)
        · rfl
        · cases command with
          | accept raw => exact absurd ⟨raw, rfl⟩ accept
          | bundle owner => exact absurd ⟨owner, rfl⟩ bundle
          | _ => rfl
        · rfl
      rw [kept, none, Option.toList_none, List.append_nil]

/-- In every outcome of the traced compiled secrecy-layer run with the finish pre-read of a complete-interface program, started from a log equal to the registrations of the starting transcript, the final log is the registrations of the final transcript. -/
theorem snap_compiled_traceFrom (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (program : OracleComp FullSpec Result)
    (ledger : Ledger) (held : Snap × Local) (log : List Logged) (synced : log = registrations ledger.transcript)
    (outcome : ((Result × Ledger) × (Snap × Local)) × List Logged)
    (reached : outcome ∈ support (PqxdhDeploymentRegistrationTrace.traceFrom ((simulateQ (compileSnapImpl setup codec
      route) ((simulateQ (ledgerImpl setup.source.crypto codec setup.serverKeyId bounds) program).run ledger)).run held)
        log)) :
    outcome.2 = registrations outcome.1.1.2.transcript := by
  induction program using OracleComp.inductionOn generalizing ledger held log with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, PqxdhDeploymentRegistrationTrace.traceFrom, support_pure,
      Set.mem_singleton_iff] at reached
    subst reached
    exact synced
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, PqxdhDeploymentKemTransfer.traceFrom_bind, mem_support_bind_iff] at reached
    obtain ⟨middle, first, second⟩ := reached
    obtain ⟨transcript, logged⟩ := snap_step_trace setup codec route bounds query ledger held log middle first
    exact ih middle.1.1.1 middle.1.1.2 middle.1.2 middle.2
      (by rw [logged, transcript, PqxdhDeploymentKemTransfer.registrations_append, synced]) second

/-- A traced embedded source14 program that issues no bundle call and no raw accept keeps its log. -/
theorem embed_quiet (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (noBundle : program.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = .inl 2) 0)
    (noAccept : program.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = .inl 3) 0) (log : List Logged)
    (outcome : Result × List Logged) (reached : outcome ∈ support (traceFrom (simulateQ embed program) log)) :
    outcome.2 = log := by
  rw [traceFrom_embed] at reached
  exact PqxdhDeploymentKemTransfer.traceFrom_quiet program noBundle noAccept log outcome
    (PqxdhDeploymentLaterServerCompileBudget.embed_support _ outcome reached)

/-- The log of the traced compiled LQ-F program is the registrations of its final transcript: the run part logs the registration replies of its transcript, and the terminal reads, the Server read and the post part log nothing. -/
theorem compiled_server_trace (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Result)
    (outcome : (Result × (Ledger × (Snap × Local))) × List Logged)
    (reached : outcome ∈ support (traceFrom (PqxdhDeploymentLaterServerCompile.compileServer setup codec route bounds
      mode first second) [])) :
    outcome.2 = registrations outcome.1.2.1.transcript := by
  simp only [PqxdhDeploymentLaterServerCompile.compileServer, traceFrom_bind, mem_support_bind_iff] at reached
  obtain ⟨run, runMember, beacons, beaconsMember, server, serverMember, post, postMember, final⟩ := reached
  have runLog : run.2 = registrations run.1.1.2.transcript := by
    rw [traceFrom_embed] at runMember
    exact snap_compiled_traceFrom setup codec route bounds (asModeO mode first) Ledger.empty (Snap.empty, Local.empty) []
      rfl run (PqxdhDeploymentLaterServerCompileBudget.embed_support _ run runMember)
  have beaconsLog : beacons.2 = run.2 := by
    refine embed_quiet _ ?_ ?_ run.2 beacons beaconsMember
    · simpa [PqxdhDeploymentLaterCompile.readCost, unit] using
        PqxdhDeploymentLaterCompile.terminal_bound (KemSK := KemSK) (.inl 2) run.1.2.1
          (List.range run.1.2.2.log.owners.length)
    · exact PqxdhDeploymentLaterServerCompile.terminal_quiet _ _
  have serverLog : server.2 = beacons.2 := by
    have single : traceFrom (((PqxdhDeploymentLaterServerSource.Spec KemSK).query (.inr ()) :
        OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) _)) beacons.2 =
        (fun reply => (reply, beacons.2)) <$> ((PqxdhDeploymentLaterServerSource.Spec KemSK).query (.inr ()) :
          OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) _) := by
      have bound := traceFrom_query_bind (.inr ()) (fun reply =>
        (pure reply : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) _)) beacons.2
      simp only [bind_pure] at bound
      rw [bound]
      simp only [traceFrom, simulateQ_pure, StateT.run_pure, bind_pure_comp]
      rfl
    rw [single, support_map] at serverMember
    obtain ⟨_, _, rfl⟩ := serverMember
    rfl
  have postLog : post.2 = server.2 := by
    refine embed_quiet _ ?_ ?_ server.2 post postMember
    · rw [← QueryImpl.simulateQ_compose]
      refine PqxdhDeploymentCompileSecrecy.simulate_zero ((compileImpl setup codec route) ∘ₛ postEmbed) _
        (fun query state => ?_) _ run.1.2.2
      rcases query with coin | (⟨key, message⟩ | bytes)
      · simp only [QueryImpl.apply_compose, postEmbed, simulateQ_spec_query]
        simpa [commandKind, cost, unit] using
          PqxdhDeploymentCompileBudget.step_bound setup codec route (.inl 2) (.inl coin) state
      · simp only [QueryImpl.apply_compose, postEmbed, simulateQ_spec_query]
        simpa [commandKind, cost, unit] using
          PqxdhDeploymentCompileBudget.step_bound setup codec route (.inl 2) (.inr (.hmac key message)) state
      · simp only [QueryImpl.apply_compose, postEmbed, simulateQ_spec_query]
        simpa [commandKind, cost, unit] using
          PqxdhDeploymentCompileBudget.step_bound setup codec route (.inl 2) (.inr (.hash bytes)) state
    · exact PqxdhDeploymentLaterServerCompile.post_quiet setup codec route _ _
  simp only [traceFrom, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at final
  subst final
  simp only [postLog, serverLog, beaconsLog, runLog]

end BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.prefix_kem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.prefix_kem

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.accept_kem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.accept_kem

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.kem_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.kem_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.later_kem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.later_kem

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.kem_later_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.kem_later_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.kem_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.kem_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.kem_initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.kem_initialized

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.goodKem_of_kem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.goodKem_of_kem

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.goodKem_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.goodKem_later

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.traceFrom_query_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.traceFrom_query_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.traceFrom_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.traceFrom_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.traceFrom_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.traceFrom_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.traceFrom_embed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.traceFrom_embed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.traceFrom_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.traceFrom_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.traceFrom_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.traceFrom_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.acceptsOf_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.acceptsOf_other

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.tag_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.tag_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.tag_accept_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.tag_accept_zero

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.tag_accept_succ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.tag_accept_succ

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.tag_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.tag_other

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.tag_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.tag_map

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.tag_traceFrom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.tag_traceFrom

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.tag_traced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.tag_traced

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.later_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.later_frame

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.traced_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.traced_frame

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.traced_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.traced_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.traced_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.traced_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.traced_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.traced_source

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.source_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.source_map

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.source_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.source_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.snap_bundle_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.snap_bundle_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.snap_accept_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.snap_accept_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.snap_step_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.snap_step_trace

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.snap_compiled_traceFrom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.snap_compiled_traceFrom

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.embed_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.embed_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.compiled_server_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace.compiled_server_trace
