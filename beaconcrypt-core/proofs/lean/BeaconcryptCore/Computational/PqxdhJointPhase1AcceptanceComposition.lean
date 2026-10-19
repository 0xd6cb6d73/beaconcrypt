import BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter

/-!
# One source writer followed by actual optional acceptance

The actual generated-identity source interpreter creates index zero, executes setup,
the source-ordered writer, arbitrary candidate selection and attached verification.
Setup and selection have checked zero signing/creation caps. Their actual DH, reveal,
coin and candidate interactions remain in the same full private state. Changed fields
accepted under that still-fresh identity reduce to one explicit joint weak-EUF game.
Native generation/serialization/publication and root/global composition remain separate.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
open PqxdhDynamicIdentityPool PqxdhDynamicIdentityRouting PqxdhDynamicIdentityReports
open PqxdhJointPhase1Reports PqxdhPhase1AcceptanceOracle PqxdhJointPhase1SourceWriter

/-- Actual source signing attempts, including an unavailable identity handle. Acceptance requests do not themselves sign. -/
def IsSigning : SourceSpec.Domain → Prop
  | .inl query => dynamicClass (IsClass .sign) query
  | .inr _ => False
instance : DecidablePred IsSigning := fun query => by
  cases query <;> dsimp [IsSigning] <;> infer_instance

/-- A non-signing source request can add real DH/reveal observations without changing any identity's signed-message history. -/
theorem historyUpdate_noSign (count : ℕ) (index : Fin count)
    (query : DynamicSpec.Domain) (answer : DynamicSpec.Range query) (history : GlobalState count)
    (noSign : ¬ dynamicClass (IsClass .sign) query) :
    signedMessages ((historyUpdate count query answer history).histories index) =
      signedMessages (history.histories index) := by
  cases query with
  | inl coin => rfl
  | inr request =>
    cases request with
    | create => rfl
    | reveal target =>
      simp only [historyUpdate]
      split <;> cases answer <;> rfl
    | service target request =>
      cases request with
      | sign message => exact False.elim (noSign rfl)
      | staticDh peer =>
        simp only [historyUpdate]
        split
        · cases answer with
          | none => rfl
          | some reply =>
            simp only [PqxdhJointIdentityEvents.publicUpdate]
            by_cases same : index = ⟨target, by assumption⟩
            · subst index
              simp [signedMessages, requestEvent]
            · simp [Function.update_of_ne same]
        · rfl

/-- Optional acceptance, every real DH observation and all actual seed reveals preserve the message log unless the source makes a signing request. -/
theorem bare_step_noSign (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : ℕ) (index : Fin count)
    (query : SourceSpec.Domain) (state : BareState count)
    (result : SourceSpec.Range query × BareState count)
    (noSign : ¬ IsSigning query)
    (supported : result ∈ support ((bareImpl attachedVerify primitives count query).run state)) :
    signedMessages (result.2.1.histories index) = signedMessages (state.1.histories index) := by
  cases query with
  | inr candidate =>
    simp only [bareImpl, StateT.run, mem_support_pure_iff] at supported
    subst result
    rfl
  | inl request =>
    change result ∈ support ((sourceWithHistory count (lazyImpl primitives) request).run state) at supported
    rw [sourceWithHistory_run] at supported
    obtain ⟨reply, _, final⟩ := (mem_support_bind_iff _ _ _).mp supported
    obtain rfl := eq_of_mem_support_pure _ final
    exact historyUpdate_noSign count index request reply.1 state.1 noSign

/-- A checked zero-signing query budget preserves the complete prior signing-message log through every adaptive reply, while the actual other state and effects still execute. -/
theorem bare_run_noSign (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : ℕ) (index : Fin count) {Result : Type}
    (client : OracleComp SourceSpec Result) (noSign : client.IsQueryBoundP IsSigning 0)
    (state : BareState count) (result : Result × BareState count)
    (supported : result ∈ support ((simulateQ (bareImpl attachedVerify primitives count) client).run state)) :
    signedMessages (result.2.1.histories index) = signedMessages (state.1.histories index) := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    rfl
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at noSign
    have excluded : ¬ IsSigning query := noSign.1.resolve_right (by omega)
    change result ∈ support ((bareImpl attachedVerify primitives count query).run state >>= fun reply =>
      (simulateQ (bareImpl attachedVerify primitives count) (next reply.1)).run reply.2) at supported
    obtain ⟨reply, step, rest⟩ := (mem_support_bind_iff _ _ _).mp supported
    have nextBound := noSign.2 reply.1
    simp only [excluded, ite_false] at nextBound
    exact (ih reply.1 nextBound reply.2 result rest).trans
      (bare_step_noSign attachedVerify primitives count index query state reply excluded step)


/-- Every actual optional source query extends the private created prefix; no identity is overwritten by a later creation or accepted/rejected candidate. -/
theorem bare_step_seed_extension (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : ℕ) (query : SourceSpec.Domain) (state : BareState count)
    (result : SourceSpec.Range query × BareState count)
    (supported : result ∈ support ((bareImpl attachedVerify primitives count query).run state)) :
    ∃ appended, result.2.2.seeds = state.2.seeds ++ appended := by
  cases query with
  | inr candidate =>
    simp only [bareImpl, StateT.run, mem_support_pure_iff] at supported
    subst result
    exact ⟨[], by simp⟩
  | inl request =>
    change result ∈ support ((sourceWithHistory count (lazyImpl primitives) request).run state) at supported
    rw [sourceWithHistory_run] at supported
    obtain ⟨reply, actual, final⟩ := (mem_support_bind_iff _ _ _).mp supported
    obtain rfl := eq_of_mem_support_pure _ final
    obtain ⟨appended, extended, _⟩ := lazyImpl_seed_extension primitives request state.2 reply actual
    exact ⟨appended, extended⟩

/-- An already-created handle keeps the same private seed through every optional source reply; this is an index fact, not public-key injectivity. -/
theorem bare_step_created (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count index : ℕ) (seed : IdentitySeed)
    (query : SourceSpec.Domain) (state : BareState count) (result : SourceSpec.Range query × BareState count)
    (created : state.2.seeds[index]? = some seed)
    (supported : result ∈ support ((bareImpl attachedVerify primitives count query).run state)) :
    result.2.2.seeds[index]? = some seed := by
  obtain ⟨appended, extended⟩ := bare_step_seed_extension attachedVerify primitives count query state result supported
  have earlier : index < state.2.seeds.length := by
    by_contra absent
    have none := List.getElem?_eq_none (Nat.le_of_not_gt absent)
    rw [none] at created
    cases created
  rw [extended, List.getElem?_append_left earlier, created]

/-- Arbitrary adaptive service, creation, reveal and acceptance continuations retain the same generated-index seed, including after an actual reveal. -/
theorem bare_run_created (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count index : ℕ) (seed : IdentitySeed) {Result : Type}
    (client : OracleComp SourceSpec Result) (state : BareState count)
    (created : state.2.seeds[index]? = some seed) (result : Result × BareState count)
    (supported : result ∈ support ((simulateQ (bareImpl attachedVerify primitives count) client).run state)) :
    result.2.2.seeds[index]? = some seed := by
  exact OracleComp.simulateQ_run_preserves_inv_of_query (bareImpl attachedVerify primitives count)
    (fun state => state.2.seeds[index]? = some seed)
    (fun query state retained result supported =>
      bare_step_created attachedVerify primitives count index seed query state result retained supported)
    client state created result supported

/-- Embed an unchanged identity-service request into the optional acceptance surface. -/
def dynamicToSource : QueryImpl DynamicSpec (OracleComp SourceSpec) := fun query => SourceSpec.query (.inl query)

def liftDynamic {Result : Type} (client : OracleComp DynamicSpec Result) : OracleComp SourceSpec Result :=
  simulateQ dynamicToSource client

set_option backward.isDefEq.respectTransparency false in
/-- The actual optional source interprets a lifted identity operation exactly once with the same reply and full retained state. -/
theorem bare_dynamic_compose (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : ℕ) :
    QueryImpl.compose (bareImpl attachedVerify primitives count) dynamicToSource =
      sourceWithHistory count (lazyImpl primitives) := by
  funext query
  simp only [QueryImpl.compose, dynamicToSource, simulateQ_spec_query]
  rfl

/-- The source signing block can be inserted into the optional acceptance experiment without changing any complete continuation or history. -/
theorem liftDynamic_complete (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp DynamicSpec Result) (state : BareState count) :
    (simulateQ (bareImpl attachedVerify primitives count) (liftDynamic client)).run state =
      (simulateQ (sourceWithHistory count (lazyImpl primitives)) client).run state := by
  simp only [liftDynamic, ← QueryImpl.simulateQ_compose, bare_dynamic_compose]


/-- Generate the one source-ordered signed bundle and pass its complete public fields to an adaptive candidate selector. Missing source handles stop before selection. -/
def selectedProgram (index : ℕ) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple)
    (selector : Phase1Candidate → OracleComp SourceSpec Phase1Candidate) :
    OracleComp SourceSpec (Option Phase1Candidate) := do
  let bundle ← liftDynamic (signingProgram index identity keys)
  match bundle with
  | none => pure none
  | some bundle => some <$> selector bundle

/-- The actual selector executes only after the complete source signing state is installed, retaining all its optional acceptance and joint-use effects. -/
theorem selectedProgram_complete (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count index : ℕ) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple)
    (selector : Phase1Candidate → OracleComp SourceSpec Phase1Candidate)
    (history : GlobalState count) (state : SourceState) (seed : IdentitySeed)
    (created : state.seeds[index]? = some seed) :
    (simulateQ (bareImpl attachedVerify primitives count)
      (selectedProgram index identity keys selector)).run (history, state) =
      (fun result => (some result.1, result.2)) <$>
        (simulateQ (bareImpl attachedVerify primitives count)
          (selector (signedCandidate primitives seed identity keys))).run
          (signedGlobalState primitives seed count index keys history, signedState primitives seed index keys state) := by
  simp only [selectedProgram, simulateQ_bind, StateT.run_bind, liftDynamic_complete,
    signingProgram_complete primitives count index identity keys history state seed created,
    pure_bind, simulateQ_map, StateT.run_map]

/-- A checked non-signing selector preserves the source's exact three-message signing log while still retaining all other actual requests and replies. -/
theorem selectedProgram_three_messages (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) {count : ℕ} (index : Fin count) (identity : Ed25519PublicKey)
    (keys : Phase1KeyTuple) (selector : Phase1Candidate → OracleComp SourceSpec Phase1Candidate)
    (selectorNoSign : ∀ bundle, (selector bundle).IsQueryBoundP IsSigning 0)
    (history : GlobalState count) (state : SourceState) (seed : IdentitySeed)
    (created : state.seeds[index.val]? = some seed)
    (noPriorSign : signedMessages (history.histories index) = [])
    (result : Option Phase1Candidate × BareState count)
    (supported : result ∈ support ((simulateQ (bareImpl attachedVerify primitives count)
      (selectedProgram index.val identity keys selector)).run (history, state))) :
    signedMessages (result.2.1.histories index) =
      [prekeyMessage keys.prekey, oneTimeMessage keys.oneTime, pqMessage keys.pqKey] ∧
      result.2.2.seeds[index.val]? = some seed ∧ ∃ candidate, result.1 = some candidate := by
  rw [selectedProgram_complete attachedVerify primitives count index.val identity keys selector history state seed created] at supported
  obtain ⟨selected, actual, rfl⟩ := mem_support_map_peel _ _ supported
  refine ⟨?_, ?_, ⟨selected.1, rfl⟩⟩
  · exact (bare_run_noSign attachedVerify primitives count index _ (selectorNoSign _)
      _ selected actual).trans (signedGlobalState_three_messages primitives seed index keys history noPriorSign)
  · exact bare_run_created attachedVerify primitives count index.val seed _ _ created selected actual

/-- A source-accepted changed bundle under a still-fresh created identity has an unissued original field after the actual writer and non-signing selector. No exact-log premise is assumed here. -/
theorem selectedProgram_fieldOrigin (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) {Context : Type} {count : ℕ} (index : Fin count)
    (material : Phase1Material Context) (selector : Phase1Candidate → OracleComp SourceSpec Phase1Candidate)
    (selectorNoSign : ∀ bundle, (selector bundle).IsQueryBoundP IsSigning 0)
    (history : GlobalState count) (state : SourceState) (seed : IdentitySeed)
    (created : state.seeds[index.val]? = some seed)
    (noPriorSign : signedMessages (history.histories index) = [])
    (candidate : Phase1Candidate) (finalState : BareState count)
    (supported : (some candidate, finalState) ∈ support ((simulateQ (bareImpl attachedVerify primitives count)
      (selectedProgram index.val (primitives.publicKeys seed).ed25519 material.keyTuple selector)).run (history, state)))
    (fresh : index ∉ finalState.1.reveals)
    (changed : phase1FieldSubstitutionBit primitives.verify (primitives.publicKeys seed).ed25519 material candidate = true) :
    FieldOriginFailure primitives ⟨index.val, candidate⟩ (sourceSnapshot primitives finalState) := by
  obtain ⟨messages, retained, _⟩ := selectedProgram_three_messages attachedVerify primitives index _ material.keyTuple
    selector selectorNoSign history state seed created noPriorSign _ supported
  apply singleBundle_fieldOrigin primitives ⟨index.val, candidate⟩ (sourceSnapshot primitives finalState)
    index.isLt (primitives.publicKeys seed) material
  · simp [sourceSnapshot, sourceKeys, retained]
  · exact fresh
  · exact messages
  · exact changed


/-- Public snapshots are determined by actual source replies, retaining complete private state. -/
theorem reportingImpl_snapshot (primitives : Primitives) (count : Nat)
    (query : ReportingSpec.Domain) (state : ReportingState count)
    (result : ReportingSpec.Range query × ReportingState count)
    (aligned : state.publicSnapshot = sourceSnapshot primitives state.source)
    (supported : result ∈ support ((reportingImpl primitives count query).run state)) :
    result.2.publicSnapshot = sourceSnapshot primitives result.2.source := by
  cases query with
  | inl request =>
    simp only [reportingImpl, StateT.run, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at supported
    obtain ⟨reply, actual, rfl⟩ := supported
    exact aligned ▸ (source_snapshot_step primitives count request state.source reply actual).symm
  | inr candidate =>
    rw [reportingImpl_report] at supported
    obtain rfl := OracleComp.eq_of_mem_support_pure _ supported
    exact aligned

/-- Actual private source state and public monitor stay aligned after any complete adaptive execution. -/
theorem reportingExecution_snapshot (primitives : Primitives) (count : Nat)
    {Result : Type} (client : OracleComp ReportingSpec Result)
    (state : ReportingState count)
    (aligned : state.publicSnapshot = sourceSnapshot primitives state.source) :
    ∀ result ∈ support ((simulateQ (reportingImpl primitives count) client).run state),
      result.2.publicSnapshot = sourceSnapshot primitives result.2.source := by
  apply OracleComp.simulateQ_run_preserves_inv_of_query (reportingImpl primitives count)
    (fun state => state.publicSnapshot = sourceSnapshot primitives state.source)
    _ client state aligned
  intro query before alignment result supported
  exact reportingImpl_snapshot primitives count query before result alignment supported

/-- Starting from the actual empty source, all supported full outputs have the exact reconstructed snapshot. -/
theorem reportingRun_snapshot (primitives : Primitives) (count : Nat)
    {Result : Type} (client : OracleComp ReportingSpec Result) :
    ∀ result ∈ support (reportingRun primitives count client),
      result.2.publicSnapshot = sourceSnapshot primitives result.2.source := by
  apply reportingExecution_snapshot primitives count client
  exact (initial_snapshot primitives count).symm


/-- The actual optional acceptance experiment's public field-origin monitor is the projection of its complete private source state. -/
theorem actualRun_snapshot (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (count : ℕ) {Result : Type} (client : OracleComp SourceSpec Result)
    (result : Result × CompleteState count)
    (supported : result ∈ support (actualRun attachedVerify primitives count client)) :
    result.2.1.snapshot = sourceSnapshot primitives result.2.2.source := by
  rw [actualRun_eq attachedVerify primitives adapter] at supported
  have compatible := run_compatible primitives count (instrumentedClient primitives client) result supported
  rw [run_complete] at supported
  obtain ⟨reported, actual, rfl⟩ := mem_support_map_peel _ _ supported
  exact compatible.1.trans (reportingRun_snapshot primitives count _ reported actual)


/-- Retained source execution data; the actual optional decoded input is distinct from the originally submitted candidate. -/
structure SessionResult (Context : Type) where
  index : ℕ
  publicIdentity : PublicIdentity
  material : Phase1Material Context
  candidate : Phase1Candidate
  accepted : Option AcceptedInput

/-- Source setup, three signatures, adaptive selection and actual optional acceptance run in order. Accepted attacker-owned candidates and rejection use the same interface. -/
def sessionBody {Context : Type} (index : ℕ) (publicIdentity : PublicIdentity)
    (setup : PublicIdentity → OracleComp SourceSpec (Phase1Material Context))
    (selector : Phase1Candidate → OracleComp SourceSpec Phase1Candidate) :
    OracleComp SourceSpec (Option (SessionResult Context)) := do
  let material ← setup publicIdentity
  let candidate ← selectedProgram index publicIdentity.ed25519 material.keyTuple selector
  match candidate with
  | none => pure none
  | some candidate =>
    let accepted ← SourceSpec.query (.inr ⟨index, candidate⟩)
    pure (some ⟨index, publicIdentity, material, candidate, accepted⟩)

/-- One honest created identity is sampled by the existing source interpreter, then source setup and all candidate branches execute. No honest-candidate selector premise appears. -/
def oneSession {Context : Type}
    (setup : PublicIdentity → OracleComp SourceSpec (Phase1Material Context))
    (selector : Phase1Candidate → OracleComp SourceSpec Phase1Candidate) :
    OracleComp SourceSpec (Option (SessionResult Context)) := do
  let created ← SourceSpec.query (.inl (.inr .create))
  match created with
  | none => pure none
  | some (index, publicIdentity) => sessionBody index publicIdentity setup selector

/-- Every actually selected candidate reaches the unchanged attached-verification interface and keeps its full optional reply and complete private poststate. -/
theorem sessionBody_complete {Context : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count index : ℕ) (publicIdentity : PublicIdentity)
    (setup : PublicIdentity → OracleComp SourceSpec (Phase1Material Context))
    (selector : Phase1Candidate → OracleComp SourceSpec Phase1Candidate) (state : BareState count) :
    (simulateQ (bareImpl attachedVerify primitives count) (sessionBody index publicIdentity setup selector)).run state =
      (simulateQ (bareImpl attachedVerify primitives count) (setup publicIdentity)).run state >>= fun prepared =>
        (simulateQ (bareImpl attachedVerify primitives count)
          (selectedProgram index publicIdentity.ed25519 prepared.1.keyTuple selector)).run prepared.2 >>= fun selected =>
          pure (selected.1.map (fun candidate =>
            (⟨index, publicIdentity, prepared.1, candidate, sourceAccept attachedVerify candidate⟩ : SessionResult Context)), selected.2) := by
  simp only [sessionBody, simulateQ_bind, StateT.run_bind]
  congr 1
  funext prepared
  congr 1
  funext selected
  cases selected.1 with
  | none => rfl
  | some candidate =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_pure, StateT.run_pure]
    rfl

/-- The first real source creation installs exactly the sampled seed and public index zero, retaining the actual public creation observation. -/
def singletonState (primitives : Primitives) (count : ℕ) (seed : IdentitySeed) : BareState count :=
  (PqxdhJointIdentityFreshness.initialState count,
    (createdReply primitives PqxdhDynamicIdentityPool.initialState seed).2)

set_option backward.isDefEq.respectTransparency false in
/-- A source creation preserves its full initial monitor state and installs one freshly sampled private seed. -/
theorem bare_create_initial (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : ℕ) :
    (bareImpl attachedVerify primitives count (.inl (.inr .create))).run (initialSource count) =
      (fun seed => (some (0, primitives.publicKeys seed), singletonState primitives count seed)) <$> sampleSeed := by
  change (sourceWithHistory count (lazyImpl primitives) (.inr .create)).run (initialSource count) = _
  rw [sourceWithHistory_run, lazyImpl_create]
  simp only [historyUpdate, bind_pure_comp, initialSource, createdReply,
    PqxdhDynamicIdentityPool.initialState, List.length_nil, singletonState, Functor.map_map]

set_option backward.isDefEq.respectTransparency false in
/-- The complete one-session computation samples the target seed only inside the interpreter, before its full source continuation. -/
theorem oneSession_complete {Context : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : ℕ)
    (setup : PublicIdentity → OracleComp SourceSpec (Phase1Material Context))
    (selector : Phase1Candidate → OracleComp SourceSpec Phase1Candidate) :
    bareRun attachedVerify primitives count (oneSession setup selector) = (do
      let seed ← sampleSeed
      (simulateQ (bareImpl attachedVerify primitives count)
        (sessionBody 0 (primitives.publicKeys seed) setup selector)).run (singletonState primitives count seed)) := by
  simp only [bareRun, oneSession, simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
  rw [show (PqxdhPhase1AcceptanceOracle.initialState count).2.source = initialSource count from rfl,
    bare_create_initial]
  simp only [bind_map_left]

/-- Source creation establishes index-zero ownership and an empty signing log by execution, not a target-distribution premise. -/
theorem singletonState_facts (primitives : Primitives) (count : ℕ) (seed : IdentitySeed)
    (index : Fin count) :
    (singletonState primitives count seed).2.seeds[0]? = some seed ∧
      signedMessages ((singletonState primitives count seed).1.histories index) = [] := by
  simp [singletonState, createdReply, PqxdhDynamicIdentityPool.initialState, record,
    PqxdhJointIdentityFreshness.initialState, emptyHistory, signedMessages]


/-- The actual setup/writer/selector/acceptance pipeline derives its complete final signing log and original candidate/optional response from execution. -/
theorem sessionBody_supported {Context : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) {count : ℕ} (index : Fin count) (publicIdentity : PublicIdentity)
    (setup : PublicIdentity → OracleComp SourceSpec (Phase1Material Context))
    (selector : Phase1Candidate → OracleComp SourceSpec Phase1Candidate)
    (setupNoSign : (setup publicIdentity).IsQueryBoundP IsSigning 0)
    (selectorNoSign : ∀ bundle, (selector bundle).IsQueryBoundP IsSigning 0)
    (state : BareState count) (seed : IdentitySeed) (created : state.2.seeds[index.val]? = some seed)
    (noPriorSign : signedMessages (state.1.histories index) = [])
    (result : Option (SessionResult Context) × BareState count)
    (supported : result ∈ support ((simulateQ (bareImpl attachedVerify primitives count)
      (sessionBody index.val publicIdentity setup selector)).run state)) :
    ∃ material candidate,
      result.1 = some ⟨index.val, publicIdentity, material, candidate, sourceAccept attachedVerify candidate⟩ ∧
      signedMessages (result.2.1.histories index) = honestPhase1Messages material ∧
      result.2.2.seeds[index.val]? = some seed := by
  rw [sessionBody_complete] at supported
  obtain ⟨prepared, preparation, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
  obtain ⟨selected, selection, finished⟩ := (mem_support_bind_iff _ _ _).mp supported
  obtain rfl := eq_of_mem_support_pure _ finished
  have preCreated := bare_run_created attachedVerify primitives count index.val seed _ state created prepared preparation
  have preMessages := (bare_run_noSign attachedVerify primitives count index _ setupNoSign state prepared preparation).trans noPriorSign
  obtain ⟨messages, retained, candidate, chosen⟩ := selectedProgram_three_messages attachedVerify primitives index
    publicIdentity.ed25519 prepared.1.keyTuple selector selectorNoSign prepared.2.1 prepared.2.2 seed
    preCreated preMessages selected selection
  exact ⟨prepared.1, candidate, by simp only [chosen, Option.map_some], messages, retained⟩

/-- One actual generated identity, source setup and selector establish ownership and the exact source signing policy for every supported completed candidate. -/
theorem oneSession_supported {Context : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : ℕ)
    (setup : PublicIdentity → OracleComp SourceSpec (Phase1Material Context))
    (selector : Phase1Candidate → OracleComp SourceSpec Phase1Candidate)
    (setupNoSign : ∀ publicIdentity, (setup publicIdentity).IsQueryBoundP IsSigning 0)
    (selectorNoSign : ∀ bundle, (selector bundle).IsQueryBoundP IsSigning 0)
    (result : Option (SessionResult Context) × BareState (count + 1))
    (supported : result ∈ support (bareRun attachedVerify primitives (count + 1) (oneSession setup selector))) :
    ∃ seed material candidate,
      result.1 = some ⟨0, primitives.publicKeys seed, material, candidate, sourceAccept attachedVerify candidate⟩ ∧
      signedMessages (result.2.1.histories 0) = honestPhase1Messages material ∧
      result.2.2.seeds[0]? = some seed := by
  rw [oneSession_complete] at supported
  obtain ⟨seed, _, actual⟩ := (mem_support_bind_iff _ _ _).mp supported
  obtain ⟨created, messages⟩ := singletonState_facts primitives (count + 1) seed 0
  obtain ⟨material, candidate, finished⟩ := sessionBody_supported attachedVerify primitives
    (0 : Fin (count + 1)) (primitives.publicKeys seed) setup selector (setupNoSign _) selectorNoSign
    (singletonState primitives (count + 1) seed) seed created messages result actual
  exact ⟨seed, material, candidate, finished⟩

/-- An actual completed session returns precisely the reply of its last unchanged candidate request, under any stateful interpreter. -/
theorem sessionBody_finalCandidate {Context State : Type}
    (impl : QueryImpl SourceSpec (StateT State ProbComp)) (index : ℕ) (publicIdentity : PublicIdentity)
    (setup : PublicIdentity → OracleComp SourceSpec (Phase1Material Context))
    (selector : Phase1Candidate → OracleComp SourceSpec Phase1Candidate)
    (state finalState : State) (output : SessionResult Context)
    (supported : (some output, finalState) ∈ support ((simulateQ impl
      (sessionBody index publicIdentity setup selector)).run state)) :
    ∃ before, (output.accepted, finalState) ∈ support
      ((impl (.inr ⟨output.index, output.candidate⟩)).run before) := by
  simp only [sessionBody, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨prepared, _, selected, _, finished⟩ := supported
  cases choice : selected.1 with
  | none =>
      simp only [choice, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at finished
  | some candidate =>
      simp only [choice, simulateQ_bind, StateT.run_bind, simulateQ_spec_query,
        mem_support_bind_iff, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at finished
      obtain ⟨accepted, queried, equality⟩ := finished
      cases equality
      exact ⟨selected.2, queried⟩

/-- The actual creation prefix does not change the final candidate's request or its original optional response. -/
theorem oneSession_finalCandidate {Context State : Type}
    (impl : QueryImpl SourceSpec (StateT State ProbComp))
    (setup : PublicIdentity → OracleComp SourceSpec (Phase1Material Context))
    (selector : Phase1Candidate → OracleComp SourceSpec Phase1Candidate)
    (state finalState : State) (output : SessionResult Context)
    (supported : (some output, finalState) ∈ support ((simulateQ impl
      (oneSession setup selector)).run state)) :
    ∃ before, (output.accepted, finalState) ∈ support
      ((impl (.inr ⟨output.index, output.candidate⟩)).run before) := by
  simp only [oneSession, simulateQ_bind, StateT.run_bind, simulateQ_spec_query,
    mem_support_bind_iff] at supported
  obtain ⟨created, _, continued⟩ := supported
  cases creation : created.1 with
  | none =>
      simp only [creation, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at continued
  | some value =>
      simp only [creation] at continued
      exact sessionBody_finalCandidate impl value.1 value.2 setup selector created.2 finalState output continued

/-- The actual final optional response accepts changed signed fields under the created identity while its seed remains unrevealed at acceptance. -/
def SessionChanged {Context : Type} {count : ℕ}
    (result : Option (SessionResult Context) × CompleteState (count + 1)) : Prop :=
  ∃ output decoded, result.1 = some output ∧
    output.accepted = some (output.publicIdentity.ed25519, decoded) ∧
    decoded ≠ output.material.keyTuple ∧
    (0 : Fin (count + 1)) ∉ result.2.2.source.1.reveals

/-- Actual accepted changed fields become the existing fresh-field event, with ownership and the three-entry source signing log derived from the complete execution. -/
theorem oneSession_changed_fieldOrigin {Context : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (count : ℕ) (setup : PublicIdentity → OracleComp SourceSpec (Phase1Material Context))
    (selector : Phase1Candidate → OracleComp SourceSpec Phase1Candidate)
    (setupNoSign : ∀ publicIdentity, (setup publicIdentity).IsQueryBoundP IsSigning 0)
    (selectorNoSign : ∀ bundle, (selector bundle).IsQueryBoundP IsSigning 0)
    (result : Option (SessionResult Context) × CompleteState (count + 1))
    (supported : result ∈ support (actualRun attachedVerify primitives (count + 1) (oneSession setup selector)))
    (changed : SessionChanged result) :
    ∃ output, result.1 = some output ∧
      candidateAccepted primitives ⟨output.index, output.candidate⟩ result.2.1.snapshot = true := by
  have bareSupported : erase result ∈ support (bareRun attachedVerify primitives (count + 1) (oneSession setup selector)) := by
    rw [← actualRun_erase, support_map]
    exact ⟨result, supported, rfl⟩
  obtain ⟨seed, material, candidate, completed, messages, retained⟩ :=
    oneSession_supported attachedVerify primitives count setup selector setupNoSign selectorNoSign
      (erase result) bareSupported
  change result.2.2.source.2.seeds[0]? = some seed at retained
  obtain ⟨output, decoded, returned, accepted, different, fresh⟩ := changed
  have same : output = ⟨0, primitives.publicKeys seed, material, candidate, sourceAccept attachedVerify candidate⟩ :=
    Option.some.inj (returned.symm.trans completed)
  subst output
  refine ⟨_, returned, ?_⟩
  rw [actualRun_snapshot attachedVerify primitives adapter _ _ result supported,
    candidateAccepted_iff]
  apply singleBundle_fieldOrigin primitives ⟨0, candidate⟩ (sourceSnapshot primitives result.2.2.source)
    (Nat.zero_lt_succ count) (primitives.publicKeys seed) material
  · simp [sourceSnapshot, sourceKeys, retained]
  · exact fresh
  · exact messages
  · apply (phase1FieldSubstitutionBit_eq_true_iff primitives.verify _ material candidate).mpr
    exact ⟨decoded, (sourceAccept_eq attachedVerify primitives adapter candidate).symm.trans accepted, different⟩

/-- Embedding a dynamic request into the actual source interface preserves every caller-selected query class. -/
theorem liftDynamic_query_bound {Result : Type} (client : OracleComp DynamicSpec Result)
    (predicate : SourceSpec.Domain → Prop) [DecidablePred predicate] (bound : ℕ)
    (bounded : client.IsQueryBoundP (fun query => predicate (.inl query)) bound) :
    (liftDynamic client).IsQueryBoundP predicate bound := by
  induction client using OracleComp.inductionOn generalizing bound with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      change (simulateQ dynamicToSource (DynamicSpec.query query >>= next)).IsQueryBoundP predicate bound
      rw [simulateQ_query_bind]
      change OracleComp.IsQueryBoundP
        ((SourceSpec.query (.inl query) : OracleComp SourceSpec _) >>= fun answer =>
          liftDynamic (next answer)) predicate bound
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨bounded.1, fun answer => ih answer _ (bounded.2 answer)⟩

/-- The actual source writer and every possible selector continuation retain separate query budgets. -/
theorem selectedProgram_query_bound (index : ℕ) (identity : Ed25519PublicKey)
    (keys : Phase1KeyTuple) (selector : Phase1Candidate → OracleComp SourceSpec Phase1Candidate)
    (predicate : SourceSpec.Domain → Prop) [DecidablePred predicate]
    (qWriter qSelector : ℕ)
    (writerBound : (signingProgram index identity keys).IsQueryBoundP
      (fun query => predicate (.inl query)) qWriter)
    (selectorBound : ∀ bundle, (selector bundle).IsQueryBoundP predicate qSelector) :
    (selectedProgram index identity keys selector).IsQueryBoundP predicate (qWriter + qSelector) := by
  apply isQueryBoundP_bind (liftDynamic_query_bound _ predicate qWriter writerBound)
  intro bundle _
  cases bundle with
  | none => trivial
  | some bundle => exact (isQueryBoundP_map_iff _ _ _).mpr (selectorBound bundle)

/-- Complete source accounting charges creation, setup, the exact writer, selector, and the final candidate attempt separately under every possible reply. -/
theorem oneSession_query_bound {Context : Type}
    (setup : PublicIdentity → OracleComp SourceSpec (Phase1Material Context))
    (selector : Phase1Candidate → OracleComp SourceSpec Phase1Candidate)
    (predicate : SourceSpec.Domain → Prop) [DecidablePred predicate]
    (qCreate qSetup qWriter qSelector qAccept : ℕ)
    (createBound : OracleComp.IsQueryBoundP
      (SourceSpec.query (.inl (.inr .create)) : OracleComp SourceSpec _) predicate qCreate)
    (setupBound : ∀ publicIdentity, (setup publicIdentity).IsQueryBoundP predicate qSetup)
    (writerBound : ∀ index identity keys, (signingProgram index identity keys).IsQueryBoundP
      (fun query => predicate (.inl query)) qWriter)
    (selectorBound : ∀ bundle, (selector bundle).IsQueryBoundP predicate qSelector)
    (acceptBound : ∀ report, OracleComp.IsQueryBoundP
      (SourceSpec.query (.inr report) : OracleComp SourceSpec _) predicate qAccept) :
    (oneSession setup selector).IsQueryBoundP predicate
      (qCreate + (qSetup + ((qWriter + qSelector) + qAccept))) := by
  apply isQueryBoundP_bind createBound
  intro created _
  cases created with
  | none => trivial
  | some value =>
      apply isQueryBoundP_bind (setupBound value.2)
      intro material _
      apply isQueryBoundP_bind (selectedProgram_query_bound value.1 value.2.ed25519 material.keyTuple
        selector predicate qWriter qSelector (writerBound _ _ _) selectorBound)
      intro candidate _
      cases candidate with
      | none => trivial
      | some candidate =>
          simpa only [bind_pure_comp, isQueryBoundP_map_iff] using acceptBound ⟨value.1, candidate⟩

/-- Candidate instrumentation preserves the public snapshot and records the actual public field-origin classifier. -/
theorem sourceCandidate_monitor (primitives : Primitives) (count : Nat) (candidate : CandidateReport)
    (state : CompleteState count) :
    (fun result => (result.2.1.snapshot, result.2.1.occurred)) <$>
      ((sourceImpl primitives count (.inr candidate)).run state) =
      pure (state.1.snapshot, state.1.occurred || candidateAccepted primitives candidate state.1.snapshot) := by
  rw [PqxdhJointPhase1Reports.sourceImpl, QueryImpl.Stateful.link_impl_apply_run]
  simp only [Functor.map_map]
  change (fun result => (result.1.2.snapshot, result.1.2.occurred)) <$>
    ((simulateQ (reportingImpl primitives count)
      ((wrapper primitives count (.inr candidate)).run state.1)).run state.2) = _
  cases translated : translateReport primitives candidate state.1.snapshot with
  | none =>
    simp only [wrapper, StateT.run, translated, simulateQ_pure]
    rfl
  | some forgery =>
    simp only [wrapper, StateT.run, translated, simulateQ_bind, simulateQ_spec_query,
      simulateQ_pure]
    rfl

/-- This monitor projection is independent of attached-format compatibility and of the actual optional acceptance reply. -/
theorem acceptanceCandidate_monitor
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (candidate : CandidateReport)
    (state : CompleteState count) :
    (fun result => (result.2.1.snapshot, result.2.1.occurred)) <$>
      ((acceptanceImpl attachedVerify primitives count (.inr candidate)).run state) =
      pure (state.1.snapshot, state.1.occurred || candidateAccepted primitives candidate state.1.snapshot) := by
  simpa only [acceptanceImpl, StateT.run_bind, StateT.run_pure, StateT.run_map, bind_pure_comp,
    Functor.map_map, Function.comp_def] using sourceCandidate_monitor primitives count candidate state

/-- Every supported actual optional reply carries exactly the unchanged snapshot and recorded public classifier. -/
theorem acceptanceCandidate_snapshot_occurred
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (candidate : CandidateReport)
    (state : CompleteState count) (result : Option AcceptedInput × CompleteState count)
    (supported : result ∈ support ((acceptanceImpl attachedVerify primitives count (.inr candidate)).run state)) :
    result.2.1.snapshot = state.1.snapshot ∧
      result.2.1.occurred = (state.1.occurred || candidateAccepted primitives candidate state.1.snapshot) := by
  have projected : (result.2.1.snapshot, result.2.1.occurred) ∈ support
      ((fun result => (result.2.1.snapshot, result.2.1.occurred)) <$>
        ((acceptanceImpl attachedVerify primitives count (.inr candidate)).run state)) := by
    rw [support_map]
    exact ⟨result, supported, rfl⟩
  rw [acceptanceCandidate_monitor] at projected
  have pair := OracleComp.eq_of_mem_support_pure _ projected
  exact Prod.mk.inj pair

/-- A public field-origin hit at the candidate's final snapshot is already recorded by this step. -/
theorem acceptanceCandidate_hit_recorded
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (candidate : CandidateReport)
    (state : CompleteState count) (result : Option AcceptedInput × CompleteState count)
    (supported : result ∈ support ((acceptanceImpl attachedVerify primitives count (.inr candidate)).run state))
    (hit : candidateAccepted primitives candidate result.2.1.snapshot = true) :
    result.2.1.occurred = true := by
  obtain ⟨snapshot, occurred⟩ := acceptanceCandidate_snapshot_occurred attachedVerify primitives count candidate state result supported
  rw [occurred, ← snapshot, hit, Bool.or_true]

/-- Every actual same-identity changed acceptance is already recorded by the final unchanged candidate request. -/
theorem oneSession_changed_recorded {Context : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (count : ℕ) (setup : PublicIdentity → OracleComp SourceSpec (Phase1Material Context))
    (selector : Phase1Candidate → OracleComp SourceSpec Phase1Candidate)
    (setupNoSign : ∀ publicIdentity, (setup publicIdentity).IsQueryBoundP IsSigning 0)
    (selectorNoSign : ∀ bundle, (selector bundle).IsQueryBoundP IsSigning 0)
    (result : Option (SessionResult Context) × CompleteState (count + 1))
    (supported : result ∈ support (actualRun attachedVerify primitives (count + 1) (oneSession setup selector)))
    (changed : SessionChanged result) : result.2.1.occurred = true := by
  obtain ⟨output, returned, detected⟩ := oneSession_changed_fieldOrigin attachedVerify primitives adapter count
    setup selector setupNoSign selectorNoSign result supported changed
  have finished : (some output, result.2) ∈ support (actualRun attachedVerify primitives (count + 1)
      (oneSession setup selector)) := by simpa only [← returned] using supported
  obtain ⟨before, last⟩ := oneSession_finalCandidate (acceptanceImpl attachedVerify primitives (count + 1))
    setup selector _ result.2 output finished
  exact acceptanceCandidate_hit_recorded attachedVerify primitives (count + 1)
    ⟨output.index, output.candidate⟩ before (output.accepted, result.2) last detected

/-- The one-session source creates exactly one possible honest identity when its setup and selector make no extra creation request. -/
theorem oneSession_create_bound {Context : Type}
    (setup : PublicIdentity → OracleComp SourceSpec (Phase1Material Context))
    (selector : Phase1Candidate → OracleComp SourceSpec Phase1Candidate)
    (setupNoCreate : ∀ publicIdentity, (setup publicIdentity).IsQueryBoundP
      (IsSourceClass (SourceClass IsCreate)) 0)
    (selectorNoCreate : ∀ bundle, (selector bundle).IsQueryBoundP
      (IsSourceClass (SourceClass IsCreate)) 0) :
    (oneSession setup selector).IsQueryBoundP (IsSourceClass (SourceClass IsCreate)) 1 := by
  apply oneSession_query_bound setup selector (IsSourceClass (SourceClass IsCreate)) 1 0 0 0 0
  · rw [isQueryBoundP_query_iff]
    intro _
    omega
  · exact setupNoCreate
  · intro index identity keys
    apply signingProgram_excluded_bound
    intro message
    simp [IsSourceClass, SourceClass, sourceQuery, IsCreate]
  · exact selectorNoCreate
  · intro report
    rw [isQueryBoundP_query_iff]
    intro impossible
    exact False.elim impossible

/-- The constructed single-target reduction uses the same original source program and unchanged first fresh-field extractor. It has no target seed. -/
def oneSessionReduction {Context : Type} (primitives : Primitives)
    (setup : PublicIdentity → OracleComp SourceSpec (Phase1Material Context))
    (selector : Phase1Candidate → OracleComp SourceSpec Phase1Candidate)
    (fallback : DynamicForgery) (ordinaryFallback : Forgery) : PublicIdentity → OracleComp AdversarySpec Forgery :=
  globalReduction primitives (0 : Fin 1) ordinaryFallback
    (routedAdversary 0 ordinaryFallback
      (reportExtractor primitives 1 fallback
        (routedClient primitives 1 (instrumentedClient primitives (oneSession setup selector)))))

/-- One actual generated identity, source-ordered writer and arbitrary candidate selection reduce actual fresh changed acceptance to one joint weak-EUF game, with coefficient one and no honest-target selector premise. -/
theorem oneSession_authentication_bound {Context : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (setup : PublicIdentity → OracleComp SourceSpec (Phase1Material Context))
    (selector : Phase1Candidate → OracleComp SourceSpec Phase1Candidate)
    (setupNoSign : ∀ publicIdentity, (setup publicIdentity).IsQueryBoundP IsSigning 0)
    (selectorNoSign : ∀ bundle, (selector bundle).IsQueryBoundP IsSigning 0)
    (setupNoCreate : ∀ publicIdentity, (setup publicIdentity).IsQueryBoundP
      (IsSourceClass (SourceClass IsCreate)) 0)
    (selectorNoCreate : ∀ bundle, (selector bundle).IsQueryBoundP
      (IsSourceClass (SourceClass IsCreate)) 0)
    (fallback : DynamicForgery) (ordinaryFallback : Forgery) :
    Pr[SessionChanged | actualRun attachedVerify primitives 1 (oneSession setup selector)] ≤
      advantage primitives (oneSessionReduction primitives setup selector fallback ordinaryFallback) := by
  have detected := probEvent_mono (fun result supported changed =>
    oneSession_changed_recorded attachedVerify primitives adapter 0 setup selector
      setupNoSign selectorNoSign result supported changed)
  have bounded := acceptance_advantage_le_sum attachedVerify primitives adapter 0
    (oneSession setup selector) fallback ordinaryFallback
    (oneSession_create_bound setup selector setupNoCreate selectorNoCreate)
  rw [Fin.sum_univ_succ] at bounded
  simpa [oneSessionReduction] using detected.trans bounded

/-- Every ordinary joint class keeps the setup and selector budgets; only the source writer adds three signing requests. -/
theorem oneSession_class_bound {Context : Type}
    (setup : PublicIdentity → OracleComp SourceSpec (Phase1Material Context))
    (selector : Phase1Candidate → OracleComp SourceSpec Phase1Candidate)
    (kind : Kind) (qSetup qSelector : ℕ)
    (setupBound : ∀ publicIdentity, (setup publicIdentity).IsQueryBoundP
      (IsSourceClass (SourceClass (dynamicClass (IsClass kind)))) qSetup)
    (selectorBound : ∀ bundle, (selector bundle).IsQueryBoundP
      (IsSourceClass (SourceClass (dynamicClass (IsClass kind)))) qSelector) :
    (oneSession setup selector).IsQueryBoundP
      (IsSourceClass (SourceClass (dynamicClass (IsClass kind))))
      (qSetup + ((if kind = .sign then 3 else 0) + qSelector)) := by
  simpa only [Nat.zero_add, Nat.add_zero] using oneSession_query_bound setup selector
    (IsSourceClass (SourceClass (dynamicClass (IsClass kind))))
    0 qSetup (if kind = .sign then 3 else 0) qSelector 0
    (by rw [isQueryBoundP_query_iff]; exact fun impossible => False.elim impossible)
    setupBound (fun index identity keys => signingProgram_class_bound index identity keys kind)
    selectorBound (fun report => by rw [isQueryBoundP_query_iff]; exact fun impossible => False.elim impossible)

/-- The original source position ledger counts creation, all three writer slots and the final acceptance in addition to every setup and selector request. -/
theorem oneSession_total_bound {Context : Type}
    (setup : PublicIdentity → OracleComp SourceSpec (Phase1Material Context))
    (selector : Phase1Candidate → OracleComp SourceSpec Phase1Candidate)
    (qSetup qSelector : ℕ)
    (setupBound : ∀ publicIdentity, (setup publicIdentity).IsTotalQueryBound qSetup)
    (selectorBound : ∀ bundle, (selector bundle).IsTotalQueryBound qSelector) :
    (oneSession setup selector).IsTotalQueryBound (qSetup + qSelector + 5) := by
  apply (isQueryBoundP_true_iff _ _).mp
  have bound := oneSession_query_bound setup selector (fun _ => True) 1 qSetup 3 qSelector 1
    (by rw [isQueryBoundP_query_iff]; omega)
    (fun publicIdentity => (isQueryBoundP_true_iff _ _).mpr (setupBound publicIdentity))
    (fun index identity keys => (isQueryBoundP_true_iff _ _).mpr (signingProgram_total_bound index identity keys))
    (fun bundle => (isQueryBoundP_true_iff _ _).mpr (selectorBound bundle))
    (fun report => by rw [isQueryBoundP_query_iff]; omega)
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound

/-- The actual one-target reduction inherits every joint class cap, with no additional seed reservation beyond its challenger-owned target. -/
theorem oneSessionReduction_class_bound {Context : Type} (primitives : Primitives)
    (setup : PublicIdentity → OracleComp SourceSpec (Phase1Material Context))
    (selector : Phase1Candidate → OracleComp SourceSpec Phase1Candidate)
    (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    (kind : Kind) (qSetup qSelector : ℕ)
    (setupBound : ∀ publicIdentity, (setup publicIdentity).IsQueryBoundP
      (IsSourceClass (SourceClass (dynamicClass (IsClass kind)))) qSetup)
    (selectorBound : ∀ bundle, (selector bundle).IsQueryBoundP
      (IsSourceClass (SourceClass (dynamicClass (IsClass kind)))) qSelector)
    (publicIdentity : PublicIdentity) :
    (oneSessionReduction primitives setup selector fallback ordinaryFallback publicIdentity).IsQueryBoundP
      (IsClass kind) (qSetup + ((if kind = .sign then 3 else 0) + qSelector)) := by
  simpa only [Nat.mul_zero, ite_self, Nat.zero_add, oneSessionReduction] using
    PqxdhPhase1AcceptanceOracle.reduction_query_bound primitives 0 0 fallback ordinaryFallback
      (oneSession setup selector) kind _ (oneSession_class_bound setup selector kind qSetup qSelector setupBound selectorBound)
      publicIdentity

/-- Every candidate attempt in setup/selection remains charged, including malformed or already-issued candidates; the final original candidate adds one. -/
theorem oneSession_attempt_bound {Context : Type}
    (setup : PublicIdentity → OracleComp SourceSpec (Phase1Material Context))
    (selector : Phase1Candidate → OracleComp SourceSpec Phase1Candidate)
    (qSetup qSelector : ℕ)
    (setupBound : ∀ publicIdentity, (setup publicIdentity).IsQueryBoundP (IsSourceClass IsCandidateReport) qSetup)
    (selectorBound : ∀ bundle, (selector bundle).IsQueryBoundP (IsSourceClass IsCandidateReport) qSelector) :
    (oneSession setup selector).IsQueryBoundP (IsSourceClass IsCandidateReport) (qSetup + qSelector + 1) := by
  have writer : ∀ index identity keys, (signingProgram index identity keys).IsQueryBoundP
      (fun query => IsSourceClass IsCandidateReport (.inl query)) 0 := by
    intro index identity keys
    apply signingProgram_excluded_bound
    intro message
    exact id
  simpa only [Nat.zero_add, Nat.add_assoc] using oneSession_query_bound setup selector
    (IsSourceClass IsCandidateReport) 0 qSetup 0 qSelector 1
    (by rw [isQueryBoundP_query_iff]; exact fun impossible => False.elim impossible)
    setupBound writer selectorBound (fun report => by rw [isQueryBoundP_query_iff]; omega)

def IsSourceReveal : SourceSpec.Domain → Prop
  | .inl (.inr (.reveal _)) => True
  | _ => False

instance : DecidablePred IsSourceReveal := fun query => by
  cases query with
  | inr report => exact isFalse id
  | inl query => cases query with
    | inl coin => exact isFalse id
    | inr query => cases query <;> simp only [IsSourceReveal] <;> infer_instance

/-- Every requested identity reveal, including repeated or uncreated-index attempts, stays in the source budget. -/
theorem oneSession_reveal_bound {Context : Type}
    (setup : PublicIdentity → OracleComp SourceSpec (Phase1Material Context))
    (selector : Phase1Candidate → OracleComp SourceSpec Phase1Candidate)
    (qSetup qSelector : ℕ)
    (setupBound : ∀ publicIdentity, (setup publicIdentity).IsQueryBoundP
      IsSourceReveal qSetup)
    (selectorBound : ∀ bundle, (selector bundle).IsQueryBoundP
      IsSourceReveal qSelector) :
    (oneSession setup selector).IsQueryBoundP
      IsSourceReveal (qSetup + qSelector) := by
  have writer : ∀ index identity keys, (signingProgram index identity keys).IsQueryBoundP
      (fun query => IsSourceReveal (.inl query)) 0 := by
    intro index identity keys
    apply signingProgram_excluded_bound
    intro message
    exact id
  simpa only [Nat.zero_add, Nat.add_zero] using oneSession_query_bound setup selector
    IsSourceReveal 0 qSetup 0 qSelector 0
    (by rw [isQueryBoundP_query_iff]; exact fun impossible => False.elim impossible)
    setupBound writer selectorBound
    (fun report => by rw [isQueryBoundP_query_iff]; exact fun impossible => False.elim impossible)

/-- The real one-session source pays for its generated target seed and all setup/selector coins; no opaque sampling work is declared free. -/
theorem oneSession_actual_uniform_bound {Context : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (setup : PublicIdentity → OracleComp SourceSpec (Phase1Material Context))
    (selector : Phase1Candidate → OracleComp SourceSpec Phase1Candidate)
    (setupNoCreate : ∀ publicIdentity, (setup publicIdentity).IsQueryBoundP
      (IsSourceClass (SourceClass IsCreate)) 0)
    (selectorNoCreate : ∀ bundle, (selector bundle).IsQueryBoundP
      (IsSourceClass (SourceClass IsCreate)) 0)
    (qSetup qSelector : ℕ)
    (setupBound : ∀ publicIdentity, (setup publicIdentity).IsQueryBoundP
      (IsSourceClass (SourceClass (dynamicClass (IsClass .uniform)))) qSetup)
    (selectorBound : ∀ bundle, (selector bundle).IsQueryBoundP
      (IsSourceClass (SourceClass (dynamicClass (IsClass .uniform)))) qSelector) :
    (actualRun attachedVerify primitives 1 (oneSession setup selector)).IsTotalQueryBound
      (32 + (qSetup + qSelector)) := by
  have coins := oneSession_class_bound setup selector .uniform qSetup qSelector setupBound selectorBound
  apply PqxdhPhase1AcceptanceOracle.actualRun_uniform_bound attachedVerify primitives adapter 1
    (oneSession setup selector) 1 (qSetup + qSelector)
    (oneSession_create_bound setup selector setupNoCreate selectorNoCreate)
  have same : dynamicClass (IsClass .uniform) = PqxdhDynamicIdentityPool.IsUniform := by
    funext query
    cases query with
    | inl coin => simp [dynamicClass, IsClass, PqxdhDynamicIdentityPool.IsUniform]
    | inr query => cases query with
      | create => rfl
      | reveal identity => rfl
      | service identity request => cases request <;> simp [dynamicClass, IsClass, PqxdhDynamicIdentityPool.IsUniform]
  simpa only [reduceCtorEq, ite_false, Nat.zero_add, same] using coins

/-- The entire one-target joint challenger charges its private 32-byte seed in addition to all reduction coins. -/
theorem oneSession_challenger_uniform_bound {Context : Type} (primitives : Primitives)
    (setup : PublicIdentity → OracleComp SourceSpec (Phase1Material Context))
    (selector : Phase1Candidate → OracleComp SourceSpec Phase1Candidate)
    (fallback : DynamicForgery) (ordinaryFallback : Forgery) (qSetup qSelector : ℕ)
    (setupBound : ∀ publicIdentity, (setup publicIdentity).IsQueryBoundP
      (IsSourceClass (SourceClass (dynamicClass (IsClass .uniform)))) qSetup)
    (selectorBound : ∀ bundle, (selector bundle).IsQueryBoundP
      (IsSourceClass (SourceClass (dynamicClass (IsClass .uniform)))) qSelector) :
    (game primitives (oneSessionReduction primitives setup selector fallback ordinaryFallback)).IsTotalQueryBound
      (32 + (qSetup + qSelector)) := by
  have coins := oneSession_class_bound setup selector .uniform qSetup qSelector setupBound selectorBound
  apply PqxdhPhase1AcceptanceOracle.reductionGame_uniform_bound primitives 0 0 fallback ordinaryFallback
    (oneSession setup selector) (qSetup + qSelector)
  simpa only [reduceCtorEq, ite_false, Nat.zero_add] using coins

end BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.historyUpdate_noSign' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.historyUpdate_noSign

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.bare_step_noSign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.bare_step_noSign

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.bare_run_noSign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.bare_run_noSign

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.bare_step_seed_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.bare_step_seed_extension

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.bare_step_created' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.bare_step_created

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.bare_run_created' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.bare_run_created

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.bare_dynamic_compose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.bare_dynamic_compose

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.liftDynamic_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.liftDynamic_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.selectedProgram_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.selectedProgram_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.selectedProgram_three_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.selectedProgram_three_messages

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.selectedProgram_fieldOrigin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.selectedProgram_fieldOrigin

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.reportingImpl_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.reportingImpl_snapshot

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.reportingExecution_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.reportingExecution_snapshot

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.reportingRun_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.reportingRun_snapshot

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.actualRun_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.actualRun_snapshot

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.sessionBody_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.sessionBody_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.bare_create_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.bare_create_initial

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.singletonState_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.singletonState_facts

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.sessionBody_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.sessionBody_supported

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_supported

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.sessionBody_finalCandidate' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.sessionBody_finalCandidate

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_finalCandidate' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_finalCandidate

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_changed_fieldOrigin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_changed_fieldOrigin

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.liftDynamic_query_bound' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.liftDynamic_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.selectedProgram_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.selectedProgram_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.sourceCandidate_monitor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.sourceCandidate_monitor

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.acceptanceCandidate_monitor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.acceptanceCandidate_monitor

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.acceptanceCandidate_snapshot_occurred' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.acceptanceCandidate_snapshot_occurred

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.acceptanceCandidate_hit_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.acceptanceCandidate_hit_recorded

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_changed_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_changed_recorded

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_create_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_create_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_authentication_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_authentication_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_class_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_class_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_total_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_total_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSessionReduction_class_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSessionReduction_class_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_attempt_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_attempt_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_reveal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_reveal_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_actual_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_actual_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_challenger_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition.oneSession_challenger_uniform_bound
