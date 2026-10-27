import BeaconcryptCore.Computational.AdaptiveCtxDirectReplay
import BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff

/-! Private records in the existing ordinary random privacy experiment are retained mathematically but are not consulted by a suffix containing only source coins and public hashes. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView
open CtxRomAuth CtxNonceAeadIntCtxt CtxIndependentTags AdaptiveCtxReceive
open AdaptiveCtxDirectReplay CtxNonceAeadIndDollar
variable {Result : Type}

abbrev State := (ReceiveState × AdaptiveRawNonceAead.SealHistory) × ModifiedNonceAeadHandlerState

/-- Clear every tag-bearing private receive copy, retaining the actual public cache/history, nonce list and raw-attempt counter. -/
def receive (state : ReceiveState) : ReceiveState :=
  ⟨⟨⟨state.ctx.cache.publicCache, ∅⟩, state.ctx.usedNonces, [], state.ctx.publicInputs⟩,
    state.rawAttempts, []⟩

/-- The redundant ordinary base log and primitive record log are also private. Their nonce controls remain unchanged. -/
def project (state : State) : State :=
  ((receive state.1.1, []), ⟨state.2.usedNonces, []⟩)

/-- Full private-view projection is idempotent. -/
theorem project_idempotent (state : State) : project (project state) = project state := rfl

/-- One complete existing direct-source query, interpreted by the unchanged ordinary random primitive. -/
noncomputable def step (decode : RawDecoder) (query : ReceiveSpec.Domain) (state : State) :
    ProbComp (ReceiveSpec.Range query × State) :=
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ modifiedNonceAeadINDDollarRandomImpl ((directWithBase decode query).run state.1)).run state.2

/-- Source coins never read or alter either complete source history or either primitive history. -/
theorem uniform_step (decode : RawDecoder) (coin : unifSpec.Domain) (state : State) :
    step decode (.inl (.inl coin)) state =
      (fun reply => (reply, state)) <$> (unifSpec.query coin : ProbComp _) := by
  simp only [step, directWithBase, directImpl, StateT.run, bind_pure_comp,
    simulateQ_map, simulateQ_spec_query]
  simp only [modifiedNonceAeadINDDollarRandomImpl, QueryImpl.add_apply_inl, recordBase]
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    ((fun value => (value, state.1)) <$> StateT.lift (unifSpec.query coin : ProbComp _)).run state.2 = _
  simp only [StateT.run_map, StateT.run_lift, Functor.map_map]
  rfl

/-- Lifted source sampling leaves the complete ordinary random primitive state untouched. -/
theorem lifted_step (work : ProbComp Result) (state : ModifiedNonceAeadHandlerState) :
    (simulateQ modifiedNonceAeadINDDollarRandomImpl
      (OracleComp.liftComp work ModifiedNonceAeadAdversarySpec)).run state =
      (fun value => (value, state)) <$> work := by
  simp only [modifiedNonceAeadINDDollarRandomImpl, QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  simp only [StateT.run_monadLift, monadLift_eq_self, bind_pure_comp]

/-- A public hash updates only the public cache and its public input history, retaining all private copies. -/
theorem public_step (decode : RawDecoder) (input : CtxRO.Domain) (state : State) :
    step decode (.inl (.inr (.inl input))) state =
      (fun result => (result.1,
        (({state.1.1 with ctx := result.2}, state.1.2), state.2))) <$>
          (ctxIndependentPublicOracle input).run state.1.1.ctx := by
  simp only [step, directWithBase, directImpl, StateT.run, directPublic,
    bind_pure_comp, simulateQ_map, recordBase, Functor.map_map]
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    ((fun answer => (answer.1, ({state.1.1 with ctx := answer.2}, state.1.2))) <$>
      simulateQ modifiedNonceAeadINDDollarRandomImpl
        (OracleComp.liftComp ((ctxIndependentPublicOracle input).run state.1.1.ctx)
          ModifiedNonceAeadAdversarySpec)).run state.2 = _
  simp only [StateT.run_map, lifted_step, Functor.map_map]
  rfl

/-- Complete public-cache effects commute with erasing every private record copy. -/
theorem public_project (decode : RawDecoder) (input : CtxRO.Domain) (state : State) :
    Prod.map id project <$> step decode (.inl (.inr (.inl input))) state =
      Prod.map id project <$> step decode (.inl (.inr (.inl input))) (project state) := by
  simp only [public_step, ctxIndependentPublicOracle, StateT.run, bind_pure_comp,
    Functor.map_map, project, receive, CtxIndependentTagState.addPublic]
  rfl

/-- Every nonsealing, nonreceiving request preserves the same public view, including the complete public hash cache. -/
theorem quiet_project (decode : RawDecoder) (query : ReceiveSpec.Domain) (state : State)
    (noSeal : ¬ AdaptiveCtxQueryBounds.SourceSeal query) (noRaw : ¬ IsRawQuery query) :
    Prod.map id project <$> step decode query state =
      Prod.map id project <$> step decode query (project state) := by
  rcases query with ((coin | (input | request)) | raw)
  · simp only [uniform_step, Functor.map_map, Prod.map_apply, id_eq, project_idempotent]
  · exact public_project decode input state
  · exact False.elim (noSeal trivial)
  · exact False.elim (noRaw trivial)

/-- Stateful type of the complete ordinary random handler. -/
noncomputable def impl (decode : RawDecoder) : QueryImpl ReceiveSpec (StateT State ProbComp) :=
  step decode

/-- The flattened query handler is the existing complete ordinary random experiment, with both full histories retained. -/
theorem program_source (decode : RawDecoder) (work : OracleComp ReceiveSpec Result) (state : State) :
    (simulateQ (impl decode) work).run state =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ modifiedNonceAeadINDDollarRandomImpl
          ((simulateQ (directWithBase decode) work).run state.1)).run state.2 := by
  exact (congrFun (PqxdhSelectedStateInterpreter.program
    modifiedNonceAeadINDDollarRandomImpl (directWithBase decode) work) state).symm

/-- An arbitrary adaptive suffix with no selected seals or raw attempts cannot consult private record copies. Its actual public queries and final reply are preserved. -/
theorem program_project (decode : RawDecoder) (work : OracleComp ReceiveSpec Result)
    (noSeal : work.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 0)
    (noRaw : work.IsQueryBoundP IsRawQuery 0) (state : State) :
    Prod.map id project <$> (simulateQ (impl decode) work).run state =
      Prod.map id project <$> (simulateQ (impl decode) work).run (project state) := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_apply, id_eq, project_idempotent]
  | query_bind query next ih =>
    simp only [OracleComp.isQueryBoundP_query_bind_iff, Nat.lt_irrefl, or_false,
      Nat.zero_sub, ite_self] at noSeal noRaw
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    have factor (start : State) :
        (do let result ← (impl decode query).run start
            Prod.map id project <$> (simulateQ (impl decode) (next result.1)).run result.2) =
          (do let result ← Prod.map id project <$> (impl decode query).run start
              Prod.map id project <$> (simulateQ (impl decode) (next result.1)).run result.2) := by
      rw [bind_map_left]
      apply bind_congr
      intro result
      exact ih result.1 (noSeal.2 result.1) (noRaw.2 result.1) result.2
    rw [factor state, factor (project state)]
    exact congrArg (fun work => work >>= fun result =>
      Prod.map id project <$> (simulateQ (impl decode) (next result.1)).run result.2)
      (quiet_project decode query state noSeal.1 noRaw.1)

/-- Equal public projections give the same full public continuation, without a distribution or independence premise. -/
theorem program_congr (decode : RawDecoder) (work : OracleComp ReceiveSpec Result)
    (noSeal : work.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 0)
    (noRaw : work.IsQueryBoundP IsRawQuery 0) (left right : State)
    (same : project left = project right) :
    Prod.map id project <$> (simulateQ (impl decode) work).run left =
      Prod.map id project <$> (simulateQ (impl decode) work).run right := by
  rw [program_project decode work noSeal noRaw left,
    program_project decode work noSeal noRaw right, same]

/-- A private suffix lookup keeps the actual source cache/history and leaves the ordinary primitive state untouched. -/
theorem private_step (suffix : Pqxdh.Bytes) (state : ReceiveState)
    (primitive : ModifiedNonceAeadHandlerState) :
    (simulateQ modifiedNonceAeadINDDollarRandomImpl (directPrivate suffix state)).run primitive =
      (fun result => ((result.1,
        ⟨{state.ctx with cache := result.2}, state.rawAttempts, suffix :: state.privateInputs⟩), primitive)) <$>
          ctxKeyFreeSuffixStep suffix state.ctx.cache := by
  simp only [directPrivate, bind_pure_comp, simulateQ_map, StateT.run_map, lifted_step,
    Functor.map_map]

/-- The selected primitive and private suffix table have not yet been used. -/
def Unused (state : State) : Prop :=
  state.1.1.ctx.cache.suffixCache = ∅ ∧ state.2.usedNonces = []

/-- A nonsealing, nonreceiving source request cannot initialize either selected private table. -/
theorem quiet_unused (decode : RawDecoder) (query : ReceiveSpec.Domain) (state : State)
    (noSeal : ¬ AdaptiveCtxQueryBounds.SourceSeal query) (noRaw : ¬ IsRawQuery query)
    (unused : Unused state) (result : ReceiveSpec.Range query × State)
    (supported : result ∈ support (step decode query state)) : Unused result.2 := by
  rcases query with ((coin | (input | request)) | raw)
  · rw [uniform_step, support_map] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    exact unused
  · simp only [public_step, ctxIndependentPublicOracle, StateT.run, bind_pure_comp,
      Functor.map_map, support_map] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    exact unused
  · exact False.elim (noSeal trivial)
  · exact False.elim (noRaw trivial)

/-- Every actually reached state before the first selected seal retains the empty selected nonce and suffix tables. All public-hash cache work remains present. -/
theorem program_unused (decode : RawDecoder) (work : OracleComp ReceiveSpec Result)
    (noSeal : work.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 0)
    (noRaw : work.IsQueryBoundP IsRawQuery 0) (state : State) (unused : Unused state)
    (result : Result × State) (supported : result ∈ support ((simulateQ (impl decode) work).run state)) :
    Unused result.2 := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact unused
  | query_bind query next ih =>
    simp only [OracleComp.isQueryBoundP_query_bind_iff, Nat.lt_irrefl, or_false,
      Nat.zero_sub, ite_self] at noSeal noRaw
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, support_bind,
      Set.mem_iUnion] at supported
    obtain ⟨reply, stepSupported, tailSupported⟩ := supported
    exact ih reply.1 (noSeal.2 reply.1) (noRaw.2 reply.1) reply.2
      (quiet_unused decode query state noSeal.1 noRaw.1 unused reply stepSupported) tailSupported

/-- The ordinary seal's actual optional ciphertext precedes the source private commitment lookup and full source update. -/
theorem seal_step (input : CtxSealInput) (state : ReceiveState)
    (primitive : ModifiedNonceAeadHandlerState) :
    (simulateQ modifiedNonceAeadINDDollarRandomImpl (directSeal input state)).run primitive = (do
      let encrypted ← (modifiedNonceAeadINDDollarRandomSealOracle (CtxNonceAeadIntCtxt.CtxSealInput.toModifiedNonceAeadSealInput input)).run primitive
      match encrypted.1 with
      | none => pure ((none, state), encrypted.2)
      | some ciphertext =>
        let suffix := CtxSplitCache.outerSuffix input.nonce input.context ciphertext.tag
        let commitment ← ctxKeyFreeSuffixStep suffix state.ctx.cache
        let record : CtxRomRecord := ⟨ciphertext.body, ciphertext.tag, ciphertext.tagLength, commitment.1⟩
        let next : ReceiveState :=
          ⟨state.ctx.addSeal ⟨input, record⟩ commitment.2, state.rawAttempts, suffix :: state.privateInputs⟩
        pure ((some record, next), encrypted.2)) := by
  simp only [directSeal, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  change (do let encrypted ← (modifiedNonceAeadINDDollarRandomSealOracle
    (CtxNonceAeadIntCtxt.CtxSealInput.toModifiedNonceAeadSealInput input)).run primitive
             _) = _
  apply bind_congr
  rintro ⟨encrypted, after⟩
  cases encrypted with
  | none => rfl
  | some ciphertext =>
    simp only [bind_pure_comp, simulateQ_map, StateT.run_map, private_step, Functor.map_map]
    rfl

/-- The full flattened sealer records the same actual optional reply in its redundant ordinary history. -/
theorem seal_base (decode : RawDecoder) (input : CtxSealInput) (state : State) :
    step decode (.inl (.inr (.inr input))) state =
      (fun result => (result.1.1,
        ((result.1.2, recordBase (.inl (.inr (.inr input))) result.1.1 state.1.2), result.2))) <$>
          (simulateQ modifiedNonceAeadINDDollarRandomImpl (directSeal input state.1.1)).run state.2 := by
  simp only [step, directWithBase, directImpl, StateT.run, bind_pure_comp, simulateQ_map]
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    ((fun reply => (reply.1, (reply.2, recordBase (.inl (.inr (.inr input))) reply.1 state.1.2))) <$>
      simulateQ modifiedNonceAeadINDDollarRandomImpl (directSeal input state.1.1)).run state.2 = _
  simp only [StateT.run_map, Functor.map_map]
  rfl

/-- Public projection after an actual selected seal: only its per-key nonce controls are changed. -/
def afterSeal (input : CtxSealInput) (state : State) : State :=
  ((⟨{(receive state.1.1).ctx with usedNonces := input.nonce :: state.1.1.ctx.usedNonces},
      state.1.1.rawAttempts, []⟩, []), ⟨input.nonce :: state.2.usedNonces, []⟩)

/-- The first selected seal samples its actual random body, tag and commitment without conditioning on any writer or later public reply. All tag-bearing private copies are retained until the final projection. -/
theorem first_seal (decode : RawDecoder) (input : CtxSealInput) (state : State) (unused : Unused state) :
    Prod.map id project <$> step decode (.inl (.inr (.inr input))) state = (do
      let body ← $ᵗ (FixedBytes input.plaintext.length)
      let tag ← $ᵗ (FixedBytes 16)
      let commitment ← $ᵗ CtxDigest
      pure (some (⟨body.toList, tag.toList, tag.toList_length, commitment⟩ : CtxRomRecord),
        afterSeal input state)) := by
  rw [seal_base, seal_step]
  simp only [modifiedNonceAeadINDDollarRandomSealOracle, StateT.run, unused.2,
    List.not_mem_nil, ite_false, map_bind]
  simp only [bind_assoc, pure_bind, CtxNonceAeadIntCtxt.CtxSealInput.toModifiedNonceAeadSealInput,
    ctxKeyFreeSuffixStep, unused.1, QueryCache.empty_apply, map_bind, map_pure]
  rfl

/-- A continuation that does not receive the seal reply and has no further selected seal/raw query has the exact joint random-record/public-view law. This is unconditional, including arbitrary future public-hash behavior. -/
theorem first_seal_suffix (decode : RawDecoder) (input : CtxSealInput) (state : State)
    (unused : Unused state) (work : OracleComp ReceiveSpec Result)
    (noSeal : work.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 0)
    (noRaw : work.IsQueryBoundP IsRawQuery 0) :
    (do let sealed ← step decode (.inl (.inr (.inr input))) state
        let final ← Prod.map id project <$> (simulateQ (impl decode) work).run sealed.2
        pure (sealed.1, final)) = (do
      let body ← $ᵗ (FixedBytes input.plaintext.length)
      let tag ← $ᵗ (FixedBytes 16)
      let commitment ← $ᵗ CtxDigest
      let final ← Prod.map id project <$> (simulateQ (impl decode) work).run (afterSeal input state)
      pure (some (⟨body.toList, tag.toList, tag.toList_length, commitment⟩ : CtxRomRecord), final)) := by
  have factor : (do
      let sealed ← step decode (.inl (.inr (.inr input))) state
      let final ← Prod.map id project <$> (simulateQ (impl decode) work).run sealed.2
      pure (sealed.1, final)) =
      (do let sealed ← Prod.map id project <$> step decode (.inl (.inr (.inr input))) state
          let final ← Prod.map id project <$> (simulateQ (impl decode) work).run sealed.2
          pure (sealed.1, final)) := by
    rw [bind_map_left]
    apply bind_congr
    intro sealed
    rw [program_project decode work noSeal noRaw sealed.2]
    rfl
  rw [factor, first_seal decode input state unused]
  simp only [bind_assoc, pure_bind]

/-- The existing ordinary random privacy game begins with both selected tables unused. -/
theorem initial_unused : Unused ((initialState, []), emptyModifiedNonceAeadHandlerState) :=
  ⟨rfl, rfl⟩

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.project_idempotent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.project_idempotent

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.uniform_step

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.lifted_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.lifted_step

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.public_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.public_step

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.public_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.public_project

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.quiet_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.quiet_project

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.program_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.program_project

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.program_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.program_congr

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.private_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.private_step

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.quiet_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.quiet_unused

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.program_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.program_unused

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.seal_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.seal_step

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.seal_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.seal_base

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.first_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.first_seal

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.first_seal_suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.first_seal_suffix

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.initial_unused' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView.initial_unused

