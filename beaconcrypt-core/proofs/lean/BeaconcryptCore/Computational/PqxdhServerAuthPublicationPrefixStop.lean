import BeaconcryptCore.Computational.PqxdhServerAuthPublicationDominance

/-! Explicit private publication markers connect a chronological before-raw condition to the actual stopped source. Markers are emitted only after complete callbacks; the original component interpreter owns all cryptographic state. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixStop
open PqxdhServerAuthPublicationPruning
variable {Result : Type}

abbrev Spec := AdaptiveCtxDynamicKnownKeys.Spec + (Bool →ₒ Unit)

def liftDynamic : QueryImpl AdaptiveCtxDynamicKnownKeys.Spec (OracleComp Spec) :=
  fun query => Spec.query (.inl query)

/-- Private markers have no source-visible result. -/
def erase : QueryImpl Spec (OracleComp AdaptiveCtxDynamicKnownKeys.Spec)
  | .inl query => AdaptiveCtxDynamicKnownKeys.Spec.query query
  | .inr _ => pure ()

/-- Killing acts after the complete callback emitted its actual publication marker. -/
def kill : QueryImpl Spec (OptionT (OracleComp AdaptiveCtxDynamicKnownKeys.Spec))
  | .inl query => OptionT.mk (some <$> AdaptiveCtxDynamicKnownKeys.Spec.query query)
  | .inr published => OptionT.mk (pure (if published then none else some ()))

/-- Erasing private markers preserves every original component query and continuation. -/
theorem erase_lift (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result) :
    simulateQ erase (simulateQ liftDynamic work) = work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : erase ∘ₛ liftDynamic = QueryImpl.id' AdaptiveCtxDynamicKnownKeys.Spec := by
    funext query
    rfl
  rw [same, simulateQ_id']

/-- The kill interpreter forwards an original component program in full when it contains no marker. -/
theorem kill_lift (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result) :
    (simulateQ kill (simulateQ liftDynamic work)).run = some <$> work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, liftDynamic, kill, OptionT.run_bind,
        OptionT.run_mk, Option.elimM, bind_map_left, Option.elim_some, map_bind]
      exact bind_congr ih

/-- Observe the publication flag at the first selected raw query, retaining all real preceding replies and the actual selected seal record. Later markers cannot change that prefix. -/
noncomputable def capture (work : OracleComp Spec Result) :
    Option CtxRomAuth.CtxRomRecord → Bool → OracleComp AdaptiveCtxDynamicKnownKeys.Spec
      (Bool × PqxdhServerAuthPublicationGuess.Candidate) :=
  OracleComp.recOn work
    (fun _ _ published => pure (published, none))
    (fun query _ recurse saved published => match query with
      | .inl (.inl (.inr raw)) => pure (published, saved.map fun record => (record, raw))
      | .inl query => do
          let reply ← AdaptiveCtxDynamicKnownKeys.Spec.query query
          recurse reply (remembered query reply saved) published
      | .inr flag => recurse () saved (published || flag))

/-- Nonraw source queries execute before either the saved record or the marker-prefix observation advances. -/
theorem capture_query (query : AdaptiveCtxDynamicKnownKeys.Spec.Domain)
    (notRaw : ∀ raw, query ≠ .inl (.inr raw))
    (next : AdaptiveCtxDynamicKnownKeys.Spec.Range query → OracleComp Spec Result)
    (saved : Option CtxRomAuth.CtxRomRecord) (published : Bool) :
    capture (do let reply ← Spec.query (.inl query); next reply) saved published = (do
      let reply ← AdaptiveCtxDynamicKnownKeys.Spec.query query
      capture (next reply) (remembered query reply saved) published) := by
  rcases query with (((coin | (input | request)) | raw) | known)
  all_goals try rfl
  exact (notRaw raw rfl).elim

/-- Once a publication marker precedes the first raw request, the clean-prefix capture event has zero mass under every complete stateful interpreter. -/
theorem capture_seen_zero {State : Type}
    (impl : QueryImpl AdaptiveCtxDynamicKnownKeys.Spec (StateT State ProbComp))
    (work : OracleComp Spec Result) (saved : Option CtxRomAuth.CtxRomRecord) (state : State)
    (event : PqxdhServerAuthPublicationGuess.Candidate → Prop) :
    Pr{let result ← (simulateQ impl (capture work saved true)).run state}[result.1.1 = false ∧ event result.1.2] = 0 := by
  classical
  induction work using OracleComp.inductionOn generalizing saved state with
  | pure value =>
      change Pr{let result ← (pure ((true, none), state) : ProbComp ((Bool × PqxdhServerAuthPublicationGuess.Candidate) × State))}[result.1.1 = false ∧ event result.1.2] = 0
      rw [prEvent_pure]
      simp
  | query_bind query next ih =>
      cases query with
      | inl query =>
          rcases Classical.em (∃ bytes : Pqxdh.Bytes, query = .inl (.inr bytes)) with raw | raw
          · obtain ⟨bytes, rfl⟩ := raw
            change Pr{let result ← (pure ((true, saved.map fun record => (record, bytes)), state) : ProbComp _)}[result.1.1 = false ∧ event result.1.2] = 0
            rw [prEvent_pure]
            simp
          · rw [capture_query query (fun bytes equal => raw ⟨bytes, equal⟩)]
            simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, OracleComp.prEvent_bind_eq_tsum,
              ih, mul_zero, tsum_zero]
      | inr flag => exact ih () saved state

/-- Clean first-raw capture in the full marker program has exactly the event probability of capture after killing on the first publication marker. The interpreter and every preceding callback effect are shared. -/
theorem clean_capture {State : Type}
    (impl : QueryImpl AdaptiveCtxDynamicKnownKeys.Spec (StateT State ProbComp))
    (work : OracleComp Spec Result) (saved : Option CtxRomAuth.CtxRomRecord) (state : State)
    (event : PqxdhServerAuthPublicationGuess.Candidate → Prop) (empty : ¬ event none) :
    Pr{let result ← (simulateQ impl (capture work saved false)).run state}[result.1.1 = false ∧ event result.1.2] =
    Pr{let result ← ((simulateQ impl
      (PqxdhServerAuthPublicationCaptureSource.dynamic (simulateQ kill work).run saved)).run state)}[event result.1] := by
  classical
  induction work using OracleComp.inductionOn generalizing saved state with
  | pure value =>
      change Pr{let result ← (pure ((false, none), state) : ProbComp _)}[result.1.1 = false ∧ event result.1.2] =
        Pr{let result ← (pure (none, state) : ProbComp _)}[event result.1]
      rw [prEvent_pure, prEvent_pure]
      simp [empty]
  | query_bind query next ih =>
      cases query with
      | inl query =>
          simp only [simulateQ_bind, simulateQ_spec_query, kill, OptionT.run_bind,
            OptionT.run_mk, Option.elimM, bind_map_left, Option.elim_some]
          rcases Classical.em (∃ bytes : Pqxdh.Bytes, query = .inl (.inr bytes)) with raw | raw
          · obtain ⟨bytes, rfl⟩ := raw
            change Pr{let result ← (pure ((false, saved.map fun record => (record, bytes)), state) : ProbComp _)}[result.1.1 = false ∧ event result.1.2] =
              Pr{let result ← (pure (saved.map fun record => (record, bytes), state) : ProbComp _)}[event result.1]
            rw [prEvent_pure, prEvent_pure]
            simp
          · rw [capture_query query (fun bytes equal => raw ⟨bytes, equal⟩)]
            have step := dynamic_query (Left := Option Result) query (fun bytes equal => raw ⟨bytes, equal⟩)
              (fun reply => (simulateQ kill (next reply)).run) saved
            refine Eq.trans ?_ (congrArg (fun program =>
              Pr{let result ← (simulateQ impl program).run state}[event result.1]) step.symm)
            simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, OracleComp.prEvent_bind_eq_tsum]
            exact tsum_congr fun reply => congrArg (fun value => _ * value) (ih reply.1 _ reply.2)
      | inr flag =>
          cases flag with
          | false => exact ih () saved state
          | true =>
              rw [show capture (do let reply ← Spec.query (.inr true); next reply) saved false =
                capture (next ()) saved true from rfl]
              rw [capture_seen_zero]
              change 0 = Pr{let result ← (pure (none, state) : ProbComp _)}[event result.1]
              rw [prEvent_pure]
              simp [empty]

/-- The exact clean-prefix comparison retains the actual selected-key draw and initial shared source state. -/
theorem source_clean (real : Bool) (decode : AdaptiveCtxReceive.RawDecoder) (crypto : Pqxdh.Crypto)
    (work : OracleComp Spec Result) (saved : Option CtxRomAuth.CtxRomRecord)
    (event : PqxdhServerAuthPublicationGuess.Candidate → Prop) (empty : ¬ event none) :
    Pr{let result ← AdaptiveCtxDynamicKnownKeys.sourceGame real decode crypto (capture work saved false)}[result.1.1 = false ∧ event result.1.2] =
    Pr{let result ← (AdaptiveCtxDynamicKnownKeys.sourceGame real decode crypto
      (PqxdhServerAuthPublicationCaptureSource.dynamic (simulateQ kill work).run saved))}[event result.1] := by
  simp only [AdaptiveCtxDynamicKnownKeys.sourceGame, OracleComp.prEvent_bind_eq_tsum]
  exact tsum_congr fun key => congrArg (fun value => _ * value)
    (clean_capture (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key) work saved
      AdaptiveCtxDynamicKnownKeys.initialSource event empty)

/-- Prefix capture preserves every original component query before its raw cutoff. Marker bookkeeping cannot introduce a component query or discard a reached callback prefix. -/
theorem capture_prunes (work : OracleComp Spec Result) (saved : Option CtxRomAuth.CtxRomRecord)
    (published : Bool) : Prunes (capture work saved published) (simulateQ erase work) := by
  induction work using OracleComp.inductionOn generalizing saved published with
  | pure value => exact .stop (published, none) _
  | query_bind query next ih =>
      cases query with
      | inl query =>
          simp only [simulateQ_bind, simulateQ_spec_query, erase]
          rcases Classical.em (∃ bytes : Pqxdh.Bytes, query = .inl (.inr bytes)) with raw | raw
          · obtain ⟨bytes, rfl⟩ := raw
            exact .stop (published, saved.map fun record => (record, bytes)) _
          · rw [capture_query query (fun bytes equal => raw ⟨bytes, equal⟩)]
            exact .query query _ _ fun reply => ih reply _ published
      | inr flag =>
          simp only [simulateQ_bind, simulateQ_spec_query, erase, pure_bind]
          change Prunes (capture (next ()) saved (published || flag)) (simulateQ erase (next ()))
          exact ih () saved (published || flag)

/-- The first selected raw bytes are observed without issuing a selected opening, including malformed bytes. Known-key calls retain their original full work. -/
theorem capture_no_raw (work : OracleComp Spec Result) (saved : Option CtxRomAuth.CtxRomRecord)
    (published : Bool) :
    (capture work saved published).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 := by
  induction work using OracleComp.inductionOn generalizing saved published with
  | pure value => trivial
  | query_bind query next ih =>
      cases query with
      | inr flag => exact ih () saved (published || flag)
      | inl query =>
          rcases Classical.em (∃ bytes : Pqxdh.Bytes, query = .inl (.inr bytes)) with raw | raw
          · obtain ⟨bytes, rfl⟩ := raw
            trivial
          · rw [capture_query query (fun bytes equal => raw ⟨bytes, equal⟩), isQueryBoundP_query_bind_iff]
            have quiet : ¬ AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery query := by
              rcases query with (selected | bytes) | known
              · simp [AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxReceive.IsRawQuery]
              · exact fun _ => raw ⟨bytes, rfl⟩
              · simp [AdaptiveCtxDynamicKnownBounds.TargetClass]
            exact ⟨Or.inl quiet, fun reply => by simpa only [quiet, ↓reduceIte, Nat.sub_zero] using ih reply _ published⟩

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixStop

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixStop.erase_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixStop.erase_lift
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixStop.kill_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixStop.kill_lift
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixStop.capture_query' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixStop.capture_query
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixStop.capture_seen_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixStop.capture_seen_zero
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixStop.clean_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixStop.clean_capture
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixStop.source_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixStop.source_clean
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixStop.capture_prunes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixStop.capture_prunes
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixStop.capture_no_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixStop.capture_no_raw
