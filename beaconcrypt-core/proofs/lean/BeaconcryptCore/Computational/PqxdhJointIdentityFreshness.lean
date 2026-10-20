import BeaconcryptCore.Computational.PqxdhJointIdentitySessions
import BeaconcryptCore.Computational.VCVioForwardOracleComp

/-!
# Identity reveals and explicit target freshness

The global wrapper returns actual generated seeds for identity-reveal requests and records the complete reveal order. Target freshness means the selected identity has not been revealed before the final test. A reduction stops at a reveal of its selected target; no primitive endpoint is changed to provide an unavailable secret. Later event-relative compromise and production ownership/lookup remain separate global interfaces.
-/

open OracleSpec OracleComp ENNReal
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhJointIdentityFreshness

open PqxdhJointIdentity PqxdhJointIdentityFamily

abbrev RevealSpec (count : ℕ) : OracleSpec (Fin count) := fun _ => IdentitySeed
abbrev GlobalSpec (count : ℕ) := FamilyAdversarySpec count + RevealSpec count

/-- Every generated identity has its full sign/DH history, plus one global chronological reveal log. -/
structure GlobalState (count : ℕ) where
  histories : FamilyHistory count
  reveals : List (Fin count)

def initialState (count : ℕ) : GlobalState count := ⟨emptyHistory count, []⟩

/-- Reveals return the actual generated seed, even for an identity later selected as the target. -/
def sourceImpl (primitives : Primitives) {count : ℕ} (seeds : Fin count → IdentitySeed) :
    QueryImpl (GlobalSpec count) (StateT (GlobalState count) ProbComp) := fun query state =>
  match query with
  | .inl request => do
    let (answer, histories) ← (familyImpl primitives seeds request).run state.histories
    pure (answer, { state with histories })
  | .inr identity => pure (seeds identity, { state with reveals := state.reveals ++ [identity] })

/-- Once revealed, an identity remains recorded through every subsequent source query. -/
theorem sourceImpl_revealed (primitives : Primitives) {count : ℕ} (seeds : Fin count → IdentitySeed)
    (target : Fin count) :
    QueryImpl.PreservesInv (sourceImpl primitives seeds) (fun state => target ∈ state.reveals) := by
  intro query state revealed result supported
  cases query with
  | inl request =>
    simp only [sourceImpl, StateT.run, mem_support_bind_iff] at supported
    obtain ⟨⟨answer, histories⟩, _, supported⟩ := supported
    simp only [mem_support_pure_iff] at supported
    subst result
    exact revealed
  | inr identity =>
    simp only [sourceImpl, StateT.run, mem_support_pure_iff] at supported
    subst result
    exact List.mem_append_left _ revealed

/-- An arbitrary complete continuation cannot restore a revealed identity's freshness. -/
theorem sourceRun_revealed (primitives : Primitives) {count : ℕ} (seeds : Fin count → IdentitySeed)
    (target : Fin count) {Result : Type} (client : OracleComp (GlobalSpec count) Result)
    (state : GlobalState count) (revealed : target ∈ state.reveals) :
    ∀ result ∈ support ((simulateQ (sourceImpl primitives seeds) client).run state),
      target ∈ result.2.reveals :=
  OracleComp.simulateQ_run_preserves_inv_of_query (sourceImpl primitives seeds)
    (fun state => target ∈ state.reveals) (sourceImpl_revealed primitives seeds target) client state revealed

/-- Stop before releasing the selected target seed while retaining every earlier actual query and reply. -/
def stopBeforeReveal {count : ℕ} (target : Fin count) {Result : Type}
    (client : OracleComp (GlobalSpec count) Result) : OracleComp (GlobalSpec count) (Option Result) :=
  OracleComp.recOn client
    (fun result => pure (some result))
    (fun query _ recurse => match query with
      | .inl request => do
        let answer ← (GlobalSpec count).query (.inl request)
        recurse answer
      | .inr identity =>
        if identity = target then pure none else do
          let answer ← (GlobalSpec count).query (.inr identity)
          recurse answer)

@[simp] theorem stopBeforeReveal_pure {count : ℕ} (target : Fin count) {Result : Type} (value : Result) :
    stopBeforeReveal target (pure value) = pure (some value) := rfl

@[simp] theorem stopBeforeReveal_service {count : ℕ} (target : Fin count) {Result : Type}
    (request : (FamilyAdversarySpec count).Domain)
    (next : (FamilyAdversarySpec count).Range request → OracleComp (GlobalSpec count) Result) :
    stopBeforeReveal target ((GlobalSpec count).query (.inl request) >>= next) = (do
      let answer ← (GlobalSpec count).query (.inl request)
      stopBeforeReveal target (next answer)) := rfl

@[simp] theorem stopBeforeReveal_reveal {count : ℕ} (target identity : Fin count) {Result : Type}
    (next : IdentitySeed → OracleComp (GlobalSpec count) Result) :
    stopBeforeReveal target ((GlobalSpec count).query (.inr identity) >>= next) =
      (if identity = target then pure none else do
        let answer ← (GlobalSpec count).query (.inr identity)
        stopBeforeReveal target (next answer)) := rfl

/-- Freshness is a global wrapper predicate; the underlying primitive game still uses ordinary message freshness. -/
def Fresh {count : ℕ} (target : Fin count) (state : GlobalState count) : Prop := target ∉ state.reveals

/-- Revealed identities contribute zero to every fresh final event, regardless of the complete later continuation. -/
theorem revealed_fresh_probability_zero (primitives : Primitives) {count : ℕ}
    (seeds : Fin count → IdentitySeed) (target : Fin count) {Result : Type}
    (client : OracleComp (GlobalSpec count) Result) (state : GlobalState count)
    (revealed : target ∈ state.reveals) (observer : Result × GlobalState count → Prop) :
    Pr{let result ← (simulateQ (sourceImpl primitives seeds) client).run state}[
      Fresh target result.2 ∧ observer result] = 0 := by
  refine prEvent_eq_zero_of_forall_mem_support _ _ fun result supported accepted => ?_
  exact accepted.1 (sourceRun_revealed primitives seeds target client state revealed result supported)

/-- Aborted runs have no fresh target output; surviving runs retain the complete client result and global state. -/
def StoppedEvent {count : ℕ} (target : Fin count) {Result : Type}
    (observer : Result × GlobalState count → Prop) (result : Option Result × GlobalState count) : Prop :=
  match result.1 with
  | none => False
  | some value => Fresh target result.2 ∧ observer (value, result.2)

/-- Stopping at target compromise preserves every fresh full-output event, rather than assuming no adversary ever requests that reveal. -/
theorem fresh_probability_eq_stopped (primitives : Primitives) {count : ℕ}
    (seeds : Fin count → IdentitySeed) (target : Fin count) {Result : Type}
    (client : OracleComp (GlobalSpec count) Result) (state : GlobalState count)
    (fresh : Fresh target state) (observer : Result × GlobalState count → Prop) :
    Pr{let result ← (simulateQ (sourceImpl primitives seeds) client).run state}[
      Fresh target result.2 ∧ observer result] =
    Pr{let result ← (simulateQ (sourceImpl primitives seeds) (stopBeforeReveal target client)).run state}[
      StoppedEvent target observer result] := by
  classical
  induction client using OracleComp.inductionOn generalizing state with
  | pure value =>
      rw [stopBeforeReveal_pure, simulateQ_pure, simulateQ_pure, StateT.run_pure, StateT.run_pure,
        prEvent_pure, prEvent_pure]
      by_cases accepted : Fresh target state ∧ observer (value, state)
      · simp [StoppedEvent, accepted]
      · simp [StoppedEvent, accepted]
  | query_bind query rest ih =>
    cases query with
    | inl request =>
      rw [stopBeforeReveal_service]
      simp only [simulateQ_query_bind, StateT.run_bind]
      change Pr{let result ←
          (((familyImpl primitives seeds request).run state.histories >>= fun result =>
            pure (result.1, { state with histories := result.2 })) >>= fun result =>
              (simulateQ (sourceImpl primitives seeds) (rest result.1)).run result.2 : ProbComp _)}[
          Fresh target result.2 ∧ observer result] =
        Pr{let result ←
          (((familyImpl primitives seeds request).run state.histories >>= fun result =>
            pure (result.1, { state with histories := result.2 })) >>= fun result =>
              (simulateQ (sourceImpl primitives seeds) (stopBeforeReveal target (rest result.1))).run
                result.2 : ProbComp _)}[StoppedEvent target observer result]
      have shape {β : Type} (next : _ → ProbComp β) :
          (((familyImpl primitives seeds request).run state.histories >>= fun result =>
            pure (result.1, { state with histories := result.2 })) >>= next) =
          ((familyImpl primitives seeds request).run state.histories >>= fun result =>
            next (result.1, { state with histories := result.2 })) := by
        simp only [bind_assoc, pure_bind]
      rw [shape, shape]
      exact prEvent_bind_congr _ _ _ _ _ fun result =>
        ih result.1 { state with histories := result.2 } fresh
    | inr identity =>
      rw [stopBeforeReveal_reveal]
      by_cases selected : identity = target
      · subst identity
        have sourceStep :
            (sourceImpl primitives seeds (.inr target)).run state =
              pure (seeds target, { state with reveals := state.reveals ++ [target] }) := rfl
        have stopped : ¬StoppedEvent target observer (none, state) := by
          simp [StoppedEvent]
        have run : (simulateQ (sourceImpl primitives seeds)
            ((GlobalSpec count).query (.inr target) >>= rest)).run state =
            (simulateQ (sourceImpl primitives seeds) (rest (seeds target))).run
              { state with reveals := state.reveals ++ [target] } := by
          simp only [simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query,
            id_eq, monadLift_self, StateT.run_bind, sourceStep, pure_bind]
        rw [ite_eq_left rfl, run, simulateQ_pure, StateT.run_pure, prEvent_pure, ite_eq_right stopped]
        exact revealed_fresh_probability_zero primitives seeds target _ _ (by simp) observer
      · simp only [selected, ite_false, simulateQ_query_bind, StateT.run_bind]
        change Pr{let result ←
            (pure (seeds identity, { state with reveals := state.reveals ++ [identity] }) >>= fun value =>
              (simulateQ (sourceImpl primitives seeds) (rest value.1)).run value.2 : ProbComp _)}[
            Fresh target result.2 ∧ observer result] =
          Pr{let result ←
            (pure (seeds identity, { state with reveals := state.reveals ++ [identity] }) >>= fun value =>
              (simulateQ (sourceImpl primitives seeds) (stopBeforeReveal target (rest value.1))).run
                value.2 : ProbComp _)}[StoppedEvent target observer result]
        rw [pure_bind, pure_bind]
        apply ih
        simpa [Fresh, List.mem_append, selected, Ne.symm selected] using fresh

/-- The exact selected identity-reveal request is a global-interface class, not a primitive oracle. -/
def IsTargetReveal {count : ℕ} (target : Fin count) : (GlobalSpec count).Domain → Prop
  | .inl _ => False
  | .inr identity => identity = target

instance {count : ℕ} (target : Fin count) : DecidablePred (IsTargetReveal target) := fun query => by
  cases query with
  | inl request => exact inferInstanceAs (Decidable False)
  | inr identity => exact inferInstanceAs (Decidable (identity = target))

/-- The stopped reduction never asks an interpreter to manufacture the target's unavailable seed. -/
theorem stopBeforeReveal_no_target {count : ℕ} (target : Fin count) {Result : Type}
    (client : OracleComp (GlobalSpec count) Result) :
    (stopBeforeReveal target client).IsQueryBoundP (IsTargetReveal target) 0 := by
  induction client using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query rest ih =>
    cases query with
    | inl request =>
      rw [stopBeforeReveal_service, OracleComp.isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl id, fun answer => ih answer⟩
    | inr identity =>
      rw [stopBeforeReveal_reveal]
      by_cases selected : identity = target
      · simp [selected]
      · simp only [selected, ite_false, OracleComp.isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl selected, fun answer => by simpa [IsTargetReveal, selected] using ih answer⟩

/-- Stopping at compromise retains every source class cap, including non-target reveal traffic. -/
theorem stopBeforeReveal_query_bound {count : ℕ} (target : Fin count) {Result : Type}
    (client : OracleComp (GlobalSpec count) Result) (predicate : (GlobalSpec count).Domain → Prop)
    [DecidablePred predicate] (bound : ℕ) (bounded : client.IsQueryBoundP predicate bound) :
    (stopBeforeReveal target client).IsQueryBoundP predicate bound := by
  induction client using OracleComp.inductionOn generalizing bound with
  | pure value => simp
  | query_bind query rest ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
    cases query with
    | inl request =>
      rw [stopBeforeReveal_service, OracleComp.isQueryBoundP_query_bind_iff]
      exact ⟨bounded.1, fun answer => ih answer _ (bounded.2 answer)⟩
    | inr identity =>
      rw [stopBeforeReveal_reveal]
      by_cases selected : identity = target
      · simp [selected]
      · simp only [selected, ite_false, OracleComp.isQueryBoundP_query_bind_iff]
        exact ⟨bounded.1, fun answer => ih answer _ (bounded.2 answer)⟩

/-- Locally answer only other identities' reveals and delegate all shared identity services unchanged. The target branch is unreachable in every stopped client. -/
def revealRouting {count : ℕ} (target : Fin (count + 1)) (others : Fin count → IdentitySeed) :
    QueryImpl (GlobalSpec (count + 1))
      (StateT (List (Fin (count + 1))) (OracleComp (FamilyAdversarySpec (count + 1)))) := fun query reveals =>
  match query with
  | .inl request => do
    let answer ← (FamilyAdversarySpec (count + 1)).query request
    pure (answer, reveals)
  | .inr identity =>
    Fin.succAboveCases target
      (pure (⟨List.replicate 32 0, by simp⟩, reveals ++ [target]))
      (fun other => pure (others other, reveals ++ [target.succAbove other])) identity

/-- Explicitly combine the reveal-order state with the complete per-identity histories. -/
def revealState {count : ℕ} (state : List (Fin count) × FamilyHistory count) : GlobalState count :=
  ⟨state.2, state.1⟩

/-- Away from the stopped target reveal, local reveal routing returns the exact source seed and complete global state. -/
theorem revealRouting_step (primitives : Primitives) {count : ℕ} (target : Fin (count + 1))
    (seed : IdentitySeed) (others : Fin count → IdentitySeed)
    (query : (GlobalSpec (count + 1)).Domain) (permitted : ¬IsTargetReveal target query)
    (state : List (Fin (count + 1)) × FamilyHistory (count + 1)) :
    Prod.map id revealState <$>
      (QueryImpl.Stateful.link (revealRouting target others)
        (familyImpl primitives (target.insertNth seed others)) query).run state =
      (sourceImpl primitives (target.insertNth seed others) query).run (revealState state) := by
  rcases state with ⟨reveals, histories⟩
  rw [QueryImpl.Stateful.link_impl_apply_run, Functor.map_map]
  change (fun result : ((GlobalSpec (count + 1)).Range query × List (Fin (count + 1))) × FamilyHistory (count + 1) =>
    (result.1.1, (⟨result.2, result.1.2⟩ : GlobalState (count + 1)))) <$>
    (simulateQ (familyImpl primitives (target.insertNth seed others))
      ((revealRouting target others query).run reveals)).run histories = _
  cases query with
  | inl request =>
    simp only [revealRouting, StateT.run, bind_pure_comp, simulateQ_map, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map]
    change (fun result : ((FamilyAdversarySpec (count + 1)).Range request × List (Fin (count + 1))) × FamilyHistory (count + 1) =>
      (result.1.1, (⟨result.2, result.1.2⟩ : GlobalState (count + 1)))) <$>
      (do let result ← (familyImpl primitives (target.insertNth seed others) request).run histories
          pure ((result.1, reveals), result.2) : ProbComp _) = _
    simp [sourceImpl, StateT.run, revealState, bind_pure_comp, Functor.map_map]
  | inr identity =>
    induction identity using Fin.succAboveCases target with
    | x => exact False.elim (permitted rfl)
    | p other =>
      simp [revealRouting, sourceImpl, StateT.run, revealState]
      change (fun result : (IdentitySeed × List (Fin (count + 1))) × FamilyHistory (count + 1) =>
        (result.1.1, (⟨result.2, result.1.2⟩ : GlobalState (count + 1)))) <$>
        (pure ((others other, reveals ++ [target.succAbove other]), histories) : ProbComp _) = _
      simp

/-- A complete client with no selected-target reveal has exactly the source global-state projection under local reveal routing. -/
theorem revealRouting_complete (primitives : Primitives) {count : ℕ} (target : Fin (count + 1))
    (seed : IdentitySeed) (others : Fin count → IdentitySeed) {Result : Type}
    (client : OracleComp (GlobalSpec (count + 1)) Result)
    (noTarget : client.IsQueryBoundP (IsTargetReveal target) 0)
    (state : List (Fin (count + 1)) × FamilyHistory (count + 1)) :
    Prod.map id revealState <$>
      (simulateQ (QueryImpl.Stateful.link (revealRouting target others)
        (familyImpl primitives (target.insertNth seed others))) client).run state =
      (simulateQ (sourceImpl primitives (target.insertNth seed others)) client).run (revealState state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query rest ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at noTarget
    have permitted : ¬IsTargetReveal target query := noTarget.1.resolve_right (by omega)
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rw [← revealRouting_step primitives target seed others query permitted state, bind_map_left]
    apply bind_congr
    intro result
    exact ih result.1 (by simpa only [permitted, ite_false] using noTarget.2 result.1) result.2

/-- The actual stopped global client is eligible for exact local reveal simulation by a proved zero target-reveal bound. -/
theorem stopped_revealRouting_complete (primitives : Primitives) {count : ℕ}
    (target : Fin (count + 1)) (seed : IdentitySeed) (others : Fin count → IdentitySeed)
    {Result : Type} (client : OracleComp (GlobalSpec (count + 1)) Result)
    (reveals : List (Fin (count + 1))) (histories : FamilyHistory (count + 1)) :
    (fun result : ((Option Result × List (Fin (count + 1))) × FamilyHistory (count + 1)) =>
      (result.1.1, (⟨result.2, result.1.2⟩ : GlobalState (count + 1)))) <$>
      (simulateQ (familyImpl primitives (target.insertNth seed others))
        ((simulateQ (revealRouting target others) (stopBeforeReveal target client)).run reveals)).run histories =
    (simulateQ (sourceImpl primitives (target.insertNth seed others)) (stopBeforeReveal target client)).run
      ⟨histories, reveals⟩ := by
  have complete := revealRouting_complete primitives target seed others (stopBeforeReveal target client)
    (stopBeforeReveal_no_target target client) (reveals, histories)
  rw [QueryImpl.Stateful.simulateQ_link_run, Functor.map_map] at complete
  exact complete

/-- The whole stopped client is executable with only the locally generated non-target identity seeds. -/
def reductionWork {count : ℕ} (primitives : Primitives) (target : Fin (count + 1))
    (others : Fin count → IdentitySeed) {Result : Type}
    (client : OracleComp (GlobalSpec (count + 1)) Result)
    (reveals : List (Fin (count + 1))) (localHistory : FamilyHistory count) :
    OracleComp AdversarySpec ((Option Result × List (Fin (count + 1))) × FamilyHistory count) :=
  (simulateQ (PqxdhJointIdentityFamily.reductionImpl primitives target others)
    ((simulateQ (revealRouting target others) (stopBeforeReveal target client)).run reveals)).run localHistory

/-- Combine the actual challenger history and all local histories/reveals without exposing the target seed. -/
def reductionState {count : ℕ} (target : Fin (count + 1)) {Result : Type}
    (result : (((Option Result × List (Fin (count + 1))) × FamilyHistory count) × History)) :
    Option Result × GlobalState (count + 1) :=
  (result.1.1.1, ⟨combineHistory target (result.1.2, result.2), result.1.1.2⟩)

/-- Full source state on the stopped execution equals the constructed reduction's complete retained state, including all permitted prior reveals. -/
theorem reductionWork_complete (primitives : Primitives) {count : ℕ} (target : Fin (count + 1))
    (seed : IdentitySeed) (others : Fin count → IdentitySeed) {Result : Type}
    (client : OracleComp (GlobalSpec (count + 1)) Result)
    (reveals : List (Fin (count + 1))) (localHistory : FamilyHistory count) (targetHistory : History) :
    reductionState target <$>
      (simulateQ (jointImpl primitives seed)
        (reductionWork primitives target others client reveals localHistory)).run targetHistory =
    (simulateQ (sourceImpl primitives (target.insertNth seed others)) (stopBeforeReveal target client)).run
      ⟨combineHistory target (localHistory, targetHistory), reveals⟩ := by
  rw [← stopped_revealRouting_complete]
  rw [← targetRouting_complete primitives target seed others]
  simp only [Functor.map_map, reductionWork]
  rfl

/-- A source-shaped global client observes public identities, requests arbitrary services/reveals, then selects one ordinary forgery. -/
def globalRun (primitives : Primitives) (count : ℕ)
    (adversary : (Fin count → PublicIdentity) → OracleComp (GlobalSpec count) (FamilyForgery count)) :
    ProbComp ((Fin count → PublicIdentity) × FamilyForgery count × GlobalState count) := do
  let seeds ← sampleFamily count
  let (result, state) ← (simulateQ (sourceImpl primitives seeds)
    (adversary (familyPublic primitives seeds))).run (initialState count)
  pure (familyPublic primitives seeds, result, state)

def TargetEvent (primitives : Primitives) {count : ℕ} (target : Fin count)
    (result : (Fin count → PublicIdentity) × FamilyForgery count × GlobalState count) : Prop :=
  Fresh target result.2.2 ∧
    wins primitives (result.1 target) result.2.1.forgery (result.2.2.histories target) = true

/-- Reveal freshness and signature-message freshness are separate, explicit tests. -/
def GlobalEvent (primitives : Primitives) {count : ℕ}
    (result : (Fin count → PublicIdentity) × FamilyForgery count × GlobalState count) : Prop :=
  TargetEvent primitives result.2.1.identity result

/-- Aborted target-compromise branches return only a fixed ordinary forgery; they can only enlarge the upper bound. -/
def fallbackForgery {count : ℕ} (fallback : Forgery) (result : Option (FamilyForgery count)) : Forgery :=
  (result.map FamilyForgery.forgery).getD fallback

/-- The actual joint-use reduction knows only the other identities' seeds and never requests a target reveal. -/
def globalReduction (primitives : Primitives) {count : ℕ} (target : Fin (count + 1))
    (fallback : Forgery)
    (adversary : (Fin (count + 1) → PublicIdentity) →
      OracleComp (GlobalSpec (count + 1)) (FamilyForgery (count + 1)))
    (jointPublic : PublicIdentity) : OracleComp AdversarySpec Forgery := do
  let others ← OracleComp.liftComp (sampleFamily count) AdversarySpec
  let result ← reductionWork primitives target others
    (adversary (target.insertNth jointPublic (familyPublic primitives others))) [] (emptyHistory count)
  pure (fallbackForgery fallback result.1.1)

/-- For each fixed full seed family, every fresh target forgery gives an ordinary joint-use challenger win under the exact stopped simulation. -/
theorem freshExecution_le_reductionWork (primitives : Primitives) {count : ℕ}
    (target : Fin (count + 1)) (seed : IdentitySeed) (others : Fin count → IdentitySeed)
    (fallback : Forgery) (client : OracleComp (GlobalSpec (count + 1)) (FamilyForgery (count + 1))) :
    Pr{let result ← (simulateQ (sourceImpl primitives (target.insertNth seed others)) client).run
        (initialState (count + 1))}[Fresh target result.2 ∧
      wins primitives (primitives.publicKeys seed) result.1.forgery (result.2.histories target) = true] ≤
    Pr{let result ← (simulateQ (jointImpl primitives seed)
        (reductionWork primitives target others client [] (emptyHistory count))).run []}[
      wins primitives (primitives.publicKeys seed) (fallbackForgery fallback result.1.1.1) result.2 = true] := by
  rw [fresh_probability_eq_stopped primitives (target.insertNth seed others) target client
    (initialState (count + 1)) (by simp [Fresh, initialState])]
  have exactRun := reductionWork_complete primitives target seed others client [] (emptyHistory count) []
  simp only [combineHistory_empty] at exactRun
  rw [show initialState (count + 1) = ⟨emptyHistory (count + 1), []⟩ from rfl,
    ← exactRun, prEvent_map]
  apply prEvent_mono
  intro result accepted
  dsimp only [Function.comp_apply, reductionState, StoppedEvent] at accepted
  cases completed : result.1.1.1 with
  | none => simp [completed] at accepted
  | some forgery =>
    rw [completed] at accepted
    simpa [fallbackForgery, completed, combineHistory] using accepted.2

/-- The target-indexed global event reduces to the ordinary joint-use game even though the source permits every identity reveal. -/
theorem targetEvent_le_jointAdvantage (primitives : Primitives) {count : ℕ}
    (target : Fin (count + 1)) (fallback : Forgery)
    (adversary : (Fin (count + 1) → PublicIdentity) →
      OracleComp (GlobalSpec (count + 1)) (FamilyForgery (count + 1))) :
    Pr{let result ← globalRun primitives (count + 1) adversary}[TargetEvent primitives target result] ≤
      advantage primitives (globalReduction primitives target fallback adversary) := by
  have reordered :
      Pr{let result ← globalRun primitives (count + 1) adversary}[TargetEvent primitives target result] =
      Pr{let result ← (do
        let seed ← sampleSeed
        let others ← sampleFamily count
        let (result, state) ← (simulateQ (sourceImpl primitives (target.insertNth seed others))
          (adversary (familyPublic primitives (target.insertNth seed others)))).run (initialState (count + 1))
        pure (familyPublic primitives (target.insertNth seed others), result, state))}[
        TargetEvent primitives target result] :=
    (sampleFamily_target_first count target _).prEvent_eq _
  rw [reordered]
  simp only [advantage, game, run, globalReduction, simulateQ_bind, StateT.run_bind,
    simulateQ_pure, StateT.run_pure, simulate_joint_uniform, bind_map_left, pure_bind, bind_assoc]
  refine OracleComp.prEvent_bind_mono_of_support _ _ _ fun seed _ => ?_
  refine OracleComp.prEvent_bind_mono_of_support _ _ _ fun others _ => ?_
  simp only [TargetEvent, familyPublic_insertNth, Fin.insertNth_apply_same]
  exact freshExecution_le_reductionWork primitives target seed others fallback _

/-- Adaptive final identity selection incurs one sum over generated identities, even with arbitrary non-target reveals. -/
theorem global_advantage_le_sum (primitives : Primitives) (count : ℕ) (fallback : Forgery)
    (adversary : (Fin (count + 1) → PublicIdentity) →
      OracleComp (GlobalSpec (count + 1)) (FamilyForgery (count + 1))) :
    Pr{let result ← globalRun primitives (count + 1) adversary}[GlobalEvent primitives result] ≤
      ∑ target : Fin (count + 1), advantage primitives (globalReduction primitives target fallback adversary) := by
  classical
  calc
    _ ≤ Pr{let result ← globalRun primitives (count + 1) adversary}[
        ∃ target ∈ (Finset.univ : Finset (Fin (count + 1))), TargetEvent primitives target result] :=
      prEvent_mono _ _ _ (fun result accepted => ⟨result.2.1.identity, Finset.mem_univ _, accepted⟩)
    _ ≤ ∑ target : Fin (count + 1), Pr{let result ← globalRun primitives (count + 1) adversary}[
        TargetEvent primitives target result] :=
      prEvent_exists_finset_le Finset.univ _ _
    _ ≤ _ := Finset.sum_le_sum fun target _ => targetEvent_le_jointAdvantage primitives target fallback adversary

/-- A common bound on each constructed joint-use reduction gives exactly the generated-identity factor. -/
theorem global_advantage_le_count (primitives : Primitives) (count : ℕ) (fallback : Forgery)
    (adversary : (Fin (count + 1) → PublicIdentity) →
      OracleComp (GlobalSpec (count + 1)) (FamilyForgery (count + 1)))
    (epsilon : ℝ≥0∞)
    (bounded : ∀ target, advantage primitives (globalReduction primitives target fallback adversary) ≤ epsilon) :
    Pr{let result ← globalRun primitives (count + 1) adversary}[GlobalEvent primitives result] ≤
      (count + 1 : ℕ) * epsilon := by
  exact (global_advantage_le_sum primitives count fallback adversary).trans
    ((Finset.sum_le_sum fun target _ => bounded target).trans_eq (by simp))

/-- Pull a primitive query class through the global services; seed reveals are deterministic local work. -/
def globalClass {count : ℕ} (predicate : AdversarySpec.Domain → Prop) : (GlobalSpec count).Domain → Prop
  | .inl request => familyClass predicate request
  | .inr _ => False

instance {count : ℕ} (predicate : AdversarySpec.Domain → Prop) [DecidablePred predicate] :
    DecidablePred (globalClass (count := count) predicate) := fun query => by
  cases query with
  | inl request => exact inferInstanceAs (Decidable (familyClass predicate request))
  | inr _ => exact inferInstanceAs (Decidable False)

/-- Each locally answered reveal makes zero primitive-oracle calls; every service is forwarded exactly once. -/
theorem revealRouting_query_bound {count : ℕ} (target : Fin (count + 1))
    (others : Fin count → IdentitySeed) (predicate : AdversarySpec.Domain → Prop) [DecidablePred predicate]
    (query : (GlobalSpec (count + 1)).Domain) (reveals : List (Fin (count + 1))) :
    ((revealRouting target others query).run reveals).IsQueryBoundP (familyClass predicate)
      (if globalClass predicate query then 1 else 0) := by
  cases query with
  | inl request =>
    simp only [revealRouting, StateT.run, globalClass, bind_pure_comp, OracleComp.isQueryBoundP_map_iff]
    exact (OracleComp.isQueryBoundP_query_iff (spec := FamilyAdversarySpec (count + 1))
      (p := familyClass predicate) request _).mpr (fun selected => by simp [selected])
  | inr identity =>
    induction identity using Fin.succAboveCases target with
    | x => simp [revealRouting, StateT.run]
    | p other => simp [revealRouting, StateT.run]

/-- The complete stopped simulation retains each primitive class cap and all permitted local reveal work. -/
theorem reductionWork_query_bound (primitives : Primitives) {count : ℕ} (target : Fin (count + 1))
    (others : Fin count → IdentitySeed) {Result : Type} (client : OracleComp (GlobalSpec (count + 1)) Result)
    (predicate : AdversarySpec.Domain → Prop) [DecidablePred predicate] (bound : ℕ)
    (bounded : client.IsQueryBoundP (globalClass predicate) bound)
    (reveals : List (Fin (count + 1))) (history : FamilyHistory count) :
    (reductionWork primitives target others client reveals history).IsQueryBoundP predicate bound := by
  apply routed_query_bound primitives target others predicate
  exact (stopBeforeReveal_query_bound target client _ bound bounded).simulateQ_run_StateT_of_step
    (revealRouting_query_bound target others predicate) reveals

/-- Every reduction pays for the other seeds and every source uniform/sign/DH request class separately. -/
theorem globalReduction_query_bound (primitives : Primitives) {count : ℕ} (target : Fin (count + 1))
    (fallback : Forgery)
    (adversary : (Fin (count + 1) → PublicIdentity) →
      OracleComp (GlobalSpec (count + 1)) (FamilyForgery (count + 1)))
    (kind : Kind) (bound : ℕ)
    (bounded : ∀ publicKeys, (adversary publicKeys).IsQueryBoundP (globalClass (IsClass kind)) bound)
    (jointPublic : PublicIdentity) :
    (globalReduction primitives target fallback adversary jointPublic).IsQueryBoundP (IsClass kind)
      ((if kind = .uniform then 32 * count else 0) + bound) := by
  unfold globalReduction
  apply OracleComp.isQueryBoundP_bind (sampleFamily_lift_bound count kind)
  intro others _
  simpa only [bind_pure_comp, OracleComp.isQueryBoundP_map_iff] using
    reductionWork_query_bound primitives target others _ (IsClass kind) bound (bounded _) [] (emptyHistory count)

/-- The full interpreted challenger pays for all generated identities, including its own seed, plus the source uniform work. -/
theorem globalReductionGame_uniform_bound (primitives : Primitives) {count : ℕ}
    (target : Fin (count + 1)) (fallback : Forgery)
    (adversary : (Fin (count + 1) → PublicIdentity) →
      OracleComp (GlobalSpec (count + 1)) (FamilyForgery (count + 1)))
    (bound : ℕ)
    (bounded : ∀ publicKeys, (adversary publicKeys).IsQueryBoundP (globalClass (IsClass .uniform)) bound) :
    (game primitives (globalReduction primitives target fallback adversary)).IsTotalQueryBound
      (32 * (count + 1) + bound) := by
  have counted := jointGame_uniform_bound primitives (globalReduction primitives target fallback adversary)
    (32 * count + bound) (fun publicKeys => by
      simpa only [ite_true] using
        globalReduction_query_bound primitives target fallback adversary .uniform bound bounded publicKeys)
  convert counted using 1
  omega

/-- Reveal attempts have a separate source cap; repeated reveals still occupy that cap and append another log entry. -/
def IsReveal {count : ℕ} : (GlobalSpec count).Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance {count : ℕ} : DecidablePred (IsReveal (count := count)) := fun query => by
  cases query <;> simp only [IsReveal] <;> infer_instance

/-- Each actual reveal appends one identity, including repeated or target reveals. -/
theorem sourceImpl_reveal_count (primitives : Primitives) {count : ℕ} (seeds : Fin count → IdentitySeed)
    (query : (GlobalSpec count).Domain) (state : GlobalState count)
    (result : (GlobalSpec count).Range query × GlobalState count)
    (supported : result ∈ support ((sourceImpl primitives seeds query).run state)) :
    result.2.reveals.length = state.reveals.length + if IsReveal query then 1 else 0 := by
  cases query with
  | inl request =>
    simp only [sourceImpl, StateT.run, mem_support_bind_iff] at supported
    obtain ⟨⟨answer, histories⟩, _, supported⟩ := supported
    simp only [mem_support_pure_iff] at supported
    subst result
    simp [IsReveal]
  | inr identity =>
    simp only [sourceImpl, StateT.run, mem_support_pure_iff] at supported
    subst result
    simp [IsReveal]

/-- An arbitrary adaptive source continuation preserves the complete reveal log and obeys its explicit reveal cap. -/
theorem sourceRun_reveal_bound (primitives : Primitives) {count : ℕ} (seeds : Fin count → IdentitySeed)
    {Result : Type} (client : OracleComp (GlobalSpec count) Result) (bound : ℕ)
    (bounded : client.IsQueryBoundP IsReveal bound) (state : GlobalState count)
    (result : Result × GlobalState count)
    (supported : result ∈ support ((simulateQ (sourceImpl primitives seeds) client).run state)) :
    result.2.reveals.length ≤ state.reveals.length + bound := by
  induction client using OracleComp.inductionOn generalizing bound state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact Nat.le_add_right _ _
  | query_bind query rest ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
    rw [simulateQ_query_bind, StateT.run_bind] at supported
    simp only [mem_support_bind_iff] at supported
    obtain ⟨⟨answer, next⟩, step, restSupport⟩ := supported
    have stepCount := sourceImpl_reveal_count primitives seeds query state (answer, next) step
    have remaining := ih answer _ (bounded.2 answer) next result restSupport
    by_cases selected : IsReveal query
    · have positive : 0 < bound := bounded.1.resolve_left (not_not.mpr selected)
      simp only [selected, ite_eq_left] at stepCount remaining
      omega
    · simp only [selected, ite_false] at stepCount remaining
      omega

/-- Source interpretation forwards exactly one random request and uses no additional randomness for a deterministic service or reveal. -/
theorem sourceImpl_uniform_bound (primitives : Primitives) {count : ℕ} (seeds : Fin count → IdentitySeed)
    (query : (GlobalSpec count).Domain) (state : GlobalState count) :
    ((sourceImpl primitives seeds query).run state).IsQueryBoundP (fun _ => True)
      (if globalClass (IsClass .uniform) query then 1 else 0) := by
  cases query with
  | inl request =>
    cases request with
    | inl coin =>
      change OracleComp.IsQueryBoundP
        ((fun answer => (answer, state)) <$> (unifSpec.query coin : ProbComp _))
        (fun _ => True) 1
      simp only [OracleComp.isQueryBoundP_map_iff]
      exact (OracleComp.isQueryBoundP_query_iff (spec := unifSpec) (p := fun _ => True) coin 1).mpr (by simp)
    | inr request =>
      rcases request with ⟨identity, service⟩
      cases service <;> change (pure _ : ProbComp _).IsQueryBoundP (fun _ => True) 0 <;> trivial
  | inr identity =>
    change (pure _ : ProbComp _).IsQueryBoundP (fun _ => True) 0
    trivial

/-- The actual source execution accounts for every identity seed, arbitrary source uniform requests, and no hidden random reveal work. -/
theorem globalRun_uniform_bound (primitives : Primitives) (count : ℕ)
    (adversary : (Fin count → PublicIdentity) → OracleComp (GlobalSpec count) (FamilyForgery count))
    (bound : ℕ)
    (bounded : ∀ publicKeys, (adversary publicKeys).IsQueryBoundP (globalClass (IsClass .uniform)) bound) :
    (globalRun primitives count adversary).IsTotalQueryBound (32 * count + bound) := by
  unfold globalRun
  apply OracleComp.isTotalQueryBound_bind (sampleFamily_uniform_bound count)
  intro seeds
  simp only [bind_pure_comp, OracleComp.IsTotalQueryBound, OracleComp.isQueryBound_map_iff]
  exact (OracleComp.isQueryBoundP_true_iff _ _).mp
    ((bounded _).simulateQ_run_StateT_of_step (sourceImpl_uniform_bound primitives seeds) (initialState count))

/-- Actual sign/DH histories retain the same per-class accounting even when arbitrary seed reveals are interleaved. -/
theorem sourceImpl_history_count (primitives : Primitives) {count : ℕ} (seeds : Fin count → IdentitySeed)
    (kind : Kind) (target : Fin count) (query : (GlobalSpec count).Domain) (state : GlobalState count)
    (result : (GlobalSpec count).Range query × GlobalState count)
    (supported : result ∈ support ((sourceImpl primitives seeds query).run state)) :
    historyCount kind (result.2.histories target) ≤ historyCount kind (state.histories target) +
      if globalClass (IsClass kind) query then 1 else 0 := by
  cases query with
  | inl request =>
    simp only [sourceImpl, StateT.run, mem_support_bind_iff] at supported
    obtain ⟨⟨answer, histories⟩, historySupport, supported⟩ := supported
    simp only [mem_support_pure_iff] at supported
    subst result
    exact familyImpl_count primitives seeds kind target request state.histories (answer, histories) historySupport
  | inr identity =>
    simp only [sourceImpl, StateT.run, mem_support_pure_iff] at supported
    subst result
    simp [globalClass]

/-- The complete source service history counts all raw DH replies, including rejection, under the supplied source service caps. -/
theorem sourceRun_history_bound (primitives : Primitives) {count : ℕ} (seeds : Fin count → IdentitySeed)
    (kind : Kind) (target : Fin count) {Result : Type} (client : OracleComp (GlobalSpec count) Result)
    (bound : ℕ) (bounded : client.IsQueryBoundP (globalClass (IsClass kind)) bound) (state : GlobalState count)
    (result : Result × GlobalState count)
    (supported : result ∈ support ((simulateQ (sourceImpl primitives seeds) client).run state)) :
    historyCount kind (result.2.histories target) ≤ historyCount kind (state.histories target) + bound := by
  induction client using OracleComp.inductionOn generalizing bound state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact Nat.le_add_right _ _
  | query_bind query rest ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
    rw [simulateQ_query_bind, StateT.run_bind] at supported
    simp only [mem_support_bind_iff] at supported
    obtain ⟨⟨answer, next⟩, step, restSupport⟩ := supported
    have stepCount := sourceImpl_history_count primitives seeds kind target query state (answer, next) step
    have remaining := ih answer _ (bounded.2 answer) next result restSupport
    by_cases selected : globalClass (IsClass kind) query
    · have positive : 0 < bound := bounded.1.resolve_left (not_not.mpr selected)
      simp only [selected, ite_eq_left] at stepCount remaining
      omega
    · simp only [selected, ite_false] at stepCount remaining
      omega

/-- Rejected DH requests remain bounded by all actual DH attempts, including around identity reveals. -/
theorem sourceRun_rejectedDh_bound (primitives : Primitives) {count : ℕ} (seeds : Fin count → IdentitySeed)
    (target : Fin count) {Result : Type} (client : OracleComp (GlobalSpec count) Result)
    (bound : ℕ) (bounded : client.IsQueryBoundP (globalClass (IsClass .staticDh)) bound)
    (result : Result × GlobalState count)
    (supported : result ∈ support ((simulateQ (sourceImpl primitives seeds) client).run (initialState count))) :
    rejectedDhCount (result.2.histories target) ≤ bound := by
  exact (rejectedDhCount_le _).trans (by
    simpa [initialState, emptyHistory, historyCount] using
      sourceRun_history_bound primitives seeds .staticDh target client bound bounded (initialState count) result supported)

end BeaconcryptCore.Computational.PqxdhJointIdentityFreshness

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentityFreshness.fresh_probability_eq_stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentityFreshness.fresh_probability_eq_stopped

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentityFreshness.stopBeforeReveal_no_target' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentityFreshness.stopBeforeReveal_no_target

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentityFreshness.reductionWork_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentityFreshness.reductionWork_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentityFreshness.global_advantage_le_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentityFreshness.global_advantage_le_sum

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentityFreshness.globalReduction_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentityFreshness.globalReduction_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentityFreshness.globalReductionGame_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentityFreshness.globalReductionGame_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentityFreshness.sourceRun_reveal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentityFreshness.sourceRun_reveal_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentityFreshness.globalRun_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentityFreshness.globalRun_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentityFreshness.sourceRun_rejectedDh_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentityFreshness.sourceRun_rejectedDh_bound
