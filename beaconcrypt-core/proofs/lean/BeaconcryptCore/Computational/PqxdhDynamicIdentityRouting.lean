import BeaconcryptCore.Computational.PqxdhDynamicIdentityPool

/-!
# Routing dynamically created identities into the joint-use family

The public router stores only a created-index count and the actual public query/reply trace. Reserved private seeds remain exclusively in the existing family interpreter. Source signing and reveal histories are updated from actual replies, including optional DH rejection, and uncreated indices reject before a family query. Native byte-based identity lookup and caller-owned identities remain separate interfaces.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting

open PqxdhJointIdentity PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
  PqxdhJointIdentityEvents
open PqxdhDynamicIdentityPool (PoolQuery DynamicSpec Observation)


/-- The router knows only how many public identities have been created and the complete actual public trace. It never stores a reserved private seed. -/
structure PublicState where
  created : ℕ
  transcript : List Observation

def initialPublicState : PublicState := ⟨0, []⟩

def appendObservation (query : DynamicSpec.Domain) (answer : DynamicSpec.Range query)
    (state : PublicState) : PublicState :=
  { state with transcript := state.transcript ++ [⟨query, answer⟩] }

/-- Joint family calls are issued only for already-created indices; creation publishes only the next known public key. Exhaustion and uncreated indices return the source optional rejection. -/
def routeImpl {count : ℕ} (publicKeys : Fin count → PublicIdentity) :
    QueryImpl DynamicSpec (StateT PublicState (OracleComp (GlobalSpec count))) := fun query state =>
  match query with
  | .inl coin => do
    let answer ← (GlobalSpec count).query (.inl (.inl coin))
    pure (answer, appendObservation (.inl coin) answer state)
  | .inr .create =>
    if available : state.created < count then
      let answer := some (state.created, publicKeys ⟨state.created, available⟩)
      pure (answer, appendObservation (.inr .create) answer { state with created := state.created + 1 })
    else pure (none, appendObservation (.inr .create) none state)
  | .inr (.service identity request) =>
    if available : identity < state.created ∧ identity < count then do
      let answer ← (GlobalSpec count).query (.inl (.inr (⟨identity, available.2⟩, request)))
      pure (some answer, appendObservation (.inr (.service identity request)) (some answer) state)
    else pure (none, appendObservation (.inr (.service identity request)) none state)
  | .inr (.reveal identity) =>
    if available : identity < state.created ∧ identity < count then do
      let answer ← (GlobalSpec count).query (.inr ⟨identity, available.2⟩)
      pure (some answer, appendObservation (.inr (.reveal identity)) (some answer) state)
    else pure (none, appendObservation (.inr (.reveal identity)) none state)

/-- Exact global sign/DH/reveal history instrumentation is computable from source replies alone. Rejected uncreated-index calls add no nonexistent primitive action. -/
def historyUpdate (count : ℕ) (query : DynamicSpec.Domain) (answer : DynamicSpec.Range query)
    (history : GlobalState count) : GlobalState count :=
  match query with
  | .inl _ => history
  | .inr .create => history
  | .inr (.service identity request) =>
    if valid : identity < count then
      match answer with
      | none => history
      | some reply => publicUpdate (.inl (.inr (⟨identity, valid⟩, request))) reply history
    else history
  | .inr (.reveal identity) =>
    if valid : identity < count then
      match answer with
      | none => history
      | some reply => publicUpdate (.inr ⟨identity, valid⟩) reply history
    else history

/-- Instrumentation forwards the original request and keeps its exact reply before updating the public family history. -/
def historyImpl (count : ℕ) : QueryImpl DynamicSpec
    (StateT (GlobalState count) (OracleComp DynamicSpec)) := fun query history => do
  let answer ← DynamicSpec.query query
  pure (answer, historyUpdate count query answer history)

/-- The complete source interpreter retains both the private created prefix and all earlier family service/reveal histories. -/
def sourceWithHistory (count : ℕ)
    (source : QueryImpl DynamicSpec (StateT PqxdhDynamicIdentityPool.SourceState ProbComp)) :
    QueryImpl DynamicSpec (StateT (GlobalState count × PqxdhDynamicIdentityPool.SourceState) ProbComp) :=
  QueryImpl.Stateful.link (historyImpl count) source

/-- Source private state is reconstructed only by the family interpreter from the created prefix. Future reserved seeds remain absent. -/
def sourceState {count : ℕ} (seeds : Fin count → IdentitySeed) (state : PublicState) :
    PqxdhDynamicIdentityPool.SourceState :=
  ⟨(List.ofFn seeds).take state.created, state.transcript⟩

/-- All global histories are retained exactly alongside the complete reconstructed source state. -/
def projection {count : ℕ} (seeds : Fin count → IdentitySeed)
    (state : PublicState × GlobalState count) : GlobalState count × PqxdhDynamicIdentityPool.SourceState :=
  (state.2, sourceState seeds state.1)

/-- The source monitor neither adds an oracle request nor replaces a reply; it records the exact same per-family history update after that reply. -/
theorem sourceWithHistory_run (count : ℕ)
    (source : QueryImpl DynamicSpec (StateT PqxdhDynamicIdentityPool.SourceState ProbComp))
    (query : DynamicSpec.Domain) (history : GlobalState count) (state : PqxdhDynamicIdentityPool.SourceState) :
    (sourceWithHistory count source query).run (history, state) =
      (source query).run state >>= fun reply =>
        pure (reply.1, (historyUpdate count query reply.1 history, reply.2)) := by
  rw [sourceWithHistory, QueryImpl.Stateful.link_impl_apply_run]
  simp only [historyImpl, StateT.run, simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
  change (fun result : (DynamicSpec.Range query × GlobalState count) × PqxdhDynamicIdentityPool.SourceState =>
      (result.1.1, (result.1.2, result.2))) <$>
    ((source query).run state >>= fun reply =>
      pure ((reply.1, historyUpdate count query reply.1 history), reply.2)) = _
  simp only [map_bind, map_pure]
  rfl

/-- Created-count validity makes the reconstructed source prefix length exact. -/
theorem sourceState_length {count : ℕ} (seeds : Fin count → IdentitySeed) (state : PublicState)
    (valid : state.created ≤ count) : (sourceState seeds state).seeds.length = state.created := by
  simp [sourceState, Nat.min_eq_left valid]

/-- Every index visible to the router has exactly the same seed in the source prefix and full family. -/
theorem sourceState_lookup {count : ℕ} (seeds : Fin count → IdentitySeed) (state : PublicState)
    (identity : ℕ) (created : identity < state.created) (valid : identity < count) :
    (sourceState seeds state).seeds[identity]? = some (seeds ⟨identity, valid⟩) := by
  simp [sourceState, created, valid]

/-- An index at or beyond the created prefix is rejected before any reserved seed can be observed. -/
theorem sourceState_uncreated {count : ℕ} (seeds : Fin count → IdentitySeed) (state : PublicState)
    (identity : ℕ) (uncreated : state.created ≤ identity) :
    (sourceState seeds state).seeds[identity]? = none := by
  simp [sourceState, Nat.not_lt.mpr uncreated]

/-- The next created private prefix appends exactly the next indexed family seed. -/
theorem sourceState_next_seed {count : ℕ} (seeds : Fin count → IdentitySeed) (state : PublicState)
    (available : state.created < count) :
    (List.ofFn seeds).take (state.created + 1) =
      (sourceState seeds state).seeds ++ [seeds ⟨state.created, available⟩] := by
  simp [sourceState, List.take_add_one, available]

/-- Typed creation replies keep the dependent source range intact through the routing equality. -/
def createdPublicReply (state : PublicState) (publicKey : PublicIdentity) :
    DynamicSpec.Range (.inr .create) × PublicState :=
  let answer : DynamicSpec.Range (.inr .create) := some (state.created, publicKey)
  (answer, appendObservation (.inr .create) answer { state with created := state.created + 1 })

def rejectedCreateReply (state : PublicState) : DynamicSpec.Range (.inr .create) × PublicState :=
  (none, appendObservation (.inr .create) none state)

theorem eagerSource_create_available (primitives : Primitives) {count : ℕ}
    (seeds : Fin count → IdentitySeed) (state : PublicState) (available : state.created < count) :
    (PqxdhDynamicIdentityPool.eagerImpl primitives (List.ofFn seeds) (.inr .create)).run
      (sourceState seeds state) = pure (PqxdhDynamicIdentityPool.createdReply primitives
        (sourceState seeds state) (seeds ⟨state.created, available⟩)) := by
  have prefixLength := sourceState_length seeds state (Nat.le_of_lt available)
  simp only [PqxdhDynamicIdentityPool.eagerImpl, PqxdhDynamicIdentityPool.poolImpl, StateT.run,
    prefixLength, List.getElem?_ofFn, available, dite_true, pure_bind,
    PqxdhDynamicIdentityPool.createdReply]

/-- Dynamically publishing the next family public key preserves both full retained histories and the actual newly created private prefix. -/
theorem create_projection (primitives : Primitives) {count : ℕ} (seeds : Fin count → IdentitySeed)
    (state : PublicState) (history : GlobalState count) (valid : state.created ≤ count) :
    Prod.map id (projection seeds) <$>
      (QueryImpl.Stateful.link (routeImpl (familyPublic primitives seeds))
        (sourceImpl primitives seeds) (.inr .create)).run (state, history) =
      (sourceWithHistory count (PqxdhDynamicIdentityPool.eagerImpl primitives (List.ofFn seeds))
        (.inr .create)).run (projection seeds (state, history)) := by
  rw [QueryImpl.Stateful.link_impl_apply_run, Functor.map_map]
  change (fun result : ((DynamicSpec.Range (.inr .create) × PublicState) × GlobalState count) =>
    (result.1.1, (result.2, sourceState seeds result.1.2))) <$>
      (simulateQ (sourceImpl primitives seeds)
        ((routeImpl (familyPublic primitives seeds) (.inr .create)).run state)).run history = _
  rw [show projection seeds (state, history) = (history, sourceState seeds state) from rfl,
    sourceWithHistory_run]
  have prefixLength := sourceState_length seeds state valid
  by_cases available : state.created < count
  · have routeReply : (routeImpl (familyPublic primitives seeds) (.inr .create)).run state =
        pure (createdPublicReply state (primitives.publicKeys (seeds ⟨state.created, available⟩))) := by
      simp only [routeImpl, StateT.run, available, dite_true, familyPublic, createdPublicReply]
    rw [routeReply, simulateQ_pure, StateT.run_pure, map_pure,
      eagerSource_create_available primitives seeds state available, pure_bind]
    simp only [createdPublicReply, PqxdhDynamicIdentityPool.createdReply, historyUpdate,
      sourceState, appendObservation, PqxdhDynamicIdentityPool.record]
    simp only [List.take_add_one, List.getElem?_ofFn, available, dite_true,
      List.length_take, List.length_ofFn, Nat.min_eq_left valid]
    rfl
  · have full : state.created = count := by omega
    have routeReply : (routeImpl (familyPublic primitives seeds) (.inr .create)).run state =
        pure (rejectedCreateReply state) := by
      simp only [routeImpl, StateT.run, available, dite_false, rejectedCreateReply]
    rw [routeReply, simulateQ_pure, StateT.run_pure, map_pure]
    simp [PqxdhDynamicIdentityPool.eagerImpl, PqxdhDynamicIdentityPool.poolImpl, StateT.run,
      full, historyUpdate, sourceState, appendObservation, PqxdhDynamicIdentityPool.record,
      rejectedCreateReply]

/-- Source and router uniformly forward the same explicit coin, preserving every prior family history and the complete created private prefix. -/
theorem uniform_projection (primitives : Primitives) {count : ℕ} (seeds : Fin count → IdentitySeed)
    (coin : ℕ) (state : PublicState) (history : GlobalState count) :
    Prod.map id (projection seeds) <$>
      (QueryImpl.Stateful.link (routeImpl (familyPublic primitives seeds))
        (sourceImpl primitives seeds) (.inl coin)).run (state, history) =
      (sourceWithHistory count (PqxdhDynamicIdentityPool.eagerImpl primitives (List.ofFn seeds))
        (.inl coin)).run (projection seeds (state, history)) := by
  rw [QueryImpl.Stateful.link_impl_apply_run, Functor.map_map]
  change (fun result : ((DynamicSpec.Range (.inl coin) × PublicState) × GlobalState count) =>
    (result.1.1, (result.2, sourceState seeds result.1.2))) <$>
      (simulateQ (sourceImpl primitives seeds)
        ((routeImpl (familyPublic primitives seeds) (.inl coin)).run state)).run history = _
  rw [show projection seeds (state, history) = (history, sourceState seeds state) from rfl,
    sourceWithHistory_run]
  simp only [routeImpl, StateT.run, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    PqxdhDynamicIdentityPool.eagerImpl, PqxdhDynamicIdentityPool.poolImpl]
  change (fun result : ((unifSpec.Range coin × PublicState) × GlobalState count) =>
    (result.1.1, (result.2, sourceState seeds result.1.2))) <$>
      ((unifSpec.query coin : ProbComp _) >>= fun answer =>
        pure ((answer, appendObservation (.inl coin) answer state), history)) =
    ((unifSpec.query coin : ProbComp _) >>= fun answer =>
      pure (answer, (history, PqxdhDynamicIdentityPool.record (.inl coin) answer (sourceState seeds state))))
  simp only [map_bind, map_pure]
  rfl

/-- Every chosen signing/DH service uses the same already-created seed, preserves the actual optional reply and retains all prior histories; an uncreated index makes no family query. -/
theorem service_projection (primitives : Primitives) {count : ℕ} (seeds : Fin count → IdentitySeed)
    (identity : ℕ) (request : JointSpec.Domain) (state : PublicState) (history : GlobalState count)
    (valid : state.created ≤ count) :
    Prod.map id (projection seeds) <$>
      (QueryImpl.Stateful.link (routeImpl (familyPublic primitives seeds))
        (sourceImpl primitives seeds) (.inr (.service identity request))).run (state, history) =
      (sourceWithHistory count (PqxdhDynamicIdentityPool.eagerImpl primitives (List.ofFn seeds))
        (.inr (.service identity request))).run (projection seeds (state, history)) := by
  rw [QueryImpl.Stateful.link_impl_apply_run, Functor.map_map]
  change (fun result : ((DynamicSpec.Range (.inr (.service identity request)) × PublicState) × GlobalState count) =>
    (result.1.1, (result.2, sourceState seeds result.1.2))) <$>
      (simulateQ (sourceImpl primitives seeds)
        ((routeImpl (familyPublic primitives seeds) (.inr (.service identity request))).run state)).run history = _
  rw [show projection seeds (state, history) = (history, sourceState seeds state) from rfl,
    sourceWithHistory_run]
  by_cases available : identity < state.created ∧ identity < count
  · have lookup := sourceState_lookup seeds state identity available.1 available.2
    simp only [routeImpl, StateT.run, available, PqxdhDynamicIdentityPool.eagerImpl,
      PqxdhDynamicIdentityPool.poolImpl, lookup, Option.map_some]
    change (fun result : ((DynamicSpec.Range (.inr (.service identity request)) × PublicState) × GlobalState count) =>
      (result.1.1, (result.2, sourceState seeds result.1.2))) <$>
      pure ((some (primitiveReply primitives (seeds ⟨identity, available.2⟩) request),
        appendObservation (.inr (.service identity request))
          (some (primitiveReply primitives (seeds ⟨identity, available.2⟩) request)) state),
        publicUpdate (.inl (.inr (⟨identity, available.2⟩, request)))
          (primitiveReply primitives (seeds ⟨identity, available.2⟩) request) history) =
      pure (some (primitiveReply primitives (seeds ⟨identity, available.2⟩) request),
        (historyUpdate count (.inr (.service identity request))
          (some (primitiveReply primitives (seeds ⟨identity, available.2⟩) request)) history,
          PqxdhDynamicIdentityPool.record (.inr (.service identity request))
            (some (primitiveReply primitives (seeds ⟨identity, available.2⟩) request)) (sourceState seeds state)))
    simp only [map_pure, historyUpdate, available.2, dite_true]
    rfl
  · have uncreated : state.created ≤ identity := by omega
    have lookup := sourceState_uncreated seeds state identity uncreated
    simp only [routeImpl, StateT.run, available, dite_false, simulateQ_pure,
      PqxdhDynamicIdentityPool.eagerImpl, PqxdhDynamicIdentityPool.poolImpl, lookup, Option.map_none]
    change (fun result : ((DynamicSpec.Range (.inr (.service identity request)) × PublicState) × GlobalState count) =>
      (result.1.1, (result.2, sourceState seeds result.1.2))) <$>
      pure ((none, appendObservation (.inr (.service identity request)) none state), history) =
      pure (none, (historyUpdate count (.inr (.service identity request)) none history,
        PqxdhDynamicIdentityPool.record (.inr (.service identity request)) none (sourceState seeds state)))
    simp only [map_pure, historyUpdate, dite_eq_ite, ite_self]
    rfl

/-- Every created-identity reveal returns its actual retained seed and appends the same family reveal history. Requests before creation reveal nothing and leave freshness unchanged. -/
theorem reveal_projection (primitives : Primitives) {count : ℕ} (seeds : Fin count → IdentitySeed)
    (identity : ℕ) (state : PublicState) (history : GlobalState count)
    (valid : state.created ≤ count) :
    Prod.map id (projection seeds) <$>
      (QueryImpl.Stateful.link (routeImpl (familyPublic primitives seeds))
        (sourceImpl primitives seeds) (.inr (.reveal identity))).run (state, history) =
      (sourceWithHistory count (PqxdhDynamicIdentityPool.eagerImpl primitives (List.ofFn seeds))
        (.inr (.reveal identity))).run (projection seeds (state, history)) := by
  rw [QueryImpl.Stateful.link_impl_apply_run, Functor.map_map]
  change (fun result : ((DynamicSpec.Range (.inr (.reveal identity)) × PublicState) × GlobalState count) =>
    (result.1.1, (result.2, sourceState seeds result.1.2))) <$>
      (simulateQ (sourceImpl primitives seeds)
        ((routeImpl (familyPublic primitives seeds) (.inr (.reveal identity))).run state)).run history = _
  rw [show projection seeds (state, history) = (history, sourceState seeds state) from rfl,
    sourceWithHistory_run]
  by_cases available : identity < state.created ∧ identity < count
  · have lookup := sourceState_lookup seeds state identity available.1 available.2
    simp only [routeImpl, StateT.run, available, PqxdhDynamicIdentityPool.eagerImpl,
      PqxdhDynamicIdentityPool.poolImpl, lookup]
    change (fun result : ((DynamicSpec.Range (.inr (.reveal identity)) × PublicState) × GlobalState count) =>
      (result.1.1, (result.2, sourceState seeds result.1.2))) <$>
      pure ((some (seeds ⟨identity, available.2⟩),
        appendObservation (.inr (.reveal identity))
          (some (seeds ⟨identity, available.2⟩)) state),
        publicUpdate (.inr ⟨identity, available.2⟩)
          (seeds ⟨identity, available.2⟩) history) =
      pure (some (seeds ⟨identity, available.2⟩),
        (historyUpdate count (.inr (.reveal identity))
          (some (seeds ⟨identity, available.2⟩)) history,
          PqxdhDynamicIdentityPool.record (.inr (.reveal identity))
            (some (seeds ⟨identity, available.2⟩)) (sourceState seeds state)))
    simp only [map_pure, historyUpdate, available.2, dite_true]
    rfl
  · have uncreated : state.created ≤ identity := by omega
    have lookup := sourceState_uncreated seeds state identity uncreated
    simp only [routeImpl, StateT.run, available, dite_false, simulateQ_pure,
      PqxdhDynamicIdentityPool.eagerImpl, PqxdhDynamicIdentityPool.poolImpl, lookup]
    change (fun result : ((DynamicSpec.Range (.inr (.reveal identity)) × PublicState) × GlobalState count) =>
      (result.1.1, (result.2, sourceState seeds result.1.2))) <$>
      pure ((none, appendObservation (.inr (.reveal identity)) none state), history) =
      pure (none, (historyUpdate count (.inr (.reveal identity)) none history,
        PqxdhDynamicIdentityPool.record (.inr (.reveal identity)) none (sourceState seeds state)))
    simp only [map_pure, historyUpdate, dite_eq_ite, ite_self]
    rfl

/-- Every dynamic query preserves its exact source reply, created private prefix and complete prior family history under the public router. -/
theorem projection_step (primitives : Primitives) {count : ℕ} (seeds : Fin count → IdentitySeed)
    (query : DynamicSpec.Domain) (state : PublicState × GlobalState count)
    (valid : state.1.created ≤ count) :
    Prod.map id (projection seeds) <$>
      (QueryImpl.Stateful.link (routeImpl (familyPublic primitives seeds))
        (sourceImpl primitives seeds) query).run state =
      (sourceWithHistory count (PqxdhDynamicIdentityPool.eagerImpl primitives (List.ofFn seeds))
        query).run (projection seeds state) := by
  rcases state with ⟨publicState, history⟩
  cases query with
  | inl coin => exact uniform_projection primitives seeds coin publicState history
  | inr request =>
    cases request with
    | create => exact create_projection primitives seeds publicState history valid
    | service identity request => exact service_projection primitives seeds identity request publicState history valid
    | reveal identity => exact reveal_projection primitives seeds identity publicState history valid

/-- The public router never exposes a created index beyond the reserved family's size, even under arbitrary possible oracle replies. -/
theorem routeImpl_preserves_count {count : ℕ} (publicKeys : Fin count → PublicIdentity)
    (query : DynamicSpec.Domain) (state : PublicState) (valid : state.created ≤ count)
    (result : DynamicSpec.Range query × PublicState)
    (supported : result ∈ support ((routeImpl publicKeys query).run state)) :
    result.2.created ≤ count := by
  cases query with
  | inl coin =>
    simp only [routeImpl, StateT.run, mem_support_bind_iff] at supported
    obtain ⟨answer, _, supported⟩ := supported
    obtain rfl := eq_of_mem_support_pure supported
    exact valid
  | inr request =>
    cases request with
    | create =>
      by_cases available : state.created < count
      · simp only [routeImpl, StateT.run, available, dite_true] at supported
        obtain rfl := eq_of_mem_support_pure supported
        change state.created + 1 ≤ count
        omega
      · simp only [routeImpl, StateT.run, available, dite_false] at supported
        obtain rfl := eq_of_mem_support_pure supported
        exact valid
    | service identity request =>
      change Option (JointSpec.Range request) × PublicState at result
      by_cases available : identity < state.created ∧ identity < count
      · change result ∈ support (if h : identity < state.created ∧ identity < count then
          ((GlobalSpec count).query (.inl (.inr (⟨identity, h.2⟩, request))) : OracleComp (GlobalSpec count) _) >>= fun answer =>
            pure (some answer, appendObservation (.inr (.service identity request)) (some answer) state)
          else pure (none, appendObservation (.inr (.service identity request)) none state)) at supported
        rw [dif_pos available, mem_support_bind_iff] at supported
        obtain ⟨answer, _, supported⟩ := supported
        obtain rfl := OracleComp.eq_of_mem_support_pure _ supported
        exact valid
      · simp only [routeImpl, StateT.run, available, dite_false] at supported
        obtain rfl := eq_of_mem_support_pure supported
        exact valid
    | reveal identity =>
      change Option { l : List UInt8 // l.length = 32 } × PublicState at result
      by_cases available : identity < state.created ∧ identity < count
      · change result ∈ support (if h : identity < state.created ∧ identity < count then
          ((GlobalSpec count).query (.inr ⟨identity, h.2⟩) : OracleComp (GlobalSpec count) _) >>= fun answer =>
            pure (some answer, appendObservation (.inr (.reveal identity)) (some answer) state)
          else pure (none, appendObservation (.inr (.reveal identity)) none state)) at supported
        rw [dif_pos available, mem_support_bind_iff] at supported
        obtain ⟨answer, _, supported⟩ := supported
        obtain rfl := OracleComp.eq_of_mem_support_pure _ supported
        exact valid
      · simp only [routeImpl, StateT.run, available, dite_false] at supported
        obtain rfl := eq_of_mem_support_pure supported
        exact valid

/-- Interpreting real joint services and reveals preserves the same public created-count invariant. -/
theorem linked_preserves_count (primitives : Primitives) {count : ℕ} (seeds : Fin count → IdentitySeed) :
    QueryImpl.PreservesInv
      (QueryImpl.Stateful.link (routeImpl (familyPublic primitives seeds)) (sourceImpl primitives seeds))
      (fun state => state.1.created ≤ count) := by
  rintro query ⟨state, history⟩ valid result supported
  rw [QueryImpl.Stateful.link_impl_apply_run] at supported
  obtain ⟨value, valueSupported, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
  have publicSupported : value.1 ∈ support
      ((simulateQ (sourceImpl primitives seeds) ((routeImpl (familyPublic primitives seeds) query).run state)).run' history) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨value, valueSupported, rfl⟩
  have routed := OracleComp.support_simulateQ_run'_subset (sourceImpl primitives seeds)
    ((routeImpl (familyPublic primitives seeds) query).run state) history publicSupported
  exact routeImpl_preserves_count (familyPublic primitives seeds) query state valid value.1 routed

/-- Complete adaptive routing retains the entire source private prefix, public transcript, returned client result and every prior family history. No target secret is supplied to the router. -/
theorem route_complete (primitives : Primitives) {count : ℕ} (seeds : Fin count → IdentitySeed)
    {Result : Type} (client : OracleComp DynamicSpec Result) (state : PublicState × GlobalState count)
    (valid : state.1.created ≤ count) :
    Prod.map id (projection seeds) <$>
      (simulateQ (QueryImpl.Stateful.link (routeImpl (familyPublic primitives seeds))
        (sourceImpl primitives seeds)) client).run state =
      (simulateQ (sourceWithHistory count (PqxdhDynamicIdentityPool.eagerImpl primitives (List.ofFn seeds)))
        client).run (projection seeds state) := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (QueryImpl.Stateful.link (routeImpl (familyPublic primitives seeds)) (sourceImpl primitives seeds))
    (sourceWithHistory count (PqxdhDynamicIdentityPool.eagerImpl primitives (List.ofFn seeds)))
    (fun state => state.1.created ≤ count) (projection seeds)
    (linked_preserves_count primitives seeds) (projection_step primitives seeds) client state valid

/-- Public history instrumentation preserves every declared source query class, including attempted invalid-index requests. -/
theorem historyRun_query_bound {Result : Type} (count : ℕ)
    (client : OracleComp DynamicSpec Result) (predicate : DynamicSpec.Domain → Prop)
    [DecidablePred predicate] (bound : ℕ) (bounded : client.IsQueryBoundP predicate bound)
    (history : GlobalState count) :
    ((simulateQ (historyImpl count) client).run history).IsQueryBoundP predicate bound := by
  apply OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step bounded _ history
  intro query state
  change OracleComp.IsQueryBoundP
    ((fun answer : DynamicSpec.Range query => (answer, historyUpdate count query answer state)) <$>
      (DynamicSpec.query query : OracleComp DynamicSpec _)) predicate _
  rw [OracleComp.isQueryBoundP_map_iff, OracleComp.isQueryBoundP_query_iff]
  split_ifs <;> simp_all

/-- Reserving the full future seed family preserves the complete dynamically sampled source and all actual service/reveal histories jointly. -/
theorem lazy_eager_history_complete (primitives : Primitives) {Result : Type}
    (count : ℕ) (client : OracleComp DynamicSpec Result)
    (bounded : client.IsQueryBoundP PqxdhDynamicIdentityPool.IsCreate count)
    (history : GlobalState count) (state : PqxdhDynamicIdentityPool.SourceState) :
    𝒮[(simulateQ (sourceWithHistory count (PqxdhDynamicIdentityPool.lazyImpl primitives)) client).run
      (history, state)] =
      𝒮[PqxdhDynamicIdentityPool.sampleSeeds count >>= fun future =>
        (simulateQ (sourceWithHistory count
          (PqxdhDynamicIdentityPool.eagerImpl primitives (state.seeds ++ future))) client).run (history, state)] := by
  have law := PqxdhDynamicIdentityPool.lazy_eager_complete primitives
    ((simulateQ (historyImpl count) client).run history) count
    (historyRun_query_bound count client PqxdhDynamicIdentityPool.IsCreate count bounded history) state
  have mapped := congrArg (fun distribution =>
    (fun value : (Result × GlobalState count) × PqxdhDynamicIdentityPool.SourceState =>
      (value.1.1, (value.1.2, value.2))) <$> distribution) law
  simp_rw [sourceWithHistory, QueryImpl.Stateful.simulateQ_link_run]
  change 𝒮[(fun value : (Result × GlobalState count) × PqxdhDynamicIdentityPool.SourceState =>
      (value.1.1, (value.1.2, value.2))) <$>
    (simulateQ (PqxdhDynamicIdentityPool.lazyImpl primitives)
      ((simulateQ (historyImpl count) client).run history)).run state] =
    𝒮[PqxdhDynamicIdentityPool.sampleSeeds count >>= fun future =>
      (fun value : (Result × GlobalState count) × PqxdhDynamicIdentityPool.SourceState =>
        (value.1.1, (value.1.2, value.2))) <$>
      (simulateQ (PqxdhDynamicIdentityPool.eagerImpl primitives (state.seeds ++ future))
        ((simulateQ (historyImpl count) client).run history)).run state]
  simpa only [evalSPMF_map, evalSPMF_bind, map_bind] using mapped

/-- The real source starts with no created identity; only actual creation requests draw fresh seeds. -/
def dynamicRun (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp DynamicSpec Result) :
    ProbComp (Result × (GlobalState count × PqxdhDynamicIdentityPool.SourceState)) :=
  (simulateQ (sourceWithHistory count (PqxdhDynamicIdentityPool.lazyImpl primitives)) client).run
    (PqxdhJointIdentityFreshness.initialState count, PqxdhDynamicIdentityPool.initialState)

/-- The bounded family interpreter reserves seeds privately; the continued router receives only its public family. Full terminal private state is retained solely in this analysis projection. -/
def reservedRun (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp DynamicSpec Result) :
    ProbComp (Result × (GlobalState count × PqxdhDynamicIdentityPool.SourceState)) := do
  let seeds ← sampleFamily count
  let result ← (simulateQ (QueryImpl.Stateful.link (routeImpl (familyPublic primitives seeds))
    (sourceImpl primitives seeds)) client).run
    (initialPublicState, PqxdhJointIdentityFreshness.initialState count)
  pure (result.1, projection seeds result.2)

/-- Actual on-demand generation and public family routing have exactly the same complete evaluated source execution, under a source creation cap and without an honest-selected-target premise. -/
theorem dynamic_reserved_complete (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp DynamicSpec Result)
    (bounded : client.IsQueryBoundP PqxdhDynamicIdentityPool.IsCreate count) :
    𝒮[dynamicRun primitives count client] = 𝒮[reservedRun primitives count client] := by
  rw [dynamicRun, lazy_eager_history_complete primitives count client bounded]
  simp only [PqxdhDynamicIdentityPool.initialState, List.nil_append,
    PqxdhDynamicIdentityPool.sampleSeeds, bind_map_left, reservedRun, bind_pure_comp]
  apply evalSPMF_bind_congr'
  intro seeds
  have exactRun := route_complete primitives seeds client
    (initialPublicState, PqxdhJointIdentityFreshness.initialState count) (Nat.zero_le count)
  change 𝒮[(simulateQ (sourceWithHistory count (PqxdhDynamicIdentityPool.eagerImpl primitives (List.ofFn seeds)))
      client).run (projection seeds (initialPublicState, PqxdhJointIdentityFreshness.initialState count))] = _
  rw [← exactRun]
  rfl

/-- Source class counts include attempted service requests even when their generated index does not yet exist. -/
def dynamicClass (predicate : AdversarySpec.Domain → Prop) : DynamicSpec.Domain → Prop
  | .inl coin => predicate (.inl coin)
  | .inr (.service _ request) => predicate (.inr request)
  | .inr .create => False
  | .inr (.reveal _) => False

instance (predicate : AdversarySpec.Domain → Prop) [DecidablePred predicate] :
    DecidablePred (dynamicClass predicate) := fun query => by
  cases query with
  | inl coin => exact inferInstanceAs (Decidable (predicate (.inl coin)))
  | inr request => cases request <;> dsimp [dynamicClass] <;> infer_instance

/-- The public router makes at most the one corresponding primitive-class request. Uncreated-index rejection still consumes the source class allowance. -/
theorem routeImpl_query_bound {count : ℕ} (publicKeys : Fin count → PublicIdentity)
    (predicate : AdversarySpec.Domain → Prop) [DecidablePred predicate]
    (query : DynamicSpec.Domain) (state : PublicState) :
    ((routeImpl publicKeys query).run state).IsQueryBoundP (globalClass predicate)
      (if dynamicClass predicate query then 1 else 0) := by
  cases query with
  | inl coin =>
    change OracleComp.IsQueryBoundP
      ((fun answer => (answer, appendObservation (.inl coin) answer state)) <$>
        ((GlobalSpec count).query (.inl (.inl coin)) : OracleComp (GlobalSpec count) _))
      (globalClass predicate) _
    rw [OracleComp.isQueryBoundP_map_iff]
    apply (OracleComp.isQueryBoundP_query_iff (spec := GlobalSpec count)
      (p := globalClass predicate) (.inl (.inl coin)) _).mpr
    simp only [globalClass, familyClass, dynamicClass]
    split_ifs <;> simp_all
  | inr request =>
    cases request with
    | create =>
      simp only [routeImpl, StateT.run]
      split <;> trivial
    | service identity request =>
      simp only [routeImpl, StateT.run]
      split
      · rename_i available
        change OracleComp.IsQueryBoundP
          ((fun answer : JointSpec.Range request =>
            (some answer, appendObservation (.inr (.service identity request)) (some answer) state)) <$>
            ((GlobalSpec count).query (.inl (.inr (⟨identity, available.2⟩, request))) :
              OracleComp (GlobalSpec count) _)) (globalClass predicate) _
        rw [OracleComp.isQueryBoundP_map_iff]
        apply (OracleComp.isQueryBoundP_query_iff (spec := GlobalSpec count)
          (p := globalClass predicate) (.inl (.inr (⟨identity, available.2⟩, request))) _).mpr
        simp only [globalClass, familyClass, dynamicClass]
        split_ifs <;> simp_all
      · trivial
    | reveal identity =>
      simp only [routeImpl, StateT.run]
      split
      · rename_i available
        change OracleComp.IsQueryBoundP
          ((fun answer : IdentitySeed =>
            (some answer, appendObservation (.inr (.reveal identity)) (some answer) state)) <$>
            ((GlobalSpec count).query (.inr ⟨identity, available.2⟩) :
              OracleComp (GlobalSpec count) _)) (globalClass predicate) _
        rw [OracleComp.isQueryBoundP_map_iff]
        apply (OracleComp.isQueryBoundP_query_iff (spec := GlobalSpec count)
          (p := globalClass predicate) (.inr ⟨identity, available.2⟩) _).mpr
        simp only [globalClass, false_implies]
      · trivial

/-- Every adaptive continued router inherits each declared source primitive-class cap. -/
theorem routeRun_query_bound {count : ℕ} (publicKeys : Fin count → PublicIdentity)
    {Result : Type} (client : OracleComp DynamicSpec Result)
    (predicate : AdversarySpec.Domain → Prop) [DecidablePred predicate]
    (bound : ℕ) (bounded : client.IsQueryBoundP (dynamicClass predicate) bound) (state : PublicState) :
    ((simulateQ (routeImpl publicKeys) client).run state).IsQueryBoundP (globalClass predicate) bound :=
  bounded.simulateQ_run_StateT_of_step (routeImpl_query_bound publicKeys predicate) state

/-- A dynamic client can choose any natural-number identity, including an uncreated one. -/
structure DynamicForgery where
  identity : ℕ
  forgery : Forgery

/-- The dynamic source event requires an actually created seed at the selected index and freshness through the final decision. There is no assumed target choice restriction on the client. -/
def DynamicEvent (primitives : Primitives) {count : ℕ}
    (result : DynamicForgery × (GlobalState count × PqxdhDynamicIdentityPool.SourceState)) : Prop :=
  ∃ valid : result.1.identity < count, ∃ seed,
    result.2.2.seeds[result.1.identity]? = some seed ∧
      Fresh ⟨result.1.identity, valid⟩ result.2.1 ∧
      wins primitives (primitives.publicKeys seed) result.1.forgery
        (result.2.1.histories ⟨result.1.identity, valid⟩) = true

/-- An invalid selected index is mapped to a fixed fallback. Such extra primitive wins only enlarge the reduction's upper bound. -/
def selectedForgery (count : ℕ) (fallback : Forgery) (candidate : DynamicForgery) :
    FamilyForgery (count + 1) :=
  if valid : candidate.identity < count + 1 then ⟨⟨candidate.identity, valid⟩, candidate.forgery⟩
  else ⟨0, fallback⟩

/-- The global adversary runs the exact public dynamic router and returns the unchanged selected forgery whenever its generated index exists in the reserved family. It never receives a private seed. -/
def routedAdversary (count : ℕ) (fallback : Forgery) (client : OracleComp DynamicSpec DynamicForgery)
    (publicKeys : Fin (count + 1) → PublicIdentity) :
    OracleComp (GlobalSpec (count + 1)) (FamilyForgery (count + 1)) := do
  let result ← (simulateQ (routeImpl publicKeys) client).run initialPublicState
  pure (selectedForgery count fallback result.1)

/-- A successful dynamic event implies the ordinary indexed signature event under the same seed and complete histories. This does not identify indices by equality of public key bytes. -/
theorem dynamicEvent_implies_global (primitives : Primitives) (count : ℕ) (fallback : Forgery)
    (seeds : Fin (count + 1) → IdentitySeed)
    (result : (DynamicForgery × PublicState) × GlobalState (count + 1))
    (accepted : DynamicEvent primitives
      (result.1.1, projection seeds (result.1.2, result.2))) :
    GlobalEvent primitives
      (familyPublic primitives seeds, selectedForgery count fallback result.1.1, result.2) := by
  obtain ⟨valid, seed, lookup, fresh, signature⟩ := accepted
  have lookupExact : (sourceState seeds result.1.2).seeds[result.1.1.identity]? =
      if result.1.1.identity < result.1.2.created then
        some (seeds ⟨result.1.1.identity, valid⟩) else none := by
    by_cases created : result.1.1.identity < result.1.2.created
    · rw [sourceState_lookup seeds result.1.2 result.1.1.identity created valid, if_pos created]
    · rw [sourceState_uncreated seeds result.1.2 result.1.1.identity (Nat.le_of_not_gt created), if_neg created]
  change (sourceState seeds result.1.2).seeds[result.1.1.identity]? = some seed at lookup
  rw [lookupExact] at lookup
  by_cases created : result.1.1.identity < result.1.2.created
  · rw [if_pos created] at lookup
    have seedEq := Option.some.inj lookup
    simp only [GlobalEvent, TargetEvent, selectedForgery, dif_pos valid]
    exact ⟨fresh, by simpa only [projection, familyPublic, seedEq] using signature⟩
  · simp [created] at lookup

/-- The complete reserved dynamic execution is bounded by the existing family event, with no loss for creation timing or invalid-index rejection. -/
theorem reserved_event_le_global (primitives : Primitives) (count : ℕ) (fallback : Forgery)
    (client : OracleComp DynamicSpec DynamicForgery) :
    Pr[DynamicEvent primitives | reservedRun primitives (count + 1) client] ≤
      Pr[GlobalEvent primitives | globalRun primitives (count + 1) (routedAdversary count fallback client)] := by
  unfold reservedRun globalRun
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro seeds
  apply mul_le_mul' le_rfl
  rw [QueryImpl.Stateful.simulateQ_link_run]
  simp only [routedAdversary, bind_pure_comp, simulateQ_map, StateT.run_map,
    Functor.map_map, probEvent_map, Function.comp_def]
  apply probEvent_mono
  intro result _ accepted
  exact dynamicEvent_implies_global primitives count fallback seeds result accepted

/-- Dynamic generated-identity selection reduces to the same explicitly stronger joint-use weak-EUF endpoints. The only selection loss is the sum over the reserved creation cap. -/
theorem dynamic_advantage_le_sum (primitives : Primitives) (count : ℕ) (fallback : Forgery)
    (client : OracleComp DynamicSpec DynamicForgery)
    (bounded : client.IsQueryBoundP PqxdhDynamicIdentityPool.IsCreate (count + 1)) :
    Pr[DynamicEvent primitives | dynamicRun primitives (count + 1) client] ≤
      ∑ target : Fin (count + 1), advantage primitives
        (globalReduction primitives target fallback (routedAdversary count fallback client)) := by
  have same := OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
    (dynamic_reserved_complete primitives (count + 1) client bounded)
      (p := DynamicEvent primitives) (q := DynamicEvent primitives)
  rw [same]
  exact (reserved_event_le_global primitives count fallback client).trans
    (global_advantage_le_sum primitives count fallback (routedAdversary count fallback client))

/-- The completed dynamic client keeps all source primitive-class budgets in the existing global family interface. -/
theorem routedAdversary_query_bound (count : ℕ) (fallback : Forgery)
    (client : OracleComp DynamicSpec DynamicForgery)
    (predicate : AdversarySpec.Domain → Prop) [DecidablePred predicate]
    (bound : ℕ) (bounded : client.IsQueryBoundP (dynamicClass predicate) bound)
    (publicKeys : Fin (count + 1) → PublicIdentity) :
    (routedAdversary count fallback client publicKeys).IsQueryBoundP (globalClass predicate) bound := by
  simpa only [routedAdversary, bind_pure_comp, OracleComp.isQueryBoundP_map_iff] using
    routeRun_query_bound publicKeys client predicate bound bounded initialPublicState

/-- Each selected reduction pays for every other reserved seed and inherits the full source signing/DH/uniform class cap. -/
theorem dynamicReduction_query_bound (primitives : Primitives) (count : ℕ)
    (target : Fin (count + 1)) (fallback : Forgery) (client : OracleComp DynamicSpec DynamicForgery)
    (kind : Kind) (bound : ℕ) (bounded : client.IsQueryBoundP (dynamicClass (IsClass kind)) bound)
    (jointPublic : PublicIdentity) :
    (globalReduction primitives target fallback (routedAdversary count fallback client) jointPublic).IsQueryBoundP
      (IsClass kind) ((if kind = .uniform then 32 * count else 0) + bound) :=
  globalReduction_query_bound primitives target fallback (routedAdversary count fallback client) kind bound
    (routedAdversary_query_bound count fallback client (IsClass kind) bound bounded) jointPublic

/-- Challenger seed generation is included: a full interpreted selected reduction costs 32 times the reservation cap plus every source uniform request. -/
theorem dynamicReductionGame_uniform_bound (primitives : Primitives) (count : ℕ)
    (target : Fin (count + 1)) (fallback : Forgery) (client : OracleComp DynamicSpec DynamicForgery)
    (bound : ℕ) (bounded : client.IsQueryBoundP (dynamicClass (IsClass .uniform)) bound) :
    (game primitives (globalReduction primitives target fallback
      (routedAdversary count fallback client))).IsTotalQueryBound (32 * (count + 1) + bound) :=
  globalReductionGame_uniform_bound primitives target fallback (routedAdversary count fallback client) bound
    (routedAdversary_query_bound count fallback client (IsClass .uniform) bound bounded)

/-- The actual monitored source pays only for seeds actually created and explicit source coin queries; monitoring preserves their exact caps. -/
theorem dynamicRun_uniform_bound (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp DynamicSpec Result) (qCreate qUniform : ℕ)
    (creates : client.IsQueryBoundP PqxdhDynamicIdentityPool.IsCreate qCreate)
    (coins : client.IsQueryBoundP PqxdhDynamicIdentityPool.IsUniform qUniform) :
    (dynamicRun primitives count client).IsTotalQueryBound (32 * qCreate + qUniform) := by
  rw [dynamicRun, sourceWithHistory, QueryImpl.Stateful.simulateQ_link_run]
  simp only [OracleComp.IsTotalQueryBound, OracleComp.isQueryBound_map_iff]
  exact PqxdhDynamicIdentityPool.lazyRun_uniform_bound primitives
    ((simulateQ (historyImpl count) client).run (PqxdhJointIdentityFreshness.initialState count)) qCreate qUniform
    (historyRun_query_bound count client PqxdhDynamicIdentityPool.IsCreate qCreate creates _)
    (historyRun_query_bound count client PqxdhDynamicIdentityPool.IsUniform qUniform coins _)
    PqxdhDynamicIdentityPool.initialState

/-- Every actual query class is counted in the retained dynamic trace, including repeated reveals, uncreated indices and rejected DH requests. -/
theorem dynamicRun_trace_bound (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp DynamicSpec Result) (predicate : DynamicSpec.Domain → Prop)
    [DecidablePred predicate] (bound : ℕ) (bounded : client.IsQueryBoundP predicate bound)
    (result : Result × (GlobalState count × PqxdhDynamicIdentityPool.SourceState))
    (supported : result ∈ support (dynamicRun primitives count client)) :
    PqxdhDynamicIdentityPool.traceCount predicate result.2.2 ≤ bound := by
  rw [dynamicRun, sourceWithHistory, QueryImpl.Stateful.simulateQ_link_run] at supported
  obtain ⟨actual, actualSupported, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
  have counted := PqxdhDynamicIdentityPool.lazyRun_trace_bound primitives predicate
    ((simulateQ (historyImpl count) client).run (PqxdhJointIdentityFreshness.initialState count)) bound
    (historyRun_query_bound count client predicate bound bounded _) PqxdhDynamicIdentityPool.initialState
    actual actualSupported
  change PqxdhDynamicIdentityPool.traceCount predicate actual.2 ≤ bound
  simpa only [PqxdhDynamicIdentityPool.traceCount, PqxdhDynamicIdentityPool.initialState,
    List.countP_nil, Nat.zero_add] using counted

/-- The two public spellings of the source uniform-query class are exactly equal. -/
theorem dynamicClass_uniform : dynamicClass (IsClass .uniform) = PqxdhDynamicIdentityPool.IsUniform := by
  funext query
  cases query with
  | inl coin => simp [dynamicClass, IsClass, PqxdhDynamicIdentityPool.IsUniform]
  | inr request =>
    cases request with
    | create => rfl
    | service identity request => cases request <;> simp [dynamicClass, IsClass, PqxdhDynamicIdentityPool.IsUniform]
    | reveal identity => rfl

/-- A common endpoint bound gives the single generated-identity selection factor. Creation timing and attempted invalid-index calls introduce no additional loss. -/
theorem dynamic_advantage_le_count (primitives : Primitives) (count : ℕ) (fallback : Forgery)
    (client : OracleComp DynamicSpec DynamicForgery)
    (creates : client.IsQueryBoundP PqxdhDynamicIdentityPool.IsCreate (count + 1))
    (epsilon : ℝ≥0∞)
    (bounded : ∀ target, advantage primitives
      (globalReduction primitives target fallback (routedAdversary count fallback client)) ≤ epsilon) :
    Pr[DynamicEvent primitives | dynamicRun primitives (count + 1) client] ≤
      (count + 1 : ℕ) * epsilon := by
  exact (dynamic_advantage_le_sum primitives count fallback client creates).trans
    ((Finset.sum_le_sum fun target _ => bounded target).trans_eq (by simp))

/-- With no generated-identity index available the signature event is false, independently of the client's behavior. -/
theorem zero_identity_event (primitives : Primitives) (client : OracleComp DynamicSpec DynamicForgery) :
    Pr[DynamicEvent primitives | dynamicRun primitives 0 client] = 0 := by
  apply probEvent_eq_zero
  intro result _ accepted
  obtain ⟨valid, _⟩ := accepted
  exact Nat.not_lt_zero _ valid

end BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting.route_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting.route_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting.lazy_eager_history_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting.lazy_eager_history_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting.dynamic_reserved_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting.dynamic_reserved_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting.dynamic_advantage_le_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting.dynamic_advantage_le_sum

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting.dynamicReduction_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting.dynamicReduction_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting.dynamicReductionGame_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting.dynamicReductionGame_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting.dynamicRun_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting.dynamicRun_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting.dynamicRun_trace_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting.dynamicRun_trace_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting.dynamic_advantage_le_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting.dynamic_advantage_le_count
