import BeaconcryptCore.Computational.KemValueClasses
import BeaconcryptCore.Model.Pqxdh.Primitives

/-!
This finite functional KEM graph retains the complete actual public-key derivation, encapsulation and decapsulation addresses and their actual replies. Public/private call tags route to the same graph; they record dispatch and do not enforce a native capability or attacker-access policy. Repeated addresses reuse the whole answer, while unseen addresses append their actual result. Outputs may coincide across distinct inputs. Matching-key correctness constrains equal ciphertexts and every prior decapsulation reply, including a prior rejection, without public-key, coin, ciphertext or shared-secret injectivity.

The source interpreter uses the existing fixed functional Pqxdh.Crypto interface: encapsulation is total and decapsulation returns its actual Option. The accompanying base interpreter retains arbitrary stateful effects and caller randomness. These statements do not instantiate native optional public-key validation/encapsulation, a probabilistic ML-KEM implementation, or honest coin distributions. Functional primitive evaluation, byte equality and table work remain local computation; exact underlying-oracle cap preservation does not declare them free.

Checked lookup and private shared byte-class recording erase to the exact original adaptive client result and complete primitive state in every lawful target monad. Input and answer fields share one actual-value table, so the existing retained-lookup branch theorem applies to equality and disequality. Graphs, classes, secret input bytes and call histories are private ghost state, excluded from network, reveal, snapshot and persistence interfaces. Class indices are not public encodings, guess-resistant names, or permission tokens.

The source-independent ValidExtension relation permits an exact cached answer or a new complete binding subject to operation shape and necessary finite matching-key consistency constraints. It permits ordinary distinct outputs and aliases. It is an overapproximation: these constraints do not characterize all graphs realizable by one global Crypto instance and supply no distribution on abstract choices. The traced interpreter internally constructs every actual KEM request/reply event in chronological order, including repeats and rejection; other base calls are forwarded unchanged without appearing in this KEM-only transcript. Every supported original execution has the same complete result/state plus such a trace and unique value representatives.

This is the bounded functional graph/trace interface for a later applied-pi service, not a ProVerif process simulation, source-free probabilistic scheduler, hidden-value guessing or collision bound, ordinary KEM reduction, or global protocol security theorem. Future public evaluations and guesses must retain actual common-byte consistency; the former forced coin-only quotient is not reinstated. Native capability routing, optional/error domains, actual primitive work and the persistent admitted-state/event/observation mapping remain explicit next obligations.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.KemFunctionalGraph

inductive Address where
  | publicKey (secret : Pqxdh.Bytes)
  | encapsulate (publicKey coins : Pqxdh.Bytes)
  | decapsulate (secret ciphertext : Pqxdh.Bytes)
  deriving DecidableEq

inductive Answer where
  | publicKey (value : Pqxdh.Bytes)
  | encapsulated (ciphertext secret : Pqxdh.Bytes)
  | decapsulated (secret : Option Pqxdh.Bytes)
  deriving DecidableEq

def evaluate (c : Pqxdh.Crypto) : Address → Answer
  | .publicKey secret => .publicKey (c.kemPub secret)
  | .encapsulate publicKey coins =>
    let result := c.encap publicKey coins
    .encapsulated result.1 result.2
  | .decapsulate secret ciphertext => .decapsulated (c.decap secret ciphertext)

abbrev Graph := List (Address × Answer)

def Consistent (c : Pqxdh.Crypto) (graph : Graph) : Prop :=
  ∀ entry ∈ graph, entry.2 = evaluate c entry.1

def remember (query : Address) (answer : Answer) (graph : Graph) : Graph :=
  if (graph.lookup query).isSome then graph else graph ++ [(query, answer)]

def tableStep (c : Pqxdh.Crypto) (query : Address) (graph : Graph) : Answer × Graph :=
  let answer := (graph.lookup query).getD (evaluate c query)
  (answer, remember query answer graph)

/-- Every successful lookup in the actual graph has exactly its original functional answer. -/
theorem lookup_consistent (c : Pqxdh.Crypto) (query : Address) (graph : Graph)
    (consistent : Consistent c graph) (answer : Answer)
    (found : graph.lookup query = some answer) : answer = evaluate c query := by
  induction graph with
  | nil => simp at found
  | cons entry tail ih =>
    by_cases same : query = entry.1
    · simp [List.lookup, same] at found
      subst answer
      exact same ▸ consistent entry (by simp)
    · have different : (query == entry.1) = false := by
        apply Bool.eq_false_iff.mpr
        intro equal
        exact same (eq_of_beq equal)
      simp only [List.lookup, different] at found
      exact ih (fun entry member => consistent entry (by simp [member])) found

/-- The memoized reply equals the original complete functional reply. -/
theorem tableStep_reply (c : Pqxdh.Crypto) (query : Address) (graph : Graph)
    (consistent : Consistent c graph) : (tableStep c query graph).1 = evaluate c query := by
  cases found : graph.lookup query with
  | none => simp [tableStep, found]
  | some answer => simpa [tableStep, found] using lookup_consistent c query graph consistent answer found

/-- The actual hit/miss update preserves every binding's functional interpretation. -/
theorem tableStep_consistent (c : Pqxdh.Crypto) (query : Address) (graph : Graph)
    (consistent : Consistent c graph) : Consistent c (tableStep c query graph).2 := by
  have reply := tableStep_reply c query graph consistent
  change Consistent c (remember query (tableStep c query graph).1 graph)
  unfold remember
  split
  · exact consistent
  · intro entry member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact consistent entry old
    · exact reply

/-- An append preserves left-hand lookup precedence. -/
theorem lookup_append (query : Address) (left right : Graph) :
    (left ++ right).lookup query = (left.lookup query).orElse (fun _ => right.lookup query) := by
  induction left with
  | nil => rfl
  | cons entry tail ih =>
    simp only [List.cons_append, List.lookup]
    cases query == entry.1 <;> simp [ih]

/-- Every earlier complete-address binding survives a later step. -/
theorem tableStep_preserves (c : Pqxdh.Crypto) (query previous : Address) (graph : Graph)
    (answer : Answer) (found : graph.lookup previous = some answer) :
    (tableStep c query graph).2.lookup previous = some answer := by
  unfold tableStep remember
  split
  · exact found
  · simp [lookup_append, found]

/-- The returned complete answer is stored at the requested address. -/
theorem tableStep_lookup (c : Pqxdh.Crypto) (query : Address) (graph : Graph) :
    (tableStep c query graph).2.lookup query = some (tableStep c query graph).1 := by
  cases found : graph.lookup query with
  | none => simp [tableStep, remember, found, lookup_append, List.lookup]
  | some answer => simp [tableStep, remember, found]

/-- A call either reuses its existing complete answer or appends one actual new binding. -/
theorem tableStep_cases (c : Pqxdh.Crypto) (query : Address) (graph : Graph) :
    (∃ answer, graph.lookup query = some answer ∧ tableStep c query graph = (answer, graph)) ∨
      (graph.lookup query = none ∧
        tableStep c query graph = (evaluate c query, graph ++ [(query, evaluate c query)])) := by
  cases found : graph.lookup query with
  | none => exact Or.inr ⟨rfl, by simp [tableStep, remember, found]⟩
  | some answer => exact Or.inl ⟨answer, rfl, by simp [tableStep, remember, found]⟩

/-- Repeating an address returns the same answer and leaves the entire graph unchanged. -/
theorem tableStep_repeat (c : Pqxdh.Crypto) (query : Address) (graph : Graph) :
    tableStep c query (tableStep c query graph).2 = tableStep c query graph := by
  have found := tableStep_lookup c query graph
  cases result_eq : tableStep c query graph with
  | mk answer next =>
    rw [result_eq] at found
    simp [tableStep, remember, found]

/-- A call appends at most one binding without changing the old prefix. -/
theorem tableStep_extends (c : Pqxdh.Crypto) (query : Address) (graph : Graph) :
    ∃ suffix, (tableStep c query graph).2 = graph ++ suffix ∧ suffix.length ≤ 1 := by
  rcases tableStep_cases c query graph with ⟨answer, _, equality⟩ | ⟨_, equality⟩
  · exact ⟨[], by simp [equality]⟩
  · exact ⟨[(query, evaluate c query)], by simp [equality]⟩

/-- Each call grows the finite graph by zero or one entry. -/
theorem tableStep_length (c : Pqxdh.Crypto) (query : Address) (graph : Graph) :
    graph.length ≤ (tableStep c query graph).2.length ∧
      (tableStep c query graph).2.length ≤ graph.length + 1 := by
  obtain ⟨suffix, extension, bound⟩ := tableStep_extends c query graph
  simp only [extension, List.length_append]
  omega

/-- Functional matching-key correctness couples equal ciphertexts to equal shared secrets. -/
theorem same_key_ciphertext (c : Pqxdh.Crypto) (secret leftCoins rightCoins : Pqxdh.Bytes)
    (same : (c.encap (c.kemPub secret) leftCoins).1 =
      (c.encap (c.kemPub secret) rightCoins).1) :
    (c.encap (c.kemPub secret) leftCoins).2 =
      (c.encap (c.kemPub secret) rightCoins).2 := by
  have left := c.decap_encap secret leftCoins
  have right := c.decap_encap secret rightCoins
  rw [same, right] at left
  exact Option.some.inj left.symm

/-- A prior successful decapsulation fixes the matching later encapsulation's actual secret. -/
theorem decap_before_encap (c : Pqxdh.Crypto) (graph : Graph)
    (consistent : Consistent c graph) (secret ciphertext coins shared : Pqxdh.Bytes)
    (previous : graph.lookup (.decapsulate secret ciphertext) = some (.decapsulated (some shared)))
    (same : (c.encap (c.kemPub secret) coins).1 = ciphertext) :
    (tableStep c (.encapsulate (c.kemPub secret) coins) graph).1 =
      .encapsulated ciphertext shared := by
  have old := lookup_consistent c _ graph consistent _ previous
  have recovered : some shared = c.decap secret ciphertext := Answer.decapsulated.inj old
  have correct := c.decap_encap secret coins
  rw [same, ← recovered] at correct
  rw [tableStep_reply c _ graph consistent]
  simp only [evaluate, same, Option.some.inj correct]

/-- Every prior optional decapsulation reply agrees with a later matching ciphertext, so prior rejection is impossible in this case. -/
theorem decap_prior_reply (c : Pqxdh.Crypto) (graph : Graph)
    (consistent : Consistent c graph) (secret ciphertext coins : Pqxdh.Bytes)
    (observed : Option Pqxdh.Bytes)
    (previous : graph.lookup (.decapsulate secret ciphertext) = some (.decapsulated observed))
    (same : (c.encap (c.kemPub secret) coins).1 = ciphertext) :
    observed = some (c.encap (c.kemPub secret) coins).2 := by
  have old := lookup_consistent c _ graph consistent _ previous
  have recovered : observed = c.decap secret ciphertext := Answer.decapsulated.inj old
  rw [recovered, ← same]
  exact c.decap_encap secret coins

structure CheckedGraph (c : Pqxdh.Crypto) where
  entries : Graph
  consistent : Consistent c entries

def empty (c : Pqxdh.Crypto) : CheckedGraph c :=
  ⟨[], by intro entry member; simp at member⟩

def checkedStep (c : Pqxdh.Crypto) (query : Address) (graph : CheckedGraph c) :
    Answer × CheckedGraph c :=
  let next := tableStep c query graph.entries
  (next.1, ⟨next.2, tableStep_consistent c query graph.entries graph.consistent⟩)

inductive Access where
  | publicCall
  | privateCall
  deriving DecidableEq

abbrev ServiceSpec := (Access × Address) →ₒ Answer
abbrev Spec {ι : Type} (base : OracleSpec ι) := base + ServiceSpec

def sourceImpl {State : Type} {ι : Type} {base : OracleSpec ι}
    {m : Type → Type} [Monad m] (c : Pqxdh.Crypto)
    (impl : QueryImpl base (StateT State m)) :
    QueryImpl (Spec base) (StateT State m)
  | .inl query => impl query
  | .inr request => fun state => pure (evaluate c request.2, state)

def tableImpl {State : Type} {ι : Type} {base : OracleSpec ι}
    {m : Type → Type} [Monad m] (c : Pqxdh.Crypto)
    (impl : QueryImpl base (StateT State m)) :
    QueryImpl (Spec base) (StateT (State × CheckedGraph c) m)
  | .inl query => fun state => do
    let result ← impl query state.1
    pure (result.1, (result.2, state.2))
  | .inr request => fun state =>
    let next := checkedStep c request.2 state.2
    pure (next.1, (state.1, next.2))

/-- Public and private dispatch tags share exactly the same graph computation. -/
theorem public_private_same {State : Type} {ι : Type} {base : OracleSpec ι}
    {m : Type → Type} [Monad m] (c : Pqxdh.Crypto)
    (impl : QueryImpl base (StateT State m)) (query : Address) :
    tableImpl c impl (.inr (.publicCall, query)) =
      tableImpl c impl (.inr (.privateCall, query)) := rfl

/-- Erasing the graph retains the dependent reply and complete primitive poststate. -/
theorem table_step_erasure {State : Type} {ι : Type} {base : OracleSpec ι}
    {m : Type → Type} [Monad m] [LawfulMonad m] (c : Pqxdh.Crypto)
    (impl : QueryImpl base (StateT State m)) (query : (Spec base).Domain)
    (state : State) (graph : CheckedGraph c) :
    (fun result => (result.1, result.2.1)) <$>
      tableImpl c impl query (state, graph) = sourceImpl c impl query state := by
  cases query with
  | inl query => simp [tableImpl, sourceImpl]
  | inr request =>
    simp [tableImpl, sourceImpl, checkedStep,
      tableStep_reply c request.2 graph.entries graph.consistent]

/-- Graph erasure preserves the whole arbitrary adaptive interpreted client. -/
theorem table_execution_erasure {State Result : Type} {ι : Type} {base : OracleSpec ι}
    {m : Type → Type} [Monad m] [LawfulMonad m] (c : Pqxdh.Crypto)
    (impl : QueryImpl base (StateT State m)) (client : OracleComp (Spec base) Result)
    (state : State) (graph : CheckedGraph c) :
    (fun result => (result.1, result.2.1)) <$>
      (simulateQ (tableImpl c impl) client).run (state, graph) =
        (simulateQ (sourceImpl c impl) client).run state := by
  induction client using OracleComp.inductionOn generalizing state graph with
  | pure result => simp
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    simp only [StateT.run] at ih
    cases query with
    | inl query => simp [StateT.run, tableImpl, sourceImpl, ih]
    | inr request =>
      simp [StateT.run, tableImpl, sourceImpl, ih, checkedStep,
        tableStep_reply c request.2 graph.entries graph.consistent]

def inputFields : Address → List Pqxdh.Bytes
  | .publicKey secret => [secret]
  | .encapsulate publicKey coins => [publicKey, coins]
  | .decapsulate secret ciphertext => [secret, ciphertext]

def answerFields : Answer → List Pqxdh.Bytes
  | .publicKey value => [value]
  | .encapsulated ciphertext secret => [ciphertext, secret]
  | .decapsulated none => []
  | .decapsulated (some secret) => [secret]

def observed {ι : Type} {base : OracleSpec ι} :
    (query : (Spec base).Domain) → (Spec base).Range query → List Pqxdh.Bytes
  | .inl _, _ => []
  | .inr request, answer => inputFields request.2 ++ answerFields answer

abbrev classifiedImpl {State : Type} {ι : Type} {base : OracleSpec ι}
    {m : Type → Type} [Monad m] (c : Pqxdh.Crypto)
    (impl : QueryImpl base (StateT State m)) :=
  KemValueClasses.annotatedImpl (tableImpl c impl) observed

/-- Erasing both private tables retains the original complete adaptive computation. -/
theorem classified_execution_erasure {State Result : Type} {ι : Type} {base : OracleSpec ι}
    {m : Type → Type} [Monad m] [LawfulMonad m] (c : Pqxdh.Crypto)
    (impl : QueryImpl base (StateT State m)) (client : OracleComp (Spec base) Result)
    (state : State) (graph : CheckedGraph c) (classes : List Pqxdh.Bytes) :
    (fun result => (result.1, result.2.1.1)) <$>
      (simulateQ (classifiedImpl c impl) client).run ((state, graph), classes) =
        (simulateQ (sourceImpl c impl) client).run state := by
  have graphErasure := KemValueClasses.annotated_execution (tableImpl c impl) observed
    client (state, graph) classes
  have erased := congrArg (fun computation =>
    (fun result => (result.1, result.2.1)) <$> computation) graphErasure
  simpa only [Functor.map_map, Function.comp_def] using
    erased.trans (table_execution_erasure c impl client state graph)

/-- Every selective underlying-oracle cap is exactly preserved by graph/class recording. -/
theorem classified_query_bounds {State Result : Type} {ι κ : Type}
    {base : OracleSpec ι} {target : OracleSpec κ} (c : Pqxdh.Crypto)
    (impl : QueryImpl base (StateT State (OracleComp target)))
    (client : OracleComp (Spec base) Result) (state : State)
    (graph : CheckedGraph c) (classes : List Pqxdh.Bytes)
    (predicate : target.Domain → Prop) [DecidablePred predicate] (bound : Nat) :
    ((simulateQ (classifiedImpl c impl) client).run ((state, graph), classes)).IsQueryBoundP
        predicate bound ↔
      ((simulateQ (sourceImpl c impl) client).run state).IsQueryBoundP predicate bound := by
  rw [← classified_execution_erasure c impl client state graph classes]
  exact (OracleComp.isQueryBoundP_map_iff _ _ _).symm

/-- All supported runs preserve unique representatives in the common byte-value table. -/
theorem classified_supported_nodup {State Result : Type} {ι κ : Type}
    {base : OracleSpec ι} {target : OracleSpec κ} (c : Pqxdh.Crypto)
    (impl : QueryImpl base (StateT State (OracleComp target)))
    (client : OracleComp (Spec base) Result) (state : State)
    (graph : CheckedGraph c) (classes : List Pqxdh.Bytes) (unique : classes.Nodup)
    (result : Result × ((State × CheckedGraph c) × List Pqxdh.Bytes))
    (present : result ∈ support
      ((simulateQ (classifiedImpl c impl) client).run ((state, graph), classes))) :
    result.2.2.Nodup :=
  KemValueClasses.annotated_supported_nodup (tableImpl c impl) observed client
    (state, graph) classes unique result present

/-- A KEM call records at most four actual input/reply fields. -/
theorem observed_length {ι : Type} {base : OracleSpec ι}
    (query : (Spec base).Domain) (answer : (Spec base).Range query) :
    (observed query answer).length ≤ 4 := by
  cases query with
  | inl query => simp [observed]
  | inr request =>
    rcases request with ⟨access, request⟩
    cases request <;> cases answer <;> simp [observed, inputFields, answerFields]
    all_goals split <;> simp

/-- Each recorded actual field has a retained value-class lookup. -/
theorem recorded_field (fields classes : List Pqxdh.Bytes) (value : Pqxdh.Bytes)
    (member : value ∈ fields) :
    ∃ index : Nat, (KemValueClasses.record fields classes)[index]? = some value := by
  induction fields generalizing classes with
  | nil => simp at member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨(KemValueClasses.intern value classes).1,
        KemValueClasses.record_preserves_lookup rest _ value _
          (KemValueClasses.intern_value value classes)⟩
    · exact ih _ later

def Matches : Address → Answer → Prop
  | .publicKey _, .publicKey _ => True
  | .encapsulate _ _, .encapsulated _ _ => True
  | .decapsulate _ _, .decapsulated _ => True
  | _, _ => False

def Compatible (graph : Graph) : Prop :=
  (∀ query answer, graph.lookup query = some answer → Matches query answer) ∧
  (∀ secret publicKey coins ciphertext shared observed,
    graph.lookup (.publicKey secret) = some (.publicKey publicKey) →
    graph.lookup (.encapsulate publicKey coins) = some (.encapsulated ciphertext shared) →
    graph.lookup (.decapsulate secret ciphertext) = some (.decapsulated observed) →
    observed = some shared) ∧
  (∀ secret publicKey leftCoins rightCoins ciphertext leftShared rightShared,
    graph.lookup (.publicKey secret) = some (.publicKey publicKey) →
    graph.lookup (.encapsulate publicKey leftCoins) = some (.encapsulated ciphertext leftShared) →
    graph.lookup (.encapsulate publicKey rightCoins) = some (.encapsulated ciphertext rightShared) →
    leftShared = rightShared)

/-- Actual graph replies retain the operation's answer shape. -/
theorem consistent_matches (c : Pqxdh.Crypto) (graph : Graph)
    (consistent : Consistent c graph) (query : Address) (answer : Answer)
    (found : graph.lookup query = some answer) : Matches query answer := by
  rw [lookup_consistent c query graph consistent answer found]
  cases query <;> simp [evaluate, Matches]

/-- Existing key, encapsulation and optional decapsulation bindings obey actual matching-key correctness. -/
theorem consistent_decapsulation (c : Pqxdh.Crypto) (graph : Graph)
    (consistent : Consistent c graph) (secret publicKey coins ciphertext shared : Pqxdh.Bytes)
    (observed : Option Pqxdh.Bytes)
    (key : graph.lookup (.publicKey secret) = some (.publicKey publicKey))
    (encapsulation : graph.lookup (.encapsulate publicKey coins) =
      some (.encapsulated ciphertext shared))
    (decapsulation : graph.lookup (.decapsulate secret ciphertext) =
      some (.decapsulated observed)) : observed = some shared := by
  have keyValue := Answer.publicKey.inj (lookup_consistent c _ graph consistent _ key)
  have pair := Answer.encapsulated.inj (lookup_consistent c _ graph consistent _ encapsulation)
  have recovered := Answer.decapsulated.inj
    (lookup_consistent c _ graph consistent _ decapsulation)
  change publicKey = c.kemPub secret at keyValue
  change ciphertext = (c.encap publicKey coins).1 ∧ shared = (c.encap publicKey coins).2 at pair
  change observed = c.decap secret ciphertext at recovered
  rw [recovered, pair.1, keyValue, c.decap_encap, ← keyValue, ← pair.2]

/-- Existing same-key ciphertext aliases share the same actual secret even before decapsulation is requested. -/
theorem consistent_ciphertexts (c : Pqxdh.Crypto) (graph : Graph)
    (consistent : Consistent c graph)
    (secret publicKey leftCoins rightCoins ciphertext leftShared rightShared : Pqxdh.Bytes)
    (key : graph.lookup (.publicKey secret) = some (.publicKey publicKey))
    (left : graph.lookup (.encapsulate publicKey leftCoins) =
      some (.encapsulated ciphertext leftShared))
    (right : graph.lookup (.encapsulate publicKey rightCoins) =
      some (.encapsulated ciphertext rightShared)) : leftShared = rightShared := by
  have keyValue := Answer.publicKey.inj (lookup_consistent c _ graph consistent _ key)
  have leftPair := Answer.encapsulated.inj (lookup_consistent c _ graph consistent _ left)
  have rightPair := Answer.encapsulated.inj (lookup_consistent c _ graph consistent _ right)
  change publicKey = c.kemPub secret at keyValue
  change ciphertext = (c.encap publicKey leftCoins).1 ∧
    leftShared = (c.encap publicKey leftCoins).2 at leftPair
  change ciphertext = (c.encap publicKey rightCoins).1 ∧
    rightShared = (c.encap publicKey rightCoins).2 at rightPair
  rw [leftPair.2, rightPair.2, keyValue]
  apply same_key_ciphertext
  simpa [← keyValue] using leftPair.1.symm.trans rightPair.1

/-- Every actual graph satisfies the stated necessary finite constraints. -/
theorem consistent_compatible (c : Pqxdh.Crypto) (graph : Graph)
    (consistent : Consistent c graph) : Compatible graph :=
  ⟨consistent_matches c graph consistent,
    consistent_decapsulation c graph consistent,
    consistent_ciphertexts c graph consistent⟩

inductive Extension : Graph → Address → Answer → Graph → Prop where
  | repeat (graph : Graph) (query : Address) (answer : Answer)
      (found : graph.lookup query = some answer) : Extension graph query answer graph
  | append (graph : Graph) (query : Address) (answer : Answer)
      (absent : graph.lookup query = none) :
      Extension graph query answer (graph ++ [(query, answer)])

def ValidExtension (before : Graph) (query : Address) (answer : Answer) (after : Graph) : Prop :=
  Extension before query answer after ∧ Compatible after

/-- Every actual call is an allowed source-independent finite table transition. -/
theorem tableStep_extension (c : Pqxdh.Crypto) (query : Address) (graph : Graph)
    (consistent : Consistent c graph) :
    ValidExtension graph query (tableStep c query graph).1 (tableStep c query graph).2 := by
  refine ⟨?_, consistent_compatible c _ (tableStep_consistent c query graph consistent)⟩
  rcases tableStep_cases c query graph with ⟨answer, found, equality⟩ | ⟨absent, equality⟩
  · simpa only [equality] using Extension.repeat graph query answer found
  · simpa only [equality] using Extension.append graph query (evaluate c query) absent

abbrev Call := (Access × Address) × Answer

inductive Trace : Graph → List Call → Graph → Prop where
  | nil (graph : Graph) : Trace graph [] graph
  | snoc {before after final : Graph} {calls : List Call} (request : Access × Address)
      (answer : Answer) (history : Trace before calls after)
      (step : ValidExtension after request.2 answer final) :
      Trace before (calls ++ [(request, answer)]) final

structure TracedGraph (c : Pqxdh.Crypto) where
  graph : CheckedGraph c
  calls : List Call
  valid : Trace [] calls graph.entries

def initial (c : Pqxdh.Crypto) : TracedGraph c :=
  ⟨empty c, [], Trace.nil []⟩

def tracedStep (c : Pqxdh.Crypto) (request : Access × Address) (state : TracedGraph c) :
    Answer × TracedGraph c :=
  let next := checkedStep c request.2 state.graph
  (next.1, ⟨next.2, state.calls ++ [(request, next.1)],
    Trace.snoc request next.1 state.valid
      (tableStep_extension c request.2 state.graph.entries state.graph.consistent)⟩)

def tracedImpl {State : Type} {ι : Type} {base : OracleSpec ι}
    {m : Type → Type} [Monad m] (c : Pqxdh.Crypto)
    (impl : QueryImpl base (StateT State m)) :
    QueryImpl (Spec base) (StateT (State × TracedGraph c) m)
  | .inl query => fun state => do
    let result ← impl query state.1
    pure (result.1, (result.2, state.2))
  | .inr request => fun state =>
    let next := tracedStep c request state.2
    pure (next.1, (state.1, next.2))

/-- Adding a private chronological event preserves the actual answer. -/
theorem traced_step_reply (c : Pqxdh.Crypto) (request : Access × Address)
    (state : TracedGraph c) : (tracedStep c request state).1 = evaluate c request.2 :=
  tableStep_reply c request.2 state.graph.entries state.graph.consistent

/-- Erasing the KEM call transcript retains the full arbitrary adaptive source computation. -/
theorem traced_execution_erasure {State Result : Type} {ι : Type} {base : OracleSpec ι}
    {m : Type → Type} [Monad m] [LawfulMonad m] (c : Pqxdh.Crypto)
    (impl : QueryImpl base (StateT State m)) (client : OracleComp (Spec base) Result)
    (state : State) (graph : TracedGraph c) :
    (fun result => (result.1, result.2.1)) <$>
      (simulateQ (tracedImpl c impl) client).run (state, graph) =
        (simulateQ (sourceImpl c impl) client).run state := by
  induction client using OracleComp.inductionOn generalizing state graph with
  | pure result => simp
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    simp only [StateT.run] at ih
    cases query with
    | inl query => simp [StateT.run, tracedImpl, sourceImpl, ih]
    | inr request =>
      simp [StateT.run, tracedImpl, sourceImpl, ih, traced_step_reply]

/-- Erasing the transcript and common byte classes retains the same complete source result/state. -/
theorem traced_fields_erasure {State Result : Type} {ι : Type} {base : OracleSpec ι}
    {m : Type → Type} [Monad m] [LawfulMonad m] (c : Pqxdh.Crypto)
    (impl : QueryImpl base (StateT State m)) (client : OracleComp (Spec base) Result)
    (state : State) (graph : TracedGraph c) (classes : List Pqxdh.Bytes) :
    (fun result => (result.1, result.2.1.1)) <$>
      (simulateQ (KemValueClasses.annotatedImpl (tracedImpl c impl) observed) client).run
        ((state, graph), classes) = (simulateQ (sourceImpl c impl) client).run state := by
  have graphErasure := KemValueClasses.annotated_execution (tracedImpl c impl) observed
    client (state, graph) classes
  have erased := congrArg (fun computation =>
    (fun result => (result.1, result.2.1)) <$> computation) graphErasure
  simpa only [Functor.map_map, Function.comp_def] using
    erased.trans (traced_execution_erasure c impl client state graph)

/-- Every supported actual execution internally supplies a valid finite KEM trace with the same full outcome and unique byte representatives. -/
theorem source_supported_trace {State Result : Type} {ι κ : Type}
    {base : OracleSpec ι} {target : OracleSpec κ} (c : Pqxdh.Crypto)
    (impl : QueryImpl base (StateT State (OracleComp target)))
    (client : OracleComp (Spec base) Result) (state : State) (result : Result × State)
    (present : result ∈ support ((simulateQ (sourceImpl c impl) client).run state)) :
    ∃ final : (Result × ((State × TracedGraph c) × List Pqxdh.Bytes)),
      final ∈ support
        ((simulateQ (KemValueClasses.annotatedImpl (tracedImpl c impl) observed) client).run
          ((state, initial c), [])) ∧
      (final.1, final.2.1.1) = result ∧
      Trace [] final.2.1.2.calls final.2.1.2.graph.entries ∧ final.2.2.Nodup := by
  rw [← traced_fields_erasure c impl client state (initial c) []] at present
  rw [support_map, Set.mem_image] at present
  obtain ⟨final, supported, equality⟩ := present
  exact ⟨final, supported, equality, final.2.1.2.valid,
    KemValueClasses.annotated_supported_nodup (tracedImpl c impl) observed client
      (state, initial c) [] (by simp) final supported⟩

/-- Every abstract hit/miss transition appends at most one binding. -/
theorem Extension.length {before after : Graph} {query : Address} {answer : Answer}
    (step : Extension before query answer after) :
    before.length ≤ after.length ∧ after.length ≤ before.length + 1 := by
  cases step <;> simp

/-- A finite abstract trace retains the old prefix length and grows by at most its call count. -/
theorem Trace.length {before after : Graph} {calls : List Call}
    (history : Trace before calls after) :
    before.length ≤ after.length ∧ after.length ≤ before.length + calls.length := by
  induction history with
  | nil => simp
  | snoc request answer history step ih =>
    have growth := step.1.length
    simp only [List.length_append, List.length_singleton]
    omega

/-- All earlier complete bindings survive every later allowed transition. -/
theorem Trace.preserves_lookup {before after : Graph} {calls : List Call}
    (history : Trace before calls after) (query : Address) (answer : Answer)
    (found : before.lookup query = some answer) : after.lookup query = some answer := by
  induction history with
  | nil => exact found
  | snoc request result history step ih =>
    cases step.1
    · exact ih
    · simp [lookup_append, ih]

/-- Logging the actual trace and byte fields preserves every selective underlying-oracle cap. -/
theorem traced_query_bounds {State Result : Type} {ι κ : Type}
    {base : OracleSpec ι} {target : OracleSpec κ} (c : Pqxdh.Crypto)
    (impl : QueryImpl base (StateT State (OracleComp target)))
    (client : OracleComp (Spec base) Result) (state : State)
    (graph : TracedGraph c) (classes : List Pqxdh.Bytes)
    (predicate : target.Domain → Prop) [DecidablePred predicate] (bound : Nat) :
    ((simulateQ (KemValueClasses.annotatedImpl (tracedImpl c impl) observed) client).run
        ((state, graph), classes)).IsQueryBoundP predicate bound ↔
      ((simulateQ (sourceImpl c impl) client).run state).IsQueryBoundP predicate bound := by
  rw [← traced_fields_erasure c impl client state graph classes]
  exact (OracleComp.isQueryBoundP_map_iff _ _ _).symm

end BeaconcryptCore.Computational.KemFunctionalGraph

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.lookup_consistent' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.lookup_consistent

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.tableStep_reply' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.tableStep_reply

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.tableStep_consistent' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.tableStep_consistent

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.lookup_append' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.lookup_append

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.tableStep_preserves' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.tableStep_preserves

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.tableStep_lookup' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.tableStep_lookup

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.tableStep_cases' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.tableStep_cases

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.tableStep_repeat' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.tableStep_repeat

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.tableStep_extends' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.tableStep_extends

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.tableStep_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.tableStep_length

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.same_key_ciphertext' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.same_key_ciphertext

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.decap_before_encap' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.decap_before_encap

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.decap_prior_reply' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.decap_prior_reply

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.public_private_same' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.public_private_same

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.table_step_erasure' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.table_step_erasure

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.table_execution_erasure' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.table_execution_erasure

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.classified_execution_erasure' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.classified_execution_erasure

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.classified_query_bounds' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.classified_query_bounds

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.classified_supported_nodup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.classified_supported_nodup

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.observed_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.observed_length

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.recorded_field' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.recorded_field

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.consistent_matches' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.consistent_matches

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.consistent_decapsulation' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.consistent_decapsulation

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.consistent_ciphertexts' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.consistent_ciphertexts

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.consistent_compatible' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.consistent_compatible

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.tableStep_extension' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.tableStep_extension

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.traced_step_reply' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.traced_step_reply

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.traced_execution_erasure' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.traced_execution_erasure

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.traced_fields_erasure' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.traced_fields_erasure

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.source_supported_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.source_supported_trace

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.Extension.length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.Extension.length

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.Trace.length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.Trace.length

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.Trace.preserves_lookup' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.Trace.preserves_lookup

/--
info: 'BeaconcryptCore.Computational.KemFunctionalGraph.traced_query_bounds' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemFunctionalGraph.traced_query_bounds
