import BeaconcryptCore.Computational.PqxdhJointIdentityEvents

/-!
# Dynamically created joint identities

The source generates a fresh seed only when its public create operation is requested. Service and reveal requests at uncreated indices reject. A bounded eager interpreter may privately sample a pool first, but unused seeds do not enter the protocol state or adversary view. The checked correspondence quantifies over the complete continued evaluated distribution, including all created private seeds and the exact public query/reply trace. Native public-byte lookup and caller-supplied seed policies remain separate adapters.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDynamicIdentityPool

open PqxdhJointIdentity PqxdhJointIdentityFamily

/-- The existing indexed family sampler viewed as the exact source-order seed list. -/
def sampleSeeds (count : ℕ) : ProbComp (List IdentitySeed) :=
  List.ofFn <$> sampleFamily count

@[simp] theorem sampleSeeds_zero : sampleSeeds 0 = pure [] := by
  simp [sampleSeeds, sampleFamily]

/-- List sampling retains the same generator order and adds no placeholder draw. -/
theorem sampleSeeds_succ (count : ℕ) : sampleSeeds (count + 1) = (do
    let seed ← sampleSeed
    let rest ← sampleSeeds count
    pure (seed :: rest)) := by
  simp [sampleSeeds, sampleFamily, map_bind, List.ofFn_succ]

/-- Every sampled pool has exactly the declared number of seeds. -/
theorem sampleSeeds_length (count : ℕ) (seeds : List IdentitySeed)
    (supported : seeds ∈ support (sampleSeeds count)) : seeds.length = count := by
  simp only [sampleSeeds, support_map, Set.mem_image] at supported
  obtain ⟨family, _, rfl⟩ := supported
  simp

inductive PoolQuery where
  | create
  | service (identity : ℕ) (request : JointSpec.Domain)
  | reveal (identity : ℕ)

def PoolRange : PoolQuery → Type
  | .create => Option (ℕ × PublicIdentity)
  | .service _ request => Option (JointSpec.Range request)
  | .reveal _ => Option IdentitySeed

abbrev PoolSpec : OracleSpec PoolQuery := PoolRange
abbrev DynamicSpec := unifSpec + PoolSpec

/-- Every public request and actual reply is retained, including rejected requests and explicit adversary random queries. -/
abbrev Observation := (query : DynamicSpec.Domain) × DynamicSpec.Range query

/-- Only successfully created private seeds belong to the source state; a sampled unused pool remains interpreter-private. -/
structure SourceState where
  seeds : List IdentitySeed
  transcript : List Observation

def initialState : SourceState := ⟨[], []⟩

def record (query : DynamicSpec.Domain) (answer : DynamicSpec.Range query) (state : SourceState) : SourceState :=
  { state with transcript := state.transcript ++ [⟨query, answer⟩] }

/-- The only difference between lazy and eager execution is how the next create seed is supplied. All returned values and state transitions are otherwise shared. -/
def poolImpl (primitives : Primitives) (supply : SourceState → ProbComp (Option IdentitySeed)) :
    QueryImpl DynamicSpec (StateT SourceState ProbComp) := fun query state =>
  match query with
  | .inl coin => do
    let answer ← unifSpec.query coin
    pure (answer, record (.inl coin) answer state)
  | .inr .create => do
    let generated ← supply state
    match generated with
    | none => pure (none, record (.inr .create) none state)
    | some seed =>
      let answer := some (state.seeds.length, primitives.publicKeys seed)
      pure (answer, record (.inr .create) answer { state with seeds := state.seeds ++ [seed] })
  | .inr (.service identity request) =>
    let answer := (state.seeds[identity]?).map fun seed => primitiveReply primitives seed request
    pure (answer, record (.inr (.service identity request)) answer state)
  | .inr (.reveal identity) =>
    let answer := state.seeds[identity]?
    pure (answer, record (.inr (.reveal identity)) answer state)

/-- The source samples exactly one actual seed per create call under the ordinary successful honest key-generation contract. -/
def lazyImpl (primitives : Primitives) : QueryImpl DynamicSpec (StateT SourceState ProbComp) :=
  poolImpl primitives (fun _ => some <$> sampleSeed)

/-- The eager interpreter's pool is not an argument to the adversary or a field of its source state. Exhaustion returns none; the bounded correspondence must prove that branch unreachable. -/
def eagerImpl (primitives : Primitives) (pool : List IdentitySeed) :
    QueryImpl DynamicSpec (StateT SourceState ProbComp) :=
  poolImpl primitives (fun state => pure (pool[state.seeds.length]?))

/-- Creation is a separately counted source query class. -/
def IsCreate : DynamicSpec.Domain → Prop
  | .inr .create => True
  | _ => False

instance : DecidablePred IsCreate := fun query => by
  cases query with
  | inl _ => exact inferInstanceAs (Decidable False)
  | inr request => cases request <;> simp only [IsCreate] <;> infer_instance

/-- Unused future seeds can be integrated out only because the ordinary seed sampler never fails. This equality includes the whole subsequent evaluated computation. -/
theorem sampleSeeds_unused {Result : Type} (count : ℕ) (work : ProbComp Result) :
    𝒮[sampleSeeds count >>= fun _ => work] = 𝒮[work] := by
  apply evalSPMF_ext
  intro result
  simp only [probOutput_bind_const, probFailure_eq_zero, tsub_zero, one_mul]

/-- Every create result publishes the next generated index and retains exactly that new private seed. -/
def createdReply (primitives : Primitives) (state : SourceState) (seed : IdentitySeed) :
    DynamicSpec.Range (.inr .create) × SourceState :=
  let answer := some (state.seeds.length, primitives.publicKeys seed)
  (answer, record (.inr .create) answer { state with seeds := state.seeds ++ [seed] })

/-- Lazy creation preserves the actual draw-before-publication order. -/
theorem lazyImpl_create (primitives : Primitives) (state : SourceState) :
    (lazyImpl primitives (.inr .create)).run state =
      (createdReply primitives state) <$> sampleSeed := by
  simp only [lazyImpl, poolImpl, StateT.run, bind_map_left, bind_pure_comp]
  rfl

/-- A nonempty reserved suffix supplies exactly the next seed at creation; no unused future seed is exposed. -/
theorem eagerImpl_create (primitives : Primitives) (state : SourceState)
    (seed : IdentitySeed) (future : List IdentitySeed) :
    (eagerImpl primitives (state.seeds ++ seed :: future) (.inr .create)).run state =
      pure (createdReply primitives state seed) := by
  simp [eagerImpl, poolImpl, StateT.run, createdReply]

/-- Non-creation services depend only on already created source state, never on the reserved seed pool. -/
theorem noncreate_step_eq (primitives : Primitives) (pool : List IdentitySeed)
    (query : DynamicSpec.Domain) (notCreate : ¬ IsCreate query) (state : SourceState) :
    (lazyImpl primitives query).run state = (eagerImpl primitives pool query).run state := by
  cases query with
  | inl coin => rfl
  | inr request =>
    cases request with
    | create => exact False.elim (notCreate trivial)
    | service identity request => rfl
    | reveal identity => rfl

/-- Every non-creation request retains the complete private seed prefix, even when it reveals a created seed or rejects an uncreated index. -/
theorem noncreate_seeds_preserved (primitives : Primitives) (query : DynamicSpec.Domain)
    (notCreate : ¬ IsCreate query) (state : SourceState)
    (result : DynamicSpec.Range query × SourceState)
    (supported : result ∈ support ((lazyImpl primitives query).run state)) :
    result.2.seeds = state.seeds := by
  cases query with
  | inl coin =>
    simp only [lazyImpl, poolImpl, StateT.run, mem_support_bind_iff] at supported
    obtain ⟨answer, _, supported⟩ := supported
    simp only [mem_support_pure_iff] at supported
    subst result
    rfl
  | inr request =>
    cases request with
    | create => exact False.elim (notCreate trivial)
    | service identity request =>
      simp only [lazyImpl, poolImpl, StateT.run, mem_support_pure_iff] at supported
      subst result
      rfl
    | reveal identity =>
      simp only [lazyImpl, poolImpl, StateT.run, mem_support_pure_iff] at supported
      subst result
      rfl

/-- Private eager reservation and actual on-demand creation have identical complete evaluated executions. The result includes every created secret seed and every public reply; the unused pool is confined to the interpreter. -/
theorem lazy_eager_complete (primitives : Primitives) {Result : Type}
    (client : OracleComp DynamicSpec Result) (count : ℕ)
    (bounded : client.IsQueryBoundP IsCreate count) (state : SourceState) :
    𝒮[(simulateQ (lazyImpl primitives) client).run state] =
      𝒮[sampleSeeds count >>= fun future =>
        (simulateQ (eagerImpl primitives (state.seeds ++ future)) client).run state] := by
  induction client using OracleComp.inductionOn generalizing count state with
  | pure value =>
    simpa only [simulateQ_pure, StateT.run_pure] using
      (sampleSeeds_unused count (pure (value, state))).symm
  | query_bind query next ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
    change 𝒮[(lazyImpl primitives query).run state >>= fun result =>
      (simulateQ (lazyImpl primitives) (next result.1)).run result.2] =
      𝒮[sampleSeeds count >>= fun future =>
        (eagerImpl primitives (state.seeds ++ future) query).run state >>= fun result =>
          (simulateQ (eagerImpl primitives (state.seeds ++ future)) (next result.1)).run result.2]
    by_cases creates : IsCreate query
    · have queryEq : query = .inr .create := by
        cases query with
        | inl coin => exact False.elim creates
        | inr request => cases request <;> simp_all [IsCreate]
      subst query
      have positive : 0 < count := bounded.1.resolve_left (not_not.mpr creates)
      cases count with
      | zero => omega
      | succ count =>
        rw [lazyImpl_create, sampleSeeds_succ]
        simp only [bind_assoc]
        simp only [bind_map_left, pure_bind]
        apply evalSPMF_bind_congr' sampleSeed
        intro seed
        simp only [eagerImpl_create, pure_bind]
        simpa only [createdReply, record, List.append_assoc, List.singleton_append] using
          ih (createdReply primitives state seed).1 count
            (by simpa [IsCreate] using bounded.2 (createdReply primitives state seed).1)
            (createdReply primitives state seed).2
    · have stepEq (future : List IdentitySeed) :=
        noncreate_step_eq primitives (state.seeds ++ future) query creates state
      simp_rw [← stepEq]
      rw [PqxdhSecretInputKdf.evalSPMF_sample_comm (sampleSeeds count)
        ((lazyImpl primitives query).run state)]
      apply evalSPMF_bind_congr
      intro result supported
      have sameSeeds := noncreate_seeds_preserved primitives query creates state result supported
      simpa only [sameSeeds] using
        ih result.1 count (by simpa [creates] using bounded.2 result.1) result.2

/-- Explicit adversary uniform-oracle queries, separately from private seed generation. -/
def IsUniform : DynamicSpec.Domain → Prop
  | .inl _ => True
  | .inr _ => False

instance : DecidablePred IsUniform := fun query => by
  cases query <;> simp only [IsUniform] <;> infer_instance

/-- Each reserved seed costs the same 32 byte-valued uniform queries as source creation. -/
theorem sampleSeeds_uniform_bound (count : ℕ) :
    (sampleSeeds count).IsTotalQueryBound (32 * count) := by
  simpa only [sampleSeeds, OracleComp.IsTotalQueryBound, OracleComp.isQueryBound_map_iff] using sampleFamily_uniform_bound count

/-- Actual creation draws 32 bytes; an explicit source uniform query costs one; deterministic services and reveals make no further oracle query. -/
theorem lazyImpl_uniform_step (primitives : Primitives) (query : DynamicSpec.Domain)
    (state : SourceState) :
    ((lazyImpl primitives query).run state).IsTotalQueryBound
      ((if IsCreate query then 32 else 0) + (if IsUniform query then 1 else 0)) := by
  cases query with
  | inl coin =>
    change OracleComp.IsTotalQueryBound
      ((fun (answer : unifSpec.Range coin) => (answer, record (.inl coin) answer state)) <$>
        (unifSpec.query coin : ProbComp _)) 1
    simpa only [OracleComp.IsTotalQueryBound, OracleComp.isQueryBound_map_iff] using
      ((OracleComp.isQueryBoundP_true_iff _ _).mp
        ((OracleComp.isQueryBoundP_query_iff (spec := unifSpec) (p := fun _ => True) coin 1).mpr (by simp)))
  | inr request =>
    cases request with
    | create =>
      rw [ite_eq_left (show IsCreate (.inr .create) from trivial),
        ite_eq_right (show ¬IsUniform (.inr .create) from by trivial), Nat.add_zero]
      rw [lazyImpl_create]
      simpa only [OracleComp.IsTotalQueryBound, OracleComp.isQueryBound_map_iff] using
        sampleSeed_uniform_bound
    | service identity request => trivial
    | reveal identity => trivial

/-- The eager interpreter makes only forwarded adversary uniform queries after its private reservation. -/
theorem eagerImpl_uniform_step (primitives : Primitives) (pool : List IdentitySeed)
    (query : DynamicSpec.Domain) (state : SourceState) :
    ((eagerImpl primitives pool query).run state).IsQueryBoundP (fun _ => True)
      (if IsUniform query then 1 else 0) := by
  cases query with
  | inl coin =>
    change OracleComp.IsQueryBoundP
      ((fun (answer : unifSpec.Range coin) => (answer, record (.inl coin) answer state)) <$>
        (unifSpec.query coin : ProbComp _)) (fun _ => True) 1
    simp only [OracleComp.isQueryBoundP_map_iff]
    exact (OracleComp.isQueryBoundP_query_iff (spec := unifSpec) (p := fun _ => True) coin 1).mpr (by simp)
  | inr request =>
    cases request with
    | create =>
      simp only [eagerImpl, poolImpl, StateT.run, pure_bind]
      cases pool[state.seeds.length]? <;> trivial
    | service identity request => trivial
    | reveal identity => trivial

/-- The actual interpreted source pays 32 byte draws per permitted creation and every explicit uniform request. -/
theorem lazyRun_uniform_bound (primitives : Primitives) {Result : Type}
    (client : OracleComp DynamicSpec Result) (qCreate qUniform : ℕ)
    (creates : client.IsQueryBoundP IsCreate qCreate)
    (coins : client.IsQueryBoundP IsUniform qUniform) (state : SourceState) :
    ((simulateQ (lazyImpl primitives) client).run state).IsTotalQueryBound (32 * qCreate + qUniform) := by
  induction client using OracleComp.inductionOn generalizing qCreate qUniform state with
  | pure value => trivial
  | query_bind query next ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at creates coins
    change ((lazyImpl primitives query).run state >>= fun result =>
      (simulateQ (lazyImpl primitives) (next result.1)).run result.2).IsTotalQueryBound _
    have accounted := OracleComp.isTotalQueryBound_bind (lazyImpl_uniform_step primitives query state)
      (fun result => ih result.1 _ _ (creates.2 result.1) (coins.2 result.1) result.2)
    apply accounted.mono
    have createPositive : IsCreate query → 0 < qCreate := fun h => creates.1.resolve_left (not_not.mpr h)
    have uniformPositive : IsUniform query → 0 < qUniform := fun h => coins.1.resolve_left (not_not.mpr h)
    by_cases hc : IsCreate query <;> by_cases hu : IsUniform query <;>
      simp [hc, hu] at createPositive uniformPositive ⊢ <;> omega

/-- After reservation, the complete eager continuation forwards exactly the source uniform-query budget. -/
theorem eagerRun_uniform_bound (primitives : Primitives) (pool : List IdentitySeed)
    {Result : Type} (client : OracleComp DynamicSpec Result) (qUniform : ℕ)
    (coins : client.IsQueryBoundP IsUniform qUniform) (state : SourceState) :
    ((simulateQ (eagerImpl primitives pool) client).run state).IsTotalQueryBound qUniform := by
  exact (OracleComp.isQueryBoundP_true_iff _ _).mp
    (coins.simulateQ_run_StateT_of_step (eagerImpl_uniform_step primitives pool) state)

/-- The complete reserved execution charges every future seed, including seeds unused after adaptive stopping. -/
theorem eagerReserved_uniform_bound (primitives : Primitives) {Result : Type}
    (client : OracleComp DynamicSpec Result) (count qUniform : ℕ)
    (coins : client.IsQueryBoundP IsUniform qUniform) (state : SourceState) :
    (sampleSeeds count >>= fun future =>
      (simulateQ (eagerImpl primitives (state.seeds ++ future)) client).run state).IsTotalQueryBound
        (32 * count + qUniform) := by
  exact OracleComp.isTotalQueryBound_bind (sampleSeeds_uniform_bound count)
    (fun future => eagerRun_uniform_bound primitives _ client qUniform coins state)

/-- Count any declared source query class in the actual complete public trace. Invalid indices and repeated reveals are counted too. -/
def traceCount (predicate : DynamicSpec.Domain → Prop) [DecidablePred predicate]
    (state : SourceState) : ℕ :=
  state.transcript.countP (fun observation => decide (predicate observation.1))

theorem record_traceCount (predicate : DynamicSpec.Domain → Prop) [DecidablePred predicate]
    (query : DynamicSpec.Domain) (answer : DynamicSpec.Range query) (state : SourceState) :
    traceCount predicate (record query answer state) =
      traceCount predicate state + if predicate query then 1 else 0 := by
  simp [traceCount, record, List.countP_append]

/-- One source step appends its exact actual reply, including an optional rejection, with no loss of the prior trace. -/
theorem lazyImpl_transcript (primitives : Primitives) (query : DynamicSpec.Domain)
    (state : SourceState) (result : DynamicSpec.Range query × SourceState)
    (supported : result ∈ support ((lazyImpl primitives query).run state)) :
    result.2.transcript = state.transcript ++ [⟨query, result.1⟩] := by
  cases query with
  | inl coin =>
    simp only [lazyImpl, poolImpl, StateT.run, mem_support_bind_iff] at supported
    obtain ⟨answer, _, supported⟩ := supported
    obtain rfl := eq_of_mem_support_pure supported
    rfl
  | inr request =>
    cases request with
    | create =>
      rw [lazyImpl_create, support_map] at supported
      obtain ⟨seed, _, rfl⟩ := supported
      rfl
    | service identity request =>
      change result ∈ support (pure _) at supported
      obtain rfl := eq_of_mem_support_pure supported
      rfl
    | reveal identity =>
      change result ∈ support (pure _) at supported
      obtain rfl := eq_of_mem_support_pure supported
      rfl

/-- The trace charges exactly one attempted source request in its declared class. -/
theorem lazyImpl_trace_count (primitives : Primitives)
    (predicate : DynamicSpec.Domain → Prop) [DecidablePred predicate]
    (query : DynamicSpec.Domain) (state : SourceState) (result : DynamicSpec.Range query × SourceState)
    (supported : result ∈ support ((lazyImpl primitives query).run state)) :
    traceCount predicate result.2 = traceCount predicate state + if predicate query then 1 else 0 := by
  simpa only [traceCount, record, lazyImpl_transcript primitives query state result supported] using
    record_traceCount predicate query result.1 state

/-- Every adaptive source query class obeys its own cap, including rejected service indices and repeated actual seed reveals. -/
theorem lazyRun_trace_bound (primitives : Primitives)
    (predicate : DynamicSpec.Domain → Prop) [DecidablePred predicate]
    {Result : Type} (client : OracleComp DynamicSpec Result) (bound : ℕ)
    (bounded : client.IsQueryBoundP predicate bound) (state : SourceState)
    (result : Result × SourceState)
    (supported : result ∈ support ((simulateQ (lazyImpl primitives) client).run state)) :
    traceCount predicate result.2 ≤ traceCount predicate state + bound := by
  induction client using OracleComp.inductionOn generalizing bound state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact Nat.le_add_right _ _
  | query_bind query next ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
    change result ∈ support ((lazyImpl primitives query).run state >>= fun reply =>
      (simulateQ (lazyImpl primitives) (next reply.1)).run reply.2) at supported
    obtain ⟨reply, step, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
    have stepCount := lazyImpl_trace_count primitives predicate query state reply step
    have remaining := ih reply.1 _ (bounded.2 reply.1) reply.2 result supported
    by_cases selected : predicate query
    · have positive : 0 < bound := bounded.1.resolve_left (not_not.mpr selected)
      simp only [selected, ite_true] at stepCount remaining
      omega
    · simp only [selected, ite_false] at stepCount remaining
      omega

/-- Exactly one new private seed is appended by creation; every other source request retains the prefix. This asserts fresh indices, not distinct seed or public-key bytes. -/
theorem lazyImpl_seed_extension (primitives : Primitives) (query : DynamicSpec.Domain)
    (state : SourceState) (result : DynamicSpec.Range query × SourceState)
    (supported : result ∈ support ((lazyImpl primitives query).run state)) :
    ∃ appended, result.2.seeds = state.seeds ++ appended ∧
      appended.length = if IsCreate query then 1 else 0 := by
  by_cases creates : IsCreate query
  · have queryEq : query = .inr .create := by
      cases query with
      | inl coin => exact False.elim creates
      | inr request => cases request <;> simp_all [IsCreate]
    subst query
    rw [lazyImpl_create, support_map] at supported
    obtain ⟨seed, _, rfl⟩ := supported
    exact ⟨[seed], rfl, rfl⟩
  · exact ⟨[], by simpa using noncreate_seeds_preserved primitives query creates state result supported,
      by simp [creates]⟩

/-- Dynamically generated identities have an append-only private prefix and at most the stated number of new indices, even across arbitrary service/reveal scheduling and adaptive stopping. -/
theorem lazyRun_seed_extension (primitives : Primitives) {Result : Type}
    (client : OracleComp DynamicSpec Result) (qCreate : ℕ)
    (creates : client.IsQueryBoundP IsCreate qCreate) (state : SourceState)
    (result : Result × SourceState)
    (supported : result ∈ support ((simulateQ (lazyImpl primitives) client).run state)) :
    ∃ appended, result.2.seeds = state.seeds ++ appended ∧ appended.length ≤ qCreate := by
  induction client using OracleComp.inductionOn generalizing qCreate state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact ⟨[], by simp, Nat.zero_le _⟩
  | query_bind query next ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at creates
    change result ∈ support ((lazyImpl primitives query).run state >>= fun reply =>
      (simulateQ (lazyImpl primitives) (next reply.1)).run reply.2) at supported
    obtain ⟨reply, step, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
    obtain ⟨first, hfirst, firstCount⟩ := lazyImpl_seed_extension primitives query state reply step
    obtain ⟨later, hlater, laterCount⟩ := ih reply.1 _ (creates.2 reply.1) reply.2 result supported
    refine ⟨first ++ later, by rw [hlater, hfirst, List.append_assoc], ?_⟩
    rw [List.length_append, firstCount]
    by_cases selected : IsCreate query
    · have positive : 0 < qCreate := creates.1.resolve_left (not_not.mpr selected)
      simp only [selected, ite_true] at laterCount ⊢
      omega
    · simpa only [selected, ite_false, Nat.zero_add] using laterCount

end BeaconcryptCore.Computational.PqxdhDynamicIdentityPool

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.sampleSeeds_succ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.sampleSeeds_succ

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.lazy_eager_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.lazy_eager_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.lazyImpl_uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.lazyImpl_uniform_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.lazyRun_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.lazyRun_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.eagerReserved_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.eagerReserved_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.lazyImpl_transcript' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.lazyImpl_transcript

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.lazyRun_trace_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.lazyRun_trace_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.lazyImpl_seed_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.lazyImpl_seed_extension

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.lazyRun_seed_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.lazyRun_seed_extension
