import BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily
import VCVio.ProgramLogic.Relational.SimulateQ.Epsilon

/-!
# Splitting a random-oracle table at a hidden uniform suffix (item 2, stage S1a, lemma G1)

This module is generic and contains no protocol code. It concerns one lazily sampled random-oracle table on byte strings, the restricted zero-key 192-byte HMAC-SHA-512 Extract slice of route R1, read in two ways by a client:

- a hidden read at 128-byte coordinates `m` reads the table at `familyInput m secret = padFF32 ‖ m ‖ secret`, where `secret` is a uniform 32-byte value that the client never sees;
- a direct read at a byte string `x` reads the table at `x`.

In the shared world (`sharedGame`) a prefix computation first produces the table's initial cache and the client's context, then `secret` is drawn uniformly, and all reads go to the one table: this is the exact joint sampler, with one secret shared by all hidden reads and one table shared by hidden and direct reads. In the split world (`splitGame`) hidden reads go to a separate lazily sampled table keyed by the coordinates (`ExtractOracle.randomOracle`), direct reads go to the public table, and no secret is drawn.

The main theorem `hidden_suffix_bound` says that the two worlds are distinguishable with advantage at most `Q / 2^256`, where `Q` bounds, for every outcome `p` of the prefix, the number of keys of the prefix cache (covered by the finite set `keys p`) plus the number of direct reads of the client after the prefix (`residual p`). The budget depends on the prefix outcome, so prefix cache keys and post-prefix direct reads share one cap; this gives coefficient one.

The step is valid only because the slice is modelled as a random oracle: it is the one step of the item 2 hybrid after which table entries at distinct coordinates are independent. Without that idealization it would be a forbidden decorrelation. The secret never enters any public context: in the split world it is drawn by nothing, and in the proof it is used only by the deferred guessing test.

Proof outline (route (a) of the plan):

1. Common state (`Tables`): a public cache, a hidden cache keyed by coordinates, and a log of direct reads. `sharedFlag secret` answers a direct read at `familyInput m secret` from the hidden cache; `view` projects the common state onto the one table, and `shared_project` shows that the shared world is that projection whenever the prefix cache has no key of that shape (otherwise the outcome is an initial collision, charged through `keys`).
2. Identical until bad: `splitFlag secret` and `sharedFlag secret` agree on every transition that does not read a direct point of the shape `familyInput m secret`; both set a monotone flag on such a read. VCVio's `tvDist_simulateQ_run_le_probEvent_output_bad` bounds the distance by the flag probability in the split world.
3. Pure observer: the split world does not use the secret; the flag is a function of the direct-read log (`flag_log`), and the logged split run `splitLog` is secret-free (`splitFlag_log`).
4. Union bound: for a fixed prefix outcome and a fixed log, a uniform secret makes one of at most `(keys p).card + log.length` byte strings have the hidden shape with probability at most that number over `2^256` (`guess_finset_le`); the log has at most `residual p` entries (`splitLog_length`).
5. The bound passes from total variation to the Boolean advantage.
-/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix

open PqxdhSecretInputKdf PqxdhKemIndCca PqxdhCorrelatedExtractFamily

/-- Direct reads of the zero-key 192-byte slice, keyed by the full byte string. -/
abbrev TableOracle := Pqxdh.Bytes →ₒ HmacBlock

/-- The client's oracles: uniform coins, hidden reads at 128-byte coordinates, and direct reads. -/
abbrev HiddenSpec := unifSpec + (ExtractOracle + TableOracle)

/-- A direct read of the table. -/
def IsDirect : HiddenSpec.Domain → Prop
  | .inr (.inr _) => True
  | _ => False

instance : DecidablePred IsDirect
  | .inl _ => inferInstanceAs (Decidable False)
  | .inr (.inl _) => inferInstanceAs (Decidable False)
  | .inr (.inr _) => inferInstanceAs (Decidable True)

/-- Shared world: one table; a hidden read at `m` reads it at `familyInput m secret`, a direct read at `x` reads it at `x`. -/
noncomputable def sharedImpl (secret : MlKemSharedSecret) :
    QueryImpl HiddenSpec (StateT HmacOracle.QueryCache ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT HmacOracle.QueryCache ProbComp) +
    ((fun message => HmacOracle.randomOracle (familyInput message secret) :
        QueryImpl ExtractOracle (StateT HmacOracle.QueryCache ProbComp)) +
      (HmacOracle.randomOracle : QueryImpl TableOracle (StateT HmacOracle.QueryCache ProbComp)))

/-- Split world: hidden reads go to a separate coordinate-keyed table, direct reads to the public table. -/
noncomputable def splitImpl :
    QueryImpl HiddenSpec (StateT (HmacOracle.QueryCache × ExtractOracle.QueryCache) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (HmacOracle.QueryCache × ExtractOracle.QueryCache) ProbComp) +
    ((fun message => StateT.mk fun state =>
        (fun result => (result.1, (state.1, result.2))) <$> (ExtractOracle.randomOracle message).run state.2 :
        QueryImpl ExtractOracle (StateT (HmacOracle.QueryCache × ExtractOracle.QueryCache) ProbComp)) +
      (fun point => StateT.mk fun state =>
        (fun result => (result.1, (result.2, state.2))) <$> (HmacOracle.randomOracle point).run state.1 :
        QueryImpl TableOracle (StateT (HmacOracle.QueryCache × ExtractOracle.QueryCache) ProbComp)))

/-- The shared world after a prefix that produces the initial table and the client's context; the secret is drawn after the prefix. -/
noncomputable def sharedGame {C : Type} (start : ProbComp (HmacOracle.QueryCache × C))
    (client : C → OracleComp HiddenSpec Bool) : ProbComp Bool := do
  let p ← start
  let secret ← $ᵗ MlKemSharedSecret
  (simulateQ (sharedImpl secret) (client p.2)).run' p.1

/-- The split world after the same prefix; the hidden table starts empty and no secret is drawn. -/
noncomputable def splitGame {C : Type} (start : ProbComp (HmacOracle.QueryCache × C))
    (client : C → OracleComp HiddenSpec Bool) : ProbComp Bool := do
  let p ← start
  (simulateQ splitImpl (client p.2)).run' (p.1, ∅)

/-! ### The hidden shape -/

/-- The coordinates of a byte string of the shape `familyInput m secret`, if it has that shape. -/
def coordinate (secret : MlKemSharedSecret) (point : Pqxdh.Bytes) : Option Message :=
  if shape : point.length = 192 ∧ point.take 32 = Pqxdh.padFF32 ∧ point.drop 160 = secret.toList then
    some ⟨(point.drop 32).take 128, by simp [shape.1]⟩
  else none

theorem coordinate_familyInput (secret : MlKemSharedSecret) (message : Message) :
    coordinate secret (familyInput message secret) = some message := by
  have pad : Pqxdh.padFF32.length = 32 := Pqxdh.padFF32_length
  have front : (Pqxdh.padFF32 ++ message.toList).length = 160 := by simp [pad]
  have shape : (Pqxdh.padFF32 ++ message.toList ++ secret.toList).length = 192 ∧
      (Pqxdh.padFF32 ++ message.toList ++ secret.toList).take 32 = Pqxdh.padFF32 ∧
      (Pqxdh.padFF32 ++ message.toList ++ secret.toList).drop 160 = secret.toList :=
    ⟨by simp [pad], by simp [pad, List.append_assoc], List.drop_left' front⟩
  unfold coordinate familyInput
  rw [dite_eq_left_of_eq_true (eq_true shape)]
  congr 1
  apply List.Vector.toList_injective
  simp [List.append_assoc, List.drop_left' pad, List.take_left']

theorem eq_familyInput_of_coordinate {secret : MlKemSharedSecret} {point : Pqxdh.Bytes}
    {message : Message} (same : coordinate secret point = some message) :
    point = familyInput message secret := by
  unfold coordinate at same
  split at same
  · rename_i shape
    obtain ⟨length, front, back⟩ := shape
    cases same
    unfold familyInput
    simp only [List.Vector.toList_mk]
    rw [← front, ← back]
    conv_lhs => rw [← List.take_append_drop 32 point, ← List.take_append_drop 128 (point.drop 32)]
    simp [List.drop_drop, List.append_assoc]
  · cases same

theorem secret_of_coordinate {secret : MlKemSharedSecret} {point : Pqxdh.Bytes}
    (shaped : (coordinate secret point).isSome) : secret.toList = point.drop 160 := by
  unfold coordinate at shaped
  split at shaped
  · rename_i shape
    exact shape.2.2.symm
  · simp at shaped

/-! ### Guessing the suffix -/

theorem secret_card : Fintype.card MlKemSharedSecret = 2 ^ 256 := by
  rw [card_vector]
  have byte : Fintype.card UInt8 = 256 := by
    set_option maxRecDepth 100000 in
      rfl
  rw [byte]
  norm_num

set_option linter.deprecated false in
/-- A fixed byte string has the hidden shape for a uniform secret with probability at most `2^-256`. -/
theorem guess_le (point : Pqxdh.Bytes) :
    Pr[fun secret => (coordinate secret point).isSome | $ᵗ MlKemSharedSecret] ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  by_cases exists_secret : ∃ candidate : MlKemSharedSecret, (coordinate candidate point).isSome
  · obtain ⟨candidate, shaped⟩ := exists_secret
    calc Pr[fun secret => (coordinate secret point).isSome | $ᵗ MlKemSharedSecret]
        ≤ Pr[fun secret => secret = candidate | $ᵗ MlKemSharedSecret] := by
          refine probEvent_mono fun secret _ hit => ?_
          apply List.Vector.toList_injective
          rw [secret_of_coordinate hit, secret_of_coordinate shaped]
      _ = (2 ^ 256 : ℝ≥0∞)⁻¹ := by
          rw [probEvent_eq_eq_probOutput, probOutput_uniformSample, secret_card]
          norm_num
  · push Not at exists_secret
    calc Pr[fun secret => (coordinate secret point).isSome | $ᵗ MlKemSharedSecret] = 0 := by
          rw [probEvent_eq_zero_iff]
          intro secret _
          simpa using exists_secret secret
      _ ≤ _ := zero_le

set_option linter.deprecated false in
/-- Union bound: some string of a finite set has the hidden shape for a uniform secret with probability at most its size over `2^256`. -/
theorem guess_finset_le (points : Finset Pqxdh.Bytes) :
    Pr[fun secret => ∃ point ∈ points, (coordinate secret point).isSome | $ᵗ MlKemSharedSecret] ≤
      points.card * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  refine (probEvent_exists_finset_le_sum points ($ᵗ MlKemSharedSecret)
    (fun point secret => (coordinate secret point).isSome)).trans ?_
  calc ∑ point ∈ points, Pr[fun secret => (coordinate secret point).isSome | $ᵗ MlKemSharedSecret]
      ≤ ∑ _point ∈ points, (2 ^ 256 : ℝ≥0∞)⁻¹ := Finset.sum_le_sum fun point _ => guess_le point
    _ = points.card * (2 ^ 256 : ℝ≥0∞)⁻¹ := by simp [Finset.sum_const, nsmul_eq_mul]

/-! ### The common state -/

/-- The public cache, the hidden cache keyed by coordinates, and the log of direct reads. -/
structure Tables where
  pub : HmacOracle.QueryCache
  hid : ExtractOracle.QueryCache
  log : List Pqxdh.Bytes

/-- A lazily sampled read of the hidden cache. -/
noncomputable def readHidden (message : Message) (tables : Tables) : ProbComp (HmacBlock × Tables) :=
  match tables.hid message with
  | some answer => pure (answer, tables)
  | none => do
      let answer ← $ᵗ HmacBlock
      pure (answer, { tables with hid := tables.hid.cacheQuery message answer })

/-- A lazily sampled read of the public cache. -/
noncomputable def readPublic (point : Pqxdh.Bytes) (tables : Tables) : ProbComp (HmacBlock × Tables) :=
  match tables.pub point with
  | some answer => pure (answer, tables)
  | none => do
      let answer ← $ᵗ HmacBlock
      pure (answer, { tables with pub := tables.pub.cacheQuery point answer })

/-- Append a direct read to the log. -/
def logged (point : Pqxdh.Bytes) (tables : Tables) : Tables :=
  { tables with log := tables.log ++ [point] }

/-- The split world with a log of direct reads; it does not depend on any secret. -/
noncomputable def splitLog : QueryImpl HiddenSpec (StateT Tables ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT Tables ProbComp) +
    ((fun message => StateT.mk (readHidden message) : QueryImpl ExtractOracle (StateT Tables ProbComp)) +
      (fun point => StateT.mk fun tables =>
        (fun result => (result.1, logged point result.2)) <$> readPublic point tables :
        QueryImpl TableOracle (StateT Tables ProbComp)))

/-- The flagged split world: the flag records a direct read of the hidden shape. -/
noncomputable def splitFlag (secret : MlKemSharedSecret) :
    QueryImpl HiddenSpec (StateT (Tables × Bool) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (Tables × Bool) ProbComp) +
    ((fun message => StateT.mk fun state =>
        (fun result => (result.1, (result.2, state.2))) <$> readHidden message state.1 :
        QueryImpl ExtractOracle (StateT (Tables × Bool) ProbComp)) +
      (fun point => StateT.mk fun state =>
        (fun result => (result.1, (logged point result.2,
          state.2 || (coordinate secret point).isSome))) <$> readPublic point state.1 :
        QueryImpl TableOracle (StateT (Tables × Bool) ProbComp)))

/-- The flagged shared world on the common state: a direct read of the hidden shape reads the hidden cache and sets the flag. -/
noncomputable def sharedFlag (secret : MlKemSharedSecret) :
    QueryImpl HiddenSpec (StateT (Tables × Bool) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (Tables × Bool) ProbComp) +
    ((fun message => StateT.mk fun state =>
        (fun result => (result.1, (result.2, state.2))) <$> readHidden message state.1 :
        QueryImpl ExtractOracle (StateT (Tables × Bool) ProbComp)) +
      (fun point => StateT.mk fun state => match coordinate secret point with
        | some message =>
            (fun result => (result.1, (logged point result.2, true))) <$> readHidden message state.1
        | none =>
            (fun result => (result.1, (logged point result.2, state.2))) <$> readPublic point state.1 :
        QueryImpl TableOracle (StateT (Tables × Bool) ProbComp)))

/-- The one table seen through the common state. -/
def view (secret : MlKemSharedSecret) (tables : Tables) : HmacOracle.QueryCache :=
  fun point => match coordinate secret point with
    | some message => tables.hid message
    | none => tables.pub point

theorem view_familyInput (secret : MlKemSharedSecret) (tables : Tables) (message : Message) :
    view secret tables (familyInput message secret) = tables.hid message := by
  simp [view, coordinate_familyInput]

theorem view_public (secret : MlKemSharedSecret) (tables : Tables) (point : Pqxdh.Bytes)
    (plain : coordinate secret point = none) : view secret tables point = tables.pub point := by
  simp [view, plain]

@[simp]
theorem view_logged (secret : MlKemSharedSecret) (tables : Tables) (point : Pqxdh.Bytes) :
    view secret (logged point tables) = view secret tables := rfl

theorem view_hidden_update (secret : MlKemSharedSecret) (tables : Tables) (message : Message)
    (answer : HmacBlock) :
    view secret { tables with hid := tables.hid.cacheQuery message answer } =
      (view secret tables).cacheQuery (familyInput message secret) answer := by
  funext point
  cases shape : coordinate secret point with
  | none =>
      have distinct : point ≠ familyInput message secret := by
        rintro rfl
        simp [coordinate_familyInput] at shape
      simp [view, shape, QueryCache.cacheQuery_of_ne _ _ distinct]
  | some other =>
      obtain rfl := eq_familyInput_of_coordinate shape
      by_cases same : other = message
      · subst same
        simp [view, coordinate_familyInput]
      · have distinct : familyInput other secret ≠ familyInput message secret := by
          intro equal
          have := congrArg (coordinate secret) equal
          simp [coordinate_familyInput] at this
          exact same this
        simp [view, coordinate_familyInput, QueryCache.cacheQuery_of_ne _ _ distinct,
          QueryCache.cacheQuery_of_ne _ _ same]

theorem view_public_update (secret : MlKemSharedSecret) (tables : Tables) (point : Pqxdh.Bytes)
    (plain : coordinate secret point = none) (answer : HmacBlock) :
    view secret { tables with pub := tables.pub.cacheQuery point answer } =
      (view secret tables).cacheQuery point answer := by
  funext other
  cases shape : coordinate secret other with
  | none =>
      by_cases same : other = point
      · subst same
        simp [view, shape]
      · simp [view, shape, QueryCache.cacheQuery_of_ne _ _ same]
  | some message =>
      have distinct : other ≠ point := by
        rintro rfl
        simp [plain] at shape
      simp [view, shape, QueryCache.cacheQuery_of_ne _ _ distinct]

/-! ### Projections -/

/-- Every step of the flagged shared world projects through `view` onto a step of the shared world. -/
theorem sharedFlag_step (secret : MlKemSharedSecret) (query : HiddenSpec.Domain) (state : Tables × Bool) :
    Prod.map id (fun state : Tables × Bool => view secret state.1) <$> (sharedFlag secret query).run state =
      (sharedImpl secret query).run (view secret state.1) := by
  obtain ⟨tables, flag⟩ := state
  rcases query with coin | message | point
  · simp [sharedFlag, sharedImpl]
  · cases hit : tables.hid message with
    | some answer =>
        simp [sharedFlag, sharedImpl, readHidden, hit, view_familyInput]
    | none =>
        simp [sharedFlag, sharedImpl, readHidden, hit, view_familyInput,
          view_hidden_update]
  · cases shape : coordinate secret point with
    | some message =>
        obtain rfl := eq_familyInput_of_coordinate shape
        cases hit : tables.hid message with
        | some answer =>
            simp [sharedFlag, sharedImpl, readHidden, hit, shape, view_familyInput]
        | none =>
            simp [sharedFlag, sharedImpl, readHidden, hit, shape, view_familyInput,
              view_hidden_update]
    | none =>
        cases hit : tables.pub point with
        | some answer =>
            simp [sharedFlag, sharedImpl, readPublic, hit, shape,
              view_public secret tables point shape]
        | none =>
            simp [sharedFlag, sharedImpl, readPublic, hit, shape,
              view_public secret tables point shape, view_public_update secret tables point shape]

/-- Every step of the flagged split world projects onto a step of the split world. -/
theorem splitFlag_step (secret : MlKemSharedSecret) (query : HiddenSpec.Domain) (state : Tables × Bool) :
    Prod.map id (fun state : Tables × Bool => (state.1.pub, state.1.hid)) <$>
        (splitFlag secret query).run state =
      (splitImpl query).run (state.1.pub, state.1.hid) := by
  obtain ⟨tables, flag⟩ := state
  rcases query with coin | message | point
  · simp [splitFlag, splitImpl]
  · cases hit : tables.hid message with
    | some answer => simp [splitFlag, splitImpl, readHidden, hit]
    | none => simp [splitFlag, splitImpl, readHidden, hit]
  · cases hit : tables.pub point with
    | some answer => simp [splitFlag, splitImpl, readPublic, hit, logged]
    | none => simp [splitFlag, splitImpl, readPublic, hit, logged]

/-- Every step of the flagged split world projects onto a step of the secret-free logged split world. -/
theorem splitFlag_log_step (secret : MlKemSharedSecret) (query : HiddenSpec.Domain) (state : Tables × Bool) :
    Prod.map id Prod.fst <$> (splitFlag secret query).run state = (splitLog query).run state.1 := by
  obtain ⟨tables, flag⟩ := state
  rcases query with coin | message | point
  · simp [splitFlag, splitLog]
  · simp [splitFlag, splitLog, Functor.map_map]
  · simp [splitFlag, splitLog, Functor.map_map]

/-- The shared world from a prefix cache with no key of the hidden shape is the projection of the flagged shared world. -/
theorem shared_project {α : Type} (secret : MlKemSharedSecret) (oa : OracleComp HiddenSpec α)
    (cache : HmacOracle.QueryCache) (clean : ∀ point, cache point ≠ none → coordinate secret point = none) :
    (simulateQ (sharedImpl secret) oa).run' cache =
      Prod.fst <$> (simulateQ (sharedFlag secret) oa).run (⟨cache, ∅, []⟩, false) := by
  have start : view secret ⟨cache, ∅, []⟩ = cache := by
    funext point
    cases shape : coordinate secret point with
    | none => simp [view, shape]
    | some message =>
        have empty : cache point = none := by
          by_contra filled
          simp [clean point filled] at shape
        simp [view, shape, empty]
  have project := OracleComp.map_run_simulateQ_eq_of_query_map_eq (sharedFlag secret) (sharedImpl secret)
    (fun state : Tables × Bool => view secret state.1) (sharedFlag_step secret) oa (⟨cache, ∅, []⟩, false)
  have key : (simulateQ (sharedImpl secret) oa).run cache =
      Prod.map id (fun state : Tables × Bool => view secret state.1) <$>
        (simulateQ (sharedFlag secret) oa).run (⟨cache, ∅, []⟩, false) := by
    rw [project]
    exact congrArg _ start.symm
  rw [StateT.run'_eq, key]
  simp [Functor.map_map]

/-- The split world is the projection of the flagged split world. -/
theorem split_project {α : Type} (secret : MlKemSharedSecret) (oa : OracleComp HiddenSpec α)
    (cache : HmacOracle.QueryCache) :
    (simulateQ splitImpl oa).run' (cache, ∅) =
      Prod.fst <$> (simulateQ (splitFlag secret) oa).run (⟨cache, ∅, []⟩, false) := by
  have project := OracleComp.map_run_simulateQ_eq_of_query_map_eq (splitFlag secret) splitImpl
    (fun state : Tables × Bool => (state.1.pub, state.1.hid)) (splitFlag_step secret) oa
    (⟨cache, ∅, []⟩, false)
  rw [StateT.run'_eq]
  change Prod.fst <$> (simulateQ splitImpl oa).run ((⟨cache, ∅, []⟩ : Tables).pub, (⟨cache, ∅, []⟩ : Tables).hid) = _
  rw [← project]
  simp [Functor.map_map]

/-- The flagged split world projects onto the logged split world. -/
theorem splitFlag_log {α : Type} (secret : MlKemSharedSecret) (oa : OracleComp HiddenSpec α)
    (state : Tables × Bool) :
    Prod.map id Prod.fst <$> (simulateQ (splitFlag secret) oa).run state =
      (simulateQ splitLog oa).run state.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq (splitFlag secret) splitLog Prod.fst
    (splitFlag_log_step secret) oa state

/-! ### Identical until bad -/

set_option linter.deprecated false in
theorem flag_agree (secret : MlKemSharedSecret) (query : HiddenSpec.Domain) (tables : Tables)
    (answer : HiddenSpec.Range query) (next : Tables) :
    Pr[= (answer, (next, false)) | (splitFlag secret query).run (tables, false)] =
      Pr[= (answer, (next, false)) | (sharedFlag secret query).run (tables, false)] := by
  rcases query with coin | message | point
  · rfl
  · rfl
  · cases shape : coordinate secret point with
    | none => simp [splitFlag, sharedFlag, shape]
    | some message =>
        rw [probOutput_eq_zero_of_not_mem_support, probOutput_eq_zero_of_not_mem_support]
        · simp [sharedFlag, shape]
        · simp [splitFlag, shape]

theorem splitFlag_mono (secret : MlKemSharedSecret) (query : HiddenSpec.Domain) (state : Tables × Bool)
    (flagged : state.2 = true) :
    ∀ result ∈ support ((splitFlag secret query).run state), result.2.2 = true := by
  obtain ⟨tables, flag⟩ := state
  simp only at flagged
  subst flagged
  rcases query with coin | message | point
  · intro result member
    simp [splitFlag] at member
    obtain ⟨_, rfl⟩ := member
    rfl
  · intro result member
    simp [splitFlag] at member
    obtain ⟨_, _, _, rfl⟩ := member
    rfl
  · intro result member
    simp [splitFlag] at member
    obtain ⟨_, _, _, rfl⟩ := member
    rfl

theorem sharedFlag_mono (secret : MlKemSharedSecret) (query : HiddenSpec.Domain) (state : Tables × Bool)
    (flagged : state.2 = true) :
    ∀ result ∈ support ((sharedFlag secret query).run state), result.2.2 = true := by
  obtain ⟨tables, flag⟩ := state
  simp only at flagged
  subst flagged
  rcases query with coin | message | point
  · intro result member
    simp [sharedFlag] at member
    obtain ⟨_, rfl⟩ := member
    rfl
  · intro result member
    simp [sharedFlag] at member
    obtain ⟨_, _, _, rfl⟩ := member
    rfl
  · intro result member
    cases shape : coordinate secret point with
    | none =>
        simp [sharedFlag, shape] at member
        obtain ⟨_, _, _, rfl⟩ := member
        rfl
    | some message =>
        simp [sharedFlag, shape] at member
        obtain ⟨_, _, _, rfl⟩ := member
        rfl

set_option linter.deprecated false in
/-- Identical until bad: the flagged worlds are within the flag probability of the split world. -/
theorem flagged_tvDist {α : Type} (secret : MlKemSharedSecret) (oa : OracleComp HiddenSpec α)
    (tables : Tables) :
    tvDist ((simulateQ (sharedFlag secret) oa).run (tables, false))
        ((simulateQ (splitFlag secret) oa).run (tables, false)) ≤
      Pr[fun result : α × Tables × Bool => result.2.2 = true |
        (simulateQ (splitFlag secret) oa).run (tables, false)].toReal := by
  rw [tvDist_comm]
  exact tvDist_simulateQ_run_le_probEvent_output_bad (splitFlag secret) (sharedFlag secret) oa tables
    (fun query tables answer next => flag_agree secret query tables answer next)
    (fun query state flagged => splitFlag_mono secret query state flagged)
    (fun query state flagged => sharedFlag_mono secret query state flagged)

/-! ### The flag is a function of the direct-read log -/

theorem flag_log {α : Type} (secret : MlKemSharedSecret) (oa : OracleComp HiddenSpec α) (tables : Tables)
    (empty : tables.log = []) :
    ∀ result ∈ support ((simulateQ (splitFlag secret) oa).run (tables, false)),
      (result.2.2 = true ↔ ∃ point ∈ result.2.1.log, (coordinate secret point).isSome) := by
  refine OracleComp.simulateQ_run_preserves_inv_of_query (splitFlag secret)
    (fun state : Tables × Bool => (state.2 = true ↔ ∃ point ∈ state.1.log, (coordinate secret point).isSome))
    ?_ oa (tables, false) (by simp [empty])
  intro query state holds result member
  obtain ⟨current, flag⟩ := state
  rcases query with coin | message | point
  · simp [splitFlag] at member
    obtain ⟨_, rfl⟩ := member
    exact holds
  · simp [splitFlag] at member
    obtain ⟨_, next, reads, rfl⟩ := member
    have same : next.log = current.log := by
      unfold readHidden at reads
      split at reads
      · simp at reads
        rw [reads.2]
      · simp at reads
        obtain ⟨_, rfl⟩ := reads
        rfl
    simpa [same] using holds
  · simp [splitFlag] at member
    obtain ⟨_, next, reads, rfl⟩ := member
    have same : next.log = current.log := by
      unfold readPublic at reads
      split at reads
      · simp at reads
        rw [reads.2]
      · simp at reads
        obtain ⟨_, rfl⟩ := reads
        rfl
    simp only [logged, same, List.mem_append, List.mem_singleton]
    rw [Bool.or_eq_true, holds]
    constructor
    · rintro (⟨other, member, shaped⟩ | shaped)
      · exact ⟨other, Or.inl member, shaped⟩
      · exact ⟨point, Or.inr rfl, shaped⟩
    · rintro ⟨other, member | rfl, shaped⟩
      · exact Or.inl ⟨other, member, shaped⟩
      · exact Or.inr shaped

/-! ### The log length -/

theorem splitLog_step_length (query : HiddenSpec.Domain) (tables : Tables) :
    ∀ result ∈ support ((splitLog query).run tables),
      result.2.log.length = tables.log.length + if IsDirect query then 1 else 0 := by
  intro result member
  rcases query with coin | message | point
  · simp [splitLog] at member
    obtain ⟨_, rfl⟩ := member
    simp [IsDirect]
  · simp [splitLog] at member
    unfold readHidden at member
    split at member
    · simp at member
      subst member
      simp [IsDirect]
    · simp at member
      obtain ⟨_, _, rfl⟩ := member
      simp [IsDirect]
  · simp [splitLog] at member
    obtain ⟨_, next, reads, rfl⟩ := member
    have same : next.log = tables.log := by
      unfold readPublic at reads
      split at reads
      · simp at reads
        rw [reads.2]
      · simp at reads
        obtain ⟨_, rfl⟩ := reads
        rfl
    simp [logged, same, IsDirect]

/-- A client with at most `bound` direct reads appends at most `bound` entries to the log. -/
theorem splitLog_length {α : Type} (oa : OracleComp HiddenSpec α) (bound : ℕ)
    (bounded : oa.IsQueryBoundP IsDirect bound) (tables : Tables) :
    ∀ result ∈ support ((simulateQ splitLog oa).run tables),
      result.2.log.length ≤ tables.log.length + bound := by
  induction oa using OracleComp.inductionOn generalizing bound tables with
  | pure value =>
      intro result member
      simp at member
      subst member
      simp
  | query_bind query next ih =>
      intro result member
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at member
      obtain ⟨step, stepMember, member⟩ := member
      have stepLength := splitLog_step_length query tables step stepMember
      have rest := ih step.1 _ (bounded.2 step.1) step.2 result member
      by_cases direct : IsDirect query
      · have positive : 0 < bound := bounded.1.resolve_left (not_not.mpr direct)
        simp only [direct, ↓reduceIte] at stepLength rest
        omega
      · simp only [direct, ↓reduceIte] at stepLength rest
        omega

/-! ### Per-prefix bound -/

set_option linter.deprecated false in
/-- Total variation over a common first draw is bounded by the probability of an event of a joint computation whenever it is bounded pointwise by the event's probability. -/
theorem tvDist_bind_le_probEvent {α β γ : Type} (mx : ProbComp α) (f g : α → ProbComp β)
    (h : α → ProbComp γ) (event : α → γ → Prop)
    (bound : ∀ a ∈ support mx, tvDist (f a) (g a) ≤ (Pr[event a | h a]).toReal) :
    tvDist (mx >>= f) (mx >>= g) ≤
      (Pr[fun pair : α × γ => event pair.1 pair.2 | do let a ← mx; let c ← h a; pure (a, c)]).toReal := by
  refine (tvDist_bind_left_le mx f g).trans ?_
  have expand : Pr[fun pair : α × γ => event pair.1 pair.2 | do let a ← mx; let c ← h a; pure (a, c)] =
      ∑' a, Pr[= a | mx] * Pr[event a | h a] := by
    rw [probEvent_bind_eq_tsum]
    refine tsum_congr fun a => ?_
    congr 1
    rw [show (do let c ← h a; pure (a, c) : ProbComp (α × γ)) = (fun c => (a, c)) <$> h a by
      simp [map_eq_bind_pure_comp]]
    rw [probEvent_map]
    rfl
  have finite : ∑' a, Pr[= a | mx] * Pr[event a | h a] ≠ ⊤ := by
    rw [← expand]
    exact probEvent_ne_top
  rw [expand, ENNReal.tsum_toReal_eq (fun a => ENNReal.mul_ne_top probOutput_ne_top probEvent_ne_top)]
  have weights : Summable (fun a => (Pr[= a | mx]).toReal) :=
    ENNReal.summable_toReal (ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one)
  refine Summable.tsum_le_tsum (fun a => ?_)
    (weights.of_nonneg_of_le (fun a => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _))
      (fun a => mul_le_of_le_one_right ENNReal.toReal_nonneg (tvDist_le_one _ _)))
    (ENNReal.summable_toReal finite)
  rw [ENNReal.toReal_mul]
  by_cases member : a ∈ support mx
  · exact mul_le_mul_of_nonneg_left (bound a member) ENNReal.toReal_nonneg
  · simp [probOutput_eq_zero_of_not_mem_support member]

/-- The bad event for one prefix outcome: some prefix cache key or some logged direct read has the hidden shape. -/
def Bad (keys : Finset Pqxdh.Bytes) (secret : MlKemSharedSecret) (tables : Tables) : Prop :=
  ∃ point ∈ keys ∪ tables.log.toFinset, (coordinate secret point).isSome

set_option linter.deprecated false in
/-- For one secret, the shared and split worlds are within the probability of the bad event in the secret-free logged split world. -/
theorem secret_tvDist {α : Type} (secret : MlKemSharedSecret) (oa : OracleComp HiddenSpec α)
    (cache : HmacOracle.QueryCache) (keys : Finset Pqxdh.Bytes)
    (covers : ∀ point, cache point ≠ none → point ∈ keys) :
    tvDist ((simulateQ (sharedImpl secret) oa).run' cache) ((simulateQ splitImpl oa).run' (cache, ∅)) ≤
      (Pr[fun result : α × Tables => Bad keys secret result.2 |
        (simulateQ splitLog oa).run ⟨cache, ∅, []⟩]).toReal := by
  by_cases collision : ∃ point ∈ keys, (coordinate secret point).isSome
  · have certain : Pr[fun result : α × Tables => Bad keys secret result.2 |
        (simulateQ splitLog oa).run ⟨cache, ∅, []⟩] = 1 := by
      rw [probEvent_eq_one_iff]
      refine ⟨probFailure_eq_zero, fun result _ => ?_⟩
      obtain ⟨point, member, shaped⟩ := collision
      exact ⟨point, Finset.mem_union_left _ member, shaped⟩
    rw [certain, ENNReal.toReal_one]
    exact tvDist_le_one _ _
  · push Not at collision
    have clean : ∀ point, cache point ≠ none → coordinate secret point = none := by
      intro point filled
      have := collision point (covers point filled)
      simpa [Option.isSome_iff_ne_none] using this
    rw [shared_project secret oa cache clean, split_project secret oa cache]
    refine (tvDist_map_le _ _ _).trans ((flagged_tvDist secret oa ⟨cache, ∅, []⟩).trans ?_)
    refine ENNReal.toReal_mono probEvent_ne_top ?_
    calc Pr[fun result : α × Tables × Bool => result.2.2 = true |
          (simulateQ (splitFlag secret) oa).run (⟨cache, ∅, []⟩, false)]
        = Pr[fun result : α × Tables × Bool => ∃ point ∈ result.2.1.log, (coordinate secret point).isSome |
            (simulateQ (splitFlag secret) oa).run (⟨cache, ∅, []⟩, false)] :=
          probEvent_ext fun result member => flag_log secret oa ⟨cache, ∅, []⟩ rfl result member
      _ = Pr[fun result : α × Tables => ∃ point ∈ result.2.log, (coordinate secret point).isSome |
            (simulateQ splitLog oa).run ⟨cache, ∅, []⟩] := by
          rw [← splitFlag_log secret oa (⟨cache, ∅, []⟩, false), probEvent_map]
          rfl
      _ ≤ Pr[fun result : α × Tables => Bad keys secret result.2 |
            (simulateQ splitLog oa).run ⟨cache, ∅, []⟩] := by
          refine probEvent_mono fun result _ hit => ?_
          obtain ⟨point, member, shaped⟩ := hit
          exact ⟨point, Finset.mem_union_right _ (List.mem_toFinset.mpr member), shaped⟩

set_option linter.deprecated false in
/-- The per-prefix bound: averaged over the secret, the shared and split worlds are within `(keys.card + residual) / 2^256`. -/
theorem prefix_tvDist {α : Type} (oa : OracleComp HiddenSpec α) (cache : HmacOracle.QueryCache)
    (keys : Finset Pqxdh.Bytes) (residual : ℕ) (covers : ∀ point, cache point ≠ none → point ∈ keys)
    (bounded : oa.IsQueryBoundP IsDirect residual) :
    tvDist (do let secret ← $ᵗ MlKemSharedSecret; (simulateQ (sharedImpl secret) oa).run' cache)
        (do let _secret ← $ᵗ MlKemSharedSecret; (simulateQ splitImpl oa).run' (cache, ∅)) ≤
      ((keys.card + residual : ℕ) : ℝ) / 2 ^ 256 := by
  refine (tvDist_bind_le_probEvent ($ᵗ MlKemSharedSecret) _ _ (fun _ => (simulateQ splitLog oa).run ⟨cache, ∅, []⟩)
    (fun secret result => Bad keys secret result.2)
    (fun secret _ => secret_tvDist secret oa cache keys covers)).trans ?_
  have swapped := probEvent_bind_bind_swap ($ᵗ MlKemSharedSecret) ((simulateQ splitLog oa).run ⟨cache, ∅, []⟩)
    (fun secret result => (pure (secret, result) : ProbComp (MlKemSharedSecret × α × Tables)))
    (fun pair => Bad keys pair.1 pair.2.2)
  have bound : Pr[fun pair : MlKemSharedSecret × α × Tables => Bad keys pair.1 pair.2.2 |
      ($ᵗ MlKemSharedSecret >>= fun secret => (simulateQ splitLog oa).run ⟨cache, ∅, []⟩ >>= fun result =>
        pure (secret, result))] ≤ ((keys.card + residual : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
    rw [swapped]
    refine probEvent_bind_le_of_forall_le fun result member => ?_
    have length := splitLog_length oa residual bounded ⟨cache, ∅, []⟩ result member
    simp only [List.length_nil, zero_add] at length
    have mapped : (($ᵗ MlKemSharedSecret >>= fun secret => pure (secret, result)) :
        ProbComp (MlKemSharedSecret × α × Tables)) =
        (fun secret => (secret, result)) <$> ($ᵗ MlKemSharedSecret) := by
      simp [map_eq_bind_pure_comp]
    rw [mapped, probEvent_map]
    refine (guess_finset_le (keys ∪ result.2.log.toFinset)).trans ?_
    gcongr
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add_left ((List.toFinset_card_le _).trans length) _)
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    (ENNReal.inv_ne_top.mpr (pow_ne_zero _ two_ne_zero))) bound).trans_eq ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, div_eq_mul_inv]

/-! ### The main bound -/

/-- The Boolean advantage is at most the total variation distance. -/
theorem boolDistAdvantage_le_tvDist (left right : ProbComp Bool) :
    left.boolDistAdvantage right ≤ tvDist left right := by
  rw [ProbComp.boolDistAdvantage]
  simpa only [evalDist_apply_singleton] using abs_probOutput_toReal_sub_le_tvDist left right

set_option linter.deprecated false in
/-- G1: the shared and split worlds are distinguishable with advantage at most `Q / 2^256`, where `Q` bounds, for every prefix outcome, the prefix cache keys (covered by `keys`) plus the client's direct reads after the prefix (`residual`). -/
theorem hidden_suffix_bound {C : Type} (start : ProbComp (HmacOracle.QueryCache × C))
    (client : C → OracleComp HiddenSpec Bool) (Q : ℕ)
    (keys : HmacOracle.QueryCache × C → Finset Pqxdh.Bytes) (residual : HmacOracle.QueryCache × C → ℕ)
    (covers : ∀ p ∈ support start, ∀ x, p.1 x ≠ none → x ∈ keys p)
    (bounded : ∀ p ∈ support start, (client p.2).IsQueryBoundP IsDirect (residual p))
    (total : ∀ p ∈ support start, (keys p).card + residual p ≤ Q) :
    (sharedGame start client).boolDistAdvantage (splitGame start client) ≤ (Q : ℝ) / 2 ^ 256 := by
  refine (boolDistAdvantage_le_tvDist _ _).trans ?_
  let paddedSplit : ProbComp Bool := start >>= fun p => $ᵗ MlKemSharedSecret >>= fun _secret =>
    (simulateQ splitImpl (client p.2)).run' (p.1, ∅)
  have padded : 𝒮[splitGame start client] = 𝒮[paddedSplit] := by
    unfold splitGame
    refine OracleComp.DeferredSampling.evalSPMF_bind_congr_left _ _ _ fun p => ?_
    exact (OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails _ probFailure_eq_zero _).symm
  have same : tvDist (sharedGame start client) (splitGame start client) =
      tvDist (sharedGame start client) paddedSplit := by
    simp only [tvDist, padded]
  rw [same]
  refine tvDist_bind_left_le_const start _ _ _ fun p member => ?_
  refine (prefix_tvDist (client p.2) p.1 (keys p) (residual p) (covers p member) (bounded p member)).trans ?_
  have := total p member
  gcongr

end BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.coordinate_familyInput' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.coordinate_familyInput

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.eq_familyInput_of_coordinate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.eq_familyInput_of_coordinate

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.secret_of_coordinate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.secret_of_coordinate

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.secret_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.secret_card

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.guess_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.guess_le

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.guess_finset_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.guess_finset_le

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.view_familyInput' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.view_familyInput

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.view_public' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.view_public

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.view_logged' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.view_logged

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.view_hidden_update' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.view_hidden_update

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.view_public_update' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.view_public_update

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.sharedFlag_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.sharedFlag_step

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.splitFlag_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.splitFlag_step

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.splitFlag_log_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.splitFlag_log_step

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.shared_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.shared_project

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.split_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.split_project

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.splitFlag_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.splitFlag_log

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.flag_agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.flag_agree

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.splitFlag_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.splitFlag_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.sharedFlag_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.sharedFlag_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.flagged_tvDist' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.flagged_tvDist

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.flag_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.flag_log

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.splitLog_step_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.splitLog_step_length

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.splitLog_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.splitLog_length

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.tvDist_bind_le_probEvent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.tvDist_bind_le_probEvent

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.secret_tvDist' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.secret_tvDist

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.prefix_tvDist' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.prefix_tvDist

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.boolDistAdvantage_le_tvDist' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.boolDistAdvantage_le_tvDist

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.hidden_suffix_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix.hidden_suffix_bound
