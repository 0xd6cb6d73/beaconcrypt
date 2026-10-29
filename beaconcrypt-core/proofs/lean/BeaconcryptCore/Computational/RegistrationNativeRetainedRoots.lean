-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKeyServiceBound

/-! Root replies retained privately at preparation remain tied to the same persistent protected PRK. This invariant justifies recomputing complete native material at demand after erasing the retained root, rather than treating the root as independent side information. Ordinary side roots remain the actual fixed source function. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRetainedRoots
open RegistrationNativeRelatedFamily (Message)
open PqxdhSecretInputKdf (RootOutput HmacBlock HmacOracle HmacSha512 expandRoot)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open RegistrationNativeKeyPhases (Meta)

abbrev Memo := Message → Option RootOutput
abbrev State := Memo × RegistrationNativeKeyPhases.State

def Cached (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (cache : HmacOracle.QueryCache) (message : Message) (root : RootOutput) : Prop :=
  ∃ bytes, input message = some bytes ∧
    if inside bytes then ∃ prk, cache bytes = some prk ∧ root = expandRoot hmac prk
    else root = RegistrationNativeRelatedRoot.nativeRoot source bytes

def Good (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (state : State) : Prop :=
  ∀ message root, state.1 message = some root →
    Cached source hmac input inside state.2.2 message root ∧
      ∃ bytes, input message = some bytes ∧ state.2.1.prepared bytes = true

set_option maxRecDepth 4096 in
/-- Every reached lazy query caches its returned value and preserves all earlier cached points. -/
theorem query_receipts (bytes : Pqxdh.Bytes) (before : HmacOracle.QueryCache)
    (result : HmacBlock × HmacOracle.QueryCache)
    (reached : result ∈ support ((HmacOracle.randomOracle bytes).run before)) :
    result.2 bytes = some result.1 ∧
      ∀ old prk, before old = some prk → result.2 old = some prk := by
  cases cached : before bytes with
  | none =>
    rw [LazyOracleDiscard.query_of_none cached] at reached
    simp only [bind_pure_comp, support_map] at reached
    obtain ⟨prk, _sampled, equal⟩ := reached
    cases equal
    constructor
    · exact QueryCache.cacheQuery_self _ _ _
    · intro old value stored
      have different : old ≠ bytes := by intro same; subst old; rw [cached] at stored; cases stored
      exact (QueryCache.cacheQuery_of_ne before prk different).trans stored
  | some prk =>
    rw [LazyOracleDiscard.query_of_some cached, support_pure] at reached
    subst result
    exact ⟨cached, fun _ _ stored => stored⟩

private theorem prepareMeta_run (input : Message → Option Pqxdh.Bytes) (message : Message) (before : Meta) :
    (RegistrationNativeKeyPhases.prepareMeta input message).run before = match input message with
      | none => pure (none, { before with prepares := before.prepares + 1 })
      | some bytes => pure (some message, { before with
          prepared := Function.update before.prepared bytes true
          prepares := before.prepares + 1
          roots := before.roots + 1 }) := rfl

private theorem cache_query_run (bytes : Pqxdh.Bytes) (before : RegistrationNativeKeyPhases.State) :
    (RegistrationNativeKeyPhases.cacheLens.query bytes).run before =
      (fun result => (result.1, (before.1, result.2))) <$> (HmacOracle.randomOracle bytes).run before.2 := rfl

private def marked (before : Meta) (bytes : Pqxdh.Bytes) : Meta :=
  { before with
    prepared := Function.update before.prepared bytes true
    prepares := before.prepares + 1
    roots := before.roots + 1 }

private theorem prepare_run (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (message : Message) (before : RegistrationNativeKeyPhases.State) :
    (RegistrationNativeKeyPreparation.prepare source hmac input inside message).run before =
      match input message with
      | none => pure (none, ({ before.1 with prepares := before.1.prepares + 1 }, before.2))
      | some bytes => if inside bytes then
          (fun result => (some (message, expandRoot hmac result.1), (marked before.1 bytes, result.2))) <$>
            (HmacOracle.randomOracle bytes).run before.2
        else pure (some (message, RegistrationNativeRelatedRoot.nativeRoot source bytes), (marked before.1 bytes, before.2)) := by
  simp only [RegistrationNativeKeyPreparation.prepare, StateT.run_bind,
    RegistrationNativeKeyPhases.onMeta_run, prepareMeta_run]
  cases actual : input message with
  | none => simp [StateT.run_pure]
  | some bytes =>
    cases protectedInput : inside bytes <;>
      simp only [protectedInput, map_pure, pure_bind, Bool.false_eq_true, ite_false, ite_true,
        StateT.run_pure, StateT.run_map, cache_query_run, Functor.map_map, marked]

private theorem marked_keeps (before : Meta) (bytes old : Pqxdh.Bytes)
    (prepared : before.prepared old = true) : (marked before bytes).prepared old = true := by
  by_cases same : old = bytes
  · subst old
    simp only [marked, Function.update_self]
  · simpa only [marked, Function.update_of_ne same] using prepared

/-- Actual dependent preparation never changes an earlier private PRK or revokes a successful input preparation. -/
theorem prepare_persists (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (message : Message)
    (before after : RegistrationNativeKeyPhases.State) (reply : Option (Message × RootOutput))
    (reached : (reply, after) ∈ support
      ((RegistrationNativeKeyPreparation.prepare source hmac input inside message).run before)) :
    (∀ bytes prk, before.2 bytes = some prk → after.2 bytes = some prk) ∧
      ∀ bytes, before.1.prepared bytes = true → after.1.prepared bytes = true := by
  rw [prepare_run] at reached
  cases actual : input message with
  | none =>
      simp only [actual, support_pure] at reached
      rcases reached with ⟨rfl, rfl⟩
      exact ⟨fun _ _ present => present, fun _ prepared => prepared⟩
  | some bytes =>
      cases protectedInput : inside bytes
      · simp only [actual, protectedInput, Bool.false_eq_true, ite_false, support_pure] at reached
        rcases reached with ⟨rfl, rfl⟩
        exact ⟨fun _ _ present => present, fun old prepared => marked_keeps before.1 bytes old prepared⟩
      · simp only [actual, protectedInput, ite_true, support_map] at reached
        obtain ⟨queried, possible, equal⟩ := reached
        cases equal
        exact ⟨(query_receipts bytes before.2 queried possible).2,
          fun old prepared => marked_keeps before.1 bytes old prepared⟩

/-- The actual dependent prepare reply is readable from the reached persistent cache or its unchanged ordinary source root. -/
theorem prepare_cached (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (message : Message)
    (before after : RegistrationNativeKeyPhases.State) (reference : Message) (root : RootOutput)
    (reached : (some (reference, root), after) ∈ support
      ((RegistrationNativeKeyPreparation.prepare source hmac input inside message).run before)) :
    reference = message ∧ Cached source hmac input inside after.2 message root ∧
      ∃ bytes, input message = some bytes ∧ after.1.prepared bytes = true := by
  simp only [RegistrationNativeKeyPreparation.prepare, StateT.run_bind,
    RegistrationNativeKeyPhases.onMeta_run, prepareMeta_run] at reached
  cases realized : input message with
  | none => simp [realized] at reached
  | some bytes =>
    cases protectedInput : inside bytes
    · simp only [realized, protectedInput, map_pure, pure_bind, Bool.false_eq_true, ite_false,
        StateT.run_pure, support_pure, ] at reached
      rcases reached with ⟨⟨rfl, rfl⟩, rfl⟩
      simp [Cached, realized, protectedInput]

    · simp only [realized, protectedInput, map_pure, pure_bind, ite_true, StateT.run_map,
        cache_query_run, Functor.map_map, support_map] at reached
      obtain ⟨queried, possible, equal⟩ := reached
      simp only [Prod.mk.injEq, Option.some.injEq] at equal
      rcases equal with ⟨⟨rfl, rfl⟩, rfl⟩
      have cached := (query_receipts bytes before.2 queried possible).1
      refine ⟨rfl, ⟨bytes, realized, ?_⟩, ⟨bytes, rfl, ?_⟩⟩
      · simp only [protectedInput, ite_true]
        exact ⟨queried.1, cached, rfl⟩
      · simp only [Function.update_self]

/-- Cache extension preserves every already justified native root, including ordinary side inputs. -/
theorem Cached.mono (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (before after : HmacOracle.QueryCache)
    (extension : ∀ bytes prk, before bytes = some prk → after bytes = some prk)
    (message : Message) (root : RootOutput)
    (cached : Cached source hmac input inside before message root) :
    Cached source hmac input inside after message root := by
  obtain ⟨bytes, realized, cached⟩ := cached
  refine ⟨bytes, realized, ?_⟩
  cases protectedInput : inside bytes
  · simpa only [protectedInput, Bool.false_eq_true, ite_false] using cached
  · simp only [protectedInput, ite_true] at cached ⊢
    obtain ⟨prk, present, rootEq⟩ := cached
    exact ⟨prk, extension bytes prk present, rootEq⟩

noncomputable def remember (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (message : Message) :
    StateT State ProbComp (Option Message) := fun before =>
  (fun result => (result.1.map Prod.fst,
    (Function.update before.1 message (result.1.map Prod.snd), result.2))) <$>
      (RegistrationNativeKeyPreparation.prepare source hmac input inside message).run before.2

/-- Retaining the actual returned root establishes its cache receipt and preserves every earlier receipt. -/
theorem remember_good (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (message : Message)
    (before after : State) (reply : Option Message)
    (good : Good source hmac input inside before)
    (reached : (reply, after) ∈ support ((remember source hmac input inside message).run before)) :
    Good source hmac input inside after := by
  simp only [remember, StateT.run, support_map] at reached
  obtain ⟨result, generated, equal⟩ := reached
  cases equal
  intro other root stored
  by_cases same : other = message
  · subst other
    simp only [Function.update_self] at stored
    cases actual : result.1 with
    | none => simp only [actual, Option.map_none] at stored; cases stored
    | some pair =>
      rcases pair with ⟨reference, returned⟩
      simp only [actual, Option.map_some, Option.some.injEq] at stored
      subst root
      have reachedRoot : (some (reference, returned), result.2) ∈ support
          ((RegistrationNativeKeyPreparation.prepare source hmac input inside message).run before.2) := by
        have pair : (result.1, result.2) = result := Prod.mk.eta
        rw [← pair, actual] at generated
        exact generated
      exact (prepare_cached source hmac input inside message before.2 result.2 reference returned reachedRoot).2
  · have previous : before.1 other = some root := by
      simpa only [Function.update_of_ne same] using stored
    obtain ⟨cached, bytes, realized, prepared⟩ := good other root previous
    obtain ⟨cacheKeeps, preparedKeeps⟩ :=
      prepare_persists source hmac input inside message before.2 result.2 result.1 generated
    exact ⟨Cached.mono source hmac input inside before.2.2 result.2.2 cacheKeeps other root cached,
      bytes, realized, preparedKeeps bytes prepared⟩

def output : RegistrationNativeKeyPhases.Value → PqxdhServerAuthKeySchedule.Output
  | .known value | .hidden value => value

def demand (source : FixedHkdfSha512NoSaltSource) (message : Message) :
    StateT State ProbComp (Option PqxdhServerAuthKeySchedule.Output) := fun before =>
  match before.1 message with
  | none => pure (none, before)
  | some root => pure (some (PqxdhServerAuthKeySchedule.fromRoot source root),
      (before.1, ({ before.2.1 with demands := before.2.1.demands + 1, material := before.2.1.material + 1 }, before.2.2)))

private theorem demandMeta_run (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (message : Message) (before : Meta) :
    (RegistrationNativeKeyPhases.demandMeta input inside message).run before =
      match input message with
      | none => pure (none, { before with demands := before.demands + 1 })
      | some bytes => if before.prepared bytes then
          pure (some (bytes, inside bytes), { before with demands := before.demands + 1, material := before.material + 1 })
        else pure (none, { before with demands := before.demands + 1 }) := rfl

private theorem native_demand (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (message : Message) (before : RegistrationNativeKeyPhases.State) (bytes : Pqxdh.Bytes)
    (realized : input message = some bytes) (prepared : before.1.prepared bytes = true) :
    (RegistrationNativeKeyServiceBound.native source hmac input inside (.inr (.demand message))).run before =
      if inside bytes then
        (fun result => (some (RegistrationNativeKeyPhases.Value.hidden
          (PqxdhServerAuthKeySchedule.keySchedule source hmac result.1)),
          ({ before.1 with demands := before.1.demands + 1, material := before.1.material + 1 }, result.2))) <$>
            (HmacOracle.randomOracle bytes).run before.2
      else pure (some (.known (PqxdhServerAuthKeySchedule.fromRoot source
        (RegistrationNativeRelatedRoot.nativeRoot source bytes))),
        ({ before.1 with demands := before.1.demands + 1, material := before.1.material + 1 }, before.2)) := by
  simp only [RegistrationNativeKeyServiceBound.native, RegistrationNativeKeyPhases.erased,
    StateT.run_bind, RegistrationNativeKeyPhases.onMeta_run, demandMeta_run, realized, prepared,
    ite_true, map_pure, pure_bind]
  cases protectedInput : inside bytes <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, StateT.run_pure,
      StateT.run_map, cache_query_run, Functor.map_map]

/-- Recomputing material from the same cached PRK equals the material of its retained dependent root, with all phase metadata unchanged except the actual demand counters. -/
theorem demand_project (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (message : Message) (before : State) (good : Good source hmac input inside before) :
    Prod.map id Prod.snd <$> (demand source message).run before =
      if (before.1 message).isSome then
        Prod.map (Option.map output) id <$>
          (RegistrationNativeKeyServiceBound.native source hmac input inside (.inr (.demand message))).run before.2
      else pure (none, before.2) := by
  cases stored : before.1 message with
  | none => simp only [demand, StateT.run, stored, Option.isSome_none, Bool.false_eq_true, ite_false, map_pure]; rfl
  | some root =>
    obtain ⟨cached, bytes, realized, prepared⟩ := good message root stored
    obtain ⟨other, otherInput, rootCached⟩ := cached
    have same : other = bytes := Option.some.inj (otherInput.symm.trans realized)
    subst other
    cases protectedInput : inside bytes
    · simp only [protectedInput, Bool.false_eq_true, ite_false] at rootCached
      subst root
      rw [native_demand source hmac input inside message before.2 bytes realized prepared]
      simp only [demand, StateT.run, stored, Option.isSome_some, ite_true, protectedInput,
        Bool.false_eq_true, ite_false, map_pure, Prod.map, id_eq, Option.map_some, output]
    · simp only [protectedInput, ite_true] at rootCached
      obtain ⟨prk, cached, rootEq⟩ := rootCached
      subst root
      rw [native_demand source hmac input inside message before.2 bytes realized prepared]
      simp only [demand, StateT.run, stored, Option.isSome_some, ite_true, protectedInput,
        ite_true, map_pure]
      have hit : HmacOracle.randomOracle bytes before.2.2 = pure (prk, before.2.2) :=
        LazyOracleDiscard.query_of_some cached
      rw [hit]
      simp only [map_pure, Prod.map, id_eq, Option.map_some, output]
      rfl

/-- Demand never changes a cached root receipt or its public preparation status. -/
theorem demand_good (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (message : Message) (before after : State) (reply : Option PqxdhServerAuthKeySchedule.Output)
    (good : Good source hmac input inside before)
    (reached : (reply, after) ∈ support ((demand source message).run before)) :
    Good source hmac input inside after := by
  simp only [demand, StateT.run] at reached
  cases actual : before.1 message
  all_goals simp only [actual, support_pure] at reached
  all_goals rcases reached with ⟨rfl, rfl⟩
  all_goals exact good

/-- The actual optional root reply depends on the protected cache, while preparation metadata remains separate analysis state. -/
noncomputable def root (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (message : Message) :
    StateT HmacOracle.QueryCache ProbComp (Option RootOutput) :=
  match input message with
  | none => pure none
  | some bytes => if inside bytes then
      (fun prk => some (expandRoot hmac prk)) <$> HmacOracle.randomOracle bytes
    else pure (some (RegistrationNativeRelatedRoot.nativeRoot source bytes))

/-- The reached native prepare-time root and private cache are exactly the original root service after forgetting only analysis preparation counters. -/
theorem prepare_root (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (message : Message)
    (before : RegistrationNativeKeyPhases.State) :
    Prod.map (Option.map Prod.snd) Prod.snd <$>
      (RegistrationNativeKeyPreparation.prepare source hmac input inside message).run before =
      (root source hmac input inside message).run before.2 := by
  rw [prepare_run]
  cases actual : input message with
  | none => simp only [actual, root, StateT.run_pure, map_pure, Prod.map, Option.map_none]
  | some bytes =>
    cases protectedInput : inside bytes <;>
      simp only [actual, root, protectedInput, Bool.false_eq_true, ite_false, ite_true,
        StateT.run_pure, StateT.run_map, map_pure, Functor.map_map, Prod.map,
        Option.map_some]

/-- Actual root memoization is unchanged after adding or forgetting only the preparation metadata. -/
theorem remember_root (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (message : Message) (before : State) :
    Prod.map id (fun state => (state.1, state.2.2)) <$> (remember source hmac input inside message).run before = (do
      let result ← (root source hmac input inside message).run before.2.2
      pure (result.1.map (fun _ => message), (Function.update before.1 message result.1, result.2))) := by
  change Prod.map id (fun state => (state.1, state.2.2)) <$>
      (fun result => (result.1.map Prod.fst,
        (Function.update before.1 message (result.1.map Prod.snd), result.2))) <$>
          (RegistrationNativeKeyPreparation.prepare source hmac input inside message).run before.2 = _
  rw [prepare_run]
  cases actual : input message with
  | none => simp only [actual, root, StateT.run_pure, map_pure, pure_bind, Prod.map,
      Option.map_none, id_eq]
  | some bytes =>
    cases protectedInput : inside bytes <;>
      simp only [actual, root, protectedInput, Bool.false_eq_true, ite_false, ite_true,
        StateT.run_pure, StateT.run_map, map_pure, bind_pure_comp, Functor.map_map,
        Prod.map, Option.map_some, id_eq]

end BeaconcryptCore.Computational.RegistrationNativeRetainedRoots

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedRoots.query_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedRoots.query_receipts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedRoots.prepare_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedRoots.prepare_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedRoots.prepare_persists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedRoots.prepare_persists

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedRoots.Cached.mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedRoots.Cached.mono
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedRoots.remember_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedRoots.remember_good

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedRoots.demand_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedRoots.demand_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedRoots.demand_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedRoots.demand_good

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedRoots.prepare_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedRoots.prepare_root

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedRoots.remember_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedRoots.remember_root
