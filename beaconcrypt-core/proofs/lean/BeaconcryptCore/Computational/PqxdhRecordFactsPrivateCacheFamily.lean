-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheRandom

/-! Coordinate-family cache lenses for the shared CTX experiment. -/
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily
open CtxRomAuth CtxSplitCache AdaptiveCtxReceive
open LazyOracleDiscard PqxdhRecordFactsPrivateCache
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode KeyedSpec materialAt)
variable {n : Nat}

/-- One ordinary lazy digest oracle indexed by both material coordinate and suffix. -/
abbrev FamilyRO (n : Nat) := ((Label n × Pqxdh.Bytes) →ₒ CtxDigest)

/-- Every private suffix dictionary, with all local histories and the base state framed around it. -/
def familyLens : CacheLens (FamilyRO n) (CtxPrivate n) where
  get state := fun q => (state.keys q.1).2 q.2
  set state cache := { state with keys := fun label => ((state.keys label).1, fun suffix => cache (label, suffix)) }
  get_set state cache := by rfl
  set_get state := by rfl
  set_set state cache cache' := by rfl

/-- The exact one-key state and shared ROM used by a keyed request. -/
noncomputable def localLens (label : Label n) : StateLens (CtxPrivate n) PqxdhRecordFactsPrivateCache.State where
  get state := (state.keys label, state.base.primitive.2)
  set state pair := { state with
    base := { state.base with primitive := (state.base.primitive.1, pair.2) }
    keys := Function.update state.keys label pair.1 }
  get_set state pair := by simp
  set_get state := by simp
  set_set state pair pair' := by simp

/-- The existing one-key endpoint in its coordinate, omitting only the outer uniform-query counter instrumentation. -/
noncomputable def uncountedKeyed (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto) :
    QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp) := fun q state =>
  ((localLens q.1).lift (PqxdhRecordFactsPrivateCacheRandom.linked decode crypto
    (materialAt state.base.chain q.1).1 (modes q.1) q.2)).run state

/-- Explicit full-state form for the counter-erasure source join. -/
theorem uncountedKeyed_run (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (q : (KeyedSpec n).Domain) (state : CtxPrivate n) :
    (uncountedKeyed modes decode crypto q).run state =
      (fun r => (r.1, { state with
        base := { state.base with primitive := (state.base.primitive.1, r.2.2) }
        keys := Function.update state.keys q.1 r.2.1 })) <$>
      (PqxdhRecordFactsPrivateCacheRandom.linked decode crypto (materialAt state.base.chain q.1).1
        (modes q.1) q.2).run (state.keys q.1, state.base.primitive.2) := rfl

/-- Everything except the family's private suffix dictionaries. -/
def observeFamily (state : CtxPrivate n) := (state.base, fun label => (state.keys label).1)

theorem observeFamily_set (state : CtxPrivate n) (cache : (FamilyRO n).QueryCache) :
    observeFamily (familyLens.set state cache) = observeFamily state := rfl

/-- Completing one family point is exactly completing the same local suffix at that coordinate. -/
theorem complete_local (label : Label n) (suffix : Pqxdh.Bytes) (state : CtxPrivate n) :
    familyLens.complete (label, suffix) state =
      ((localLens label).comp suffixLens).complete suffix state := by
  simp only [StateLens.complete, complete_run, familyLens, localLens, StateLens.comp,
    suffixLens, StateLens.fst, StateLens.snd]
  cases cached : (state.keys label).2 suffix with
  | none =>
      simp only [Functor.map_map]
      congr 1
      funext digest
      congr 1
      funext other
      by_cases same : other = label
      · subst other
        simp only [Function.update_self]
        congr 1
        funext otherSuffix
        by_cases sameSuffix : otherSuffix = suffix
        · subst otherSuffix; simp
        · simp [QueryCache.cacheQuery, Function.update_of_ne, sameSuffix]
      · simp only [Function.update_of_ne same]
        apply Prod.ext
        · rfl
        · funext otherSuffix
          simp [QueryCache.cacheQuery, Function.update_of_ne, same]
  | some digest =>
      simp only [map_pure, Prod.eta, Function.update_eq_self]

/-- A step on one coordinate cannot inspect the suffix dictionary of another coordinate. -/
theorem localLift_other_commutes {Result : Type} (label other : Label n) (different : label ≠ other)
    (step : StateT PqxdhRecordFactsPrivateCache.State ProbComp Result) :
    Commutes ((localLens other).comp suffixLens) ((localLens label).lift step) := by
  apply commutes_frame
  intro state cache
  simp only [StateLens.lift, StateT.run, localLens, StateLens.comp, suffixLens,
    StateLens.fst, StateLens.snd, Function.update_of_ne different, Functor.map_map]
  simp only [Function.update_of_ne (Ne.symm different), Function.update_comm different]

/-- The complete family cache commutes with a local step whenever that step commutes with its own suffix cache. -/
theorem localLift_commutes {Result : Type} (label : Label n)
    (step : StateT PqxdhRecordFactsPrivateCache.State ProbComp Result)
    (commutes : Commutes suffixLens step) : Commutes familyLens ((localLens label).lift step) := by
  intro point state
  rcases point with ⟨other, suffix⟩
  simp only [complete_local]
  by_cases same : other = label
  · subst other
    exact commutes_lift (localLens label) suffixLens step commutes suffix state
  · exact localLift_other_commutes label other (Ne.symm same) step suffix state

/-- Base service state is independent of every private suffix dictionary. -/
def baseRead : StateT (CtxPrivate n) ProbComp (PqxdhRecordLiftProtocol.Private n) :=
  fun state => pure (state.base, state)

theorem baseRead_commutes : Commutes familyLens (baseRead (n := n)) := by
  apply commutes_frame
  intro state cache
  simp only [baseRead, StateT.run, familyLens, map_pure]

/-- Completing an optional labeled point after a local state replacement acts through the same local lens. -/
theorem completeOpt_local (label : Label n) (point : Option Pqxdh.Bytes)
    (state : CtxPrivate n) (entry : PqxdhRecordFactsPrivateCache.State) :
    familyLens.completeOpt (point.map fun suffix => (label, suffix)) ((localLens label).set state entry) =
      (localLens label).set state <$> suffixLens.completeOpt point entry := by
  cases point with
  | none => simp only [Option.map_none, StateLens.completeOpt, map_pure]
  | some suffix =>
      simp only [Option.map_some, StateLens.completeOpt, complete_local, LazyOracleDiscard.complete_comp,
        (localLens label).get_set]
      congr 1
      funext after
      exact (localLens label).set_set state entry after

/-- The local discarded-query factor lifts to the actual coordinate/shared-ROM state. -/
theorem factor_local {Result : Type} (label : Label n)
    (step : StateT PqxdhRecordFactsPrivateCache.State ProbComp Result)
    (pointedStep : StateT PqxdhRecordFactsPrivateCache.State ProbComp (Result × Option Pqxdh.Bytes))
    (factor : ∀ entry, LawEq (step.run entry)
      (pointedStep.run entry >>= fun r => (r.1.1, ·) <$> suffixLens.completeOpt r.1.2 r.2))
    (state : CtxPrivate n) :
    LawEq (((localLens label).lift step).run state)
      (((localLens label).lift pointedStep).run state >>= fun r =>
        (r.1.1, ·) <$> familyLens.completeOpt (r.1.2.map fun suffix => (label, suffix)) r.2) := by
  have h := (factor ((localLens label).get state)).map
    (fun r => (r.1, (localLens label).set state r.2))
  simpa only [StateLens.lift, StateT.run, map_bind, bind_map_left, completeOpt_local, Functor.map_map]
    using h

/-- The reported deferred point, as well as the reply, commutes in either supported local mode. -/
theorem localPointed_commutes (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (mode : KeyMode) (supported : mode ≠ .real) (q : ReceiveSpec.Domain) :
    Commutes suffixLens (PqxdhRecordFactsPrivateCacheRandom.modePointed decode crypto key mode q) := by
  cases q with
  | inr raw => exact rawBase_commutes decode raw
  | inl q =>
      apply commutes_map suffixLens (fun answer => (answer, none))
      cases mode with
      | real => exact False.elim (supported rfl)
      | replay => exact linked_nonraw_commutes decode crypto key q
      | random => exact PqxdhRecordFactsPrivateCacheRandom.random_nonraw_commutes decode crypto key q

/-- Lift a pointed local operation selected only from retained base state. -/
noncomputable def pointedFromBase {Result : Type} (label : Label n)
    (work : PqxdhRecordLiftProtocol.Private n →
      StateT PqxdhRecordFactsPrivateCache.State ProbComp (Result × Option Pqxdh.Bytes)) :
    StateT (CtxPrivate n) ProbComp (Result × Option (FamilyRO n).Domain) := do
  let base ← baseRead
  (fun reply => (reply.1, reply.2.map fun suffix => (label, suffix))) <$> (localLens label).lift (work base)

/-- The generic pointed base-read is just the selected local run and a point relabeling. -/
theorem pointedFromBase_run {Result : Type} (label : Label n)
    (work : PqxdhRecordLiftProtocol.Private n →
      StateT PqxdhRecordFactsPrivateCache.State ProbComp (Result × Option Pqxdh.Bytes))
    (state : CtxPrivate n) :
    (pointedFromBase label work).run state =
      (fun r => ((r.1.1, r.1.2.map fun suffix => (label, suffix)), r.2)) <$>
        (((localLens label).lift (work state.base)).run state) := by
  simp only [pointedFromBase, StateT.run_bind, StateT.run_map]
  simp only [baseRead, StateT.run, pure_bind]

/-- Base-selected local factors preserve the exact family deferred-completion factor. -/
theorem factorFromBase {Result : Type} (label : Label n)
    (step : PqxdhRecordLiftProtocol.Private n → StateT PqxdhRecordFactsPrivateCache.State ProbComp Result)
    (pointedStep : PqxdhRecordLiftProtocol.Private n →
      StateT PqxdhRecordFactsPrivateCache.State ProbComp (Result × Option Pqxdh.Bytes))
    (factor : ∀ base entry, LawEq ((step base).run entry)
      ((pointedStep base).run entry >>= fun r => (r.1.1, ·) <$> suffixLens.completeOpt r.1.2 r.2))
    (state : CtxPrivate n) :
    LawEq (((localLens label).lift (step state.base)).run state)
      ((pointedFromBase label pointedStep).run state >>= fun r =>
        (r.1.1, ·) <$> familyLens.completeOpt r.1.2 r.2) := by
  apply (factor_local label (step state.base) (pointedStep state.base) (factor state.base) state).trans
  apply LawEq.of_eq
  rw [pointedFromBase_run]
  simp only [bind_map_left]

/-- Coordinate-labeled deferred raw lookup, preserving the original key/table selection. -/
noncomputable def keyedPointed (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto) :
    (q : (KeyedSpec n).Domain) → StateT (CtxPrivate n) ProbComp
      ((KeyedSpec n).Range q × Option (FamilyRO n).Domain) := fun q =>
  pointedFromBase q.1 (fun base => PqxdhRecordFactsPrivateCacheRandom.modePointed decode crypto
    (materialAt base.chain q.1).1 (modes q.1) q.2)

/-- The entire family pointed step commutes with completion at any coordinate. -/
theorem keyedPointed_commutes (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (supported : ∀ label, modes label ≠ .real) (q : (KeyedSpec n).Domain) :
    Commutes familyLens (keyedPointed modes decode crypto q) := by
  apply commutes_bind familyLens baseRead_commutes
  intro base
  apply commutes_map familyLens
  apply localLift_commutes
  exact localPointed_commutes decode crypto (materialAt base.chain q.1).1 (modes q.1) (supported q.1) q.2

/-- One pointed keyed step in the local-state form. -/
theorem keyedPointed_run (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (q : (KeyedSpec n).Domain) (state : CtxPrivate n) :
    (keyedPointed modes decode crypto q).run state =
      (fun r => ((r.1.1, r.1.2.map fun suffix => (q.1, suffix)), r.2)) <$>
        (((localLens q.1).lift (PqxdhRecordFactsPrivateCacheRandom.modePointed decode crypto
          (materialAt state.base.chain q.1).1 (modes q.1) q.2)).run state) := pointedFromBase_run q.1 _ state

/-- Per-key factorization instantiated at a coordinate without expanding a protocol material expression. -/
theorem local_mode_factor (label : Label n) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (key : CtxKey) (mode : KeyMode) (supported : mode ≠ .real) (q : ReceiveSpec.Domain)
    (state : CtxPrivate n) :
    LawEq (((localLens label).lift (PqxdhRecordFactsPrivateCacheRandom.linked decode crypto key mode q)).run state)
      (((localLens label).lift (PqxdhRecordFactsPrivateCacheRandom.modePointed decode crypto key mode q)).run state
        >>= fun r => (r.1.1, ·) <$>
          familyLens.completeOpt (r.1.2.map fun suffix => (label, suffix)) r.2) :=
  factor_local label _ _ (PqxdhRecordFactsPrivateCacheRandom.mode_factor decode crypto key mode supported q) state

/-- Factorization with an arbitrary base-selected key. -/
theorem selected_factor (label : Label n) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (select : PqxdhRecordLiftProtocol.Private n → CtxKey)
    (mode : KeyMode) (supported : mode ≠ .real) (q : ReceiveSpec.Domain) (state : CtxPrivate n) :
    LawEq ((fun r => (r.1, { state with
        base := { state.base with primitive := (state.base.primitive.1, r.2.2) }
        keys := Function.update state.keys label r.2.1 })) <$>
      (PqxdhRecordFactsPrivateCacheRandom.linked decode crypto (select state.base) mode q).run
        (state.keys label, state.base.primitive.2))
      ((pointedFromBase label (fun base => PqxdhRecordFactsPrivateCacheRandom.modePointed decode crypto
        (select base) mode q)).run state >>= fun r => (r.1.1, ·) <$> familyLens.completeOpt r.1.2 r.2) := by
  simpa only [StateLens.lift, localLens, StateT.run] using
    (factorFromBase label
      (fun base => PqxdhRecordFactsPrivateCacheRandom.linked decode crypto (select base) mode q)
      (fun base => PqxdhRecordFactsPrivateCacheRandom.modePointed decode crypto (select base) mode q)
      (fun base => PqxdhRecordFactsPrivateCacheRandom.mode_factor decode crypto (select base) mode supported q) state)


/-- Factoring one actual uncounted keyed step preserves every local entry and the shared ROM. -/
theorem keyed_factor (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (supported : ∀ label, modes label ≠ .real) (q : (KeyedSpec n).Domain) (state : CtxPrivate n) :
    LawEq ((uncountedKeyed modes decode crypto q).run state)
      ((keyedPointed modes decode crypto q).run state >>= fun r =>
        (r.1.1, ·) <$> familyLens.completeOpt r.1.2 r.2) := by
  rw [uncountedKeyed_run]
  unfold keyedPointed
  exact selected_factor q.1 decode crypto (fun base => (materialAt base.chain q.1).1)
    (modes q.1) (supported q.1) q.2 state


/-- The family interpreter with discarded raw completions omitted. -/
noncomputable def erasedKeyed (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto) :
    QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp) :=
  fun q => Prod.fst <$> keyedPointed modes decode crypto q

/-- Every adaptive sequence of coordinate requests preserves its full observed distribution after dropping only suffix dictionaries. -/
theorem keyed_observation (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (supported : ∀ label, modes label ≠ .real) {Result : Type}
    (client : OracleComp (KeyedSpec n) Result) (state : CtxPrivate n) :
    LawEq (Prod.map id observeFamily <$> (simulateQ (uncountedKeyed modes decode crypto) client).run state)
      (Prod.map id observeFamily <$> (simulateQ (erasedKeyed modes decode crypto) client).run state) := by
  exact discard_erase_proj familyLens (uncountedKeyed modes decode crypto)
    (keyedPointed modes decode crypto) (keyed_factor modes decode crypto supported)
    (fun q => commutes_map familyLens Prod.fst (keyedPointed_commutes modes decode crypto supported q))
    observeFamily observeFamily_set client state

end BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.uncountedKeyed_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.uncountedKeyed_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.observeFamily_set' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.observeFamily_set

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.complete_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.complete_local

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.localLift_other_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.localLift_other_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.localLift_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.localLift_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.baseRead_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.baseRead_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.completeOpt_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.completeOpt_local

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.factor_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.factor_local

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.localPointed_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.localPointed_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.pointedFromBase_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.pointedFromBase_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.factorFromBase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.factorFromBase

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.keyedPointed_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.keyedPointed_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.keyedPointed_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.keyedPointed_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.local_mode_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.local_mode_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.selected_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.selected_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.keyed_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.keyed_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.keyed_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily.keyed_observation
