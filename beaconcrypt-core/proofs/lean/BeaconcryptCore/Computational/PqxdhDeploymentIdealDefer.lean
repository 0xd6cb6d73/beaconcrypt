-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel

/-!
# Deferring the ideal registration's seed draws to its hidden installs (CE-11b, unit U2)

Step 4 and the end of the split chain of CE-11b design-v2 section 5.2. The eager split form `PqxdhDeploymentIdealKernel.idealSplitEager` draws the seed of a slot when the slot is first touched and later reads it without drawing (`xPeek`) to put the World's kernel on the published peer or the established owner. The final split form `idealSplit` draws the material of a slot at its first touch and the seed of a slot only at a hidden install that needs it: after the marked build when it published a peer (`serverInstall`) and after owner k's challenge finish when owner k is established (`beaconInstall`). `split_game` shows that both forms have the same law once the seed table is emptied, and `ideal_to_split` composes it with `PqxdhDeploymentIdealKernel.ideal_to_splitEager`: the ideal game and the final split game have the same law up to the split view.

- The erase engine with lists of points under an invariant (`completeList`, `discard_erase_list`), the list form of `PqxdhDeploymentSeedSplit.defer` (`PointedSeeds`, `defer_seeds`): a command may allocate no slot, one or two, so its pointed form reports the list of slots it allocated, and the factorisation holds only from well-formed states (`InvX`: the allocator's counter is at most two, every allocated slot lies below it, and every slot below it has its seed). The fixed steps keep the seed table (`fixed_seeds`) and so the invariant (`fixed_invX`), which holds initially (`initial_invX`).
- Eager against lazy reads (`eager_lazy`, `slotRunX_eager_lazy`): from a well-formed state, a slot program in front of the eager service is, in law, the program in front of the lazy service (`lazyDummy`, material only) followed by the seed draws of the slots it allocated, in order (`slotsFrom`).
- Installs (`xInstall`): read the seed of the slot of the hidden read's coordinates lazily, drawing it if absent, and apply the kernel fix when the gate holds. From a well-formed state the seed fix of the eager form is the install (`xInstall_peek`), because the fix is void when the gate is closed (`buildApply_void`, `stepApply_void`), and every install commutes with seed completions (`installStep_commutes`).
- `splitSeeds` pairs the eager split form with the pointed final form (`splitPointed`) and proves the three obligations; `splitSeeds_erased` identifies the erased handler with `idealSplit`.

These are equalities of laws of programs. They charge nothing and make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentBackend (XState RegImpl ctxLens seedLens handlerWith gameWith xinitial)
open PqxdhDeploymentIdealSlots (Coord SlotSpec SlotProgram slotCore detach attach)
open PqxdhDeploymentIdealSteps (realRegAt onSlots liftS)
open PqxdhRegistrationJointKemSecondEntry (Alloc slotImpl emptyAlloc)
open PqxdhDeploymentSeedSplit (SlotService MaterialSpec seedFree)
open PqxdhDeploymentFinishErasure (outcomeMap)
open LazyOracleDiscard (Commutes StateLens CacheLens LawEq Blind)
open PqxdhRecordLiftInterface (EnvQuery EnvSpec)

/-! ### Completing a list of points, and erasing completions of lists of points -/

section ListErase
variable {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec ι₀} [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)]
variable {σ : Type}

/-- Complete a list of points of the focused cache, in order. -/
noncomputable def completeList (L : CacheLens spec₀ σ) : List spec₀.Domain → σ → ProbComp σ
  | [], s => pure s
  | t :: rest, s => L.complete t s >>= completeList L rest

/-- A step that commutes with completions commutes with completing a list of points. -/
theorem commutes_completeList (L : CacheLens spec₀ σ) {α : Type} {step : StateT σ ProbComp α} (commutes : Commutes L step)
    (points : List spec₀.Domain) (s : σ) :
    LawEq (completeList L points s >>= step.run)
      (step.run s >>= fun r => (r.1, ·) <$> completeList L points r.2) := by
  induction points generalizing s with
  | nil =>
      simp only [completeList, pure_bind, map_pure, Prod.mk.eta, bind_pure]
      exact LawEq.refl _
  | cons t rest ih =>
      simp only [completeList, bind_assoc]
      refine (LawEq.bind (LawEq.refl _) fun s₁ => ih s₁).trans ?_
      rw [← bind_assoc]
      refine (LawEq.bind (commutes t s) fun r => LawEq.refl _).trans ?_
      simp only [bind_assoc, bind_map_left, map_bind]
      exact LawEq.refl _

/-- A completion of a list of points followed by a commuting step and a blind continuation can be dropped. -/
theorem erase_tail_list (L : CacheLens spec₀ σ) {α γ : Type} {step : StateT σ ProbComp α} (commutes : Commutes L step)
    {k : α × σ → ProbComp γ} (blind : Blind L k) (points : List spec₀.Domain) (s : σ) :
    LawEq (completeList L points s >>= fun s' => step.run s' >>= k) (step.run s >>= k) := by
  induction points generalizing s with
  | nil =>
      simp only [completeList, pure_bind]
      exact LawEq.refl _
  | cons t rest ih =>
      simp only [completeList, bind_assoc]
      refine (LawEq.bind (LawEq.refl _) fun s₁ => ih s₁).trans ?_
      exact LazyOracleDiscard.erase_tail L commutes blind (some t) s

/-- Global erasure of discarded completions of lists of points, under an invariant (the list form of `LazyOracleDiscard.discard_erase`): if every query is, in law from a state satisfying the invariant, its pointed step followed by the completion of the reported points, the invariant holds after that, and every pointed step commutes with completions, then the simulation with the handler and with the pointed steps without their points have the same law before every blind continuation. -/
theorem discard_erase_list {ι' : Type} {spec' : OracleSpec ι'} {α γ : Type} (L : CacheLens spec₀ σ) (inv : σ → Prop)
    (H : QueryImpl spec' (StateT σ ProbComp))
    (H₁ : (q : spec'.Domain) → StateT σ ProbComp (spec'.Range q × List spec₀.Domain))
    (factor : ∀ q s, inv s → LawEq ((H q).run s) ((H₁ q).run s >>= fun r => (r.1.1, ·) <$> completeList L r.1.2 r.2))
    (keeps : ∀ q s, inv s → ∀ r ∈ support ((H₁ q).run s >>= fun r => (r.1.1, ·) <$> completeList L r.1.2 r.2), inv r.2)
    (oblivious : ∀ q, Commutes L (Prod.fst <$> H₁ q))
    (k : α × σ → ProbComp γ) (blind : Blind L k) (oa : OracleComp spec' α) (s : σ) (holds : inv s) :
    LawEq ((simulateQ H oa).run s >>= k)
      ((simulateQ (fun q => Prod.fst <$> H₁ q : QueryImpl spec' (StateT σ ProbComp)) oa).run s >>= k) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => exact LawEq.refl _
  | query_bind q next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, bind_assoc]
      refine (LawEq.bind (factor q s holds) (fun r => LawEq.refl _)).trans ?_
      refine (PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun r member => ih r.1 r.2 (keeps q s holds r member)).trans ?_
      rw [StateT.run_map, bind_assoc, bind_map_left]
      refine LawEq.bind (LawEq.refl _) (fun r => ?_)
      rw [bind_map_left]
      exact erase_tail_list L (LazyOracleDiscard.commutes_simulateQ L _ oblivious (next r.1.1)) blind r.1.2 r.2

end ListErase


/-! ### The seed deferral with lists of points under an invariant -/

section DeferList
variable {KemSK Bk : Type} {n : ℕ}
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
open PqxdhDeploymentInterface (Spec FreshBounds Mode ModeSpec asModeO)

/-- The fixed steps keep the hidden-seed table. -/
theorem fixed_seeds (reg : RegImpl KemSK Bk n) (query : Spec.Domain)
    (notEnv : ∀ command : EnvQuery, query ≠ .inr command.val) (state : XState KemSK Bk n) :
    ∀ result ∈ support ((handlerWith setup codec route reg query).run state), result.2.seeds = state.seeds := by
  rcases query with coin | command
  · intro result member
    simp only [handlerWith, StateT.run_lift, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at member
    obtain ⟨_, _, rfl⟩ := member
    rfl
  · cases command
    case create pin keyId => exact absurd rfl (notEnv ⟨.create pin keyId, trivial⟩)
    case bundle owner => exact absurd rfl (notEnv ⟨.bundle owner, trivial⟩)
    case accept raw => exact absurd rfl (notEnv ⟨.accept raw, trivial⟩)
    case build session payload => exact absurd rfl (notEnv ⟨.build session payload, trivial⟩)
    case finish owner raw => exact absurd rfl (notEnv ⟨.finish owner raw, trivial⟩)
    case hmac key message => exact absurd rfl (notEnv ⟨.hmac key message, trivial⟩)
    all_goals
      intro result member
      simp only [handlerWith, PqxdhDeploymentBackend.onBase, StateLens.lift, PqxdhDeploymentBackend.baseLens,
        StateT.run, support_map, Set.mem_image] at member
      obtain ⟨_, _, rfl⟩ := member
      rfl

/-- A registration handler with a pointed form for the hidden-seed table whose steps report lists of slots, under an invariant: from a state satisfying the invariant each command is, in law, its pointed step followed by the completion of the reported slots' seeds; the invariant holds after that; and every pointed step commutes with seed completions. -/
structure PointedSeeds (inv : XState KemSK Bk n → Prop) where
  reg : RegImpl KemSK Bk n
  pointed : (query : EnvQuery) → StateT (XState KemSK Bk n) ProbComp (EnvSpec.Range query × List (PqxdhRecordLiftInterface.Slot n))
  factor : ∀ query x, inv x → LawEq ((reg query).run x)
    ((pointed query).run x >>= fun r => (r.1.1, ·) <$> completeList seedLens r.1.2 r.2)
  keeps : ∀ query x, inv x →
    ∀ r ∈ support ((pointed query).run x >>= fun r => (r.1.1, ·) <$> completeList seedLens r.1.2 r.2), inv r.2
  oblivious : ∀ query, Commutes seedLens (Prod.fst <$> pointed query)

/-- The erased handler: the pointed steps without their points. -/
noncomputable def PointedSeeds.erased {inv : XState KemSK Bk n → Prop} (pair : PointedSeeds inv) : RegImpl KemSK Bk n :=
  fun query => Prod.fst <$> pair.pointed query

/-- The pointed handler of the whole game: registration commands report their slots, the fixed steps none. -/
noncomputable def pointedWithSeeds {inv : XState KemSK Bk n → Prop} (pair : PointedSeeds inv) :
    (query : Spec.Domain) → StateT (XState KemSK Bk n) ProbComp (Spec.Range query × List (PqxdhRecordLiftInterface.Slot n))
  | .inr (.create pin keyId) => pair.pointed ⟨.create pin keyId, trivial⟩
  | .inr (.bundle owner) => pair.pointed ⟨.bundle owner, trivial⟩
  | .inr (.accept raw) => pair.pointed ⟨.accept raw, trivial⟩
  | .inr (.build session payload) => pair.pointed ⟨.build session payload, trivial⟩
  | .inr (.finish owner raw) => pair.pointed ⟨.finish owner raw, trivial⟩
  | .inr (.hmac key message) => pair.pointed ⟨.hmac key message, trivial⟩
  | query => (·, []) <$> handlerWith setup codec route pair.reg query

/-- Without its points, the pointed handler of the whole game is the handler with the erased registration handler. -/
theorem pointedWithSeeds_erased {inv : XState KemSK Bk n → Prop} (pair : PointedSeeds inv) :
    (fun query => Prod.fst <$> pointedWithSeeds setup codec route pair query : QueryImpl Spec _) =
      handlerWith setup codec route pair.erased := by
  funext query
  rcases query with coin | command
  · simp only [pointedWithSeeds, handlerWith, Functor.map_map, id_map']
  · cases command <;> simp only [pointedWithSeeds, handlerWith, PointedSeeds.erased, Functor.map_map, id_map'] <;> rfl

/-- The seed deferral with lists of points under an invariant (the list form of `PqxdhDeploymentSeedSplit.defer`): if each constructed Server's registration handler has a pointed form for the seed table under an invariant that holds initially and that the fixed steps keep, then the game with the handler and the game with its erased handler have the same law of the Server's public data, the output, the ledger and the final state with the seed table emptied. -/
theorem defer_seeds (inv : XState KemSK Bk n → Prop) (pair : PqxdhLiveServerConstruction.Created Unit → PointedSeeds inv)
    (init : PqxdhLiveServerConstruction.Created Unit → Bk) (initial : ∀ created, inv (xinitial created (init created)))
    (fixedKeeps : ∀ created (query : Spec.Domain), (∀ command : EnvQuery, query ≠ .inr command.val) →
      ∀ x, inv x → ∀ r ∈ support ((handlerWith setup codec route (pair created).reg query).run x), inv r.2)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    LawEq (outcomeMap seedFree <$> (gameWith setup codec route init (fun created => (pair created).reg) ensureInit
        identityIndex bounds mode adversary).run runtime)
      (outcomeMap seedFree <$> (gameWith setup codec route init (fun created => (pair created).erased) ensureInit
        identityIndex bounds mode adversary).run runtime) := by
  simp only [gameWith, StateT.run, map_bind]
  refine LawEq.bind (LawEq.refl _) fun born => ?_
  rcases born with ⟨_ | created, after⟩
  · exact LawEq.refl _
  · have erased := discard_erase_list seedLens inv (handlerWith setup codec route (pair created).reg)
      (pointedWithSeeds setup codec route (pair created)) (fun query x holds => ?factor)
      (fun query x holds => ?keeps) (fun query => ?oblivious)
      (fun r : (X × PqxdhDeploymentSecrecy.Ledger) × XState KemSK Bk n =>
        (pure (some (PqxdhRegistrationJointServerBirth.encode created, r.1.1, r.1.2, seedFree r.2), after) :
          ProbComp _))
      (fun a t s => by
        simp only [StateLens.complete, bind_map_left, PqxdhDeploymentSeedSplit.seedFree_set]
        exact LazyOracleDiscard.lawEq_drop _ _)
      (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode adversary))
      (xinitial created (init created)) (initial created)
    case factor =>
      rcases query with coin | command
      · exact LawEq.of_eq (by simp only [pointedWithSeeds, handlerWith, StateT.run_map, bind_map_left, completeList,
          map_pure, Prod.mk.eta, bind_pure])
      · cases command
        case create pin keyId => exact (pair created).factor _ x holds
        case bundle owner => exact (pair created).factor _ x holds
        case accept raw => exact (pair created).factor _ x holds
        case build session payload => exact (pair created).factor _ x holds
        case finish owner raw => exact (pair created).factor _ x holds
        case hmac key message => exact (pair created).factor _ x holds
        all_goals exact LawEq.of_eq (by simp only [pointedWithSeeds, StateT.run_map, bind_map_left, completeList,
          map_pure, Prod.mk.eta, bind_pure])
    case keeps =>
      have fixedCase : ∀ (query' : Spec.Domain), (∀ command : EnvQuery, query' ≠ .inr command.val) →
          ∀ r ∈ support ((((·, []) <$> handlerWith setup codec route (pair created).reg query' :
            StateT (XState KemSK Bk n) ProbComp (Spec.Range query' × List (PqxdhRecordLiftInterface.Slot n)))).run x >>=
              fun r => (r.1.1, ·) <$> completeList seedLens r.1.2 r.2), inv r.2 := by
        intro query' notEnv r member
        simp only [StateT.run_map, bind_map_left, completeList, map_pure, support_bind, support_pure,
          Set.mem_iUnion, Set.mem_singleton_iff] at member
        obtain ⟨inner, innerMember, rfl⟩ := member
        exact fixedKeeps created query' notEnv x holds inner innerMember
      rcases query with coin | command
      · exact fixedCase _ fun _ same => by cases same
      · cases command
        case create pin keyId => exact (pair created).keeps ⟨.create pin keyId, trivial⟩ x holds
        case bundle owner => exact (pair created).keeps ⟨.bundle owner, trivial⟩ x holds
        case accept raw => exact (pair created).keeps ⟨.accept raw, trivial⟩ x holds
        case build session payload =>
          exact (pair created).keeps ⟨.build session payload, trivial⟩ x holds
        case finish owner raw => exact (pair created).keeps ⟨.finish owner raw, trivial⟩ x holds
        case hmac key message => exact (pair created).keeps ⟨.hmac key message, trivial⟩ x holds
        all_goals exact fixedCase _ (fun command same => by cases command with | mk command isEnv => cases same; exact isEnv.elim)
    case oblivious =>
      have fixedCase : ∀ (query' : Spec.Domain), (∀ command : EnvQuery, query' ≠ .inr command.val) →
          Commutes seedLens (Prod.fst <$> ((·, []) <$> handlerWith setup codec route (pair created).reg query' :
            StateT (XState KemSK Bk n) ProbComp (Spec.Range query' × List (PqxdhRecordLiftInterface.Slot n)))) := by
        intro query' notEnv
        rw [Functor.map_map]
        simpa only [id_map'] using PqxdhDeploymentBackend.fixed_commute_seed setup codec route _ query' notEnv
      rcases query with coin | command
      · exact fixedCase _ fun _ same => by cases same
      · cases command
        case create pin keyId => exact (pair created).oblivious ⟨.create pin keyId, trivial⟩
        case bundle owner => exact (pair created).oblivious ⟨.bundle owner, trivial⟩
        case accept raw => exact (pair created).oblivious ⟨.accept raw, trivial⟩
        case build session payload => exact (pair created).oblivious ⟨.build session payload, trivial⟩
        case finish owner raw => exact (pair created).oblivious ⟨.finish owner raw, trivial⟩
        case hmac key message => exact (pair created).oblivious ⟨.hmac key message, trivial⟩
        all_goals exact fixedCase _ (fun command same => by cases command with | mk command isEnv => cases same; exact isEnv.elim)
    rw [pointedWithSeeds_erased] at erased
    simp only [StateT.run] at erased
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, outcomeMap, Option.map_some]
    exact erased

end DeferList


/-! ### Eager and lazy seed draws in front of the allocator -/

section EagerLazy
open PqxdhDeploymentIdealKernel (eagerDummy lazyDummy MatCache SeedCache)
open PqxdhDeploymentHiddenLayout (joinOutput splitOutput)
open PqxdhDeploymentHiddenSplit (dummySeed)
open PqxdhRegistrationJointKemSecondEntry (slot_some slot_none slot_coin)

/-- The seed table inside the allocator and service state. -/
abbrev pairSeeds : CacheLens (PqxdhRecordLiftWorld.SeedSpec 2) (Alloc Coord 2 × (MatCache 2 × SeedCache 2)) :=
  (StateLens.snd (Alloc Coord 2) (MatCache 2 × SeedCache 2)).comp (StateLens.snd (MatCache 2) (SeedCache 2))

/-- A well-formed allocator and service state: no more than two slots allocated, every allocated coordinate names a slot below the allocation counter, and every slot below the counter has its seed. -/
def Seeded (state : Alloc Coord 2 × (MatCache 2 × SeedCache 2)) : Prop :=
  state.1.2 ≤ 2 ∧ (∀ coords j, state.1.1 coords = some j → j.val < state.1.2) ∧
    ∀ j : PqxdhRecordLiftInterface.Slot 2, j.val < state.1.2 → (state.2.2 j).isSome

/-- The slots from one allocation counter to another, in order. -/
def slotsFrom (a b : ℕ) : List (PqxdhRecordLiftInterface.Slot 2) :=
  (List.range' a (b - a)).filterMap fun i => if h : i < 2 then some ⟨i, h⟩ else none

/-- No slot lies between a counter and itself. -/
theorem slotsFrom_self (a : ℕ) : slotsFrom a a = [] := by
  simp [slotsFrom]

/-- Below the target counter and with room left, the slots from a counter start with its slot. -/
theorem slotsFrom_cons (a b : ℕ) (below : a < b) (room : a < 2) :
    slotsFrom a b = ⟨a, room⟩ :: slotsFrom (a + 1) b := by
  have length : b - a = (b - (a + 1)) + 1 := by omega
  rw [slotsFrom, length, List.range'_succ, List.filterMap_cons]
  simp only [room, ↓reduceDIte]
  rfl

/-- At a slot with its seed, the eager service with dummy values is the lazy one. -/
theorem eagerDummy_present (j : PqxdhRecordLiftInterface.Slot 2) (state : MatCache 2 × SeedCache 2)
    (present : (state.2 j).isSome) : (eagerDummy j).run state = (lazyDummy j).run state := by
  obtain ⟨seed, found⟩ := Option.isSome_iff_exists.mp present
  simp only [eagerDummy, lazyDummy, PqxdhDeploymentSeedSplit.splitService, StateT.run_map, StateT.run_bind]
  have hit := LazyOracleDiscard.query_of_some found
  simp only [StateT.run] at hit
  simp only [StateLens.query, StateLens.fst, StateLens.snd, StateT.run, map_bind, bind_map_left, hit, pure_bind]
  rw [Functor.map_map, map_eq_bind_pure_comp]
  refine bind_congr fun a => ?_
  change (fun p => (joinOutput (splitOutput p.1).1 dummySeed, p.2)) <$>
    (pure (joinOutput a.1 seed, (a.2, state.2)) : ProbComp _) = _
  rw [map_pure, PqxdhDeploymentHiddenLayout.split_join]
  rfl


/-- The lazy service runs on the material cache alone. -/
theorem lazyDummy_run (j : PqxdhRecordLiftInterface.Slot 2) (state : MatCache 2 × SeedCache 2) :
    (lazyDummy j).run state =
      (fun r => (joinOutput r.1 dummySeed, (r.2, state.2))) <$> ((MaterialSpec 2).randomOracle j).run state.1 := by
  unfold lazyDummy
  rw [StateT.run_map]
  change (fun p => (joinOutput p.1 dummySeed, p.2)) <$>
    ((fun r => (r.1, (r.2, state.2))) <$> ((MaterialSpec 2).randomOracle j).run state.1) = _
  rw [Functor.map_map]

/-- The split service draws the material, then the seed, of the slot. -/
theorem splitService_run (j : PqxdhRecordLiftInterface.Slot 2) (state : MatCache 2 × SeedCache 2) :
    (PqxdhDeploymentSeedSplit.splitService j).run state =
      ((MaterialSpec 2).randomOracle j).run state.1 >>= fun a =>
        ((PqxdhRecordLiftWorld.SeedSpec 2).randomOracle j).run state.2 >>= fun b =>
          pure (joinOutput a.1 b.1, (a.2, b.2)) := by
  rw [PqxdhDeploymentSeedSplit.splitService, StateT.run_bind]
  change ((fun r => (r.1, (r.2, state.2))) <$> ((MaterialSpec 2).randomOracle j).run state.1) >>= _ = _
  rw [bind_map_left]
  refine bind_congr fun a => ?_
  rw [StateT.run_bind]
  change ((fun r => (r.1, (a.2, r.2))) <$> ((PqxdhRecordLiftWorld.SeedSpec 2).randomOracle j).run state.2) >>= _ = _
  rw [bind_map_left]
  rfl

/-- The eager service with dummy values is the lazy one followed by the completion of the slot's seed. -/
theorem eagerDummy_lazy (j : PqxdhRecordLiftInterface.Slot 2) (state : MatCache 2 × SeedCache 2) :
    (eagerDummy j).run state = (lazyDummy j).run state >>= fun q =>
      (q.1, ·) <$> (StateLens.snd (MatCache 2) (SeedCache 2)).complete j q.2 := by
  rw [lazyDummy_run, bind_map_left]
  unfold eagerDummy
  rw [StateT.run_map, splitService_run, map_bind]
  refine bind_congr fun a => ?_
  simp only [StateLens.complete, StateLens.snd, LazyOracleDiscard.complete,
    PqxdhDeploymentHiddenLayout.split_join, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]


/-- A stateful step that never reads or writes the focused cache simulates, whole programs, as such a step. -/
theorem simulateQ_frame {ι' σ' α : Type} {spec' : OracleSpec ι'} (L : CacheLens (PqxdhRecordLiftWorld.SeedSpec 2) σ')
    (impl : QueryImpl spec' (StateT σ' ProbComp))
    (frame : ∀ q s c, (impl q).run (L.set s c) = (fun r => (r.1, L.set r.2 c)) <$> (impl q).run s)
    (oa : OracleComp spec' α) (s : σ') (c : (PqxdhRecordLiftWorld.SeedSpec 2).QueryCache) :
    (simulateQ impl oa).run (L.set s c) = (fun r => (r.1, L.set r.2 c)) <$> (simulateQ impl oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind q next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, frame q s c, bind_map_left, map_bind, ih]

/-- The allocator in front of the lazy service never reads or writes the seed table. -/
theorem slotImpl_lazy_frame (query : SlotSpec.Domain) (state : Alloc Coord 2 × (MatCache 2 × SeedCache 2))
    (c : SeedCache 2) :
    (slotImpl lazyDummy query).run (pairSeeds.set state c) =
      (fun r => (r.1, pairSeeds.set r.2 c)) <$> (slotImpl lazyDummy query).run state := by
  rcases query with coin | coords
  · rw [slot_coin, slot_coin, Functor.map_map]
  · change (slotImpl lazyDummy (.inr coords)).run (state.1, (state.2.1, c)) = _
    rcases found : state.1.1 coords with _ | j
    · by_cases room : state.1.2 < 2
      · rw [slot_none (state := (state.1, (state.2.1, c))) _ _ found room, slot_none _ _ _ found room,
          lazyDummy_run, lazyDummy_run, Functor.map_map, Functor.map_map, Functor.map_map]
        rfl
      · simp only [slotImpl, QueryImpl.add_apply_inr, StateT.run_mk, found, room, _root_.dite_false,
          Functor.map_map]
        rfl
    · rw [slot_some (state := (state.1, (state.2.1, c))) _ _ _ found, slot_some _ _ _ _ found, lazyDummy_run,
        lazyDummy_run, Functor.map_map, Functor.map_map, Functor.map_map]
      rfl

/-- Every simulation in front of the lazy service commutes with completions of the seed table. -/
theorem simulateQ_lazy_commutes {α : Type} (oa : OracleComp SlotSpec α) :
    Commutes pairSeeds (simulateQ (slotImpl lazyDummy) oa) :=
  LazyOracleDiscard.commutes_frame _ _ fun s c =>
    simulateQ_frame pairSeeds (slotImpl lazyDummy) (fun q s c => slotImpl_lazy_frame q s c) oa s c

/-- The allocation counter never decreases. -/
theorem slotImpl_counter {S : Type} (svc : SlotService S 2) (query : SlotSpec.Domain) (state : Alloc Coord 2 × S) :
    ∀ r ∈ support ((slotImpl svc query).run state), state.1.2 ≤ r.2.1.2 := by
  intro r member
  rcases query with coin | coords
  · rw [slot_coin, support_map] at member
    obtain ⟨_, _, rfl⟩ := member
    exact le_refl _
  · rcases found : state.1.1 coords with _ | j
    · by_cases room : state.1.2 < 2
      · rw [slot_none _ _ _ found room, support_map] at member
        obtain ⟨_, _, rfl⟩ := member
        exact Nat.le_succ _
      · simp only [slotImpl, QueryImpl.add_apply_inr, StateT.run_mk, found, room, _root_.dite_false, support_map,
          Set.mem_image] at member
        obtain ⟨_, _, rfl⟩ := member
        exact le_refl _
    · rw [slot_some _ _ _ _ found, support_map] at member
      obtain ⟨_, _, rfl⟩ := member
      exact le_refl _

/-- The allocation counter never decreases along a simulation. -/
theorem simulateQ_counter {S α : Type} (svc : SlotService S 2) (oa : OracleComp SlotSpec α) (state : Alloc Coord 2 × S) :
    ∀ r ∈ support ((simulateQ (slotImpl svc) oa).run state), state.1.2 ≤ r.2.1.2 := by
  induction oa using OracleComp.inductionOn generalizing state with
  | pure a =>
      intro r member
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact le_refl _
  | query_bind q next ih =>
      intro r member
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at member
      obtain ⟨middle, middleMember, final⟩ := member
      exact le_trans (slotImpl_counter svc q state middle middleMember) (ih middle.1 middle.2 r final)


/-- After completing a point, it is present, and every present point stays present. -/
theorem complete_support (j : PqxdhRecordLiftInterface.Slot 2) (c : SeedCache 2) :
    ∀ c' ∈ support (LazyOracleDiscard.complete j c), (c' j).isSome ∧ ∀ i, (c i).isSome → (c' i).isSome := by
  intro c' member
  rw [LazyOracleDiscard.complete_run] at member
  rcases found : c j with _ | w
  · rw [found, support_map] at member
    obtain ⟨u, _, rfl⟩ := member
    refine ⟨by simp [QueryCache.cacheQuery_self], fun i present => ?_⟩
    by_cases same : i = j
    · subst same
      simp [QueryCache.cacheQuery_self]
    · change ((c.cacheQuery j u) i).isSome = true
      rw [QueryCache.cacheQuery_of_ne c u same]
      exact present
  · rw [found, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨by rw [found]; rfl, fun _ present => present⟩

/-- A read through the allocator in front of the lazy service at coordinates with a slot. -/
theorem slotImpl_lazy_found (coords : Coord) (state : Alloc Coord 2 × (MatCache 2 × SeedCache 2))
    (j : PqxdhRecordLiftInterface.Slot 2) (found : state.1.1 coords = some j) :
    (slotImpl lazyDummy (.inr coords)).run state =
      (fun r => (joinOutput r.1 dummySeed, (state.1, (r.2, state.2.2)))) <$>
        ((MaterialSpec 2).randomOracle j).run state.2.1 := by
  rw [slot_some _ _ _ _ found, lazyDummy_run, Functor.map_map]

/-- A read through the allocator in front of the lazy service at new coordinates with room. -/
theorem slotImpl_lazy_new (coords : Coord) (state : Alloc Coord 2 × (MatCache 2 × SeedCache 2))
    (found : state.1.1 coords = none) (room : state.1.2 < 2) :
    (slotImpl lazyDummy (.inr coords)).run state =
      (fun r => (joinOutput r.1 dummySeed, ((Function.update state.1.1 coords (some ⟨state.1.2, room⟩),
        state.1.2 + 1), (r.2, state.2.2)))) <$> ((MaterialSpec 2).randomOracle ⟨state.1.2, room⟩).run state.2.1 := by
  rw [slot_none _ _ _ found room, lazyDummy_run, Functor.map_map]

/-- A read through the allocator in front of the eager service at new coordinates with room: the lazy read, then the completion of the new slot's seed. -/
theorem slotImpl_eager_new (coords : Coord) (state : Alloc Coord 2 × (MatCache 2 × SeedCache 2))
    (found : state.1.1 coords = none) (room : state.1.2 < 2) :
    (slotImpl eagerDummy (.inr coords)).run state =
      ((MaterialSpec 2).randomOracle ⟨state.1.2, room⟩).run state.2.1 >>= fun r =>
        (fun c => (joinOutput r.1 dummySeed, ((Function.update state.1.1 coords (some ⟨state.1.2, room⟩),
          state.1.2 + 1), (r.2, c)))) <$> LazyOracleDiscard.complete ⟨state.1.2, room⟩ state.2.2 := by
  rw [slot_none _ _ _ found room, eagerDummy_lazy, lazyDummy_run, bind_map_left, map_bind]
  refine bind_congr fun r => ?_
  simp only [StateLens.complete, StateLens.snd, Functor.map_map]


/-- A well-formed state stays well-formed when its material changes. -/
theorem seeded_material (state : Alloc Coord 2 × (MatCache 2 × SeedCache 2)) (m : MatCache 2) (seeded : Seeded state) :
    Seeded (state.1, (m, state.2.2)) := seeded

/-- Allocating the next slot to new coordinates and completing its seed keeps the state well-formed. -/
theorem seeded_new (state : Alloc Coord 2 × (MatCache 2 × SeedCache 2)) (coords : Coord) (found : state.1.1 coords = none)
    (room : state.1.2 < 2) (m : MatCache 2) (seeded : Seeded state) :
    ∀ c ∈ support (LazyOracleDiscard.complete ⟨state.1.2, room⟩ state.2.2),
      Seeded ((Function.update state.1.1 coords (some ⟨state.1.2, room⟩), state.1.2 + 1), (m, c)) := by
  intro c member
  obtain ⟨newPresent, kept⟩ := complete_support _ _ c member
  obtain ⟨bound, assigned, present⟩ := seeded
  refine ⟨by simp only []; omega, fun coords' j' allocated => ?_, fun j' below => ?_⟩
  · simp only [] at allocated ⊢
    by_cases same : coords' = coords
    · subst same
      rw [Function.update_self] at allocated
      cases allocated
      simp
    · rw [Function.update_of_ne same] at allocated
      have := assigned coords' j' allocated
      omega
  · simp only [] at below
    by_cases top : j'.val = state.1.2
    · have : j' = ⟨state.1.2, room⟩ := Fin.ext top
      subst this
      exact newPresent
    · exact kept j' (present j' (by omega))


/-- Eager seed draws in front of the allocator are, in law, lazy ones followed by the completion of the seeds of the newly allocated slots (from a well-formed state). -/
theorem eager_lazy {α : Type} (oa : OracleComp SlotSpec α) :
    ∀ state, Seeded state → LawEq ((simulateQ (slotImpl eagerDummy) oa).run state)
      ((simulateQ (slotImpl lazyDummy) oa).run state >>= fun r =>
        (r.1, ·) <$> completeList pairSeeds (slotsFrom state.1.2 r.2.1.2) r.2) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro state _
      simp only [simulateQ_pure, StateT.run_pure, pure_bind, slotsFrom_self, completeList, map_pure]
      exact LawEq.refl _
  | query_bind q next ih =>
      intro state seeded
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, bind_assoc]
      rcases q with coin | coords
      · rw [slot_coin, slot_coin, bind_map_left, bind_map_left]
        exact LawEq.bind (LawEq.refl _) fun reply => ih reply state seeded
      · rcases found : state.1.1 coords with _ | j
        · by_cases room : state.1.2 < 2
          · rw [slotImpl_eager_new _ _ found room, slotImpl_lazy_new _ _ found room, bind_assoc, bind_map_left]
            refine LawEq.bind (LawEq.refl _) fun r => ?_
            rw [bind_map_left]
            refine (PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun c member =>
              ih _ _ (seeded_new state coords found room r.2 seeded c member)).trans ?_
            set start : Alloc Coord 2 × (MatCache 2 × SeedCache 2) :=
              ((Function.update state.1.1 coords (some ⟨state.1.2, room⟩), state.1.2 + 1), (r.2, state.2.2))
              with start_def
            have comm := simulateQ_lazy_commutes (next (joinOutput r.1 dummySeed)) ⟨state.1.2, room⟩ start
            have lhs : (LazyOracleDiscard.complete ⟨state.1.2, room⟩ state.2.2 >>= fun c =>
                (simulateQ (slotImpl lazyDummy) (next (joinOutput r.1 dummySeed))).run (start.1, (start.2.1, c)) >>=
                  fun r' => (r'.1, ·) <$> completeList pairSeeds (slotsFrom (state.1.2 + 1) r'.2.1.2) r'.2) =
                (pairSeeds.complete ⟨state.1.2, room⟩ start >>=
                  (simulateQ (slotImpl lazyDummy) (next (joinOutput r.1 dummySeed))).run) >>=
                    fun r' => (r'.1, ·) <$> completeList pairSeeds (slotsFrom (state.1.2 + 1) r'.2.1.2) r'.2 := by
              simp only [StateLens.complete, bind_map_left, bind_assoc]
              rfl
            rw [lhs]
            refine (LawEq.bind comm fun _ => LawEq.refl _).trans (LawEq.of_eq ?_)
            rw [bind_assoc]
            refine OracleComp.bind_congr_of_forall_mem_support _ fun r' member => ?_
            have grown := simulateQ_counter lazyDummy _ start r' member
            have below : state.1.2 < r'.2.1.2 := by
              have : start.1.2 = state.1.2 + 1 := rfl
              omega
            rw [slotsFrom_cons _ _ below room]
            simp only [completeList, StateLens.complete, bind_map_left, map_bind]
            rfl
          · have same : ∀ svc : SlotService (MatCache 2 × SeedCache 2) 2,
                (slotImpl svc (.inr coords)).run state =
                  (fun answer => (answer, state)) <$> ($ᵗ PqxdhServerAuthKeySchedule.Output) := by
              intro svc
              simp only [slotImpl, QueryImpl.add_apply_inr, StateT.run_mk, found, room, _root_.dite_false]
            rw [same, same, bind_map_left, bind_map_left]
            exact LawEq.bind (LawEq.refl _) fun answer => ih answer state seeded
        · have present : (state.2.2 j).isSome := seeded.2.2 j (seeded.2.1 coords j found)
          have eager : (slotImpl eagerDummy (.inr coords)).run state = (slotImpl lazyDummy (.inr coords)).run state := by
            rw [slot_some _ _ _ _ found, slot_some _ _ _ _ found, eagerDummy_present j state.2 present]
          rw [eager, slotImpl_lazy_found _ _ j found, bind_map_left, bind_map_left]
          exact LawEq.bind (LawEq.refl _) fun r => ih _ _ (seeded_material state r.2 seeded)

end EagerLazy


/-! ### Hidden installs of the final split form -/

section Install
variable {KemSK : Type}
open PqxdhDeploymentIdealKernel (xPeek slotRunX MatCache SeedCache eagerDummy lazyDummy)
open PqxdhRegistrationJointKemSecondEntry (slot_some slot_none slot_coin)
open PqxdhDeploymentIdealKeys (detachX attachX seedPut)
open PqxdhDeploymentIdealSteps (IdealCore SplitBk)

/-- A hidden install of the final split form: when `coords` names coordinates that have a slot and `gate` holds, the seed of the slot is read lazily from the seed table (drawn at this first read) and `apply` puts the World's kernel of it in; otherwise nothing changes. -/
noncomputable def xInstall {β : Type} (coords : β × XState KemSK IdealCore 2 → Option Coord)
    (gate : β × XState KemSK IdealCore 2 → Bool)
    (apply : PqxdhRecordLiftSeed.Seed → β × XState KemSK IdealCore 2 → β × XState KemSK IdealCore 2)
    (r : β × XState KemSK SplitBk 2) : ProbComp (β × XState KemSK SplitBk 2) :=
  match coords (r.1, detachX r.2) with
  | none => pure r
  | some c => match r.2.backend.2.1.1 c with
    | none => pure r
    | some j => if gate (r.1, detachX r.2) then
        (fun q => ((apply q.1 (r.1, detachX r.2)).1,
          attachX (apply q.1 (r.1, detachX r.2)).2 r.2.backend.2.1 (r.2.backend.1, q.2.seeds))) <$>
            (seedLens.query j).run r.2
      else pure r

/-- The hidden install as a stateful step, for a fixed value. -/
noncomputable def installStep {β : Type} (coords : β × XState KemSK IdealCore 2 → Option Coord)
    (gate : β × XState KemSK IdealCore 2 → Bool)
    (apply : PqxdhRecordLiftSeed.Seed → β × XState KemSK IdealCore 2 → β × XState KemSK IdealCore 2) (b : β) :
    StateT (XState KemSK SplitBk 2) ProbComp β := fun x => xInstall coords gate apply (b, x)

/-- The seed read and fix of a hidden install at a slot. -/
noncomputable def installAt {β : Type}
    (apply : PqxdhRecordLiftSeed.Seed → β × XState KemSK IdealCore 2 → β × XState KemSK IdealCore 2) (b : β)
    (j : PqxdhRecordLiftInterface.Slot 2) : StateT (XState KemSK SplitBk 2) ProbComp β := fun x =>
  (fun q => ((apply q.1 (b, detachX x)).1,
    attachX (apply q.1 (b, detachX x)).2 x.backend.2.1 (x.backend.1, q.2.seeds))) <$> (seedLens.query j).run x

/-- A hidden install commutes with completions of the seed table, whatever the value it fixes. -/
theorem installStep_commutes {β : Type} (coords : β × XState KemSK IdealCore 2 → Option Coord)
    (gate : β × XState KemSK IdealCore 2 → Bool)
    (apply : PqxdhRecordLiftSeed.Seed → β × XState KemSK IdealCore 2 → β × XState KemSK IdealCore 2) (b : β) :
    Commutes seedLens (installStep coords gate apply b) := by
  refine PqxdhDeploymentBackend.commutes_dispatch seedLens _
    (fun x => (coords (b, detachX x), x.backend.2.1.1, gate (b, detachX x))) (fun _ _ => rfl)
    (fun d => match d.1 with
      | none => pure b
      | some c => match d.2.1 c with
        | none => pure b
        | some j => if d.2.2 then installAt apply b j else pure b) (fun x => ?_) (fun d => ?_)
  · change xInstall coords gate apply (b, x) = _
    unfold xInstall
    simp only []
    rcases hc : coords (b, detachX x) with _ | c
    · simp only [StateT.run_pure]
    · simp only []
      rcases ha : x.backend.2.1.1 c with _ | j
      · simp only [StateT.run_pure]
      · simp only []
        cases hg : gate (b, detachX x)
        · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
        · simp only [↓reduceIte]
          rfl
  · rcases d with ⟨_ | c, allocation, open_⟩
    · exact LazyOracleDiscard.commutes_pure _ _
    · simp only []
      rcases allocation c with _ | j
      · exact LazyOracleDiscard.commutes_pure _ _
      · simp only []
        cases open_
        · exact LazyOracleDiscard.commutes_pure _ _
        · exact PqxdhDeploymentBackend.commutes_focus seedLens seedLens _ id (fun _ => seedLens.query j)
            (fun x s y => ((apply s (b, detachX x)).1, attachX (apply s (b, detachX x)).2 x.backend.2.1
              (x.backend.1, y.seeds))) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
            (fun _ _ _ _ => rfl) (fun _ => LazyOracleDiscard.commutes_query _ j)


/-- The well-formedness of the allocator and the seed table of an extended state of the split forms. -/
def InvX (x : XState KemSK SplitBk 2) : Prop := Seeded (x.backend.2.1, (x.backend.1, x.seeds))

/-- Every eager read keeps the allocator and service state well-formed. -/
theorem slotImpl_eager_keeps (query : SlotSpec.Domain) (state : Alloc Coord 2 × (MatCache 2 × SeedCache 2))
    (seeded : Seeded state) : ∀ r ∈ support ((slotImpl eagerDummy query).run state), Seeded r.2 := by
  intro r member
  rcases query with coin | coords
  · rw [slot_coin, support_map] at member
    obtain ⟨_, _, rfl⟩ := member
    exact seeded
  · rcases found : state.1.1 coords with _ | j
    · by_cases room : state.1.2 < 2
      · rw [slotImpl_eager_new _ _ found room] at member
        simp only [support_bind, Set.mem_iUnion, support_map, Set.mem_image] at member
        obtain ⟨m, _, c, cMember, rfl⟩ := member
        exact seeded_new state coords found room m.2 seeded c cMember
      · simp only [slotImpl, QueryImpl.add_apply_inr, StateT.run_mk, found, room, _root_.dite_false, support_map,
          Set.mem_image] at member
        obtain ⟨_, _, rfl⟩ := member
        exact seeded
    · have present : (state.2.2 j).isSome := seeded.2.2 j (seeded.2.1 coords j found)
      rw [slot_some _ _ _ _ found, eagerDummy_present j state.2 present, ← slot_some _ _ _ _ found,
        slotImpl_lazy_found _ _ j found, support_map] at member
      obtain ⟨m, _, rfl⟩ := member
      exact seeded_material state m.2 seeded

/-- A modification that keeps the modified element changes nothing. -/
theorem modify_keep {β : Type} (l : List β) (i : ℕ) (f : β → β) (keep : ∀ a, l[i]? = some a → f a = a) :
    l.modify i f = l := by
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_modify]
  by_cases same : i = k
  · subst same
    rcases found : l[i]? with _ | a
    · rfl
    · simp only [↓reduceIte, Option.map_eq_map, Option.map_some, keep a found]
  · simp only [same, ↓reduceIte, id_map']


/-- After an eager step the seed of every allocated coordinate is present, so a gated hidden install whose effect is void when its gate is closed is the seed fix read without drawing. -/
theorem xInstall_peek {β : Type} (coords : β × XState KemSK IdealCore 2 → Option Coord)
    (gate : β × XState KemSK IdealCore 2 → Bool)
    (apply : PqxdhRecordLiftSeed.Seed → β × XState KemSK IdealCore 2 → β × XState KemSK IdealCore 2)
    (void : ∀ seed r, gate r = false → apply seed r = r) (r : β × XState KemSK SplitBk 2) (holds : InvX r.2) :
    xInstall coords gate apply r = pure (xPeek coords apply r) := by
  unfold xInstall xPeek
  rcases coords (r.1, detachX r.2) with _ | c
  · rfl
  · simp only []
    rcases allocated : r.2.backend.2.1.1 c with _ | j
    · rfl
    · simp only []
      obtain ⟨seed, found⟩ := Option.isSome_iff_exists.mp (holds.2.2 j (holds.2.1 c j allocated))
      have hit : (seedLens.query j).run r.2 = pure (seed, r.2) := by
        change (fun q => (q.1, seedLens.set r.2 q.2)) <$> ((PqxdhRecordLiftWorld.SeedSpec 2).randomOracle j).run
          r.2.seeds = _
        rw [LazyOracleDiscard.query_of_some found, map_pure]
        rfl
      have found' : r.2.seeds j = some seed := found
      simp only [found', hit, map_pure]
      cases open_ : gate (r.1, detachX r.2)
      · simp only [Bool.false_eq_true, ↓reduceIte, void seed _ open_]
        rfl
      · simp only [↓reduceIte]

/-- The fix of the build has no effect unless the build published a peer. -/
theorem buildApply_void (seed : PqxdhRecordLiftSeed.Seed)
    (r : (Option PqxdhServerRegistrationPublication.Response × Option Coord) × XState KemSK IdealCore 2)
    (closed : (PqxdhDeploymentIdealSteps.publishedKey r.1.1 r.2.base.native.shared.2.server).isSome = false) :
    PqxdhDeploymentIdealKernel.buildApply seed r = r := by
  rcases r with ⟨⟨_ | response, coords⟩, x⟩
  · rfl
  · simp only [PqxdhDeploymentIdealSteps.publishedKey, Option.isSome_map, Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none] at closed
    have upd : Function.update x.base.native.shared.2.server.server.peers response.keyId none =
        x.base.native.shared.2.server.server.peers := by
      rw [← closed]
      exact Function.update_eq_self _ _
    simp only [PqxdhDeploymentIdealKernel.buildApply, PqxdhDeploymentIdealKernel.peerFix,
      PqxdhDeploymentHiddenSplit.setPeerKernel, closed, Option.map_none, upd]

/-- The fix of owner k's challenge finish has no effect unless owner k is established. -/
theorem stepApply_void (owner : ℕ) (seed : PqxdhRecordLiftSeed.Seed)
    (r : (Option Pqxdh.Bytes × Option Coord) × XState KemSK IdealCore 2)
    (closed : PqxdhDeploymentIdealSteps.establishedAt r.2.base.native.owners owner = false) :
    PqxdhDeploymentIdealKernel.stepApply owner seed r = r := by
  unfold PqxdhDeploymentIdealKernel.stepApply
  rw [modify_keep]
  intro a found
  unfold PqxdhDeploymentIdealSteps.establishedAt at closed
  rw [found] at closed
  unfold PqxdhDeploymentIdealKernel.setKernelAt PqxdhDeploymentIdealKernel.setOwnerKernel
  split
  · rename_i control data kernel phase
    simp only [phase, Bool.true_eq_false] at closed
  · rfl


/-- A map of states that carries one cache lens to another carries completions of lists of points. -/
theorem completeList_map {σ₁ σ₂ : Type} (L₁ : CacheLens (PqxdhRecordLiftWorld.SeedSpec 2) σ₁)
    (L₂ : CacheLens (PqxdhRecordLiftWorld.SeedSpec 2) σ₂) (g : σ₁ → σ₂)
    (get_g : ∀ s, L₂.get (g s) = L₁.get s) (set_g : ∀ s c, g (L₁.set s c) = L₂.set (g s) c)
    (points : List (PqxdhRecordLiftInterface.Slot 2)) (s : σ₁) :
    g <$> completeList L₁ points s = completeList L₂ points (g s) := by
  induction points generalizing s with
  | nil => simp only [completeList, map_pure]
  | cons t rest ih =>
      simp only [completeList, map_bind, ih]
      simp only [StateLens.complete, bind_map_left, get_g, set_g]

/-- The eager slot steps keep the allocator and the seed table well-formed. -/
theorem slotRunX_eager_keeps {β : Type} (step : StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) β)
    (x : XState KemSK SplitBk 2) (holds : InvX x) :
    ∀ r ∈ support ((slotRunX eagerDummy step).run x), InvX r.2 := by
  intro r member
  change r ∈ support ((fun r => (r.1, attachX r.2.1 r.2.2.1 r.2.2.2)) <$>
    (PqxdhDeploymentIdealErase.onPair eagerDummy step).run (detachX x, (x.backend.2.1, (x.backend.1, x.seeds)))) at member
  rw [PqxdhDeploymentIdealErase.onPair_run, Functor.map_map, support_map] at member
  obtain ⟨inner, innerMember, rfl⟩ := member
  exact PqxdhDeploymentIdealSlots.simulateQ_keeps (slotImpl eagerDummy) Seeded
    (fun q st seeded => slotImpl_eager_keeps q st seeded) _ _ holds inner innerMember

/-- The lazy slot steps never read or write the extended state's seed table. -/
theorem slotRunX_lazy_frame {β : Type} (step : StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) β)
    (x : XState KemSK SplitBk 2) (c : SeedCache 2) :
    (slotRunX lazyDummy step).run (seedLens.set x c) = (fun r => (r.1, seedLens.set r.2 c)) <$>
      (slotRunX lazyDummy step).run x := by
  change (fun r => (r.1, attachX r.2.1 r.2.2.1 r.2.2.2)) <$>
      (PqxdhDeploymentIdealErase.onPair lazyDummy step).run (detachX x,
        pairSeeds.set (x.backend.2.1, (x.backend.1, x.seeds)) c) =
    (fun r => (r.1, seedLens.set r.2 c)) <$> ((fun r => (r.1, attachX r.2.1 r.2.2.1 r.2.2.2)) <$>
      (PqxdhDeploymentIdealErase.onPair lazyDummy step).run (detachX x, (x.backend.2.1, (x.backend.1, x.seeds))))
  rw [PqxdhDeploymentIdealErase.onPair_run, PqxdhDeploymentIdealErase.onPair_run,
    simulateQ_frame pairSeeds (slotImpl lazyDummy) (fun q s c => slotImpl_lazy_frame q s c), Functor.map_map,
    Functor.map_map, Functor.map_map, Functor.map_map]
  rfl

/-- The lazy slot steps commute with completions of the extended state's seed table. -/
theorem slotRunX_lazy_commutes {β : Type} (step : StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) β) :
    Commutes seedLens (slotRunX lazyDummy step) :=
  LazyOracleDiscard.commutes_frame _ _ fun x c => slotRunX_lazy_frame step x c

/-- Eager slot steps are, in law, lazy ones followed by the completion of the seeds of the newly allocated slots, on the extended state (from a well-formed state). -/
theorem slotRunX_eager_lazy {β : Type} (step : StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) β)
    (x : XState KemSK SplitBk 2) (holds : InvX x) :
    LawEq ((slotRunX eagerDummy step).run x) ((slotRunX lazyDummy step).run x >>= fun r =>
      (r.1, ·) <$> completeList seedLens (slotsFrom x.backend.2.1.2 r.2.backend.2.1.2) r.2) := by
  change LawEq ((fun r => (r.1, attachX r.2.1 r.2.2.1 r.2.2.2)) <$>
      (PqxdhDeploymentIdealErase.onPair eagerDummy step).run (detachX x, (x.backend.2.1, (x.backend.1, x.seeds))))
    (((fun r => (r.1, attachX r.2.1 r.2.2.1 r.2.2.2)) <$>
      (PqxdhDeploymentIdealErase.onPair lazyDummy step).run (detachX x, (x.backend.2.1, (x.backend.1, x.seeds)))) >>=
        fun r => (r.1, ·) <$> completeList seedLens (slotsFrom x.backend.2.1.2 r.2.backend.2.1.2) r.2)
  rw [PqxdhDeploymentIdealErase.onPair_run, PqxdhDeploymentIdealErase.onPair_run, Functor.map_map, Functor.map_map,
    bind_map_left]
  refine ((eager_lazy (step.run (detachX x)) _ holds).map _).trans (LawEq.of_eq ?_)
  rw [map_bind]
  refine bind_congr fun r => ?_
  simp only [Functor.map_map]
  have moved := completeList_map pairSeeds (seedLens (KemSK := KemSK) (Bk := SplitBk) (n := 2))
    (fun st => attachX r.1.2 st.1 st.2) (fun _ => rfl) (fun _ _ => rfl) (slotsFrom x.backend.2.1.2 r.2.1.2) r.2
  have counter : (attachX r.1.2 r.2.1 r.2.2 : XState KemSK SplitBk 2).backend.2.1.2 = r.2.1.2 := rfl
  simp only [counter, ← moved, Functor.map_map]


/-- A partly well-formed state: well-formed allocator, and the seeds of the slots below `a` present, with `a` at most the counter. -/
def Partial (a : ℕ) (state : Alloc Coord 2 × (MatCache 2 × SeedCache 2)) : Prop :=
  state.1.2 ≤ 2 ∧ (∀ coords j, state.1.1 coords = some j → j.val < state.1.2) ∧
    (∀ j : PqxdhRecordLiftInterface.Slot 2, j.val < a → (state.2.2 j).isSome) ∧ a ≤ state.1.2

/-- Every lazy read keeps a state partly well-formed. -/
theorem slotImpl_lazy_keeps (a : ℕ) (query : SlotSpec.Domain) (state : Alloc Coord 2 × (MatCache 2 × SeedCache 2))
    (holds : Partial a state) : ∀ r ∈ support ((slotImpl lazyDummy query).run state), Partial a r.2 := by
  intro r member
  obtain ⟨bound, assigned, present, below⟩ := holds
  rcases query with coin | coords
  · rw [slot_coin, support_map] at member
    obtain ⟨_, _, rfl⟩ := member
    exact ⟨bound, assigned, present, below⟩
  · rcases found : state.1.1 coords with _ | j
    · by_cases room : state.1.2 < 2
      · rw [slotImpl_lazy_new _ _ found room, support_map] at member
        obtain ⟨m, _, rfl⟩ := member
        refine ⟨by simp only []; omega, fun coords' j' allocated => ?_, fun j' small => present j' small,
          by simp only []; omega⟩
        simp only [] at allocated ⊢
        by_cases same : coords' = coords
        · subst same
          rw [Function.update_self] at allocated
          cases allocated
          simp
        · rw [Function.update_of_ne same] at allocated
          have := assigned coords' j' allocated
          omega
      · simp only [slotImpl, QueryImpl.add_apply_inr, StateT.run_mk, found, room, _root_.dite_false, support_map,
          Set.mem_image] at member
        obtain ⟨_, _, rfl⟩ := member
        exact ⟨bound, assigned, present, below⟩
    · rw [slotImpl_lazy_found _ _ j found, support_map] at member
      obtain ⟨m, _, rfl⟩ := member
      exact ⟨bound, assigned, present, below⟩

/-- Completing a list of seeds of the extended state keeps its backend, makes the listed seeds present and keeps the present ones. -/
theorem completeList_support (points : List (PqxdhRecordLiftInterface.Slot 2)) (x : XState KemSK SplitBk 2) :
    ∀ x' ∈ support (completeList seedLens points x), x'.backend = x.backend ∧
      (∀ j ∈ points, (x'.seeds j).isSome) ∧ ∀ j, (x.seeds j).isSome → (x'.seeds j).isSome := by
  induction points generalizing x with
  | nil =>
      intro x' member
      simp only [completeList, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨rfl, fun j listed => by simp at listed, fun _ present => present⟩
  | cons t rest ih =>
      intro x' member
      simp only [completeList, StateLens.complete, support_bind, support_map, Set.mem_iUnion, Set.mem_image] at member
      obtain ⟨_, ⟨c, cMember, rfl⟩, final⟩ := member
      obtain ⟨tPresent, kept⟩ := complete_support t x.seeds c cMember
      obtain ⟨sameBackend, listed, keptLater⟩ := ih _ x' final
      refine ⟨sameBackend, fun j listedJ => ?_, fun j present => keptLater j (kept j present)⟩
      rcases List.mem_cons.mp listedJ with same | later
      · subst same
        exact keptLater _ tPresent
      · exact listed j later

/-- Every slot from one counter to another is listed. -/
theorem mem_slotsFrom (a b : ℕ) (j : PqxdhRecordLiftInterface.Slot 2) (low : a ≤ j.val) (high : j.val < b) :
    j ∈ slotsFrom a b := by
  simp only [slotsFrom, List.mem_filterMap, List.mem_range']
  refine ⟨j.val, ⟨j.val - a, by omega, by omega⟩, ?_⟩
  simp only [j.isLt, ↓reduceDIte]

/-- After the lazy slot steps from a well-formed state, the completion of the seeds of the newly allocated slots makes the state well-formed again (whatever install happened in between, as long as it kept the allocator and material and did not remove seeds). -/
theorem invX_complete (x y z : XState KemSK SplitBk 2)
    (lazy : Partial x.backend.2.1.2 (y.backend.2.1, (y.backend.1, y.seeds)))
    (allocSame : z.backend.2.1 = y.backend.2.1) (grow : ∀ j, (y.seeds j).isSome → (z.seeds j).isSome) :
    ∀ w ∈ support (completeList seedLens (slotsFrom x.backend.2.1.2 y.backend.2.1.2) z), InvX w := by
  intro w member
  obtain ⟨sameBackend, listed, kept⟩ := completeList_support _ z w member
  obtain ⟨bound, assigned, present, below⟩ := lazy
  have alloc : w.backend.2.1 = y.backend.2.1 := by rw [sameBackend, allocSame]
  refine ⟨by rw [alloc]; exact bound, fun coords j allocated => ?_, fun j small => ?_⟩
  · rw [alloc] at allocated ⊢
    exact assigned coords j allocated
  · change j.val < w.backend.2.1.2 at small
    rw [alloc] at small
    by_cases old : j.val < x.backend.2.1.2
    · exact kept j (grow j (present j old))
    · exact listed j (mem_slotsFrom _ _ j (by omega) small)


/-- A lazy query keeps every present point present. -/
theorem query_grows (u : PqxdhRecordLiftInterface.Slot 2) (cache : SeedCache 2) :
    ∀ q ∈ support (((PqxdhRecordLiftWorld.SeedSpec 2).randomOracle u).run cache),
      ∀ t, (cache t).isSome → (q.2 t).isSome := by
  intro q member t present
  rcases found : cache u with _ | w
  · rw [LazyOracleDiscard.query_of_none found] at member
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at member
    obtain ⟨y, _, rfl⟩ := member
    by_cases same : t = u
    · subst same
      simp [QueryCache.cacheQuery_self]
    · change ((cache.cacheQuery u y) t).isSome = true
      rw [QueryCache.cacheQuery_of_ne cache y same]
      exact present
  · rw [LazyOracleDiscard.query_of_some found, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact present

/-- A hidden install keeps the allocator and the material and keeps every present seed present. -/
theorem xInstall_support {β : Type} (coords : β × XState KemSK IdealCore 2 → Option Coord)
    (gate : β × XState KemSK IdealCore 2 → Bool)
    (apply : PqxdhRecordLiftSeed.Seed → β × XState KemSK IdealCore 2 → β × XState KemSK IdealCore 2)
    (r : β × XState KemSK SplitBk 2) :
    ∀ r' ∈ support (xInstall coords gate apply r), r'.2.backend.2.1 = r.2.backend.2.1 ∧
      r'.2.backend.1 = r.2.backend.1 ∧ ∀ j, (r.2.seeds j).isSome → (r'.2.seeds j).isSome := by
  intro r' member
  unfold xInstall at member
  split at member
  · rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, rfl, fun _ present => present⟩
  · split at member
    · rw [support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨rfl, rfl, fun _ present => present⟩
    · split at member
      · rename_i j _ _
        rw [support_map] at member
        obtain ⟨q, qMember, rfl⟩ := member
        change q ∈ support ((fun q => (q.1, seedLens.set r.2 q.2)) <$>
          ((PqxdhRecordLiftWorld.SeedSpec 2).randomOracle j).run r.2.seeds) at qMember
        rw [support_map] at qMember
        obtain ⟨inner, innerMember, rfl⟩ := qMember
        exact ⟨rfl, rfl, query_grows j r.2.seeds inner innerMember⟩
      · rw [support_pure, Set.mem_singleton_iff] at member
        subst member
        exact ⟨rfl, rfl, fun _ present => present⟩

/-- The lazy slot steps keep a state partly well-formed. -/
theorem slotRunX_lazy_keeps {β : Type} (a : ℕ) (step : StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) β)
    (x : XState KemSK SplitBk 2) (holds : Partial a (x.backend.2.1, (x.backend.1, x.seeds))) :
    ∀ r ∈ support ((slotRunX lazyDummy step).run x), Partial a (r.2.backend.2.1, (r.2.backend.1, r.2.seeds)) := by
  intro r member
  change r ∈ support ((fun r => (r.1, attachX r.2.1 r.2.2.1 r.2.2.2)) <$>
    (PqxdhDeploymentIdealErase.onPair lazyDummy step).run (detachX x, (x.backend.2.1, (x.backend.1, x.seeds)))) at member
  rw [PqxdhDeploymentIdealErase.onPair_run, Functor.map_map, support_map] at member
  obtain ⟨inner, innerMember, rfl⟩ := member
  exact PqxdhDeploymentIdealSlots.simulateQ_keeps (slotImpl lazyDummy) (Partial a)
    (fun q st partial_ => slotImpl_lazy_keeps a q st partial_) _ _ holds inner innerMember

/-- A well-formed state is partly well-formed up to its counter. -/
theorem partial_of_inv (x : XState KemSK SplitBk 2) (holds : InvX x) :
    Partial x.backend.2.1.2 (x.backend.2.1, (x.backend.1, x.seeds)) :=
  ⟨holds.1, holds.2.1, holds.2.2, le_refl _⟩

end Install



section Generic
variable {KemSK : Type}
open PqxdhDeploymentIdealKernel (xPeek slotRunX MatCache SeedCache eagerDummy lazyDummy)
open PqxdhDeploymentIdealSteps (IdealCore SplitBk)

/-- The factor obligation of a slot step followed by a hidden install: from a well-formed state, the eager slot step with the seed fix read without drawing is, in law, the lazy slot step with the hidden install, followed by the completion of the seeds of the newly allocated slots. -/
theorem install_factor {β γ : Type} (step : StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) β) (out : β → γ)
    (coords : β × XState KemSK IdealCore 2 → Option Coord) (gate : β × XState KemSK IdealCore 2 → Bool)
    (apply : PqxdhRecordLiftSeed.Seed → β × XState KemSK IdealCore 2 → β × XState KemSK IdealCore 2)
    (void : ∀ seed r, gate r = false → apply seed r = r) (x : XState KemSK SplitBk 2) (holds : InvX x) :
    LawEq ((fun r => (out r.1, r.2)) <$> (xPeek coords apply <$> (slotRunX eagerDummy step).run x))
      (((slotRunX lazyDummy step).run x >>= fun r =>
        (fun r' => ((out r'.1, slotsFrom x.backend.2.1.2 r.2.backend.2.1.2), r'.2)) <$> xInstall coords gate apply r) >>=
          fun r => (r.1.1, ·) <$> completeList seedLens r.1.2 r.2) := by
  have peeked : xPeek coords apply <$> (slotRunX eagerDummy step).run x =
      (slotRunX eagerDummy step).run x >>= xInstall coords gate apply := by
    rw [map_eq_bind_pure_comp]
    refine OracleComp.bind_congr_of_forall_mem_support _ fun r member => ?_
    exact (xInstall_peek coords gate apply void r (slotRunX_eager_keeps step x holds r member)).symm
  rw [peeked]
  refine (LawEq.map _ (LawEq.bind (slotRunX_eager_lazy step x holds) fun _ => LawEq.refl _)).trans ?_
  simp only [bind_assoc, bind_map_left, map_bind]
  refine LawEq.bind (LawEq.refl _) fun r => ?_
  have swapped := commutes_completeList seedLens (installStep_commutes coords gate apply r.1)
    (slotsFrom x.backend.2.1.2 r.2.backend.2.1.2) r.2
  refine (LawEq.of_eq ?_).trans ((LawEq.map (fun r => (out r.1, r.2)) swapped).trans (LawEq.of_eq ?_))
  · simp only [map_bind]
    rfl
  · simp only [map_bind, Functor.map_map]
    rfl

/-- The keeps obligation of a slot step followed by a hidden install. -/
theorem install_keeps {β γ : Type} (step : StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) β) (out : β → γ)
    (coords : β × XState KemSK IdealCore 2 → Option Coord) (gate : β × XState KemSK IdealCore 2 → Bool)
    (apply : PqxdhRecordLiftSeed.Seed → β × XState KemSK IdealCore 2 → β × XState KemSK IdealCore 2)
    (x : XState KemSK SplitBk 2) (holds : InvX x) :
    ∀ w ∈ support (((slotRunX lazyDummy step).run x >>= fun r =>
        (fun r' => ((out r'.1, slotsFrom x.backend.2.1.2 r.2.backend.2.1.2), r'.2)) <$> xInstall coords gate apply r) >>=
          fun r => (r.1.1, ·) <$> completeList seedLens r.1.2 r.2), InvX w.2 := by
  intro w member
  simp only [bind_assoc, bind_map_left, mem_support_bind_iff, support_map, Set.mem_image] at member
  obtain ⟨r, rMember, r', r'Member, final⟩ := member
  obtain ⟨z, zMember, rfl⟩ := final
  obtain ⟨allocSame, _, grow⟩ := xInstall_support coords gate apply r r' r'Member
  exact invX_complete x r.2 r'.2 (slotRunX_lazy_keeps _ step x (partial_of_inv x holds) r rMember) allocSame grow z
    zMember

/-- The oblivious obligation of a slot step followed by a hidden install. -/
theorem install_oblivious {β γ : Type} (step : StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) β) (out : β → γ)
    (coords : β × XState KemSK IdealCore 2 → Option Coord) (gate : β × XState KemSK IdealCore 2 → Bool)
    (apply : PqxdhRecordLiftSeed.Seed → β × XState KemSK IdealCore 2 → β × XState KemSK IdealCore 2) :
    Commutes seedLens (slotRunX lazyDummy step >>= fun b => out <$> installStep coords gate apply b) :=
  LazyOracleDiscard.commutes_bind _ (slotRunX_lazy_commutes step) fun b =>
    LazyOracleDiscard.commutes_map _ _ (installStep_commutes coords gate apply b)

/-- The factor obligation of a slot step without install. -/
theorem plain_factor {β : Type} (step : StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) β)
    (x : XState KemSK SplitBk 2) (holds : InvX x) :
    LawEq ((slotRunX eagerDummy step).run x)
      (((fun r => ((r.1, slotsFrom x.backend.2.1.2 r.2.backend.2.1.2), r.2)) <$> (slotRunX lazyDummy step).run x) >>=
        fun r => (r.1.1, ·) <$> completeList seedLens r.1.2 r.2) := by
  rw [bind_map_left]
  exact slotRunX_eager_lazy step x holds

/-- The keeps obligation of a slot step without install. -/
theorem plain_keeps {β : Type} (step : StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) β)
    (x : XState KemSK SplitBk 2) (holds : InvX x) :
    ∀ w ∈ support (((fun r => ((r.1, slotsFrom x.backend.2.1.2 r.2.backend.2.1.2), r.2)) <$>
        (slotRunX lazyDummy step).run x) >>= fun r => (r.1.1, ·) <$> completeList seedLens r.1.2 r.2), InvX w.2 := by
  intro w member
  simp only [bind_map_left, mem_support_bind_iff, support_map, Set.mem_image] at member
  obtain ⟨r, rMember, z, zMember, rfl⟩ := member
  exact invX_complete x r.2 r.2 (slotRunX_lazy_keeps _ step x (partial_of_inv x holds) r rMember) rfl
    (fun _ present => present) z zMember

end Generic

/-! ### The final split form and the seed deferral -/

section SplitForm
variable {KemSK : Type} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhDeploymentIdealKernel (xPeek slotRunX MatCache SeedCache eagerDummy lazyDummy idealSplitEager buildStepC
  finishStepC buildApply stepApply slotCoreX_run)
open PqxdhDeploymentIdealKeys (detachX attachX)
open PqxdhDeploymentIdealSteps (IdealCore SplitBk idealProg erasedHidden publishedKey establishedAt)
open PqxdhDeploymentIdealParams (Target Params)

/-- The hidden Server install of the final split form: after the marked build, when it published a peer, the seed of the accept's slot is read lazily and the World's Server kernel of it is put on the peer. -/
noncomputable def serverInstall
    (r : (Option PqxdhServerRegistrationPublication.Response × Option Coord) × XState KemSK SplitBk 2) :
    ProbComp ((Option PqxdhServerRegistrationPublication.Response × Option Coord) × XState KemSK SplitBk 2) :=
  xInstall (fun r => r.1.2) (fun r => (publishedKey r.1.1 r.2.base.native.shared.2.server).isSome) buildApply r

/-- The hidden Beacon install of the final split form: after owner k's challenge finish, when owner k is established, the seed of the slot of its hidden read is read lazily and the World's Beacon kernel of it is put on the owner. -/
noncomputable def beaconInstall (owner : ℕ) (r : (Option Pqxdh.Bytes × Option Coord) × XState KemSK SplitBk 2) :
    ProbComp ((Option Pqxdh.Bytes × Option Coord) × XState KemSK SplitBk 2) :=
  xInstall (fun r => r.1.2) (fun r => establishedAt r.2.base.native.owners owner) (stepApply owner) r

/-- The final split form of the ideal registration (design-v2 section 5.2): the C7-erased slot program in front of the lazy service (the material of a slot drawn at its first touch, the seed never), with the marked build and owner k's challenge finish followed by their hidden installs, which draw the seed of the slot at the install. -/
noncomputable def idealSplit (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) : RegImpl KemSK SplitBk 2
  | ⟨.build session payload, _⟩ => fun x => (fun r => (r.1.1, r.2)) <$>
      ((slotRunX lazyDummy (buildStepC setup codec checks route (erasedHidden setup codec checks) created session
        payload)).run x >>= serverInstall)
  | ⟨.finish owner raw, _⟩ => fun x => (fun r => (r.1.1, r.2)) <$>
      ((slotRunX lazyDummy (finishStepC setup codec checks route t p (erasedHidden setup codec checks) created owner
        raw)).run x >>= beaconInstall owner)
  | query => PqxdhDeploymentIdealKeys.slotCoreX (idealProg setup codec route checks t p (erasedHidden setup codec checks))
      lazyDummy created query

/-- The pointed form of the final split form for the seed deferral: each command reports the slots it newly allocated. -/
noncomputable def splitPointed (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) :
    (query : EnvQuery) → StateT (XState KemSK SplitBk 2) ProbComp (EnvSpec.Range query × List (PqxdhRecordLiftInterface.Slot 2))
  | ⟨.build session payload, _⟩ => fun x =>
      (slotRunX lazyDummy (buildStepC setup codec checks route (erasedHidden setup codec checks) created session
        payload)).run x >>= fun r =>
          (fun r' => ((r'.1.1, slotsFrom x.backend.2.1.2 r.2.backend.2.1.2), r'.2)) <$> serverInstall r
  | ⟨.finish owner raw, _⟩ => fun x =>
      (slotRunX lazyDummy (finishStepC setup codec checks route t p (erasedHidden setup codec checks) created owner
        raw)).run x >>= fun r =>
          (fun r' => ((r'.1.1, slotsFrom x.backend.2.1.2 r.2.backend.2.1.2), r'.2)) <$> beaconInstall owner r
  | query => fun x => (fun r => ((r.1, slotsFrom x.backend.2.1.2 r.2.backend.2.1.2), r.2)) <$>
      (slotRunX lazyDummy (idealProg setup codec route checks t p (erasedHidden setup codec checks) created query)).run x



/-- Without its points, the pointed form of a command without install is the lazy slot step, which commutes with seed completions. -/
theorem plain_oblivious (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : EnvQuery)
    (shape : splitPointed setup codec route checks t p created query = fun x =>
      (fun r => ((r.1, slotsFrom x.backend.2.1.2 r.2.backend.2.1.2), r.2)) <$>
        (slotRunX lazyDummy (idealProg setup codec route checks t p (erasedHidden setup codec checks) created query)).run x) :
    Commutes seedLens (Prod.fst <$> splitPointed setup codec route checks t p created query) := by
  have plain : (Prod.fst <$> splitPointed setup codec route checks t p created query) =
      slotRunX lazyDummy (idealProg setup codec route checks t p (erasedHidden setup codec checks) created query) := by
    apply StateT.ext
    intro x
    rw [StateT.run_map, shape]
    change (fun r => (r.1.1, r.2)) <$> ((fun r => ((r.1, slotsFrom x.backend.2.1.2 r.2.backend.2.1.2), r.2)) <$>
      (slotRunX lazyDummy _).run x) = _
    rw [Functor.map_map]
    exact id_map _
  rw [plain]
  exact slotRunX_lazy_commutes _

/-- The deferral pair of the ideal registration: the eager split form with its pointed lazy form, under the well-formedness of the allocator and the seed table. -/
noncomputable def splitSeeds (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) : PointedSeeds (InvX (KemSK := KemSK)) where
  reg := idealSplitEager setup codec route checks t p created
  pointed := splitPointed setup codec route checks t p created
  factor query x holds := by
    rcases query with ⟨command, isEnv⟩
    cases command
    case build session payload =>
      exact install_factor _ (fun r => r.1) _ _ _ (fun seed r closed => buildApply_void seed r closed) x holds
    case finish owner raw =>
      exact install_factor _ (fun r => r.1) _ _ _ (fun seed r closed => stepApply_void owner seed r closed) x holds
    case create pin keyId =>
      change LawEq ((PqxdhDeploymentIdealKeys.slotCoreX _ eagerDummy created _).run x) _
      rw [slotCoreX_run]
      exact plain_factor _ x holds
    case bundle owner =>
      change LawEq ((PqxdhDeploymentIdealKeys.slotCoreX _ eagerDummy created _).run x) _
      rw [slotCoreX_run]
      exact plain_factor _ x holds
    case accept raw =>
      change LawEq ((PqxdhDeploymentIdealKeys.slotCoreX _ eagerDummy created _).run x) _
      rw [slotCoreX_run]
      exact plain_factor _ x holds
    case hmac key message =>
      change LawEq ((PqxdhDeploymentIdealKeys.slotCoreX _ eagerDummy created _).run x) _
      rw [slotCoreX_run]
      exact plain_factor _ x holds
    all_goals exact absurd isEnv id
  keeps query x holds := by
    rcases query with ⟨command, isEnv⟩
    cases command
    case build session payload =>
      exact install_keeps (buildStepC setup codec checks route (erasedHidden setup codec checks) created session payload)
        (fun r : Option PqxdhServerRegistrationPublication.Response × Option Coord => r.1) (fun r => r.1.2)
        (fun r => (publishedKey r.1.1 r.2.base.native.shared.2.server).isSome) buildApply x holds
    case finish owner raw =>
      exact install_keeps (finishStepC setup codec checks route t p (erasedHidden setup codec checks) created owner raw)
        (fun r : Option Pqxdh.Bytes × Option Coord => r.1) (fun r => r.1.2)
        (fun r => establishedAt r.2.base.native.owners owner) (stepApply owner) x holds
    case create pin keyId => exact plain_keeps _ x holds
    case bundle owner => exact plain_keeps _ x holds
    case accept raw => exact plain_keeps _ x holds
    case hmac key message => exact plain_keeps _ x holds
    all_goals exact absurd isEnv id
  oblivious query := by
    rcases query with ⟨command, isEnv⟩
    cases command
    case build session payload =>
      have shape : (Prod.fst <$> splitPointed setup codec route checks t p created ⟨.build session payload, isEnv⟩) =
          (slotRunX lazyDummy (buildStepC setup codec checks route (erasedHidden setup codec checks) created session
            payload) >>= fun b => (fun c : Option PqxdhServerRegistrationPublication.Response × Option Coord => c.1) <$>
              installStep (fun r => r.1.2) (fun r => (publishedKey r.1.1 r.2.base.native.shared.2.server).isSome)
                buildApply b) := by
        apply StateT.ext
        intro x
        rw [StateT.run_map, StateT.run_bind]
        simp only [StateT.run_map]
        simp only [splitPointed, StateT.run, installStep, serverInstall, map_bind, Functor.map_map]
      rw [shape]
      exact install_oblivious _ _ _ _ _
    case finish owner raw =>
      have shape : (Prod.fst <$> splitPointed setup codec route checks t p created ⟨.finish owner raw, isEnv⟩) =
          (slotRunX lazyDummy (finishStepC setup codec checks route t p (erasedHidden setup codec checks) created owner
            raw) >>= fun b => (fun c : Option Pqxdh.Bytes × Option Coord => c.1) <$>
              installStep (fun r => r.1.2) (fun r => establishedAt r.2.base.native.owners owner) (stepApply owner) b) := by
        apply StateT.ext
        intro x
        rw [StateT.run_map, StateT.run_bind]
        simp only [StateT.run_map]
        simp only [splitPointed, StateT.run, installStep, beaconInstall, map_bind, Functor.map_map]
      rw [shape]
      exact install_oblivious _ _ _ _ _
    case create pin keyId => exact plain_oblivious setup codec route checks t p created _ rfl
    case bundle owner => exact plain_oblivious setup codec route checks t p created _ rfl
    case accept raw => exact plain_oblivious setup codec route checks t p created _ rfl
    case hmac key message => exact plain_oblivious setup codec route checks t p created _ rfl
    all_goals exact absurd isEnv id


/-- The erased handler of the deferral pair is the final split form. -/
theorem splitSeeds_erased (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) :
    (splitSeeds setup codec route checks t p created).erased = idealSplit setup codec route checks t p created := by
  funext query
  apply StateT.ext
  intro x
  rcases query with ⟨command, isEnv⟩
  cases command
  case build session payload =>
    change (Prod.fst <$> splitPointed setup codec route checks t p created _).run x = _
    rw [StateT.run_map]
    simp only [splitPointed, idealSplit, StateT.run, map_bind, Functor.map_map]
  case finish owner raw =>
    change (Prod.fst <$> splitPointed setup codec route checks t p created _).run x = _
    rw [StateT.run_map]
    simp only [splitPointed, idealSplit, StateT.run, map_bind, Functor.map_map]
  all_goals
    first
    | exact absurd isEnv id
    | change (Prod.fst <$> splitPointed setup codec route checks t p created _).run x = _
      rw [StateT.run_map]
      simp only [splitPointed, idealSplit, StateT.run, Functor.map_map, slotCoreX_run]
      exact id_map _


/-- The fixed steps keep the well-formedness of the allocator and the seed table. -/
theorem fixed_invX (reg : RegImpl KemSK SplitBk 2) (query : PqxdhDeploymentInterface.Spec.Domain)
    (notEnv : ∀ command : EnvQuery, query ≠ .inr command.val) (x : XState KemSK SplitBk 2) (holds : InvX x) :
    ∀ r ∈ support ((handlerWith setup codec route reg query).run x), InvX r.2 := by
  intro r member
  have backend := PqxdhDeploymentSeedSplit.fixed_backend setup codec route reg query notEnv x r member
  have seeds := fixed_seeds setup codec route reg query notEnv x r member
  unfold InvX
  rw [backend, seeds]
  exact holds

/-- The initial state of the split form is well-formed: nothing allocated, no seed drawn. -/
theorem initial_invX (created : PqxdhLiveServerConstruction.Created Unit) :
    InvX (xinitial created (PqxdhDeploymentIdealSteps.splitInit created) : XState KemSK SplitBk 2) :=
  ⟨Nat.zero_le 2, fun _ _ none => by simp [xinitial, PqxdhDeploymentIdealSteps.splitInit, emptyAlloc] at none,
    fun _ lt => absurd lt (Nat.not_lt_zero _)⟩

/-- The seed deferral of the ideal registration (`split_game`, design-v2 section 5.2): the eager split form and the final split form, whose seeds are drawn at the hidden installs only, have the same law once the seed table is emptied. -/
theorem split_game {A X : Type} (t : Target count) (p : Params KemSK count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (runtime : A) :
    LawEq (outcomeMap seedFree <$> (gameWith setup codec route PqxdhDeploymentIdealSteps.splitInit
        (idealSplitEager setup codec route checks t p) ensureInit identityIndex bounds mode adversary).run runtime)
      (outcomeMap seedFree <$> (gameWith setup codec route PqxdhDeploymentIdealSteps.splitInit
        (idealSplit setup codec route checks t p) ensureInit identityIndex bounds mode adversary).run runtime) := by
  have erased : (fun created => (splitSeeds setup codec route checks t p created).erased) =
      idealSplit setup codec route checks t p :=
    funext fun created => splitSeeds_erased setup codec route checks t p created
  rw [← erased]
  exact defer_seeds setup codec route InvX (fun created => splitSeeds setup codec route checks t p created)
    PqxdhDeploymentIdealSteps.splitInit initial_invX
    (fun created query notEnv x holds => fixed_invX setup codec route _ query notEnv x holds)
    ensureInit identityIndex bounds mode adversary runtime

/-- The split view does not see the seed table. -/
theorem splitView_seedFree (x : XState KemSK SplitBk 2) :
    PqxdhDeploymentIdealKeys.splitView (seedFree x) = PqxdhDeploymentIdealKeys.splitView x := rfl

/-- The ideal registration and its final split form (`ideal_to_split`, design-v2 section 5.2): the ideal game and the split game with lazy materials and seeds drawn at the hidden installs have the same law up to the split view (the native state with the CTX cache emptied, together with the allocator and the ideal backend, the LQ-F snapshot and the log). -/
theorem ideal_to_split {A X : Type} (t : Target count) (p : Params KemSK count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (runtime : A) :
    LawEq (outcomeMap PqxdhDeploymentIdealKeys.splitView <$> (gameWith setup codec route
        PqxdhDeploymentIdealSteps.idealInit (PqxdhDeploymentIdealSteps.idealReg setup codec route checks t p) ensureInit
          identityIndex bounds mode adversary).run runtime)
      (outcomeMap PqxdhDeploymentIdealKeys.splitView <$> (gameWith setup codec route PqxdhDeploymentIdealSteps.splitInit
        (idealSplit setup codec route checks t p) ensureInit identityIndex bounds mode adversary).run runtime) := by
  have view : (outcomeMap (X := X) (A := A) PqxdhDeploymentIdealKeys.splitView :
      _ → Option (_ × X × _ × _) × A) = outcomeMap PqxdhDeploymentIdealKeys.splitView ∘ outcomeMap (X := X) (A := A)
        (seedFree (KemSK := KemSK) (Bk := SplitBk) (n := 2)) := by
    funext outcome
    rw [Function.comp_apply, PqxdhDeploymentIdealKeys.outcomeMap_comp]
    rfl
  refine (PqxdhDeploymentIdealKernel.ideal_to_splitEager setup codec route checks t p ensureInit identityIndex bounds mode
    adversary runtime).trans ?_
  rw [view, comp_map, comp_map]
  exact (split_game setup codec route checks t p ensureInit identityIndex bounds mode adversary runtime).map _

end SplitForm

end BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.commutes_completeList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.commutes_completeList

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.erase_tail_list' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.erase_tail_list

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.discard_erase_list' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.discard_erase_list

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.fixed_seeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.fixed_seeds

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.pointedWithSeeds_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.pointedWithSeeds_erased

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.defer_seeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.defer_seeds

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotsFrom_self' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotsFrom_self

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotsFrom_cons' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotsFrom_cons

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.eagerDummy_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.eagerDummy_present

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.lazyDummy_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.lazyDummy_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.splitService_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.splitService_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.eagerDummy_lazy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.eagerDummy_lazy

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.simulateQ_frame' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.simulateQ_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotImpl_lazy_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotImpl_lazy_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.simulateQ_lazy_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.simulateQ_lazy_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotImpl_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotImpl_counter

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.simulateQ_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.simulateQ_counter

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.complete_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.complete_support

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotImpl_lazy_found' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotImpl_lazy_found

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotImpl_lazy_new' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotImpl_lazy_new

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotImpl_eager_new' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotImpl_eager_new

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.seeded_material' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.seeded_material

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.seeded_new' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.seeded_new

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.eager_lazy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.eager_lazy

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.installStep_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.installStep_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotImpl_eager_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotImpl_eager_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.modify_keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.modify_keep

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.xInstall_peek' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.xInstall_peek

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.buildApply_void' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.buildApply_void

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.stepApply_void' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.stepApply_void

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.completeList_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.completeList_map

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotRunX_eager_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotRunX_eager_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotRunX_lazy_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotRunX_lazy_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotRunX_lazy_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotRunX_lazy_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotRunX_eager_lazy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotRunX_eager_lazy

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotImpl_lazy_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotImpl_lazy_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.completeList_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.completeList_support

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.mem_slotsFrom' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.mem_slotsFrom

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.invX_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.invX_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.query_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.query_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.xInstall_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.xInstall_support

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotRunX_lazy_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.slotRunX_lazy_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.partial_of_inv' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.partial_of_inv

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.install_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.install_factor

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.install_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.install_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.install_oblivious' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.install_oblivious

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.plain_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.plain_factor

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.plain_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.plain_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.plain_oblivious' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.plain_oblivious

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.splitSeeds_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.splitSeeds_erased

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.fixed_invX' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.fixed_invX

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.initial_invX' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.initial_invX

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.split_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.split_game

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.splitView_seedFree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.splitView_seedFree

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.ideal_to_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer.ideal_to_split
