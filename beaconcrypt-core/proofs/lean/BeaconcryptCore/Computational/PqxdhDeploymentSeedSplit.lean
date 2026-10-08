-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure

/-!
# The 108-byte split of the hidden slots and the seed deferral (generic form)

A slot service (`SlotService S n`) is how a registration handler obtains the 108-byte key-schedule output of a hidden slot from a service state `S` in its backend. Three services are compared: `tableService` is item 2's S7 persistent lazy table (`PqxdhRecordLiftLazyTable`, with query counts), `lazyService` is VCVio's lazily sampled cache of outputs, and `splitService` keeps the output as environment material (key32, nonce12) and a world seed (next32, right32), each lazily sampled at the first touch of the slot. `ServiceProj inv proj svc₁ svc₂` (critique M8's "touch" as a relation) says that the state projection `proj` carries every step of `svc₁` to the corresponding step of `svc₂` in law, from states satisfying `inv`, and preserves `inv`. The table forgets its counts (`table_service_proj`, by `LazyOracleDiscard.impl_project`), and the split joins material and seed whenever both or neither are present (`split_service_proj`, by the 108-byte bijection `PqxdhDeploymentHiddenLayout.uniform_split`).

`CoreNatural core` (M8's "uses" as a relation) says that a registration core reads slot outputs only through its service: every step of the core transports along every service projection. `represent` is the game-level transport: for a natural core, the game with one service and the game with another have the same law up to the service projection of the final state (`lawEq_run_simulateQ_of_proj` is the underlying transport in law of a simulation along a state projection gated by an invariant), and `represent_split` compares the table and the split representations through the lazy one. `defer` is the generic seed deferral: an instance of `PqxdhDeploymentFinishErasure.erase_game` at the hidden-seed lens, which erases seed completions that the handler reports as discarded, comparing final states with the seed table emptied.

The kernel identities of the split wrappers and the step "C7-erased factor form equals split form" that makes the seed completions discardable are not part of this module. These are equalities in law of lazily sampled caches and uniform bytes. No security claim is made here.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec Command ModeSpec Mode FreshBounds asModeO)
open PqxdhDeploymentBackend (XState RegImpl handlerWith gameWith xinitial seedLens)
open PqxdhDeploymentFinishErasure (PointedReg outcomeMap)
open PqxdhDeploymentHiddenLayout (Material joinOutput)
open LazyOracleDiscard (Commutes StateLens CacheLens LawEq)

/-! ### Transport in law along a state projection -/

/-- Law equality is a congruence for `bind` on the support of the prefix. -/
theorem LawEq.bind_support {α β : Type} (mx : ProbComp α) {f g : α → ProbComp β}
    (h : ∀ a ∈ support mx, LawEq (f a) (g a)) : LawEq (mx >>= f) (mx >>= g) := by
  intro γ _ k
  simp only [bind_assoc]
  exact OracleComp.evalDist_bind_congr_of_support mx _ _ fun a ha => h a ha γ k

/-- Invariant-gated transport in law of a simulation along a state projection (the law-level analogue of `OracleComp.map_run_simulateQ_eq_of_query_map_eq`). -/
theorem lawEq_run_simulateQ_of_proj {ι' σ₁ σ₂ α : Type} {spec' : OracleSpec ι'}
    (impl₁ : QueryImpl spec' (StateT σ₁ ProbComp)) (impl₂ : QueryImpl spec' (StateT σ₂ ProbComp))
    (inv : σ₁ → Prop) (proj : σ₁ → σ₂)
    (step : ∀ query state, inv state → LawEq (Prod.map id proj <$> (impl₁ query).run state) ((impl₂ query).run (proj state)))
    (keeps : ∀ query state, inv state → ∀ result ∈ support ((impl₁ query).run state), inv result.2)
    (oa : OracleComp spec' α) (state : σ₁) (holds : inv state) :
    LawEq (Prod.map id proj <$> (simulateQ impl₁ oa).run state) ((simulateQ impl₂ oa).run (proj state)) := by
  induction oa using OracleComp.inductionOn generalizing state with
  | pure value => exact LawEq.of_eq (by simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_apply, id_eq])
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, map_bind]
      refine (LawEq.bind_support _ fun result member => ih result.1 result.2 (keeps query state holds result member)).trans ?_
      have first := (step query state holds).bind (f := fun result => (simulateQ impl₂ (next result.1)).run result.2)
        (g := fun result => (simulateQ impl₂ (next result.1)).run result.2) fun _ => LawEq.refl _
      simpa only [bind_map_left, Prod.map_fst, Prod.map_snd, id_eq] using first

/-! ### Slot services -/

/-- The per-slot 108-byte outputs as a lazily sampled oracle. -/
abbrev OutputSpec (n : Nat) := PqxdhRecordLiftInterface.Slot n →ₒ PqxdhServerAuthKeySchedule.Output

/-- The per-slot environment material (key32, nonce12) as a lazily sampled oracle. -/
abbrev MaterialSpec (n : Nat) := PqxdhRecordLiftInterface.Slot n →ₒ Material

variable {n : Nat}

/-- A slot service: how a registration handler obtains slot `j`'s 108-byte output from its service state. -/
abbrev SlotService (S : Type) (n : Nat) :=
  (j : PqxdhRecordLiftInterface.Slot n) → StateT S ProbComp PqxdhServerAuthKeySchedule.Output

/-- Item 2's S7 service: the persistent lazy table of outputs, with its query counts. -/
noncomputable def tableService : SlotService (PqxdhRecordLiftLazyTable.State (OutputSpec n)) n :=
  fun j => PqxdhRecordLiftLazyTable.impl (spec := OutputSpec n) j

/-- VCVio's lazily sampled cache of outputs. -/
noncomputable def lazyService : SlotService (OutputSpec n).QueryCache n :=
  fun j => (OutputSpec n).randomOracle j

/-- The split service: the material and the seed of a slot are each lazily sampled at its first touch, and the service returns their join. -/
noncomputable def splitService :
    SlotService ((MaterialSpec n).QueryCache × (PqxdhRecordLiftWorld.SeedSpec n).QueryCache) n := fun j => do
  let m ← (StateLens.fst _ _).query (spec := MaterialSpec n) j
  let seed ← (StateLens.snd _ _).query (spec := PqxdhRecordLiftWorld.SeedSpec n) j
  pure (joinOutput m seed)

/-- `touch` as a relation (critique M8): the projection carries every step of the first service to the corresponding step of the second in law, from states satisfying the invariant, and preserves the invariant. -/
def ServiceProj {S₁ S₂ : Type} (inv : S₁ → Prop) (proj : S₁ → S₂) (svc₁ : SlotService S₁ n)
    (svc₂ : SlotService S₂ n) : Prop :=
  ∀ j state, inv state → LawEq (Prod.map id proj <$> (svc₁ j).run state) ((svc₂ j).run (proj state)) ∧
    ∀ result ∈ support ((svc₁ j).run state), inv result.2

/-- The table service forgets its counts to become the lazy service. -/
theorem table_service_proj :
    ServiceProj (n := n) (fun _ => True) Prod.fst tableService lazyService :=
  fun j state _ => ⟨LawEq.of_eq (LazyOracleDiscard.impl_project j state), fun _ _ => trivial⟩

/-- Material and seed are present together. -/
def BothOrNeither (state : (MaterialSpec n).QueryCache × (PqxdhRecordLiftWorld.SeedSpec n).QueryCache) : Prop :=
  ∀ j, (state.1 j).isSome = (state.2 j).isSome

/-- The output table of a split state: the join of material and seed where both are present. -/
def joinTable (state : (MaterialSpec n).QueryCache × (PqxdhRecordLiftWorld.SeedSpec n).QueryCache) :
    (OutputSpec n).QueryCache :=
  fun j => match state.1 j, state.2 j with
    | some m, some seed => some (joinOutput m seed)
    | _, _ => none

/-- Recording a material and a seed at a slot records their join in the output table. -/
theorem joinTable_cacheQuery (state : (MaterialSpec n).QueryCache × (PqxdhRecordLiftWorld.SeedSpec n).QueryCache)
    (j : PqxdhRecordLiftInterface.Slot n) (m : Material) (seed : PqxdhRecordLiftSeed.Seed) :
    joinTable (state.1.cacheQuery j m, state.2.cacheQuery j seed) = (joinTable state).cacheQuery j (joinOutput m seed) := by
  funext i
  by_cases same : i = j
  · subst same
    simp only [joinTable, QueryCache.cacheQuery_self]
  · simp only [joinTable, QueryCache.cacheQuery_of_ne state.1 m same, QueryCache.cacheQuery_of_ne state.2 seed same,
      QueryCache.cacheQuery_of_ne (joinTable state) (joinOutput m seed) same]

/-- At a slot with neither material nor seed, the split service draws both and records them. -/
theorem splitService_none (state : (MaterialSpec n).QueryCache × (PqxdhRecordLiftWorld.SeedSpec n).QueryCache)
    (j : PqxdhRecordLiftInterface.Slot n) (hm : state.1 j = none) (hs : state.2 j = none) :
    (splitService j).run state = (($ᵗ Material : ProbComp Material) >>= fun m =>
      ($ᵗ PqxdhRecordLiftSeed.Seed : ProbComp PqxdhRecordLiftSeed.Seed) >>= fun seed =>
        pure (joinOutput m seed, (state.1.cacheQuery j m, state.2.cacheQuery j seed))) := by
  rw [splitService, StateT.run_bind]
  change ((fun r => (r.1, (r.2, state.2))) <$> ((MaterialSpec n).randomOracle j).run state.1) >>= _ = _
  rw [LazyOracleDiscard.query_of_none hm, map_bind, bind_assoc]
  refine bind_congr fun m => ?_
  simp only [map_pure, pure_bind, StateT.run_bind]
  change ((fun r => (r.1, ((state.1.cacheQuery j m), r.2))) <$>
    ((PqxdhRecordLiftWorld.SeedSpec n).randomOracle j).run state.2) >>= _ = _
  rw [LazyOracleDiscard.query_of_none hs, map_bind, bind_assoc]
  refine bind_congr fun seed => ?_
  simp only [map_pure, pure_bind, StateT.run_pure]

/-- At a slot with material and seed, the split service returns their join and changes nothing. -/
theorem splitService_some (state : (MaterialSpec n).QueryCache × (PqxdhRecordLiftWorld.SeedSpec n).QueryCache)
    (j : PqxdhRecordLiftInterface.Slot n) (m : Material) (seed : PqxdhRecordLiftSeed.Seed)
    (hm : state.1 j = some m) (hs : state.2 j = some seed) :
    (splitService j).run state = pure (joinOutput m seed, state) := by
  rw [splitService, StateT.run_bind]
  change ((fun r => (r.1, (r.2, state.2))) <$> ((MaterialSpec n).randomOracle j).run state.1) >>= _ = _
  rw [LazyOracleDiscard.query_of_some hm, map_pure, pure_bind, StateT.run_bind]
  change ((fun r => (r.1, (state.1, r.2))) <$> ((PqxdhRecordLiftWorld.SeedSpec n).randomOracle j).run state.2) >>= _ = _
  rw [LazyOracleDiscard.query_of_some hs, map_pure, pure_bind, StateT.run_pure]

/-- The split service joins material and seed: from a state where both or neither are present, it is the lazy service on the joined table in law (the 108-byte split at the first touch), and both or neither stay present. -/
theorem split_service_proj : ServiceProj (n := n) BothOrNeither joinTable splitService lazyService := by
  intro j state holds
  rcases hm : state.1 j with _ | m
  · have hs : state.2 j = none := by
      have h := holds j
      rw [hm, Option.isSome_none] at h
      exact Option.isSome_eq_false_iff.mp h.symm |> Option.isNone_iff_eq_none.mp
    have hj : joinTable state j = none := by simp only [joinTable, hm]
    rw [splitService_none state j hm hs]
    constructor
    · have rhs : (lazyService j).run (joinTable state) =
          ($ᵗ PqxdhServerAuthKeySchedule.Output : ProbComp PqxdhServerAuthKeySchedule.Output) >>= fun output =>
            pure (output, (joinTable state).cacheQuery j output) :=
        LazyOracleDiscard.query_of_none hj
      rw [rhs]
      refine LawEq.trans (LawEq.of_eq ?_) (PqxdhDeploymentHiddenLayout.uniform_split _).symm
      simp only [map_bind, map_pure, Prod.map_apply, id_eq, joinTable_cacheQuery]
    · intro result member
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at member
      obtain ⟨m, _, seed, _, rfl⟩ := member
      intro i
      by_cases same : i = j
      · subst same
        simp only [QueryCache.cacheQuery_self, Option.isSome_some]
      · simp only [QueryCache.cacheQuery_of_ne state.1 m same, QueryCache.cacheQuery_of_ne state.2 seed same]
        exact holds i
  · have hs : ∃ seed, state.2 j = some seed := by
      have h := holds j
      rw [hm] at h
      exact Option.isSome_iff_exists.mp h.symm
    obtain ⟨seed, hs⟩ := hs
    have hj : joinTable state j = some (joinOutput m seed) := by simp only [joinTable, hm, hs]
    rw [splitService_some state j m seed hm hs]
    constructor
    · refine LawEq.of_eq ?_
      simp only [map_pure, Prod.map_apply, id_eq, lazyService]
      rw [LazyOracleDiscard.query_of_some hj]
    · intro result member
      rw [support_pure, Set.mem_singleton_iff] at member
      subst member
      exact holds

/-! ### Natural registration cores and the represent step -/

/-- Replace the service state of the backend through a projection. -/
def mapBackend {KemSK S₁ S₂ Γ : Type} (proj : S₁ → S₂) (state : XState KemSK (S₁ × Γ) n) : XState KemSK (S₂ × Γ) n :=
  ⟨state.base, (proj state.backend.1, state.backend.2), state.seeds, state.snap, state.log⟩

/-- `uses` as a relation (critique M8): a registration core, polymorphic in its service state, reads slot outputs only through its service, so every step transports along every service projection and preserves the invariant. -/
def CoreNatural {KemSK Γ : Type}
    (core : ∀ {S : Type}, SlotService S n → PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK (S × Γ) n) : Prop :=
  ∀ {S₁ S₂ : Type} (inv : S₁ → Prop) (proj : S₁ → S₂) (svc₁ : SlotService S₁ n) (svc₂ : SlotService S₂ n),
    ServiceProj inv proj svc₁ svc₂ → ∀ created query (state : XState KemSK (S₁ × Γ) n), inv state.backend.1 →
      LawEq (Prod.map id (mapBackend proj) <$> (core svc₁ created query).run state)
        ((core svc₂ created query).run (mapBackend proj state)) ∧
      ∀ result ∈ support ((core svc₁ created query).run state), inv result.2.backend.1

section Represent
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Γ : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- The fixed steps (coins, BLAKE2b, records) commute with replacing the service state, whatever the registration handlers. -/
theorem fixed_mapBackend {S₁ S₂ : Type} (proj : S₁ → S₂) (reg₁ : RegImpl KemSK (S₁ × Γ) n)
    (reg₂ : RegImpl KemSK (S₂ × Γ) n) (query : Spec.Domain)
    (notEnv : ∀ command : PqxdhRecordLiftInterface.EnvQuery, query ≠ .inr command.val)
    (state : XState KemSK (S₁ × Γ) n) :
    Prod.map id (mapBackend proj) <$> (handlerWith setup codec route reg₁ query).run state =
      (handlerWith setup codec route reg₂ query).run (mapBackend proj state) := by
  rcases query with coin | command
  · simp only [handlerWith, StateT.run_lift, map_bind, map_pure]
    rfl
  · cases command
    case create pin keyId => exact absurd rfl (notEnv ⟨.create pin keyId, trivial⟩)
    case bundle owner => exact absurd rfl (notEnv ⟨.bundle owner, trivial⟩)
    case accept raw => exact absurd rfl (notEnv ⟨.accept raw, trivial⟩)
    case build session payload => exact absurd rfl (notEnv ⟨.build session payload, trivial⟩)
    case finish owner raw => exact absurd rfl (notEnv ⟨.finish owner raw, trivial⟩)
    case hmac key message => exact absurd rfl (notEnv ⟨.hmac key message, trivial⟩)
    all_goals
      simp only [handlerWith, PqxdhDeploymentBackend.onBase, StateLens.lift, PqxdhDeploymentBackend.baseLens,
        StateT.run, Functor.map_map]
      rfl

/-- The fixed steps keep the backend. -/
theorem fixed_backend {Bk : Type} (reg : RegImpl KemSK Bk n) (query : Spec.Domain)
    (notEnv : ∀ command : PqxdhRecordLiftInterface.EnvQuery, query ≠ .inr command.val)
    (state : XState KemSK Bk n) :
    ∀ result ∈ support ((handlerWith setup codec route reg query).run state), result.2.backend = state.backend := by
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

/-- The represent step (M8): for a natural core and a service projection, the game with the first service and the game with the second have the same law up to the service projection of the final state. -/
theorem represent
    (core : ∀ {S : Type}, SlotService S n → PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK (S × Γ) n)
    (natural : CoreNatural core) {S₁ S₂ : Type} (inv : S₁ → Prop) (proj : S₁ → S₂)
    (svc₁ : SlotService S₁ n) (svc₂ : SlotService S₂ n) (related : ServiceProj inv proj svc₁ svc₂)
    (init : PqxdhLiveServerConstruction.Created Unit → S₁ × Γ) (initial : ∀ created, inv (init created).1)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    LawEq (outcomeMap (mapBackend proj) <$> (gameWith setup codec route init (fun created => core svc₁ created)
        ensureInit identityIndex bounds mode adversary).run runtime)
      ((gameWith setup codec route (fun created => (proj (init created).1, (init created).2))
        (fun created => core svc₂ created) ensureInit identityIndex bounds mode adversary).run runtime) := by
  simp only [gameWith, StateT.run, map_bind]
  refine LawEq.bind (LawEq.refl _) fun born => ?_
  rcases born with ⟨_ | created, after⟩
  · exact LawEq.refl _
  · have transported := lawEq_run_simulateQ_of_proj (handlerWith setup codec route (core svc₁ created))
      (handlerWith setup codec route (core svc₂ created)) (fun state => inv state.backend.1) (mapBackend proj)
      (fun query state holds => ?step) (fun query state holds => ?keeps)
      (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode adversary))
      (xinitial created (init created)) (initial created)
    case step =>
      by_cases env : ∃ command : PqxdhRecordLiftInterface.EnvQuery, query = .inr command.val
      · obtain ⟨⟨command, isEnv⟩, rfl⟩ := env
        cases command
        case create pin keyId => exact (natural inv proj svc₁ svc₂ related created ⟨.create pin keyId, trivial⟩ state holds).1
        case bundle owner => exact (natural inv proj svc₁ svc₂ related created ⟨.bundle owner, trivial⟩ state holds).1
        case accept raw => exact (natural inv proj svc₁ svc₂ related created ⟨.accept raw, trivial⟩ state holds).1
        case build session payload =>
          exact (natural inv proj svc₁ svc₂ related created ⟨.build session payload, trivial⟩ state holds).1
        case finish owner raw => exact (natural inv proj svc₁ svc₂ related created ⟨.finish owner raw, trivial⟩ state holds).1
        case hmac key message => exact (natural inv proj svc₁ svc₂ related created ⟨.hmac key message, trivial⟩ state holds).1
        all_goals exact isEnv.elim
      · exact LawEq.of_eq (fixed_mapBackend setup codec route proj _ _ query
          (fun command same => env ⟨command, same⟩) state)
    case keeps =>
      by_cases env : ∃ command : PqxdhRecordLiftInterface.EnvQuery, query = .inr command.val
      · obtain ⟨⟨command, isEnv⟩, rfl⟩ := env
        cases command
        case create pin keyId => exact (natural inv proj svc₁ svc₂ related created ⟨.create pin keyId, trivial⟩ state holds).2
        case bundle owner => exact (natural inv proj svc₁ svc₂ related created ⟨.bundle owner, trivial⟩ state holds).2
        case accept raw => exact (natural inv proj svc₁ svc₂ related created ⟨.accept raw, trivial⟩ state holds).2
        case build session payload =>
          exact (natural inv proj svc₁ svc₂ related created ⟨.build session payload, trivial⟩ state holds).2
        case finish owner raw => exact (natural inv proj svc₁ svc₂ related created ⟨.finish owner raw, trivial⟩ state holds).2
        case hmac key message => exact (natural inv proj svc₁ svc₂ related created ⟨.hmac key message, trivial⟩ state holds).2
        all_goals exact isEnv.elim
      · intro result member
        rw [fixed_backend setup codec route _ query (fun command same => env ⟨command, same⟩) state result member]
        exact holds
    have mapped := transported.map (fun result => (some (PqxdhRegistrationJointServerBirth.encode created,
      result.1.1, result.1.2, result.2), after))
    simp only [StateT.run, Functor.map_map, Prod.map_fst, Prod.map_snd, id_eq] at mapped
    simp only [Functor.map_map, outcomeMap, Option.map_some]
    exact mapped

/-- The table and the split representations of the hidden-slot outputs have the same law through the lazy representation: the game with the S7 table service, read through the table's cache, and the game with the split service, read through the joined table. -/
theorem represent_split
    (core : ∀ {S : Type}, SlotService S n → PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK (S × Γ) n)
    (natural : CoreNatural core) (init : PqxdhLiveServerConstruction.Created Unit → Γ)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    LawEq (outcomeMap (mapBackend Prod.fst) <$> (gameWith setup codec route
        (fun created => (PqxdhRecordLiftLazyTable.initial, init created)) (fun created => core tableService created)
        ensureInit identityIndex bounds mode adversary).run runtime)
      (outcomeMap (mapBackend joinTable) <$> (gameWith setup codec route
        (fun created => ((∅, ∅), init created)) (fun created => core splitService created)
        ensureInit identityIndex bounds mode adversary).run runtime) := by
  have table := represent setup codec route core natural (fun _ => True) Prod.fst tableService lazyService
    table_service_proj (fun created => (PqxdhRecordLiftLazyTable.initial, init created)) (fun _ => trivial)
    ensureInit identityIndex bounds mode adversary runtime
  have split := represent setup codec route core natural BothOrNeither joinTable splitService lazyService
    split_service_proj (fun created => ((∅, ∅), init created)) (fun _ _ => rfl)
    ensureInit identityIndex bounds mode adversary runtime
  have tableInit : (fun created => (Prod.fst (PqxdhRecordLiftLazyTable.initial (spec := OutputSpec n)), init created)) =
      (fun created => (joinTable ((∅, ∅) : (MaterialSpec n).QueryCache × (PqxdhRecordLiftWorld.SeedSpec n).QueryCache),
        init created)) := by
    funext created
    congr 1
  simp only [tableInit] at table
  exact table.trans split.symm

end Represent

/-! ### The seed deferral (generic) -/

/-- The final state with the hidden-seed table emptied: every coordinate except the seed table. -/
def seedFree {KemSK Bk : Type} (state : XState KemSK Bk n) : XState KemSK Bk n := seedLens.set state ∅

/-- Emptying the seed table does not see the seed table. -/
theorem seedFree_set {KemSK Bk : Type} (state : XState KemSK Bk n)
    (cache : (PqxdhRecordLiftWorld.SeedSpec n).QueryCache) : seedFree (seedLens.set state cache) = seedFree state := rfl

section Defer
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Bk Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- The seed deferral (generic, M4 form on the seed lens): if each constructed Server's registration handler is, in law, a pointed handler followed by the completion of a reported seed-table point, and the pointed steps commute with seed completions, then the game with the handler and the game with its erased handler have the same law of the Server's public data, the output, the ledger and the final state with the seed table emptied. -/
theorem defer (pair : PqxdhLiveServerConstruction.Created Unit → PointedReg (seedLens (KemSK := KemSK) (Bk := Bk) (n := n)))
    (init : PqxdhLiveServerConstruction.Created Unit → Bk) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    LawEq (outcomeMap seedFree <$> (gameWith setup codec route init (fun created => (pair created).reg) ensureInit
        identityIndex bounds mode adversary).run runtime)
      (outcomeMap seedFree <$> (gameWith setup codec route init (fun created => (pair created).erased) ensureInit
        identityIndex bounds mode adversary).run runtime) :=
  PqxdhDeploymentFinishErasure.erase_game setup codec route pair
    (fun created query => PqxdhDeploymentBackend.fixed_commute_seed setup codec route (pair created).reg query)
    seedFree seedFree_set init ensureInit identityIndex bounds mode adversary runtime

end Defer

end BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit.LawEq.bind_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit.LawEq.bind_support

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit.lawEq_run_simulateQ_of_proj' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit.lawEq_run_simulateQ_of_proj

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit.table_service_proj' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit.table_service_proj

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit.joinTable_cacheQuery' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit.joinTable_cacheQuery

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit.splitService_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit.splitService_none

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit.splitService_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit.splitService_some

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit.split_service_proj' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit.split_service_proj

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit.fixed_mapBackend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit.fixed_mapBackend

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit.fixed_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit.fixed_backend

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit.represent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit.represent

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit.represent_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit.represent_split

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit.seedFree_set' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit.seedFree_set

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit.defer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit.defer
