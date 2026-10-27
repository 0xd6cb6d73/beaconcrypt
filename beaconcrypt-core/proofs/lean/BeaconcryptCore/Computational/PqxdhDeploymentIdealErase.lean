-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps

/-!
# C7 for the ideal registration of the common deployment experiment (CE-11b, unit U2)

C7 for `CE.idealGame g` (CE-11b design-v2 section 4): the ideal registration core `PqxdhDeploymentIdealSteps.idealCore t p svc`, over any slot service, is a pointed registration handler for the CTX cache (`PqxdhDeploymentFinishErasure.FinishPair`) whose only point is owner k's challenge finish (`idealPair`), and its erased handler is the C7-erased core `idealCoreErased t p svc` (`idealPair_erased`). `erase_ideal` is `PqxdhDeploymentFinishErasure.erase_game_ctx` at this pair: the common deployment experiment with the ideal registration and with its C7-erased core have the same law of the Server's public data, the adversary's output, the ledger and the final state with the CTX cache emptied. `erase_idealGame` is the same for `CE.idealGame g` (`PqxdhDeploymentIdealSteps.idealGame`) and `CE.idealGame° g` (`idealGameErased`), after the challenger's draws.

- Slot steps on pairs (`onPair`): a slot step run against the first-touch allocator in front of a slot service is a probabilistic step on the pair of its state and the allocator and service state. `onPair` maps binds, pure steps and maps to the same, coins-only steps to steps on the first component, focused steps and dispatching steps to focused and dispatching steps; commutation with completions of a cache on the first component follows from frames (`SlotFrame`: slot steps that neither read nor write the cache), from commuting coins-only steps, and through focus and dispatch. `slotCore_pair`, `slotCore_commutes` and `slotCore_factor` carry commutation and the pointed form from a slot program on pairs to its command of `slotCore`.
- The real commands on every backend commute with completions of the CTX cache (`realRegAt_commutes_ctx`, central's `realReg_commutes_ctx` transported by `commutes_focus`), and so do create, bundle and HMAC of the ideal core (`idealCore_real_commutes_ctx`).
- The selected accept is a frame of the CTX cache (`acceptExposed_frame`): the native steps before encapsulation and the marker client under `tailCE` never read or write the cache, and the marker tail's install request writes back the game state it was given (`tailCE_tail_frame`, `serverTail_frame`). Every raw accept therefore commutes (`acceptStep_commutes`).
- The marked build commutes (`buildStep_commutes`, `buildHidden_factored_commutes`: central's `buildFactor_commutes_ctx` at the material and seed of the value read, `factoredHidden_build`).
- Owner k's challenge finish: `ownerRun` restructures the grouped owner under `ownerImplCE` (the preparation as coins, then at most one grouped finish request, then the source commit). The pointed finish (`groupPointed`, `ownerPointed`, `finishChallengePointed`, `finishStepPointed`) runs the erased hidden finish that reports the opening it discards (`PqxdhDeploymentHiddenEntry.finishPointed`). `finishStep_factor` (from `finishFactor_pointed` at the value's material and seed, `factoredHidden_after`) is an exact program equality: the finish with the factored hidden services is the pointed finish followed by the completion of the reported CTX point. `finishStep_erase` shows that the pointed finish without its report is the finish with the erased hidden services, which commutes with completions (`finishStep_erased_commutes`).

These are equalities of programs and equalities in law of a lazily sampled cache. They charge nothing and make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealErase
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentBackend (XState RegImpl ctxLens)
open PqxdhDeploymentIdealSlots (Coord SlotSpec SlotProgram slotCore detach attach)
open PqxdhDeploymentIdealSteps (realRegAt onSlots liftS)
open PqxdhRegistrationJointKemSecondEntry (Alloc slotImpl)
open LazyOracleDiscard (Commutes StateLens CacheLens LawEq)

variable {KemSK Bk : Type} {n : ℕ}

/-- The extended state at the unit backend with no slot: the backend and the seed table forgotten. -/
def forget (x : XState KemSK Bk n) : XState KemSK Unit 0 := ⟨x.base, (), ∅, x.snap, x.log⟩

/-- Reattach the backend and the seed table of `x` to a unit-backend state. -/
def reattach (x : XState KemSK Bk n) (y : XState KemSK Unit 0) : XState KemSK Bk n :=
  ⟨y.base, x.backend, x.seeds, y.snap, y.log⟩

/-! ### The real registration on every backend -/

section Real
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks)

/-- `realRegAt` on any backend is `realReg` on the forgotten state, with the backend and the seed table reattached. -/
theorem realRegAt_forget (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhRecordLiftInterface.EnvQuery)
    (x : XState KemSK Bk n) :
    (realRegAt (Bk := Bk) (n := n) setup codec route checks created query).run x =
      (fun r => (r.1, reattach x r.2)) <$>
        (PqxdhDeploymentBackend.realReg setup codec route checks created query).run (forget x) := by
  simp only [realRegAt, PqxdhDeploymentBackend.realReg, StateT.run, Functor.map_map]
  rfl

/-- Every command of `realRegAt` commutes with completions of the CTX cache, on every backend (`PqxdhDeploymentBackend.realReg_commutes_ctx` transported). -/
theorem realRegAt_commutes_ctx (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhRecordLiftInterface.EnvQuery) :
    Commutes ctxLens (realRegAt (KemSK := KemSK) (Bk := Bk) (n := n) setup codec route checks created query) :=
  PqxdhDeploymentBackend.commutes_focus ctxLens ctxLens _ forget
    (fun _ => PqxdhDeploymentBackend.realReg setup codec route checks created query)
    (fun x b r => (b, reattach x r)) (fun x => realRegAt_forget setup codec route checks created query x)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ => PqxdhDeploymentBackend.realReg_commutes_ctx setup codec route checks created query)

end Real

/-! ### Coins-only slot steps through `slotCore` -/

section Slot
variable {Γ : Type}

/-- The allocator passes coins through: a lifted probabilistic computation keeps the allocator and the service state. -/
theorem slotImpl_coins {S α : Type} (svc : PqxdhDeploymentSeedSplit.SlotService S n) (work : ProbComp α)
    (state : PqxdhRegistrationJointKemSecondEntry.Alloc Coord n × S) :
    (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl svc) (liftS work)).run state =
      (fun a => (a, state)) <$> work := by
  rw [liftS, QueryImpl.simulateQ_liftComp_left_eq_of_apply (PqxdhRegistrationJointKemSecondEntry.slotImpl svc)
    (fun query => StateT.mk fun current => (fun reply => (reply, current)) <$> (unifSpec.query query : ProbComp _))
    (fun query => by funext current; exact PqxdhRegistrationJointKemSecondEntry.slot_coin svc query current)]
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, StateT.run_mk, bind_map_left, map_bind]
      refine bind_congr fun reply => ?_
      exact ih reply state

/-- A coins-only slot step runs its probabilistic step, lifted. -/
theorem onSlots_run {σ α : Type} (step : StateT σ ProbComp α) (s : σ) : (onSlots step).run s = liftS (step.run s) := rfl

/-- A slot core runs a coins-only slot step on the detached state and reattaches the allocator and the service state. -/
theorem slotCore_onSlots (prog : PqxdhLiveServerConstruction.Created Unit → SlotProgram KemSK Γ n) {S : Type}
    (svc : PqxdhDeploymentSeedSplit.SlotService S n) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhRecordLiftInterface.EnvQuery) (step : StateT (XState KemSK Γ n) ProbComp
      (PqxdhRecordLiftInterface.EnvSpec.Range query)) (shape : prog created query = onSlots step)
    (x : XState KemSK (S × (PqxdhRegistrationJointKemSecondEntry.Alloc Coord n × Γ)) n) :
    (slotCore prog svc created query).run x =
      (fun r => (r.1, attach r.2 x.backend.2.1 x.backend.1)) <$> step.run (detach x) := by
  rw [PqxdhDeploymentIdealSlots.slotCore_run, shape]
  change (fun r => (r.1.1, attach r.1.2 r.2.1 r.2.2)) <$>
      (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl svc) (liftS (step.run (detach x)))).run
        (x.backend.2.1, x.backend.1) = _
  rw [slotImpl_coins, Functor.map_map]

/-- A coins-only slot step that commutes with CTX completions gives a slot-core command that commutes with them. -/
theorem slotCore_commutes_ctx (prog : PqxdhLiveServerConstruction.Created Unit → SlotProgram KemSK Γ n) {S : Type}
    (svc : PqxdhDeploymentSeedSplit.SlotService S n) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhRecordLiftInterface.EnvQuery) (step : StateT (XState KemSK Γ n) ProbComp
      (PqxdhRecordLiftInterface.EnvSpec.Range query)) (shape : prog created query = onSlots step)
    (commutes : Commutes ctxLens step) :
    Commutes ctxLens (slotCore prog svc created query) :=
  PqxdhDeploymentBackend.commutes_focus ctxLens ctxLens _ detach (fun _ => step)
    (fun x b r => (b, attach r x.backend.2.1 x.backend.1))
    (fun x => slotCore_onSlots prog svc created query step shape x)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ => commutes)

end Slot

/-! ### The create command and the real commands of the ideal core -/

section Ideal
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhDeploymentIdealSteps (createReg createPool idealCore IdealBk)
open PqxdhDeploymentIdealParams (Target Params)

/-- The pool create command is a frame of the CTX cache. -/
theorem createReg_commutes_ctx {Γ : Type} (pool : List (PqxdhLiveKemReservation.Pair KemSK)) (pin : Pqxdh.Bytes)
    (keyId : Std.U64) :
    Commutes ctxLens (createReg (Γ := Γ) (n := n) setup pool pin keyId) := by
  refine LazyOracleDiscard.commutes_lift PqxdhDeploymentBackend.baseLens PqxdhDeploymentBackend.nativeCtxLens _ ?_
  show Commutes PqxdhDeploymentBackend.nativeCtxLens (match PqxdhDeploymentInterface.parsePin pin with
    | none => pure none
    | some word => some <$> PqxdhDeploymentBackend.nativeLens.lift (createPool setup pool word keyId))
  split
  · exact LazyOracleDiscard.commutes_pure _ _
  · refine LazyOracleDiscard.commutes_map _ _ (LazyOracleDiscard.commutes_lift PqxdhDeploymentBackend.nativeLens _ _ ?_)
    unfold createPool
    refine LazyOracleDiscard.commutes_bind _ (PqxdhDeploymentBackend.commutes_lift_comp _ _) fun _ => ?_
    refine LazyOracleDiscard.commutes_bind _ (PqxdhDeploymentBackend.commutes_lift_comp _ _) fun _ => ?_
    exact LazyOracleDiscard.commutes_frame _ _ fun s c => by
      simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, pure_bind, StateT.run_pure,
        map_pure, bind_assoc, map_bind]
      rfl

/-- Create, bundle and HMAC of the ideal core commute with completions of the CTX cache, over every slot service. -/
theorem idealCore_real_commutes_ctx (t : Target count) (p : Params KemSK count) {S : Type}
    (svc : PqxdhDeploymentSeedSplit.SlotService S 2) (created : PqxdhLiveServerConstruction.Created Unit) :
    (∀ pin keyId, Commutes ctxLens (idealCore setup codec route checks t p svc created ⟨.create pin keyId, trivial⟩)) ∧
    (∀ owner, Commutes ctxLens (idealCore setup codec route checks t p svc created ⟨.bundle owner, trivial⟩)) ∧
    (∀ key message, Commutes ctxLens (idealCore setup codec route checks t p svc created ⟨.hmac key message, trivial⟩)) :=
  ⟨fun pin keyId => slotCore_commutes_ctx _ svc created _ _ rfl (createReg_commutes_ctx setup (p.pool t) pin keyId),
    fun owner => slotCore_commutes_ctx _ svc created _ _ rfl
      (realRegAt_commutes_ctx setup codec route checks created ⟨.bundle owner, trivial⟩),
    fun key message => slotCore_commutes_ctx _ svc created _ _ rfl
      (realRegAt_commutes_ctx setup codec route checks created ⟨.hmac key message, trivial⟩)⟩

end Ideal

/-! ### Slot steps against the allocator, as probabilistic steps on pairs -/

section Pair
variable {σ S : Type}

/-- A slot step run against the first-touch allocator in front of a slot service, as a probabilistic step on the pair of its state and the allocator and service state. -/
noncomputable def onPair (svc : PqxdhDeploymentSeedSplit.SlotService S n) {α : Type}
    (step : StateT σ (OracleComp SlotSpec) α) : StateT (σ × (Alloc Coord n × S)) ProbComp α :=
  fun z => (fun r => (r.1.1, (r.1.2, r.2))) <$> (simulateQ (slotImpl svc) (step.run z.1)).run z.2

theorem onPair_run (svc : PqxdhDeploymentSeedSplit.SlotService S n) {α : Type}
    (step : StateT σ (OracleComp SlotSpec) α) (z : σ × (Alloc Coord n × S)) :
    (onPair svc step).run z = (fun r => (r.1.1, (r.1.2, r.2))) <$> (simulateQ (slotImpl svc) (step.run z.1)).run z.2 :=
  rfl

/-- `onPair` maps binds to binds. -/
theorem onPair_bind (svc : PqxdhDeploymentSeedSplit.SlotService S n) {α β : Type}
    (step : StateT σ (OracleComp SlotSpec) α) (next : α → StateT σ (OracleComp SlotSpec) β) :
    onPair svc (step >>= next) = onPair svc step >>= fun a => onPair svc (next a) := by
  funext z
  change (onPair svc (step >>= next)).run z = (onPair svc step >>= fun a => onPair svc (next a)).run z
  rw [StateT.run_bind, onPair_run, onPair_run, StateT.run_bind, simulateQ_bind, StateT.run_bind, map_bind,
    bind_map_left]
  rfl

/-- `onPair` maps pure steps to pure steps. -/
theorem onPair_pure (svc : PqxdhDeploymentSeedSplit.SlotService S n) {α : Type} (a : α) :
    onPair (σ := σ) svc (pure a) = pure a := by
  funext z
  change (onPair svc (pure a : StateT σ (OracleComp SlotSpec) α)).run z = (pure a : StateT _ ProbComp α).run z
  rw [onPair_run, StateT.run_pure, simulateQ_pure, StateT.run_pure, map_pure, StateT.run_pure]

/-- `onPair` maps maps to maps. -/
theorem onPair_map (svc : PqxdhDeploymentSeedSplit.SlotService S n) {α β : Type} (f : α → β)
    (step : StateT σ (OracleComp SlotSpec) α) : onPair svc (f <$> step) = f <$> onPair svc step := by
  rw [map_eq_bind_pure_comp, onPair_bind, map_eq_bind_pure_comp]
  simp only [Function.comp_def, onPair_pure]

/-- A coins-only slot step is its probabilistic step on the first component. -/
theorem onPair_onSlots (svc : PqxdhDeploymentSeedSplit.SlotService S n) {α : Type} (work : StateT σ ProbComp α) :
    onPair svc (onSlots work) = (StateLens.fst σ (Alloc Coord n × S)).lift work := by
  funext z
  change (onPair svc (onSlots work)).run z = _
  rw [onPair_run]
  change (fun r => (r.1.1, (r.1.2, r.2))) <$> (simulateQ (slotImpl svc) (liftS (work.run z.1))).run z.2 = _
  rw [slotImpl_coins, Functor.map_map]
  rfl

end Pair

/-! ### Frames and commutation on pairs -/

section PairCommutes
variable {σ S : Type}
variable {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec ι₀} [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)]

/-- A cache lens on the first component of a pair. -/
abbrev pairLens (L : CacheLens spec₀ σ) : CacheLens spec₀ (σ × (Alloc Coord n × S)) :=
  (StateLens.fst σ (Alloc Coord n × S)).comp L

/-- A slot step that neither reads nor writes the component set by `put`, whatever it holds. -/
def SlotFrame {C α : Type} (put : σ → C → σ) (step : StateT σ (OracleComp SlotSpec) α) : Prop :=
  ∀ s c, step.run (put s c) = (fun r => (r.1, put r.2 c)) <$> step.run s

theorem SlotFrame.pure {C α : Type} (put : σ → C → σ) (a : α) :
    SlotFrame put (pure a : StateT σ (OracleComp SlotSpec) α) := fun s c => by
  simp only [StateT.run_pure, map_pure]

theorem SlotFrame.bind {C α β : Type} {put : σ → C → σ} {step : StateT σ (OracleComp SlotSpec) α}
    {next : α → StateT σ (OracleComp SlotSpec) β} (first : SlotFrame put step) (rest : ∀ a, SlotFrame put (next a)) :
    SlotFrame put (step >>= next) := fun s c => by
  simp only [StateT.run_bind, first s c, bind_map_left, map_bind, rest _ _ c]

theorem SlotFrame.map {C α β : Type} {put : σ → C → σ} {step : StateT σ (OracleComp SlotSpec) α} (f : α → β)
    (frame : SlotFrame put step) : SlotFrame put (f <$> step) := fun s c => by
  simp only [StateT.run_map, frame s c, Functor.map_map]

/-- A coins-only slot step is a frame when its probabilistic step is. -/
theorem SlotFrame.onSlots {C α : Type} {put : σ → C → σ} (work : StateT σ ProbComp α)
    (frame : ∀ s c, work.run (put s c) = (fun r => (r.1, put r.2 c)) <$> work.run s) :
    SlotFrame put (onSlots work) := fun s c => by
  change OracleComp.liftComp (work.run (put s c)) SlotSpec = _ <$> OracleComp.liftComp (work.run s) SlotSpec
  rw [frame s c, OracleComp.liftComp_map]

/-- A value request at coordinates not changed by `put` is a frame. -/
theorem SlotFrame.read {C : Type} (put : σ → C → σ) (coords : σ → Coord) (same : ∀ s c, coords (put s c) = coords s) :
    SlotFrame put (fun s => (fun v => (v, s)) <$> (SlotSpec.query (.inr (coords s)) : OracleComp SlotSpec _)) :=
  fun s c => by
    change (fun v => (v, put s c)) <$> (SlotSpec.query (.inr (coords (put s c))) : OracleComp SlotSpec _) =
      (fun r => (r.1, put r.2 c)) <$> ((fun v => (v, s)) <$> (SlotSpec.query (.inr (coords s)) : OracleComp SlotSpec _))
    rw [same, Functor.map_map]

/-- A simulation whose every query is a frame is a frame. -/
theorem SlotFrame.simulateQ {ι' C α : Type} {spec' : OracleSpec ι'} {put : σ → C → σ}
    (impl : QueryImpl spec' (StateT σ (OracleComp SlotSpec))) (frame : ∀ q, SlotFrame put (impl q))
    (work : OracleComp spec' α) : SlotFrame put (simulateQ impl work) := by
  induction work using OracleComp.inductionOn with
  | pure a => exact SlotFrame.pure put a
  | query_bind q next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
      exact SlotFrame.bind (frame q) ih

/-- A slot step that runs an inner slot frame on a part of the state, with the rest compatible with the frame, is a frame. -/
theorem SlotFrame.focus {ρ C α β : Type} (put : σ → C → σ) (put' : ρ → C → ρ)
    (step : StateT σ (OracleComp SlotSpec) α) (inner : StateT ρ (OracleComp SlotSpec) β) (init : σ → ρ)
    (fin : σ → β → ρ → α × σ) (shape : ∀ s, step.run s = (fun r => fin s r.1 r.2) <$> inner.run (init s))
    (init_put : ∀ s c, init (put s c) = put' (init s) c)
    (fin_put : ∀ s c b r, fin (put s c) b (put' r c) = Prod.map id (fun x => put x c) (fin s b r))
    (frame : SlotFrame put' inner) : SlotFrame put step := fun s c => by
  rw [shape, init_put, frame, Functor.map_map, shape, Functor.map_map]
  congr 1
  funext r
  exact fin_put s c r.1 r.2

/-- A slot frame of a cache is, on pairs, a frame of the cache, so it commutes with completions. -/
theorem onPair_commutes_frame (L : CacheLens spec₀ σ) (svc : PqxdhDeploymentSeedSplit.SlotService S n) {α : Type}
    (step : StateT σ (OracleComp SlotSpec) α) (frame : SlotFrame L.set step) :
    Commutes (pairLens (n := n) (S := S) L) (onPair svc step) :=
  LazyOracleDiscard.commutes_frame _ _ fun z c => by
    change (onPair svc step).run (L.set z.1 c, z.2) = _
    rw [onPair_run, onPair_run]
    change (fun r => (r.1.1, (r.1.2, r.2))) <$> (simulateQ (slotImpl svc) (step.run (L.set z.1 c))).run z.2 = _
    rw [frame z.1 c, simulateQ_map, StateT.run_map, Functor.map_map, Functor.map_map]
    rfl

/-- A coins-only slot step commutes on pairs when its probabilistic step commutes. -/
theorem onPair_commutes_onSlots (L : CacheLens spec₀ σ) (svc : PqxdhDeploymentSeedSplit.SlotService S n) {α : Type}
    (work : StateT σ ProbComp α) (commutes : Commutes L work) :
    Commutes (pairLens (n := n) (S := S) L) (onPair svc (onSlots work)) := by
  rw [onPair_onSlots]
  exact LazyOracleDiscard.commutes_lift _ L work commutes

/-- A slot step that runs an inner slot step on a part of the state, run on pairs. -/
theorem onPair_focus {ρ α β : Type} (svc : PqxdhDeploymentSeedSplit.SlotService S n)
    (step : StateT σ (OracleComp SlotSpec) α) (inner : StateT ρ (OracleComp SlotSpec) β) (init : σ → ρ)
    (fin : σ → β → ρ → α × σ) (shape : ∀ s, step.run s = (fun r => fin s r.1 r.2) <$> inner.run (init s))
    (z : σ × (Alloc Coord n × S)) :
    (onPair svc step).run z = (fun r => ((fin z.1 r.1 r.2.1).1, ((fin z.1 r.1 r.2.1).2, r.2.2))) <$>
      (onPair svc inner).run (init z.1, z.2) := by
  rw [onPair_run, onPair_run, shape, simulateQ_map, StateT.run_map, Functor.map_map, Functor.map_map]

/-- A focused slot step commutes on pairs when its inner step does and the rest is a frame of the caches. -/
theorem onPair_commutes_focus {ρ α β : Type} (L : CacheLens spec₀ σ) (M : CacheLens spec₀ ρ)
    (svc : PqxdhDeploymentSeedSplit.SlotService S n)
    (step : StateT σ (OracleComp SlotSpec) α) (inner : StateT ρ (OracleComp SlotSpec) β) (init : σ → ρ)
    (fin : σ → β → ρ → α × σ) (shape : ∀ s, step.run s = (fun r => fin s r.1 r.2) <$> inner.run (init s))
    (init_set : ∀ s c, init (L.set s c) = M.set (init s) c)
    (fin_set : ∀ s c b r, fin (L.set s c) b r = fin s b r)
    (fin_complete : ∀ s b r c, fin s b (M.set r c) = Prod.map id (fun x => L.set x c) (fin s b r))
    (commutes : Commutes (pairLens (n := n) (S := S) M) (onPair svc inner)) :
    Commutes (pairLens (n := n) (S := S) L) (onPair svc step) :=
  PqxdhDeploymentBackend.commutes_focus _ (pairLens M) _ (fun z => (init z.1, z.2)) (fun _ => onPair svc inner)
    (fun z b r => ((fin z.1 b r.1).1, ((fin z.1 b r.1).2, r.2))) (onPair_focus svc step inner init fin shape)
    (fun z c => by
      change (init (L.set z.1 c), z.2) = (M.set (init z.1) c, z.2)
      rw [init_set])
    (fun _ _ => rfl)
    (fun z c b r => by
      change ((fin (L.set z.1 c) b r.1).1, ((fin (L.set z.1 c) b r.1).2, r.2)) = _
      rw [fin_set])
    (fun z b r c => by
      change ((fin z.1 b (M.set r.1 c)).1, ((fin z.1 b (M.set r.1 c)).2, r.2)) = _
      rw [fin_complete]
      rfl)
    (fun _ => commutes)

/-- A step that dispatches on a part of the state, run on pairs. -/
theorem onPair_dispatch {τ α : Type} (svc : PqxdhDeploymentSeedSplit.SlotService S n)
    (step : StateT σ (OracleComp SlotSpec) α) (π : σ → τ) (choose : τ → StateT σ (OracleComp SlotSpec) α)
    (shape : ∀ s, step.run s = (choose (π s)).run s) (z : σ × (Alloc Coord n × S)) :
    (onPair svc step).run z = (onPair svc (choose (π z.1))).run z := by
  rw [onPair_run, onPair_run, shape]

/-- A dispatching slot step commutes on pairs when every branch does and the dispatch does not see the cache. -/
theorem onPair_commutes_dispatch {τ α : Type} (L : CacheLens spec₀ σ) (svc : PqxdhDeploymentSeedSplit.SlotService S n)
    (step : StateT σ (OracleComp SlotSpec) α) (π : σ → τ) (π_set : ∀ s c, π (L.set s c) = π s)
    (choose : τ → StateT σ (OracleComp SlotSpec) α) (shape : ∀ s, step.run s = (choose (π s)).run s)
    (commutes : ∀ p, Commutes (pairLens (n := n) (S := S) L) (onPair svc (choose p))) :
    Commutes (pairLens (n := n) (S := S) L) (onPair svc step) :=
  PqxdhDeploymentBackend.commutes_dispatch _ _ (fun z => π z.1) (fun z c => π_set z.1 c)
    (fun p => onPair svc (choose p)) (onPair_dispatch svc step π choose shape) commutes

/-- Completing an optional point of a cache on the first component of a pair completes it on the component. -/
theorem pairLens_completeOpt (L : CacheLens spec₀ σ) (point : Option spec₀.Domain) (z : σ × (Alloc Coord n × S)) :
    (pairLens (n := n) (S := S) L).completeOpt point z = (fun y => (y, z.2)) <$> L.completeOpt point z.1 := by
  cases point with
  | none => simp only [StateLens.completeOpt, map_pure]
  | some t =>
      simp only [StateLens.completeOpt, StateLens.complete, Functor.map_map]
      rfl

/-- A slot step that is a pointed slot step followed by the completion of the reported point is so on pairs. -/
theorem onPair_factor {α : Type} (L : CacheLens spec₀ σ) (svc : PqxdhDeploymentSeedSplit.SlotService S n)
    (step : StateT σ (OracleComp SlotSpec) α) (pointed : StateT σ (OracleComp SlotSpec) (α × Option spec₀.Domain))
    (factor : ∀ s, step.run s = pointed.run s >>= fun r => (r.1.1, ·) <$> liftS (L.completeOpt r.1.2 r.2))
    (z : σ × (Alloc Coord n × S)) :
    (onPair svc step).run z =
      (onPair svc pointed).run z >>= fun r => (r.1.1, ·) <$> (pairLens (n := n) (S := S) L).completeOpt r.1.2 r.2 := by
  rw [onPair_run, onPair_run, factor, simulateQ_bind, StateT.run_bind, map_bind, bind_map_left]
  refine bind_congr fun r => ?_
  rw [simulateQ_map, StateT.run_map, slotImpl_coins, Functor.map_map, Functor.map_map, pairLens_completeOpt,
    Functor.map_map]

end PairCommutes

/-! ### Slot cores through pairs -/

section CoreFocus
variable {Γ S : Type}

/-- One command of a slot core is its slot program on pairs, focused on the detached state, the allocator and the service state. -/
theorem slotCore_pair (prog : PqxdhLiveServerConstruction.Created Unit → SlotProgram KemSK Γ n)
    (svc : PqxdhDeploymentSeedSplit.SlotService S n) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhRecordLiftInterface.EnvQuery) (x : XState KemSK (S × (Alloc Coord n × Γ)) n) :
    (slotCore prog svc created query).run x =
      (fun r => (r.1, attach r.2.1 r.2.2.1 r.2.2.2)) <$>
        (onPair svc (prog created query)).run (detach x, (x.backend.2.1, x.backend.1)) := by
  rw [PqxdhDeploymentIdealSlots.slotCore_run, onPair_run, Functor.map_map]

/-- A slot-core command commutes with completions of the CTX cache when its slot program does on pairs. -/
theorem slotCore_commutes (prog : PqxdhLiveServerConstruction.Created Unit → SlotProgram KemSK Γ n)
    (svc : PqxdhDeploymentSeedSplit.SlotService S n) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhRecordLiftInterface.EnvQuery)
    (commutes : Commutes (pairLens (n := n) (S := S) ctxLens) (onPair svc (prog created query))) :
    Commutes ctxLens (slotCore prog svc created query) :=
  PqxdhDeploymentBackend.commutes_focus ctxLens (pairLens ctxLens) _ (fun x => (detach x, (x.backend.2.1, x.backend.1)))
    (fun _ => onPair svc (prog created query)) (fun _ b r => (b, attach r.1 r.2.1 r.2.2))
    (slotCore_pair prog svc created query) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ => commutes)

/-- A slot-core command is, in law, its pointed form followed by the completion of the reported CTX point, when its slot program is so on pairs. -/
theorem slotCore_factor (prog : PqxdhLiveServerConstruction.Created Unit → SlotProgram KemSK Γ n)
    (svc : PqxdhDeploymentSeedSplit.SlotService S n) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhRecordLiftInterface.EnvQuery)
    (pointed : StateT (XState KemSK Γ n × (Alloc Coord n × S)) ProbComp
      (PqxdhRecordLiftInterface.EnvSpec.Range query × Option CtxRomAuth.CtxRO.Domain))
    (factor : ∀ z, (onPair svc (prog created query)).run z =
      pointed.run z >>= fun r => (r.1.1, ·) <$> (pairLens (n := n) (S := S) ctxLens).completeOpt r.1.2 r.2)
    (x : XState KemSK (S × (Alloc Coord n × Γ)) n) :
    LawEq ((slotCore prog svc created query).run x)
      (((fun r => ((r.1.1, r.1.2), attach r.2.1 r.2.2.1 r.2.2.2)) <$>
        pointed.run (detach x, (x.backend.2.1, x.backend.1))) >>=
          fun r => (r.1.1, ·) <$> ctxLens.completeOpt r.1.2 r.2) :=
  PqxdhDeploymentFinishErasure.factor_focus ctxLens (pairLens ctxLens) _ (fun x => (detach x, (x.backend.2.1, x.backend.1)))
    (fun _ => onPair svc (prog created query)) (fun _ b r => (b, attach r.1 r.2.1 r.2.2))
    (slotCore_pair prog svc created query) (fun _ _ _ _ => rfl) (fun _ => pointed)
    (fun _ z => LawEq.of_eq (factor z)) x

end CoreFocus

/-! ### The selected accept is a frame of the CTX cache -/

section AcceptFrame
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
open PqxdhServerAuthNative (NativeState NativeGame)
open PqxdhServerAuthExperiment (GameState)
open PqxdhDeploymentBackend (gameCtxLens GameFrame)
open PqxdhDeploymentIdealSteps (tailCE acceptActive acceptInactive acceptExposed)

/-- The CTX cache of the shared native state with a recorded mark. -/
def markPut (s : NativeState KemSK × Option (ℕ × Coord)) (c : CtxRomAuth.CtxRO.QueryCache) :
    NativeState KemSK × Option (ℕ × Coord) :=
  (gameCtxLens.set s.1 c, s.2)

/-- A native step on the native component of a marked state is a slot frame when it is a frame of the CTX cache. -/
theorem frame_marked {α : Type} (step : NativeGame KemSK α) (frame : GameFrame step) :
    SlotFrame markPut (fun s => (fun r => (r.1, (r.2, s.2))) <$> liftS (step.run s.1) :
      StateT (NativeState KemSK × Option (ℕ × Coord)) (OracleComp SlotSpec) α) := fun s c => by
  change (fun r => (r.1, (r.2, s.2))) <$> OracleComp.liftComp (step.run (gameCtxLens.set s.1 c)) SlotSpec = _
  rw [frame s.1 c, OracleComp.liftComp_map, Functor.map_map]
  change _ = (fun r => (r.1, markPut r.2 c)) <$> ((fun r => (r.1, (r.2, s.2))) <$> liftS (step.run s.1))
  rw [Functor.map_map]
  rfl

/-- The marker client's private root (the restricted-ROM root and its session touch) is a frame of the CTX cache. -/
theorem romRoot_frame (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (input : PqxdhRegistrationJointKemOpaqueClient.Input Reader) :
    GameFrame (PqxdhRegistrationJointKemOpaqueClient.romRoot KemSK hmac index candidate input) := by
  unfold PqxdhRegistrationJointKemOpaqueClient.romRoot
  refine PqxdhDeploymentBackend.frame_bind ?_ fun root =>
    PqxdhDeploymentBackend.frame_bind (PqxdhDeploymentBackend.frame_local _ fun _ _ => rfl) fun _ =>
      PqxdhDeploymentBackend.frame_pure _
  intro s c
  simp only [PqxdhServerAuthNative.romRootBytes, StateT.run, Functor.map_map]
  rfl

/-- Every request of the marker client under `tailCE` is a frame of the CTX cache. -/
theorem tailCE_client_frame (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ)
    (query : (PqxdhRegistrationJointKemOpaqueClient.Spec Reader).Domain) :
    SlotFrame markPut (tailCE (KemSK := KemSK) (Reader := Reader) hmac index (.inl query)) := by
  rcases query with input | auxiliary
  · intro s c
    simp only [tailCE]
    cases input.shared with
    | challenge => rfl
    | known secret =>
        exact frame_marked _ (romRoot_frame hmac index _ input) s c
  · cases auxiliary with
    | eraseShared => exact frame_marked _ (PqxdhDeploymentBackend.frame_pure _)
    | eraseInput => exact frame_marked _ (PqxdhDeploymentBackend.frame_pure _)
    | consume rid =>
        exact frame_marked (PqxdhServerAuthNative.nativeConsume rid) (PqxdhDeploymentBackend.frame_local _ fun _ _ => rfl)

/-- The forwarded marker client under `tailCE` is a frame of the CTX cache. -/
theorem tailCE_forward_frame (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ) {α : Type}
    (work : OracleComp (PqxdhRegistrationJointKemOpaqueClient.Spec Reader) α) :
    SlotFrame markPut (simulateQ (tailCE (KemSK := KemSK) hmac index)
      (simulateQ PqxdhRegistrationJointKemOpaqueTail.forward work)) := by
  induction work using OracleComp.inductionOn with
  | pure a => simp only [simulateQ_pure]; exact SlotFrame.pure _ a
  | query_bind q next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        PqxdhRegistrationJointKemOpaqueTail.forward]
      exact SlotFrame.bind (tailCE_client_frame hmac index q) ih

/-- The marker tail after its install request: the marker client, then the pending publication. -/
noncomputable def tailRest (serverKeyId : Std.U64) (publicIdentity : PqxdhJointIdentity.PublicIdentity) (index : ℕ)
    (control : beaconcrypt_core.pqxdh.ServerState)
    (collected : Option (PqxdhRegistrationJointKemOpaqueClient.Input Reader) × List Pqxdh.Bytes) :
    OracleComp (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK) (Option ℕ) :=
  match collected.1 with
  | none => pure none
  | some input => do
      let returned ← simulateQ PqxdhRegistrationJointKemOpaqueTail.forward
        (PqxdhRegistrationJointKemOpaqueClient.client control
          ⟨PqxdhRootTableInitialization.rootArray publicIdentity.ed25519, serverKeyId⟩ input)
      match returned with
      | .ok (some token) => do
          let _ ← (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).query (.inr (.publish index token))
          pure (some index)
      | _ => pure none

/-- The marker tail is its install request followed by `tailRest`. -/
theorem tail_split (serverKeyId : Std.U64) (publicIdentity : PqxdhJointIdentity.PublicIdentity) (game : GameState KemSK)
    (collected : Option (PqxdhRegistrationJointKemOpaqueClient.Input Reader) × List Pqxdh.Bytes) :
    PqxdhRegistrationJointKemOpaqueTail.tail serverKeyId publicIdentity game collected =
      ((PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).query (.inr (.install
        { game with sessions := game.sessions + 1, server := { game.server with consumed := collected.2 } })) :
          OracleComp (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK) Unit) >>=
        fun _ => tailRest serverKeyId publicIdentity game.sessions game.server.control collected := rfl

/-- The marker tail after its install request is a frame of the CTX cache under `tailCE`. -/
theorem tailRest_frame (hmac : PqxdhSecretInputKdf.HmacSha512) (sessions : ℕ) (serverKeyId : Std.U64)
    (publicIdentity : PqxdhJointIdentity.PublicIdentity) (index : ℕ) (control : beaconcrypt_core.pqxdh.ServerState)
    (collected : Option (PqxdhRegistrationJointKemOpaqueClient.Input Reader) × List Pqxdh.Bytes) :
    SlotFrame markPut (simulateQ (tailCE (KemSK := KemSK) hmac sessions)
      (tailRest serverKeyId publicIdentity index control collected)) := by
  unfold tailRest
  rcases collected with ⟨_ | input, consumed⟩
  · simp only [simulateQ_pure]
    exact SlotFrame.pure _ _
  · simp only [simulateQ_bind]
    refine SlotFrame.bind (tailCE_forward_frame hmac sessions _) fun returned => ?_
    rcases returned with (_ | token) | _ | _
    · simp only [simulateQ_pure]
      exact SlotFrame.pure _ _
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        simulateQ_pure]
      exact SlotFrame.bind (frame_marked (PqxdhServerAuthNative.nativeModify fun current =>
        { current with pending := Function.update current.pending index (some token) })
          (PqxdhDeploymentBackend.frame_local _ fun _ _ => rfl)) fun _ => SlotFrame.pure _ _
    · simp only [simulateQ_pure]
      exact SlotFrame.pure _ _
    · simp only [simulateQ_pure]
      exact SlotFrame.pure _ _

/-- The marker tail under `tailCE`, from a game state with a replaced CTX cache, is the marker tail with its final cache replaced: its install request writes the replaced cache, and the rest is a frame. -/
theorem tailCE_tail_frame (hmac : PqxdhSecretInputKdf.HmacSha512) (serverKeyId : Std.U64)
    (publicIdentity : PqxdhJointIdentity.PublicIdentity) (game : GameState KemSK)
    (collected : Option (PqxdhRegistrationJointKemOpaqueClient.Input Reader) × List Pqxdh.Bytes)
    (family : PqxdhJointDhExtractFamily.State) (other : GameState KemSK) (mark : Option (ℕ × Coord))
    (c : CtxRomAuth.CtxRO.QueryCache) :
    (simulateQ (tailCE (KemSK := KemSK) hmac game.sessions)
        (PqxdhRegistrationJointKemOpaqueTail.tail serverKeyId publicIdentity { game with ctx := c } collected)).run
          ((family, other), mark) =
      (fun r => (r.1, markPut r.2 c)) <$> (simulateQ (tailCE (KemSK := KemSK) hmac game.sessions)
        (PqxdhRegistrationJointKemOpaqueTail.tail serverKeyId publicIdentity game collected)).run ((family, game), mark) := by
  rw [tail_split, tail_split, simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
  have install : ∀ (st : GameState KemSK) (s0 : NativeState KemSK × Option (ℕ × Coord)),
      (simulateQ (tailCE (KemSK := KemSK) (Reader := Reader) hmac game.sessions)
        (liftM ((PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).query (.inr (.install st))))).run s0 =
        pure ((), ((s0.1.1, st), s0.2)) := by
    intro st s0
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    rfl
  rw [install, install, pure_bind, pure_bind]
  exact tailRest_frame hmac game.sessions serverKeyId publicIdentity game.sessions game.server.control collected
    ((family, { game with sessions := game.sessions + 1, server := { game.server with consumed := collected.2 } }), mark) c

/-- The native accept tail, from a game state with a replaced CTX cache, is the tail with its final cache replaced (it overwrites the run state's game component). -/
theorem serverTail_frame (publicIdentity : PqxdhJointIdentity.PublicIdentity) (game : GameState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes)
    (family : PqxdhJointDhExtractFamily.State) (other : GameState KemSK) (c : CtxRomAuth.CtxRO.QueryCache) :
    (PqxdhRegistrationJointServerAccept.tail setup publicIdentity { game with ctx := c } collected).run (family, other) =
      (fun r => (r.1, gameCtxLens.set r.2 c)) <$>
        (PqxdhRegistrationJointServerAccept.tail setup publicIdentity game collected).run (family, game) := by
  have h := PqxdhDeploymentBackend.tail_frame setup publicIdentity game collected pure
    (fun _ => PqxdhDeploymentBackend.frame_pure _) family other c
  simp only [bind_pure] at h
  rw [h, PqxdhDeploymentBackend.tail_eq, PqxdhDeploymentBackend.nativeSet_run_bind,
    PqxdhDeploymentBackend.nativeSet_run_bind]

/-- The active selected accept is a slot frame of the CTX cache. -/
theorem acceptActive_frame (seed : PqxdhJointIdentity.IdentitySeed) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (verified : PqxdhServerRootPreparation.Verified Reader) :
    SlotFrame gameCtxLens.set (acceptActive (KemSK := KemSK) setup codec checks seed challenge verified) := by
  intro s c
  rcases s with ⟨family, game⟩
  change (acceptActive setup codec checks seed challenge verified).run (family, { game with ctx := c }) =
    (fun r => (r.1, gameCtxLens.set r.2 c)) <$> (acceptActive setup codec checks seed challenge verified).run (family, game)
  simp only [acceptActive, PqxdhDeploymentIdealSteps.liftS, StateT.run]
  rw [map_bind]
  refine bind_congr fun pre => ?_
  rcases pre with ⟨⟨_ | ephemeral, logged⟩, consumed⟩
  · have h := serverTail_frame (Reader := Reader) setup (setup.joint.publicKeys seed) game (none, consumed) family
      { game with ctx := c } c
    simp only [StateT.run] at h
    simp only
    rw [h, OracleComp.liftComp_map, bind_map_left, map_bind]
    refine bind_congr fun r => ?_
    rw [map_pure]
  · simp only
    rw [map_bind]
    refine bind_congr fun prepared => ?_
    have h := tailCE_tail_frame setup.hmac setup.serverKeyId (setup.joint.publicKeys seed) game prepared family
      { game with ctx := c } none c
    simp only [StateT.run] at h
    rw [h, bind_map_left, map_bind]
    refine bind_congr fun answer => ?_
    rw [map_pure]
    rfl

/-- The inactive selected accept (the LQ-F logged accept) is a slot frame of the CTX cache. -/
theorem acceptInactive_frame (seed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes) :
    SlotFrame gameCtxLens.set (acceptInactive (KemSK := KemSK) setup codec checks seed raw) := fun s c => by
  change (fun r => ((r.1, (false, none)), r.2)) <$> OracleComp.liftComp
      ((PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed raw).run (gameCtxLens.set s c)) SlotSpec = _
  rw [PqxdhDeploymentBackend.acceptLogged_frame setup codec checks seed raw s c, OracleComp.liftComp_map,
    Functor.map_map]
  change _ = (fun r => (r.1, gameCtxLens.set r.2 c)) <$> ((fun r => ((r.1, (false, none)), r.2)) <$> OracleComp.liftComp
      ((PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed raw).run s) SlotSpec)
  rw [Functor.map_map]

/-- The selected accept with its encapsulation exposed is a slot frame of the CTX cache. -/
theorem acceptExposed_frame (seed : PqxdhJointIdentity.IdentitySeed) (chosen : PqxdhLiveKemReservation.Pair KemSK)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (raw : Pqxdh.Bytes) :
    SlotFrame gameCtxLens.set (acceptExposed setup codec checks seed chosen challenge raw) := by
  unfold acceptExposed
  split
  · split
    · exact acceptActive_frame setup codec checks seed challenge _
    · exact acceptInactive_frame setup codec checks seed raw
  · exact acceptInactive_frame setup codec checks seed raw

end AcceptFrame

/-! ### The hidden build commutes with completions of the CTX cache -/

section BuildCommutes
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
open PqxdhServerAuthNative (NativeState NativeGame)
open PqxdhDeploymentBackend (gameCtxLens)
open PqxdhDeploymentIdealSteps (buildHidden)
open PqxdhRegistrationJointKemPostSkeleton (Hidden)

/-- The factored hidden build at a value is the factor-form hidden build at the value's material and seed. -/
theorem factoredHidden_build (value : PqxdhServerAuthKeySchedule.Output) :
    (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks value).hiddenBuild =
      PqxdhDeploymentHiddenEntry.buildFactor setup codec checks (PqxdhDeploymentHiddenLayout.splitOutput value).1
        (PqxdhDeploymentHiddenLayout.splitOutput value).2 := by
  unfold PqxdhDeploymentHiddenEntry.buildFactor
  rw [PqxdhDeploymentHiddenLayout.join_split]
  rfl

/-- The factored hidden finish at a value is the factor-form hidden finish at the value's material and seed. -/
theorem factoredHidden_after (value : PqxdhServerAuthKeySchedule.Output) :
    (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks value).hiddenAfter =
      PqxdhDeploymentHiddenEntry.finishFactor setup codec (PqxdhDeploymentHiddenLayout.splitOutput value).1
        (PqxdhDeploymentHiddenLayout.splitOutput value).2 := by
  unfold PqxdhDeploymentHiddenEntry.finishFactor
  rw [PqxdhDeploymentHiddenLayout.join_split]
  rfl

/-- The marked build of a session with a present pending token, in focused form. -/
noncomputable def hiddenTokenBuild (hidden : Hidden Response) (session : ℕ) (payload : Option Pqxdh.Bytes)
    (token : PqxdhServerRelatedRootConsumer.Returned) : NativeGame KemSK (Option PqxdhServerRegistrationPublication.Response) :=
  fun s => (fun r => ((PqxdhServerAuthExperiment.settle s.2.server r.1).1, (s.1, { s.2 with
      pending := Function.update s.2.pending session none
      server := (PqxdhServerAuthExperiment.settle s.2.server r.1).2
      ctx := r.2.2
      ghost := { s.2.ghost with seals := s.2.ghost.seals ++ r.2.1.map (fun context => (session, context)) } }))) <$>
    (hidden.hiddenBuild token payload s.2.server).run ([], s.2.ctx)

/-- The marked build commutes with completions of the CTX cache when its hidden build service does (the pattern of `PqxdhDeploymentBackend.nativeBuild_commutes`). -/
theorem buildHidden_commutes (hidden : Hidden Response) (session : ℕ) (payload : Option Pqxdh.Bytes)
    (commutes : ∀ token payload server, Commutes (PqxdhDeploymentHiddenEntry.sharedLens (List RawCtxSourceSend.SealContext))
      (hidden.hiddenBuild token payload server)) :
    Commutes gameCtxLens (buildHidden (KemSK := KemSK) hidden session payload) := by
  refine PqxdhDeploymentBackend.commutes_dispatch gameCtxLens _ (fun s => s.2.pending session) (fun _ _ => rfl)
    (fun found => match found with
      | none => pure none
      | some token => hiddenTokenBuild hidden session payload token)
    (fun s => ?_) (fun found => ?_)
  · change (PqxdhServerAuthNative.nativeGet >>= _).run s = _
    rw [PqxdhDeploymentBackend.nativeGet_bind]
    rcases found : s.2.pending session with _ | token
    · rfl
    · change (PqxdhServerAuthNative.nativeCoins _ >>= _).run s = _
      rw [PqxdhDeploymentBackend.nativeCoins_bind]
      simp only [hiddenTokenBuild, StateT.run, map_eq_bind_pure_comp]
      rfl
  · cases found with
    | none => exact LazyOracleDiscard.commutes_pure _ _
    | some token =>
        refine PqxdhDeploymentBackend.commutes_focus gameCtxLens
          (PqxdhDeploymentHiddenEntry.sharedLens (List RawCtxSourceSend.SealContext)) _
          (fun s => ([], s.2.ctx)) (fun s => hidden.hiddenBuild token payload s.2.server)
          (fun s b r => ((PqxdhServerAuthExperiment.settle s.2.server b).1, (s.1, { s.2 with
            pending := Function.update s.2.pending session none
            server := (PqxdhServerAuthExperiment.settle s.2.server b).2
            ctx := r.2
            ghost := { s.2.ghost with seals := s.2.ghost.seals ++ r.1.map (fun context => (session, context)) } })))
          (fun s => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
          (fun s => commutes token payload s.2.server)

/-- The factored marked build commutes with completions of the CTX cache. -/
theorem buildHidden_factored_commutes (value : PqxdhServerAuthKeySchedule.Output) (session : ℕ)
    (payload : Option Pqxdh.Bytes) :
    Commutes gameCtxLens (buildHidden (KemSK := KemSK)
      (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks value) session payload) :=
  buildHidden_commutes _ session payload fun token payload server => by
    rw [factoredHidden_build]
    exact PqxdhDeploymentHiddenEntry.buildFactor_commutes_ctx setup codec checks _ _ token payload server

end BuildCommutes

/-! ### Owner k's challenge finish, restructured -/

section FinishShape
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
open PqxdhServerAuthNative (NativeState NativeGame)
open PqxdhDeploymentIdealSteps (PreSpecCE OwnerSpecCE groupedOwnerCE preparationCE groupCE ownerImplCE finishChallenge)
open PqxdhRegistrationJointKemPostSkeleton (Hidden Pending)

/-- The preparation requests of the grouped owner pass through `ownerImplCE` as coins, with the state unchanged. -/
theorem ownerImpl_prepare (hidden : PqxdhServerAuthKeySchedule.Output → Hidden Response)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) {α : Type} (work : OracleComp (PreSpecCE KemSK Response) α)
    (s : NativeState KemSK × Option Coord) :
    (simulateQ (ownerImplCE setup codec hidden challenge)
        (simulateQ (fun query => ((OwnerSpecCE KemSK Response).query (.inl query) :
          OracleComp (OwnerSpecCE KemSK Response) _) : QueryImpl (PreSpecCE KemSK Response)
            (OracleComp (OwnerSpecCE KemSK Response))) work)).run s =
      (fun a => (a, s)) <$> liftS (simulateQ (preparationCE setup codec challenge) work) := by
  induction work using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, OracleComp.liftComp_bind, map_bind]
      change ((fun reply => (reply, s)) <$> liftS (preparationCE setup codec challenge q)) >>= _ = _
      rw [bind_map_left]
      refine bind_congr fun reply => ?_
      exact ih reply

/-- The grouped owner under `ownerImplCE`: the preparation as coins, then either the source commit without a staged result or the grouped finish request answered by `groupCE`, then the source commit. -/
theorem ownerRun (hidden : PqxdhServerAuthKeySchedule.Output → Hidden Response)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (raw : Pqxdh.Bytes) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (s : NativeState KemSK × Option Coord) :
    (simulateQ (ownerImplCE setup codec hidden challenge) (groupedOwnerCE (Response := Response) raw owner)).run s =
      match owner.beacon.phase with
      | .initSent control prekey oneTime kem =>
          liftS (simulateQ (preparationCE setup codec challenge)
            (PqxdhBeaconPhase2Shared.prepare control owner.beacon.identity prekey oneTime kem raw)) >>= fun prepared =>
              match prepared with
              | none => pure (PqxdhBeaconPhase2Publication.finish control owner none, s)
              | some prepared => (fun r => (PqxdhBeaconPhase2Publication.finish control owner r.1, r.2)) <$>
                  (groupCE setup codec hidden prepared).run s
      | _ => pure ((none, owner), s) := by
  unfold groupedOwnerCE
  split
  · rename_i control prekey oneTime kem phase
    simp only [phase]
    rw [simulateQ_bind, StateT.run_bind, ownerImpl_prepare, bind_map_left]
    refine bind_congr fun prepared => ?_
    cases prepared with
    | none => simp
    | some prepared =>
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
          StateT.run_bind, simulateQ_pure, StateT.run_pure]
        rw [map_eq_bind_pure_comp]
        rfl
  · rename_i notInit
    split
    · rename_i control prekey oneTime kem phase
      exact absurd phase (notInit _ _ _ _)
    · simp

end FinishShape

/-! ### Completions through maps of states -/

section CompleteMap
variable {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec ι₀} [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)]

/-- A map of states that carries one cache lens to another carries completions. -/
theorem completeOpt_map {σ₁ σ₂ : Type} (L₁ : CacheLens spec₀ σ₁) (L₂ : CacheLens spec₀ σ₂) (g : σ₁ → σ₂)
    (get_g : ∀ s, L₂.get (g s) = L₁.get s) (set_g : ∀ s c, g (L₁.set s c) = L₂.set (g s) c)
    (point : Option spec₀.Domain) (s : σ₁) :
    g <$> L₁.completeOpt point s = L₂.completeOpt point (g s) := by
  cases point with
  | none => simp only [StateLens.completeOpt, map_pure]
  | some t =>
      simp only [StateLens.completeOpt, StateLens.complete, Functor.map_map, get_g, set_g]

end CompleteMap

/-! ### Owner k's challenge finish in pointed form -/

section FinishPointed
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhServerAuthNative (NativeState NativeGame)
open PqxdhDeploymentIdealSteps (preparationCE groupCE ownerImplCE groupedOwnerCE finishChallenge finishStep
  initSentAt establishedAt erasedHidden IdealCore)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhRegistrationJointKemPostSkeleton (Hidden Pending embed message)
open PqxdhDeploymentBackend (gameLens gameCtxLens scheduleCtxLens)
open PqxdhDeploymentHiddenLayout (splitOutput)

/-- The CTX cache of the shared native state with recorded coordinates. -/
abbrev groupLens : CacheLens CtxRomAuth.CtxRO (NativeState KemSK × Option Coord) :=
  (StateLens.fst (NativeState KemSK) (Option Coord)).comp gameCtxLens

/-- The CTX cache of the registration state with recorded coordinates. -/
abbrev challengeLens : CacheLens CtxRomAuth.CtxRO (PqxdhRegistrationSchedule.State KemSK × Option Coord) :=
  (StateLens.fst (PqxdhRegistrationSchedule.State KemSK) (Option Coord)).comp scheduleCtxLens

/-- The grouped finish in pointed form: with the challenge marker and nonzero DH outputs, the erased hidden finish at the material and seed of the value read (`PqxdhDeploymentHiddenEntry.finishPointed`), reporting the CTX point of the opening it discards; every other grouped finish reports no point. -/
noncomputable def groupPointed (pending : Pending Response) :
    StateT (NativeState KemSK × Option Coord) (OracleComp SlotSpec)
      (Option PqxdhBeaconPhase2Publication.Staged × Option CtxRomAuth.CtxRO.Domain) := fun s =>
  match pending.root.shared with
  | .challenge =>
      if Pqxdh.dhNonZero (absBytes pending.root.dh1, absBytes pending.root.dh2, absBytes pending.root.dh3,
          absBytes pending.root.dh4) then do
        let coords := message pending.root.dh1 pending.root.dh2 pending.root.dh3 pending.root.dh4
        let value ← (SlotSpec.query (.inr coords) : OracleComp SlotSpec _)
        let r ← liftS ((PqxdhServerAuthNative.nativeCtx (KemSK := KemSK)
          (PqxdhDeploymentHiddenEntry.finishPointed setup codec (splitOutput value).1 (splitOutput value).2
            (embed pending))).run s.1)
        pure ((r.1.1, r.1.2.bind PqxdhDeploymentHiddenKernels.openPoint), (r.2, some coords))
      else pure ((none, none), s)
  | .known _ => (fun r => ((r.1, none), r.2)) <$> (groupCE setup codec (erasedHidden setup codec checks) pending).run s

/-- The grouped owner under `ownerImplCE`, restructured (`ownerRun`), with the pointed grouped finish. -/
noncomputable def ownerPointed (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (raw : Pqxdh.Bytes)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    StateT (NativeState KemSK × Option Coord) (OracleComp SlotSpec)
      ((Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) × Option CtxRomAuth.CtxRO.Domain) := fun s =>
  match owner.beacon.phase with
  | .initSent control prekey oneTime kem =>
      liftS (simulateQ (preparationCE setup codec challenge)
        (PqxdhBeaconPhase2Shared.prepare control owner.beacon.identity prekey oneTime kem raw)) >>= fun prepared =>
          match prepared with
          | none => pure ((PqxdhBeaconPhase2Publication.finish control owner none, none), s)
          | some prepared => (fun r => ((PqxdhBeaconPhase2Publication.finish control owner r.1.1, r.1.2), r.2)) <$>
              (groupPointed setup codec checks prepared).run s
  | _ => pure (((none, owner), none), s)

/-- Owner k's challenge finish in pointed form (`finishChallenge` with `ownerPointed`). -/
noncomputable def finishChallengePointed (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (index : ℕ)
    (raw : Pqxdh.Bytes) :
    StateT (PqxdhRegistrationSchedule.State KemSK × Option Coord) (OracleComp SlotSpec)
      (Option Pqxdh.Bytes × Option CtxRomAuth.CtxRO.Domain) := fun state =>
  match state.1.owners[index]? with
  | none => pure ((none, none), state)
  | some owner => do
      let result ← (ownerPointed setup codec checks challenge raw owner).run (state.1.shared, state.2)
      pure ((result.1.1.1, result.1.2),
        ({ shared := result.2.1, owners := state.1.owners.set index result.1.1.2 }, result.2.2))

/-- The finish of the ideal registration in pointed form: `finishStep` with `finishChallengePointed`; the real finish reports no point. -/
noncomputable def finishStepPointed (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (owner : ℕ) (raw : Pqxdh.Bytes) :
    StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) (Option Pqxdh.Bytes × Option CtxRomAuth.CtxRO.Domain) :=
  fun x =>
    if x.backend.active = true ∧ owner = t.kem.val ∧ initSentAt x.base.native.owners owner = true then do
      let r ← (finishChallengePointed setup codec checks p.challenge owner raw).run (x.base.native, none)
      pure ((r.1.1, r.1.2), { x with
        base := { x.base with native := r.2.1 }
        snap := PqxdhDeploymentLater.snapshotAt x.snap x.base.native.owners (some owner)
        backend := { x.backend with
          beacon := if establishedAt r.2.1.owners owner then r.2.2.or x.backend.beacon else x.backend.beacon } })
    else (fun r => ((r.1, none), r.2)) <$>
      onSlots (realRegAt setup codec route checks created ⟨.finish owner raw, trivial⟩) x

/-- The factor-form hidden finish on the shared native state is the pointed finish followed by the completion of the CTX point of the opening it discarded. -/
theorem nativeCtx_factor (m : PqxdhDeploymentHiddenLayout.Material) (seed : PqxdhRecordLiftSeed.Seed)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) (s : NativeState KemSK) :
    (PqxdhServerAuthNative.nativeCtx (PqxdhDeploymentHiddenEntry.finishFactor setup codec m seed pending)).run s =
      (PqxdhServerAuthNative.nativeCtx (PqxdhDeploymentHiddenEntry.finishPointed setup codec m seed pending)).run s >>=
        fun r => (r.1.1, ·) <$> gameCtxLens.completeOpt (r.1.2.bind PqxdhDeploymentHiddenKernels.openPoint) r.2 := by
  change (fun result => (result.1, gameLens.set s result.2)) <$>
      (PqxdhDeploymentHiddenEntry.finishFactor setup codec m seed pending).run (gameLens.get s) =
    ((fun result => (result.1, gameLens.set s result.2)) <$>
      (PqxdhDeploymentHiddenEntry.finishPointed setup codec m seed pending).run (gameLens.get s)) >>= _
  rw [PqxdhDeploymentHiddenEntry.finishFactor_pointed, map_bind, bind_map_left]
  refine bind_congr fun r => ?_
  rw [Functor.map_map]
  have moved := completeOpt_map (StateLens.snd Unit CtxRomAuth.CtxRO.QueryCache) gameCtxLens (gameLens.set s)
    (fun _ => rfl) (fun _ _ => rfl) (r.1.2.bind PqxdhDeploymentHiddenKernels.openPoint) r.2
  rw [← moved, Functor.map_map]

/-- The grouped finish with the factored hidden services is its pointed form followed by the completion of the reported point. -/
theorem group_factor (pending : Pending Response) (s : NativeState KemSK × Option Coord) :
    (groupCE setup codec (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) pending).run s =
      (groupPointed setup codec checks pending).run s >>= fun r =>
        (r.1.1, ·) <$> liftS (groupLens.completeOpt r.1.2 r.2) := by
  unfold groupPointed
  unfold groupCE
  rcases shared : pending.root.shared with _ | secret
  · simp only [StateT.run]
    split
    · rename_i nonzero
      simp only [bind_assoc, pure_bind]
      refine bind_congr fun value => ?_
      have h := nativeCtx_factor setup codec (splitOutput value).1 (splitOutput value).2 (embed pending) s.1
      simp only [StateT.run] at h
      rw [factoredHidden_after, h]
      simp only [liftS, OracleComp.liftComp_bind, bind_assoc]
      refine bind_congr fun r => ?_
      have moved := completeOpt_map gameCtxLens groupLens
        (fun n : NativeState KemSK => (n, some (message pending.root.dh1 pending.root.dh2 pending.root.dh3
          pending.root.dh4))) (fun _ => rfl) (fun _ _ => rfl) (r.1.2.bind PqxdhDeploymentHiddenKernels.openPoint) r.2
      rw [← moved]
      simp only [map_eq_bind_pure_comp, Function.comp_def, OracleComp.liftComp_bind, OracleComp.liftComp_pure,
        bind_assoc, pure_bind]
    · simp only [pure_bind, StateLens.completeOpt, OracleComp.liftComp_pure, map_pure]
  · simp only [StateT.run, map_eq_bind_pure_comp, bind_assoc, pure_bind, StateLens.completeOpt,
      OracleComp.liftComp_pure, Function.comp_def]

/-- The grouped owner with the factored hidden services is its pointed form followed by the completion of the reported point. -/
theorem owner_factor (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (raw : Pqxdh.Bytes)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (s : NativeState KemSK × Option Coord) :
    (simulateQ (ownerImplCE setup codec (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) challenge)
        (groupedOwnerCE (Response := Response) raw owner)).run s =
      (ownerPointed setup codec checks challenge raw owner).run s >>= fun r =>
        (r.1.1, ·) <$> liftS (groupLens.completeOpt r.1.2 r.2) := by
  rw [ownerRun]
  unfold ownerPointed
  split
  · simp only [StateT.run, bind_assoc]
    refine bind_congr fun prepared => ?_
    cases prepared with
    | none => simp only [pure_bind, StateLens.completeOpt, OracleComp.liftComp_pure, map_pure]
    | some prepared =>
        have h := group_factor setup codec checks prepared s
        simp only [StateT.run] at h
        simp only [h, map_bind, bind_map_left, Functor.map_map]
  · simp only [StateT.run, pure_bind, StateLens.completeOpt, OracleComp.liftComp_pure, map_pure]

/-- Owner k's challenge finish with the factored hidden services is its pointed form followed by the completion of the reported point. -/
theorem challenge_factor (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (index : ℕ) (raw : Pqxdh.Bytes)
    (state : PqxdhRegistrationSchedule.State KemSK × Option Coord) :
    (finishChallenge setup codec (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) challenge index
        raw).run state =
      (finishChallengePointed setup codec checks challenge index raw).run state >>= fun r =>
        (r.1.1, ·) <$> liftS (challengeLens.completeOpt r.1.2 r.2) := by
  unfold finishChallenge finishChallengePointed
  simp only [StateT.run]
  rcases found : state.1.owners[index]? with _ | owner
  · simp only [pure_bind, StateLens.completeOpt, OracleComp.liftComp_pure, map_pure]
  · have h := owner_factor setup codec checks challenge raw owner (state.1.shared, state.2)
    simp only [StateT.run] at h
    simp only [h, bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def]
    refine bind_congr fun r => ?_
    have moved := completeOpt_map groupLens challengeLens
      (fun n : NativeState KemSK × Option Coord =>
        (({ shared := n.1, owners := state.1.owners.set index r.1.1.2 } : PqxdhRegistrationSchedule.State KemSK), n.2))
      (fun _ => rfl) (fun _ _ => rfl) r.1.2 r.2
    rw [← moved]
    simp only [map_eq_bind_pure_comp, Function.comp_def, OracleComp.liftComp_bind, OracleComp.liftComp_pure,
      bind_assoc, pure_bind]

/-- The finish of the ideal registration with the factored hidden services is its pointed form followed by the completion of the reported point. -/
theorem finishStep_factor (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (owner : ℕ) (raw : Pqxdh.Bytes) (x : XState KemSK IdealCore 2) :
    (finishStep setup codec route checks t p (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks)
        created owner raw).run x =
      (finishStepPointed setup codec route checks t p created owner raw).run x >>= fun r =>
        (r.1.1, ·) <$> liftS (ctxLens.completeOpt r.1.2 r.2) := by
  unfold finishStep finishStepPointed
  simp only [StateT.run]
  split
  · have h := challenge_factor setup codec checks p.challenge owner raw (x.base.native, none)
    simp only [StateT.run] at h
    simp only [h, bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def]
    refine bind_congr fun r => ?_
    have moved := completeOpt_map challengeLens (ctxLens (KemSK := KemSK) (Bk := IdealCore) (n := 2))
      (fun y : PqxdhRegistrationSchedule.State KemSK × Option Coord => ({ x with
        base := { x.base with native := y.1 }
        snap := PqxdhDeploymentLater.snapshotAt x.snap x.base.native.owners (some owner)
        backend := { x.backend with
          beacon := if establishedAt y.1.owners owner then y.2.or x.backend.beacon else x.backend.beacon } } :
            XState KemSK IdealCore 2))
      (fun _ => rfl) (fun _ _ => rfl) r.1.2 r.2
    rw [← moved]
    simp only [map_eq_bind_pure_comp, Function.comp_def, OracleComp.liftComp_bind, OracleComp.liftComp_pure,
      bind_assoc, pure_bind]
  · simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, StateLens.completeOpt,
      OracleComp.liftComp_pure, Prod.mk.eta, bind_pure]

/-- The erased hidden finish on the shared native state is the pointed finish without its report. -/
theorem nativeCtx_erased (m : PqxdhDeploymentHiddenLayout.Material) (seed : PqxdhRecordLiftSeed.Seed)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) (s : NativeState KemSK) :
    (PqxdhServerAuthNative.nativeCtx (PqxdhDeploymentHiddenEntry.finishErasedSvc setup codec m seed pending)).run s =
      (fun r => (r.1.1, r.2)) <$>
        (PqxdhServerAuthNative.nativeCtx (PqxdhDeploymentHiddenEntry.finishPointed setup codec m seed pending)).run s := by
  change (fun result => (result.1, gameLens.set s result.2)) <$>
      (Prod.fst <$> PqxdhDeploymentHiddenEntry.finishPointed setup codec m seed pending).run (gameLens.get s) =
    (fun r => (r.1.1, r.2)) <$> ((fun result => (result.1, gameLens.set s result.2)) <$>
      (PqxdhDeploymentHiddenEntry.finishPointed setup codec m seed pending).run (gameLens.get s))
  rw [StateT.run_map, Functor.map_map, Functor.map_map]

/-- The pointed grouped finish without its report is the grouped finish with the erased hidden services. -/
theorem group_erase (pending : Pending Response) (s : NativeState KemSK × Option Coord) :
    (fun r => (r.1.1, r.2)) <$> (groupPointed setup codec checks pending).run s =
      (groupCE setup codec (erasedHidden setup codec checks) pending).run s := by
  unfold groupPointed
  unfold groupCE
  rcases shared : pending.root.shared with _ | secret
  · simp only [StateT.run]
    split
    · simp only [map_bind, map_pure]
      refine bind_congr fun value => ?_
      have h := nativeCtx_erased setup codec (splitOutput value).1 (splitOutput value).2 (embed pending) s.1
      simp only [StateT.run] at h
      change _ = liftS (PqxdhServerAuthNative.nativeCtx (PqxdhDeploymentHiddenEntry.finishErasedSvc setup codec
        (splitOutput value).1 (splitOutput value).2 (embed pending)) s.1) >>= _
      rw [h]
      simp only [liftS, OracleComp.liftComp_map, bind_map_left]
    · simp only [map_pure]
  · simp only [StateT.run, Functor.map_map]

/-- The pointed grouped owner without its report is the grouped owner under `ownerImplCE` with the erased hidden services. -/
theorem owner_erase (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (raw : Pqxdh.Bytes)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (s : NativeState KemSK × Option Coord) :
    (fun r => (r.1.1, r.2)) <$> (ownerPointed setup codec checks challenge raw owner).run s =
      (simulateQ (ownerImplCE setup codec (erasedHidden setup codec checks) challenge)
        (groupedOwnerCE (Response := Response) raw owner)).run s := by
  rw [ownerRun]
  unfold ownerPointed
  split
  · simp only [StateT.run, map_bind]
    refine bind_congr fun prepared => ?_
    cases prepared with
    | none => simp only [map_pure]
    | some prepared =>
        have h := group_erase setup codec checks prepared s
        simp only [StateT.run] at h
        simp only [← h, Functor.map_map]
  · simp only [StateT.run, map_pure]

/-- The pointed challenge finish without its report is the challenge finish with the erased hidden services. -/
theorem challenge_erase (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (index : ℕ) (raw : Pqxdh.Bytes)
    (state : PqxdhRegistrationSchedule.State KemSK × Option Coord) :
    (fun r => (r.1.1, r.2)) <$> (finishChallengePointed setup codec checks challenge index raw).run state =
      (finishChallenge setup codec (erasedHidden setup codec checks) challenge index raw).run state := by
  unfold finishChallenge finishChallengePointed
  simp only [StateT.run]
  rcases found : state.1.owners[index]? with _ | owner
  · simp only [map_pure]
  · have h := owner_erase setup codec checks challenge raw owner (state.1.shared, state.2)
    simp only [StateT.run] at h
    simp only [← h, map_bind, map_pure, bind_map_left]

/-- The pointed finish of the ideal registration without its report is its finish with the erased hidden services. -/
theorem finishStep_erase (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (owner : ℕ) (raw : Pqxdh.Bytes) (x : XState KemSK IdealCore 2) :
    (fun r => (r.1.1, r.2)) <$> (finishStepPointed setup codec route checks t p created owner raw).run x =
      (finishStep setup codec route checks t p (erasedHidden setup codec checks) created owner raw).run x := by
  unfold finishStep finishStepPointed
  simp only [StateT.run]
  split
  · have h := challenge_erase setup codec checks p.challenge owner raw (x.base.native, none)
    simp only [StateT.run] at h
    simp only [← h, map_bind, map_pure, bind_map_left]
  · simp only [Functor.map_map, Prod.mk.eta, id_map']

end FinishPointed

/-! ### Commutation of the ideal registration's commands -/

section IdealCommutes
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} {S : Type} (svc : PqxdhDeploymentSeedSplit.SlotService S 2)
open PqxdhDeploymentIdealSteps (acceptStep buildStep finishStep acceptExposed buildHidden publishedKey IdealCore
  idealProg createReg)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentBackend (gameCtxLens)
open PqxdhRegistrationJointKemPostSkeleton (Hidden)

/-- The raw accept of the ideal registration with its branch chosen: the selected ordinal (`acceptExposed`) or the real accept. -/
noncomputable def acceptBranch (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (raw : Pqxdh.Bytes) (selected : Bool) : StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) (Option ℕ) :=
  fun x =>
    let counted : XState KemSK IdealCore 2 := { x with backend := { x.backend with accepts := x.backend.accepts + 1 } }
    if selected then
      (fun r => (r.1.1.1, { counted with
          base := { counted.base with native := { counted.base.native with shared := r.2 } }
          log := counted.log ++ [r.1.1.2]
          backend := { counted.backend with active := r.1.2.1, marks := r.1.2.2 } })) <$>
        (acceptExposed setup codec checks created.seed p.chosen p.challenge raw).run x.base.native.shared
    else onSlots (realRegAt setup codec route checks created ⟨.accept raw, trivial⟩) counted

/-- Advancing the raw-accept counter. -/
def countAccept : StateT (XState KemSK IdealCore 2) ProbComp Unit :=
  modify fun x => { x with backend := { x.backend with accepts := x.backend.accepts + 1 } }

/-- The raw accept of the ideal registration commutes on pairs with completions of the CTX cache: the selected accept is a frame of the cache and every other accept is the real accept after the counter update. -/
theorem acceptStep_commutes (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (raw : Pqxdh.Bytes) :
    Commutes (pairLens (n := 2) (S := S) ctxLens) (onPair svc (acceptStep setup codec route checks t p created raw)) := by
  refine onPair_commutes_dispatch ctxLens svc _ (fun x => decide (x.backend.accepts = t.accept)) (fun _ _ => rfl)
    (acceptBranch setup codec route checks p created raw) (fun x => ?_) (fun selected => ?_)
  · by_cases same : x.backend.accepts = t.accept
    · simp only [acceptStep, acceptBranch, same, decide_true, ↓reduceIte, StateT.run]
    · simp only [acceptStep, acceptBranch, same, decide_false, ↓reduceIte, StateT.run, Bool.false_eq_true]
  · cases selected with
    | true =>
        refine onPair_commutes_frame ctxLens svc _ (SlotFrame.focus ctxLens.set gameCtxLens.set _
          (acceptExposed setup codec checks created.seed p.chosen p.challenge raw) (fun x => x.base.native.shared)
          (fun x b r => (b.1.1, { x with
            base := { x.base with native := { x.base.native with shared := r } }
            log := x.log ++ [b.1.2]
            backend := { x.backend with accepts := x.backend.accepts + 1, active := b.2.1, marks := b.2.2 } }))
          (fun x => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
          (acceptExposed_frame setup codec checks _ _ _ raw))
    | false =>
        have shape : acceptBranch setup codec route checks p created raw false =
            onSlots (countAccept >>= fun _ => realRegAt setup codec route checks created ⟨.accept raw, trivial⟩) := by
          funext x
          simp only [acceptBranch, countAccept, onSlots, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
            StateT.run_modify, pure_bind]
        rw [shape]
        refine onPair_commutes_onSlots ctxLens svc _ (LazyOracleDiscard.commutes_bind _ ?_ fun _ =>
          realRegAt_commutes_ctx setup codec route checks created ⟨.accept raw, trivial⟩)
        exact LazyOracleDiscard.commutes_frame _ _ fun x c => by
          simp only [countAccept, StateT.run_modify, map_pure]
          rfl

/-- A value request at fixed coordinates, as a slot step. -/
def readAt {σ : Type} (coords : Coord) : StateT σ (OracleComp SlotSpec) PqxdhServerAuthKeySchedule.Output :=
  fun x => (fun v => (v, x)) <$> (SlotSpec.query (.inr coords) : OracleComp SlotSpec _)

/-- A value request at fixed coordinates followed by a slot step. -/
theorem readAt_bind_run {σ α : Type} (coords : Coord) (next : PqxdhServerAuthKeySchedule.Output → StateT σ (OracleComp SlotSpec) α)
    (x : σ) : (readAt coords >>= next).run x =
      (SlotSpec.query (.inr coords) : OracleComp SlotSpec _) >>= fun value => (next value).run x := by
  rw [StateT.run_bind]
  simp only [readAt, StateT.run, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  rfl

/-- The marked build after its value request, in focused form. -/
noncomputable def buildFocus (hidden : Hidden Response) (session : ℕ) (payload : Option Pqxdh.Bytes) (coords : Coord) :
    StateT (XState KemSK IdealCore 2) ProbComp (Option PqxdhServerRegistrationPublication.Response) := fun x =>
  (fun r => (r.1, { x with
      base := { x.base with native := { x.base.native with shared := r.2 } }
      backend := { x.backend with
        peer := ((publishedKey r.1 r.2.2.server).map fun keyId => (keyId, coords)).or x.backend.peer } })) <$>
    (buildHidden hidden session payload).run x.base.native.shared

/-- The build of the ideal registration with its branch chosen from the mark and whether the session's token is pending. -/
noncomputable def buildBranch (hidden : PqxdhServerAuthKeySchedule.Output → Hidden Response)
    (created : PqxdhLiveServerConstruction.Created Unit) (session : ℕ) (payload : Option Pqxdh.Bytes)
    (choice : Option (ℕ × Coord) × Bool) :
    StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) (Option PqxdhServerRegistrationPublication.Response) :=
  match choice.1 with
  | some (index, coords) =>
      if index = session ∧ choice.2 = true then
        readAt coords >>= fun value => onSlots (buildFocus (hidden value) session payload coords)
      else onSlots (realRegAt setup codec route checks created ⟨.build session payload, trivial⟩)
  | none => onSlots (realRegAt setup codec route checks created ⟨.build session payload, trivial⟩)

/-- The build of the ideal registration commutes on pairs with completions of the CTX cache when every marked build does: the value request is a frame of the cache, the marked build commutes and every other build is real. -/
theorem buildStep_commutes (hidden : PqxdhServerAuthKeySchedule.Output → Hidden Response)
    (commutes : ∀ value session payload, Commutes gameCtxLens (buildHidden (KemSK := KemSK) (hidden value) session payload))
    (created : PqxdhLiveServerConstruction.Created Unit) (session : ℕ) (payload : Option Pqxdh.Bytes) :
    Commutes (pairLens (n := 2) (S := S) ctxLens)
      (onPair svc (buildStep setup codec route checks hidden created session payload)) := by
  refine onPair_commutes_dispatch ctxLens svc _
    (fun x => (x.backend.marks, (x.base.native.shared.2.pending session).isSome)) (fun _ _ => rfl)
    (buildBranch setup codec route checks hidden created session payload) (fun x => ?_) (fun choice => ?_)
  · rcases marked : x.backend.marks with _ | ⟨index, coords⟩
    · simp only [buildStep, buildBranch, marked, StateT.run]
    · by_cases chosen : index = session ∧ (x.base.native.shared.2.pending session).isSome = true
      · have branch : buildBranch setup codec route checks hidden created session payload
            (some (index, coords), (x.base.native.shared.2.pending session).isSome) =
              readAt coords >>= fun value => onSlots (buildFocus (hidden value) session payload coords) := by
          simp only [buildBranch, chosen, and_self, ↓reduceIte]
        rw [branch, readAt_bind_run]
        obtain ⟨rfl, pending⟩ := chosen
        simp only [buildStep, marked, pending, and_self, ↓reduceIte, StateT.run, onSlots, buildFocus, liftS,
          map_eq_bind_pure_comp, Function.comp_def, OracleComp.liftComp_bind, OracleComp.liftComp_pure]
      · have branch : buildBranch setup codec route checks hidden created session payload
            (some (index, coords), (x.base.native.shared.2.pending session).isSome) =
              onSlots (realRegAt setup codec route checks created ⟨.build session payload, trivial⟩) := by
          simp only [buildBranch, chosen, ↓reduceIte]
        rw [branch]
        simp only [buildStep, marked, chosen, ↓reduceIte, StateT.run]
  · rcases choice with ⟨_ | ⟨index, coords⟩, pending⟩
    · exact onPair_commutes_onSlots ctxLens svc _ (realRegAt_commutes_ctx setup codec route checks created _)
    · by_cases chosen : index = session ∧ pending = true
      · have branch : buildBranch setup codec route checks hidden created session payload
            (some (index, coords), pending) =
              readAt coords >>= fun value => onSlots (buildFocus (hidden value) session payload coords) := by
          simp only [buildBranch, chosen, and_self, ↓reduceIte]
        rw [branch, onPair_bind]
        refine LazyOracleDiscard.commutes_bind _ (onPair_commutes_frame ctxLens svc _
          (SlotFrame.read _ (fun _ => coords) fun _ _ => rfl)) fun value => ?_
        refine onPair_commutes_onSlots ctxLens svc _ (PqxdhDeploymentBackend.commutes_focus ctxLens gameCtxLens _
          (fun x => x.base.native.shared) (fun _ => buildHidden (hidden value) session payload)
          (fun x b r => (b, { x with
            base := { x.base with native := { x.base.native with shared := r } }
            backend := { x.backend with
              peer := ((publishedKey b r.2.server).map fun keyId => (keyId, coords)).or x.backend.peer } }))
          (fun x => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
          (fun _ => commutes value session payload))
      · have branch : buildBranch setup codec route checks hidden created session payload
            (some (index, coords), pending) =
              onSlots (realRegAt setup codec route checks created ⟨.build session payload, trivial⟩) := by
          simp only [buildBranch, chosen, ↓reduceIte]
        rw [branch]
        exact onPair_commutes_onSlots ctxLens svc _ (realRegAt_commutes_ctx setup codec route checks created _)

end IdealCommutes

/-! ### The erased finish commutes with completions of the CTX cache -/

section ErasedFinishCommutes
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} {S : Type} (svc : PqxdhDeploymentSeedSplit.SlotService S 2)
open PqxdhServerAuthNative (NativeState NativeGame)
open PqxdhDeploymentIdealSteps (preparationCE groupCE ownerImplCE groupedOwnerCE finishChallenge finishStep
  initSentAt establishedAt erasedHidden IdealCore)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhRegistrationJointKemPostSkeleton (Hidden Pending embed message)
open PqxdhDeploymentBackend (gameLens gameCtxLens scheduleCtxLens)

/-- Every request of item 2's native Beacon tail after the root commutes with completions of the CTX cache. -/
theorem tailNative_commutes (query : (PqxdhBeaconPhase2Shared.TailSpec Response
      PqxdhPhase2DecapsulationRouting.Shared).Domain) :
    Commutes (StateLens.snd Unit CtxRomAuth.CtxRO.QueryCache)
      (PqxdhRegistrationJointKemPostSkeleton.tailNative setup codec query) := by
  rcases query with query | (input | request | response)
  · exact PqxdhDeploymentBackend.beaconNative_commutes setup codec (.inl query)
  · exact LazyOracleDiscard.commutes_pure _ _
  · exact PqxdhDeploymentBackend.beaconNative_commutes setup codec (.inr (.initial request))
  · exact PqxdhDeploymentBackend.beaconNative_commutes setup codec (.inr (.application response))

/-- The native grouped finish with a known decapsulation result. -/
noncomputable def knownWork (pending : Pending Response) : NativeGame KemSK (Option PqxdhBeaconPhase2Publication.Staged) := do
  let root ← PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot setup.hmac (List.Vector.replicate 32 0) pending.root
  match root with
  | none => pure none
  | some root => PqxdhServerAuthNative.nativeCtx (simulateQ (PqxdhRegistrationJointKemPostSkeleton.tailNative setup codec)
      (PqxdhBeaconPhase2Shared.afterRoot codec.frameRead pending root))

/-- The native grouped finish with a known decapsulation result commutes with completions of the CTX cache. -/
theorem knownWork_commutes (pending : Pending Response) : Commutes gameCtxLens (knownWork (KemSK := KemSK) setup codec pending) := by
  unfold knownWork
  refine LazyOracleDiscard.commutes_bind _ ?_ fun root => ?_
  · unfold PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot
    split
    · exact (PqxdhDeploymentBackend.sourceRoot_frame _ _).commutes
    · exact LazyOracleDiscard.commutes_pure _ _
  · cases root with
    | none => exact LazyOracleDiscard.commutes_pure _ _
    | some root =>
        exact LazyOracleDiscard.commutes_lift gameLens _ _ (LazyOracleDiscard.commutes_simulateQ _ _
          (tailNative_commutes setup codec) _)

/-- The grouped finish with chosen branches: the hidden read and the hidden continuation on the shared CTX cache, nothing, or the known-result finish. -/
noncomputable def groupExplicit (hidden : PqxdhServerAuthKeySchedule.Output → Hidden Response) (pending : Pending Response) :
    StateT (NativeState KemSK × Option Coord) (OracleComp SlotSpec) (Option PqxdhBeaconPhase2Publication.Staged) :=
  match pending.root.shared with
  | .challenge =>
      if Pqxdh.dhNonZero (absBytes pending.root.dh1, absBytes pending.root.dh2, absBytes pending.root.dh3,
          absBytes pending.root.dh4) then
        readAt (message pending.root.dh1 pending.root.dh2 pending.root.dh3 pending.root.dh4) >>= fun value =>
          onSlots (fun s => (fun r => (r.1, (r.2, some (message pending.root.dh1 pending.root.dh2 pending.root.dh3
            pending.root.dh4)))) <$>
              (PqxdhServerAuthNative.nativeCtx ((hidden value).hiddenAfter (embed pending))).run s.1)
      else pure none
  | .known _ => onSlots (fun s => (fun r => (r.1, (r.2, s.2))) <$> (knownWork setup codec pending).run s.1)

theorem groupCE_explicit (hidden : PqxdhServerAuthKeySchedule.Output → Hidden Response) (pending : Pending Response) :
    groupCE (KemSK := KemSK) setup codec hidden pending = groupExplicit setup codec hidden pending := by
  funext s
  unfold groupCE groupExplicit
  rcases shared : pending.root.shared with _ | secret
  · simp only
    split
    · change _ = (readAt _ >>= _).run s
      rw [readAt_bind_run]
      simp only [onSlots, liftS, StateT.run, map_eq_bind_pure_comp, Function.comp_def, OracleComp.liftComp_bind,
        OracleComp.liftComp_pure]
    · rfl
  · simp only [onSlots, liftS, StateT.run, knownWork, OracleComp.liftComp_map]
    rfl

/-- The grouped finish with the erased hidden services commutes on pairs with completions of the CTX cache. -/
theorem groupCE_erased_commutes (pending : Pending Response) :
    Commutes (pairLens (n := 2) (S := S) groupLens)
      (onPair svc (groupCE (KemSK := KemSK) setup codec (erasedHidden setup codec checks) pending)) := by
  rw [groupCE_explicit]
  unfold groupExplicit
  split
  · split
    · rw [onPair_bind]
      refine LazyOracleDiscard.commutes_bind _ (onPair_commutes_frame groupLens svc _
        (SlotFrame.read _ (fun _ => _) fun _ _ => rfl)) fun value => ?_
      refine onPair_commutes_onSlots groupLens svc _ (PqxdhDeploymentBackend.commutes_focus groupLens gameCtxLens _
        (fun s => s.1) (fun _ => PqxdhServerAuthNative.nativeCtx ((erasedHidden setup codec checks value).hiddenAfter
          (embed pending)))
        (fun s b r => (b, (r, some (message pending.root.dh1 pending.root.dh2 pending.root.dh3 pending.root.dh4))))
        (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) fun _ => ?_)
      exact LazyOracleDiscard.commutes_lift gameLens _ _
        (PqxdhDeploymentHiddenEntry.finishErased_commutes_ctx setup codec _ _ (embed pending))
    · rw [onPair_pure]
      exact LazyOracleDiscard.commutes_pure _ _
  · exact onPair_commutes_onSlots groupLens svc _ (PqxdhDeploymentBackend.commutes_focus groupLens gameCtxLens _
      (fun s => s.1) (fun _ => knownWork setup codec pending) (fun s b r => (b, (r, s.2)))
      (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
      fun _ => knownWork_commutes setup codec pending)

/-- The grouped owner under `ownerImplCE` as a slot step with chosen branches (`ownerRun`). -/
noncomputable def ownerExplicit (hidden : PqxdhServerAuthKeySchedule.Output → Hidden Response)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (raw : Pqxdh.Bytes) (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    StateT (NativeState KemSK × Option Coord) (OracleComp SlotSpec)
      (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) :=
  match owner.beacon.phase with
  | .initSent control prekey oneTime kem =>
      onSlots (StateT.lift (simulateQ (preparationCE setup codec challenge)
        (PqxdhBeaconPhase2Shared.prepare control owner.beacon.identity prekey oneTime kem raw))) >>= fun prepared =>
          match prepared with
          | none => pure (PqxdhBeaconPhase2Publication.finish control owner none)
          | some prepared => (fun staged => PqxdhBeaconPhase2Publication.finish control owner staged) <$>
              groupCE setup codec hidden prepared
  | _ => pure (none, owner)

theorem owner_explicit (hidden : PqxdhServerAuthKeySchedule.Output → Hidden Response)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (raw : Pqxdh.Bytes) (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    simulateQ (ownerImplCE setup codec hidden challenge) (groupedOwnerCE (Response := Response) raw owner) =
      ownerExplicit setup codec hidden challenge raw owner := by
  funext s
  change (simulateQ (ownerImplCE setup codec hidden challenge) (groupedOwnerCE (Response := Response) raw owner)).run s =
    (ownerExplicit setup codec hidden challenge raw owner).run s
  rw [ownerRun]
  unfold ownerExplicit
  split
  · rw [StateT.run_bind]
    rw [onSlots_run]
    simp only [liftS, StateT.run_lift, OracleComp.liftComp_bind, OracleComp.liftComp_pure, bind_assoc, pure_bind]
    refine bind_congr fun prepared => ?_
    cases prepared with
    | none => rfl
    | some prepared => rw [StateT.run_map]
  · rfl

/-- The grouped owner with the erased hidden services commutes on pairs with completions of the CTX cache. -/
theorem owner_erased_commutes (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (raw : Pqxdh.Bytes)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    Commutes (pairLens (n := 2) (S := S) groupLens) (onPair svc (simulateQ (ownerImplCE setup codec
      (erasedHidden setup codec checks) challenge) (groupedOwnerCE (Response := Response) raw owner))) := by
  rw [owner_explicit]
  unfold ownerExplicit
  split
  · rw [onPair_bind]
    refine LazyOracleDiscard.commutes_bind _ (onPair_commutes_onSlots groupLens svc _
      (PqxdhDeploymentBackend.commutes_lift_comp _ _)) fun prepared => ?_
    cases prepared with
    | none =>
        rw [onPair_pure]
        exact LazyOracleDiscard.commutes_pure _ _
    | some prepared =>
        rw [onPair_map]
        exact LazyOracleDiscard.commutes_map _ _ (groupCE_erased_commutes setup codec checks svc prepared)
  · rw [onPair_pure]
    exact LazyOracleDiscard.commutes_pure _ _

/-- Owner k's challenge finish with its branch chosen from the addressed owner. -/
noncomputable def challengeBranch (hidden : PqxdhServerAuthKeySchedule.Output → Hidden Response)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (index : ℕ) (raw : Pqxdh.Bytes)
    (found : Option (PqxdhRegistrationSchedule.Owner KemSK)) :
    StateT (PqxdhRegistrationSchedule.State KemSK × Option Coord) (OracleComp SlotSpec) (Option Pqxdh.Bytes) :=
  match found with
  | none => pure none
  | some owner => fun state => (fun result => (result.1.1,
      (({ shared := result.2.1, owners := state.1.owners.set index result.1.2 } : PqxdhRegistrationSchedule.State KemSK),
        result.2.2))) <$>
      (simulateQ (ownerImplCE setup codec hidden challenge) (groupedOwnerCE (Response := Response) raw owner)).run
        (state.1.shared, state.2)

/-- Owner k's challenge finish with the erased hidden services commutes on pairs with completions of the CTX cache. -/
theorem challenge_erased_commutes (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (index : ℕ) (raw : Pqxdh.Bytes) :
    Commutes (pairLens (n := 2) (S := S) challengeLens)
      (onPair svc (finishChallenge (KemSK := KemSK) setup codec (erasedHidden setup codec checks) challenge index raw)) := by
  refine onPair_commutes_dispatch challengeLens svc _ (fun state => state.1.owners[index]?) (fun _ _ => rfl)
    (challengeBranch setup codec (erasedHidden setup codec checks) challenge index raw) (fun state => ?_)
    (fun found => ?_)
  · unfold finishChallenge challengeBranch
    simp only [StateT.run]
    rcases state.1.owners[index]? with _ | owner
    · rfl
    · simp only [map_eq_bind_pure_comp, Function.comp_def]
  · cases found with
    | none =>
        simp only [challengeBranch]
        rw [onPair_pure]
        exact LazyOracleDiscard.commutes_pure _ _
    | some owner =>
        exact onPair_commutes_focus challengeLens groupLens svc _ _ (fun state => (state.1.shared, state.2))
          (fun state b r => (b.1, (({ shared := r.1, owners := state.1.owners.set index b.2 } :
            PqxdhRegistrationSchedule.State KemSK), r.2))) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
          (fun _ _ _ _ => rfl) (owner_erased_commutes setup codec checks svc challenge raw owner)

/-- The finish of the ideal registration with its branch chosen. -/
noncomputable def finishBranch (hidden : PqxdhServerAuthKeySchedule.Output → Hidden Response) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (owner : ℕ) (raw : Pqxdh.Bytes) (challenged : Bool) :
    StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) (Option Pqxdh.Bytes) :=
  if challenged then fun x =>
    (fun r => (r.1, ({ x with
      base := { x.base with native := r.2.1 }
      snap := PqxdhDeploymentLater.snapshotAt x.snap x.base.native.owners (some owner)
      backend := { x.backend with
        beacon := if establishedAt r.2.1.owners owner then r.2.2.or x.backend.beacon else x.backend.beacon } } :
          XState KemSK IdealCore 2))) <$>
      (finishChallenge setup codec hidden p.challenge owner raw).run (x.base.native, none)
  else onSlots (realRegAt setup codec route checks created ⟨.finish owner raw, trivial⟩)

/-- The finish of the ideal registration with the erased hidden services commutes on pairs with completions of the CTX cache. -/
theorem finishStep_erased_commutes (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (owner : ℕ) (raw : Pqxdh.Bytes) :
    Commutes (pairLens (n := 2) (S := S) ctxLens)
      (onPair svc (finishStep setup codec route checks t p (erasedHidden setup codec checks) created owner raw)) := by
  refine onPair_commutes_dispatch ctxLens svc _
    (fun x => decide (x.backend.active = true ∧ owner = t.kem.val ∧ initSentAt x.base.native.owners owner = true))
    (fun _ _ => rfl) (finishBranch setup codec route checks (erasedHidden setup codec checks) p created owner raw)
    (fun x => ?_) (fun challenged => ?_)
  · unfold finishStep finishBranch
    by_cases chosen : x.backend.active = true ∧ owner = t.kem.val ∧ initSentAt x.base.native.owners owner = true
    · simp only [StateT.run, ite_eq_left chosen, decide_eq_true chosen, ↓reduceIte, map_eq_bind_pure_comp,
        Function.comp_def]
    · simp only [StateT.run, ite_eq_right chosen, decide_eq_false chosen, ↓reduceIte, Bool.false_eq_true]
  · cases challenged with
    | true =>
        exact onPair_commutes_focus ctxLens challengeLens svc _ _ (fun x => (x.base.native, none))
          (fun x b r => (b, ({ x with
            base := { x.base with native := r.1 }
            snap := PqxdhDeploymentLater.snapshotAt x.snap x.base.native.owners (some owner)
            backend := { x.backend with
              beacon := if establishedAt r.1.owners owner then r.2.or x.backend.beacon else x.backend.beacon } } :
                XState KemSK IdealCore 2)))
          (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
          (challenge_erased_commutes setup codec checks svc p.challenge owner raw)
    | false =>
        exact onPair_commutes_onSlots ctxLens svc _ (realRegAt_commutes_ctx setup codec route checks created _)

end ErasedFinishCommutes

/-! ### C7 for the ideal registration -/

section IdealPair
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhDeploymentIdealSteps (idealReg idealCore idealCoreErased idealProg TableState IdealBk idealInit IdealCore
  finishStep erasedHidden)
open PqxdhDeploymentIdealParams (Target Params drawParams)
open PqxdhDeploymentFinishErasure (PointedReg FinishPair outcomeMap fullX)
open PqxdhRecordLiftInterface (EnvQuery EnvSpec)

/-- The pointed form of each command of the ideal registration core: owner k's challenge finish reports the CTX point of the opening its hidden continuation discards (`finishStepPointed`), every other command reports none. -/
noncomputable def idealPointed (t : Target count) (p : Params KemSK count) {S : Type}
    (svc : PqxdhDeploymentSeedSplit.SlotService S 2) (created : PqxdhLiveServerConstruction.Created Unit) :
    (query : EnvQuery) →
      StateT (XState KemSK (IdealBk S) 2) ProbComp (EnvSpec.Range query × Option CtxRomAuth.CtxRO.Domain)
  | ⟨.finish owner raw, _⟩ => fun x => (fun r => ((r.1.1, r.1.2), attach r.2.1 r.2.2.1 r.2.2.2)) <$>
      (onPair svc (finishStepPointed setup codec route checks t p created owner raw)).run
        (detach x, (x.backend.2.1, x.backend.1))
  | query => (·, none) <$> idealCore setup codec route checks t p svc created query

/-- Every command of the ideal registration core other than the finish is the command of the C7-erased core. -/
theorem idealProg_erased_other (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : EnvQuery)
    (other : ∀ owner raw, query.val ≠ .finish owner raw) :
    idealProg setup codec route checks t p (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks)
        created query =
      idealProg setup codec route checks t p (erasedHidden setup codec checks) created query := by
  rcases query with ⟨command, isEnv⟩
  cases command
  case finish owner raw => exact absurd rfl (other owner raw)
  all_goals rfl

/-- The pointed finish without its report is the C7-erased core's finish. -/
theorem idealPointed_finish_erased (t : Target count) (p : Params KemSK count) {S : Type}
    (svc : PqxdhDeploymentSeedSplit.SlotService S 2) (created : PqxdhLiveServerConstruction.Created Unit)
    (owner : ℕ) (raw : Pqxdh.Bytes) :
    Prod.fst <$> idealPointed setup codec route checks t p svc created ⟨.finish owner raw, trivial⟩ =
      idealCoreErased setup codec route checks t p svc created ⟨.finish owner raw, trivial⟩ := by
  have erased : (Prod.fst <$> finishStepPointed setup codec route checks t p created owner raw) =
      finishStep setup codec route checks t p (erasedHidden setup codec checks) created owner raw := by
    funext x
    exact (StateT.run_map _ _ _).trans (finishStep_erase setup codec route checks t p created owner raw x)
  funext x
  change (Prod.fst <$> idealPointed setup codec route checks t p svc created ⟨.finish owner raw, trivial⟩).run x =
    (idealCoreErased setup codec route checks t p svc created ⟨.finish owner raw, trivial⟩).run x
  rw [StateT.run_map, PqxdhDeploymentIdealSteps.idealCoreErased, slotCore_pair]
  change _ = (fun r => (r.1, attach r.2.1 r.2.2.1 r.2.2.2)) <$>
    (onPair svc (finishStep setup codec route checks t p (erasedHidden setup codec checks) created owner raw)).run
      (detach x, (x.backend.2.1, x.backend.1))
  rw [← erased, onPair_map, StateT.run_map, Functor.map_map]
  change (fun q => (q.1.1, q.2)) <$> ((fun r => ((r.1.1, r.1.2), attach r.2.1 r.2.2.1 r.2.2.2)) <$>
    (onPair svc (finishStepPointed setup codec route checks t p created owner raw)).run
      (detach x, (x.backend.2.1, x.backend.1))) = _
  rw [Functor.map_map]

/-- Every command of the ideal registration core commutes with completions of the CTX cache, except owner k's challenge finish. -/
theorem idealCore_commutes (t : Target count) (p : Params KemSK count) {S : Type}
    (svc : PqxdhDeploymentSeedSplit.SlotService S 2) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : EnvQuery) (other : ∀ owner raw, query.val ≠ .finish owner raw) :
    Commutes ctxLens (idealCore setup codec route checks t p svc created query) := by
  rcases query with ⟨command, isEnv⟩
  cases command
  case create pin keyId => exact (idealCore_real_commutes_ctx setup codec route checks t p svc created).1 pin keyId
  case bundle owner => exact (idealCore_real_commutes_ctx setup codec route checks t p svc created).2.1 owner
  case hmac key message => exact (idealCore_real_commutes_ctx setup codec route checks t p svc created).2.2 key message
  case accept raw =>
    exact slotCore_commutes _ svc created _ (acceptStep_commutes setup codec route checks svc t p created raw)
  case build session payload =>
    exact slotCore_commutes _ svc created _ (buildStep_commutes setup codec route checks svc _
      (fun value session payload => buildHidden_factored_commutes setup codec checks value session payload)
      created session payload)
  case finish owner raw => exact absurd rfl (other owner raw)
  all_goals exact absurd isEnv id

/-- C7's pair for the ideal registration core over any slot service: the core with its pointed form, whose only point is owner k's challenge finish (the opening its hidden continuation discards). -/
noncomputable def idealPair (t : Target count) (p : Params KemSK count) {S : Type}
    (svc : PqxdhDeploymentSeedSplit.SlotService S 2) (created : PqxdhLiveServerConstruction.Created Unit) :
    FinishPair KemSK (IdealBk S) 2 where
  reg := idealCore setup codec route checks t p svc created
  pointed := idealPointed setup codec route checks t p svc created
  factor query x := by
    rcases query with ⟨command, isEnv⟩
    cases command
    case finish owner raw =>
      exact slotCore_factor _ svc created _ _ (onPair_factor ctxLens svc _ _
        (finishStep_factor setup codec route checks t p created owner raw)) x
    all_goals exact LawEq.of_eq (by
      simp only [idealPointed, StateT.run_map, bind_map_left, StateLens.completeOpt, map_pure, Prod.mk.eta, bind_pure])
  oblivious query := by
    rcases query with ⟨command, isEnv⟩
    cases command
    case finish owner raw =>
      rw [idealPointed_finish_erased]
      exact slotCore_commutes _ svc created _
        (finishStep_erased_commutes setup codec route checks svc t p created owner raw)
    all_goals
      simp only [idealPointed, Functor.map_map, id_map']
      exact idealCore_commutes setup codec route checks t p svc created _ (fun _ _ same => by cases same)

/-- The registration handler of C7's pair is the ideal registration core. -/
theorem idealPair_reg (t : Target count) (p : Params KemSK count) {S : Type}
    (svc : PqxdhDeploymentSeedSplit.SlotService S 2) (created : PqxdhLiveServerConstruction.Created Unit) :
    (idealPair setup codec route checks t p svc created).reg = idealCore setup codec route checks t p svc created := rfl

/-- The erased handler of C7's pair is the C7-erased ideal registration core. -/
theorem idealPair_erased (t : Target count) (p : Params KemSK count) {S : Type}
    (svc : PqxdhDeploymentSeedSplit.SlotService S 2) (created : PqxdhLiveServerConstruction.Created Unit) :
    (idealPair setup codec route checks t p svc created).erased =
      idealCoreErased setup codec route checks t p svc created := by
  funext query
  rcases query with ⟨command, isEnv⟩
  cases command
  case finish owner raw => exact idealPointed_finish_erased setup codec route checks t p svc created owner raw
  all_goals
    simp only [PointedReg.erased, idealPair, idealPointed, Functor.map_map, id_map']
    rfl

end IdealPair

/-! ### C7: the ideal game and its erased twin -/

section EraseGame
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} {A X : Type}
open PqxdhDeploymentIdealSteps (idealReg idealCoreErased TableState IdealBk idealInit idealGame)
open PqxdhDeploymentIdealParams (Target Params drawParams)
open PqxdhDeploymentFinishErasure (outcomeMap fullX)
open PqxdhDeploymentInterface (Budget FreshBounds Mode ModeSpec)

/-- C7 for the ideal registration (run phase, pointwise in the target and the challenger's draws): the common deployment experiment with the ideal registration and with its C7-erased core have the same law of the Server's public data, the adversary's output, the ledger and the final state with the CTX cache emptied. -/
theorem erase_ideal (t : Target count) (p : Params KemSK count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    LawEq (outcomeMap fullX <$> (PqxdhDeploymentBackend.gameWith setup codec route idealInit
        (idealReg setup codec route checks t p) ensureInit identityIndex bounds mode adversary).run runtime)
      (outcomeMap fullX <$> (PqxdhDeploymentBackend.gameWith setup codec route idealInit
        (idealCoreErased setup codec route checks t p PqxdhDeploymentSeedSplit.tableService) ensureInit identityIndex
          bounds mode adversary).run runtime) := by
  have erased := PqxdhDeploymentFinishErasure.erase_game_ctx setup codec route
    (fun created => idealPair setup codec route checks t p PqxdhDeploymentSeedSplit.tableService created) idealInit
    ensureInit identityIndex bounds mode adversary runtime
  simp only [idealPair_erased] at erased
  exact erased

/-- `CE.idealGame° g`: the challenger's draws, then the common deployment experiment with the C7-erased ideal registration core over item 2's persistent lazy table at the target of `g`, with identity index 0. -/
noncomputable def idealGameErased (budget : Budget) (g : Fin budget.accept × Fin budget.capacity)
    (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    StateT A ProbComp (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X ×
      PqxdhDeploymentSecrecy.Ledger × XState KemSK (IdealBk TableState) 2)) := fun runtime => do
  let p ← drawParams setup budget.create
  (PqxdhDeploymentBackend.gameWith setup codec route idealInit
    (idealCoreErased setup codec route checks (Target.ofCE budget g) p PqxdhDeploymentSeedSplit.tableService) ensureInit 0
      bounds mode adversary).run runtime

/-- C7 for `CE.idealGame g`: it and `CE.idealGame° g` have the same law of the Server's public data, the adversary's output, the ledger and the final state with the CTX cache emptied. -/
theorem erase_idealGame (budget : Budget) (g : Fin budget.accept × Fin budget.capacity)
    (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    LawEq (outcomeMap fullX <$> (idealGame setup codec route checks budget g ensureInit bounds mode adversary).run runtime)
      (outcomeMap fullX <$>
        (idealGameErased setup codec route checks budget g ensureInit bounds mode adversary).run runtime) := by
  simp only [idealGame, idealGameErased, StateT.run, map_bind]
  exact LawEq.bind (LawEq.refl _) fun p =>
    erase_ideal setup codec route checks (Target.ofCE budget g) p ensureInit 0 bounds mode adversary runtime

end EraseGame

end BeaconcryptCore.Computational.PqxdhDeploymentIdealErase

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.realRegAt_forget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.realRegAt_forget

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.realRegAt_commutes_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.realRegAt_commutes_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.slotImpl_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.slotImpl_coins

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.onSlots_run' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.onSlots_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.slotCore_onSlots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.slotCore_onSlots

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.slotCore_commutes_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.slotCore_commutes_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.createReg_commutes_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.createReg_commutes_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.idealCore_real_commutes_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.idealCore_real_commutes_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.onPair_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.onPair_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.onPair_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.onPair_bind

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.onPair_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.onPair_pure

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.onPair_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.onPair_map

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.onPair_onSlots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.onPair_onSlots

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.SlotFrame.pure' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.SlotFrame.pure

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.SlotFrame.bind' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.SlotFrame.bind

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.SlotFrame.map' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.SlotFrame.map

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.SlotFrame.onSlots' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.SlotFrame.onSlots

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.SlotFrame.read' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.SlotFrame.read

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.SlotFrame.simulateQ' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.SlotFrame.simulateQ

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.SlotFrame.focus' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.SlotFrame.focus

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.onPair_commutes_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.onPair_commutes_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.onPair_commutes_onSlots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.onPair_commutes_onSlots

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.onPair_focus' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.onPair_focus

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.onPair_commutes_focus' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.onPair_commutes_focus

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.onPair_dispatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.onPair_dispatch

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.onPair_commutes_dispatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.onPair_commutes_dispatch

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.pairLens_completeOpt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.pairLens_completeOpt

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.onPair_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.onPair_factor

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.slotCore_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.slotCore_pair

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.slotCore_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.slotCore_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.slotCore_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.slotCore_factor

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.frame_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.frame_marked

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.romRoot_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.romRoot_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.tailCE_client_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.tailCE_client_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.tailCE_forward_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.tailCE_forward_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.tail_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.tail_split

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.tailRest_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.tailRest_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.tailCE_tail_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.tailCE_tail_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.serverTail_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.serverTail_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.acceptActive_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.acceptActive_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.acceptInactive_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.acceptInactive_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.acceptExposed_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.acceptExposed_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.factoredHidden_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.factoredHidden_build

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.factoredHidden_after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.factoredHidden_after

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.buildHidden_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.buildHidden_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.buildHidden_factored_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.buildHidden_factored_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.ownerImpl_prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.ownerImpl_prepare

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.ownerRun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.ownerRun

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.completeOpt_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.completeOpt_map

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.nativeCtx_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.nativeCtx_factor

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.group_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.group_factor

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.owner_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.owner_factor

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.challenge_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.challenge_factor

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.finishStep_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.finishStep_factor

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.nativeCtx_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.nativeCtx_erased

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.group_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.group_erase

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.owner_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.owner_erase

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.challenge_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.challenge_erase

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.finishStep_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.finishStep_erase

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.acceptStep_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.acceptStep_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.readAt_bind_run' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.readAt_bind_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.buildStep_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.buildStep_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.tailNative_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.tailNative_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.knownWork_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.knownWork_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.groupCE_explicit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.groupCE_explicit

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.groupCE_erased_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.groupCE_erased_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.owner_explicit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.owner_explicit

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.owner_erased_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.owner_erased_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.challenge_erased_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.challenge_erased_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.finishStep_erased_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.finishStep_erased_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.idealProg_erased_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.idealProg_erased_other

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.idealPointed_finish_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.idealPointed_finish_erased

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.idealCore_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.idealCore_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.idealPair_reg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.idealPair_reg

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.idealPair_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.idealPair_erased

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.erase_ideal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.erase_ideal

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.erase_idealGame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealErase.erase_idealGame
