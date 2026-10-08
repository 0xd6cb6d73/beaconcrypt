-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentBackend

/-!
# Erasing discarded lazy completions from the pluggable native game (C7, generic form)

A pointed registration handler (`PointedReg L`) for a lazily sampled cache focused by the lens `L` of the extended state pairs a registration handler `reg` with a pointed handler: in law, every command of `reg` is its pointed step followed by the completion of the cache point the step reports (`factor`), and every pointed step commutes with completions (`oblivious`). The erased handler forgets the reported points and completes nothing. `erase_game` is the global erasure for the run phase of `gameWith` (critique M4, CE plan section 26): whenever the fixed steps of the handler (coins, BLAKE2b, records) commute with completions of the cache, the games with `reg` and with the erased handler have the same law of the Server's public data, the adversary's output, the ledger and every projection of the final state that does not see the cache. `erase_later` is the same equality for the LQ-F later game `laterWith`, whose post phase is a pluggable handler `postWith` that commutes with completions (critique m7) and whose reveal does not see the cache.

`FinishPair` is the CTX-cache instance (C7): for the CTX lens the fixed steps commute by `PqxdhDeploymentBackend.fixed_commute_ctx`, so `erase_game_ctx` and `erase_later_ctx` need no premise beyond the pointed pair itself, and they compare the final states with the CTX cache emptied. The real registration handler is a pair with no point (`realPair`), and its later game with the real post phase `realPost` is the LQ-F game (`laterWith_real`). `factor_focus` turns a pointed inner step on a sub-state into a pointed step of the whole state, the construction the ideal registration of CE-11b uses for its hidden finish with `PqxdhDeploymentHiddenEntry.finishFactor_pointed`.

C7 for the ideal game `CE.idealGame g` itself is the instance of `erase_game_ctx` at the ideal registration handler, built in CE-11b. These are equalities in law of a lazily sampled cache. No security claim is made here.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec Command ModeSpec Mode FreshBounds asModeO)
open PqxdhDeploymentBackend (XState RegImpl handlerWith gameWith xinitial ctxLens seedLens realReg)
open LazyOracleDiscard (Commutes StateLens CacheLens LawEq)

variable {KemSK Bk : Type} {n : Nat}
variable {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec ι₀} [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)]

/-! ### Pointed registration handlers -/

/-- A registration handler with its pointed form for the lazily sampled cache focused by `L`: in law, each command is its pointed step followed by the completion of the reported point, and every pointed step commutes with completions. -/
structure PointedReg (L : CacheLens spec₀ (XState KemSK Bk n)) where
  reg : RegImpl KemSK Bk n
  pointed : (query : PqxdhRecordLiftInterface.EnvQuery) →
    StateT (XState KemSK Bk n) ProbComp (PqxdhRecordLiftInterface.EnvSpec.Range query × Option spec₀.Domain)
  factor : ∀ query state, LawEq ((reg query).run state)
    ((pointed query).run state >>= fun r => (r.1.1, ·) <$> L.completeOpt r.1.2 r.2)
  oblivious : ∀ query, Commutes L (Prod.fst <$> pointed query)

/-- The erased handler: the pointed steps without their points, and no completion. -/
noncomputable def PointedReg.erased {L : CacheLens spec₀ (XState KemSK Bk n)} (pair : PointedReg L) :
    RegImpl KemSK Bk n :=
  fun query => Prod.fst <$> pair.pointed query

/-- A registration handler whose every command commutes with completions is a pointed handler with no point; its erased handler is itself. -/
noncomputable def PointedReg.ofCommuting {L : CacheLens spec₀ (XState KemSK Bk n)} (reg : RegImpl KemSK Bk n)
    (commutes : ∀ query, Commutes L (reg query)) : PointedReg L where
  reg := reg
  pointed query := (·, none) <$> reg query
  factor query state := LawEq.of_eq (by
    simp only [StateT.run_map, bind_map_left, StateLens.completeOpt, map_pure, Prod.mk.eta, bind_pure])
  oblivious query := by
    rw [Functor.map_map]
    simpa only [id_map'] using commutes query

/-- The erased handler of a pointed handler with no point is the handler itself. -/
theorem PointedReg.ofCommuting_erased {L : CacheLens spec₀ (XState KemSK Bk n)} (reg : RegImpl KemSK Bk n)
    (commutes : ∀ query, Commutes L (reg query)) : (PointedReg.ofCommuting reg commutes).erased = reg := by
  funext query
  simp only [PointedReg.erased, PointedReg.ofCommuting, Functor.map_map, id_map']

/-! ### Pointed steps through a focused sub-state -/

/-- A step that runs an inner program on a sub-state, with everything else a frame of the cache, has the pointed form of its inner program: if the inner program is, in law, a pointed step followed by the completion of the reported point of the sub-state's cache, the whole step is the lifted pointed step followed by the completion of the same point of the whole state's cache. -/
theorem factor_focus {σ ρ α β : Type} (L : CacheLens spec₀ σ) (M : CacheLens spec₀ ρ) (step : StateT σ ProbComp α)
    (init : σ → ρ) (inner : σ → StateT ρ ProbComp β) (fin : σ → β → ρ → α × σ)
    (shape : ∀ s, step.run s = (fun r => fin s r.1 r.2) <$> (inner s).run (init s))
    (fin_complete : ∀ s b r c, fin s b (M.set r c) = Prod.map id (fun x => L.set x c) (fin s b r))
    (pointedInner : σ → StateT ρ ProbComp (β × Option spec₀.Domain))
    (innerFactor : ∀ s r, LawEq ((inner s).run r)
      ((pointedInner s).run r >>= fun p => (p.1.1, ·) <$> M.completeOpt p.1.2 p.2))
    (s : σ) :
    LawEq (step.run s)
      (((fun p => (((fin s p.1.1 p.2).1, p.1.2), (fin s p.1.1 p.2).2)) <$> (pointedInner s).run (init s)) >>=
        fun r => (r.1.1, ·) <$> L.completeOpt r.1.2 r.2) := by
  have finGet : ∀ b r, L.get (fin s b r).2 = M.get r := by
    intro b r
    have h := fin_complete s b r (M.get r)
    rw [M.set_get] at h
    rw [h]
    exact L.get_set _ _
  rw [shape]
  refine ((innerFactor s (init s)).map _).trans (LawEq.of_eq ?_)
  rw [map_bind, bind_map_left]
  refine bind_congr fun p => ?_
  rcases p with ⟨⟨b, point⟩, r⟩
  cases point with
  | none => simp only [StateLens.completeOpt, map_pure]
  | some t =>
      simp only [StateLens.completeOpt, StateLens.complete, Functor.map_map, finGet]
      congr 1
      funext c
      rw [fin_complete]
      rfl

/-- The pointed form of a focused step commutes with completions when the inner pointed step does. -/
theorem oblivious_focus {σ ρ α β : Type} (L : CacheLens spec₀ σ) (M : CacheLens spec₀ ρ)
    (init : σ → ρ) (fin : σ → β → ρ → α × σ)
    (init_set : ∀ s c, init (L.set s c) = M.set (init s) c)
    (fin_set : ∀ s c b r, fin (L.set s c) b r = fin s b r)
    (fin_complete : ∀ s b r c, fin s b (M.set r c) = Prod.map id (fun x => L.set x c) (fin s b r))
    (pointedInner : σ → StateT ρ ProbComp (β × Option spec₀.Domain))
    (inner_set : ∀ s c, pointedInner (L.set s c) = pointedInner s)
    (innerCommutes : ∀ s, Commutes M (Prod.fst <$> pointedInner s)) :
    Commutes L (Prod.fst <$> (fun s => (fun p => (((fin s p.1.1 p.2).1, p.1.2), (fin s p.1.1 p.2).2)) <$>
      (pointedInner s).run (init s) : StateT σ ProbComp (α × Option spec₀.Domain))) := by
  refine PqxdhDeploymentBackend.commutes_focus L M _ init (fun s => Prod.fst <$> pointedInner s) fin
    (fun s => ?_) init_set (fun s c => by rw [inner_set]) fin_set fin_complete innerCommutes
  rw [StateT.run_map, StateT.run_map, Functor.map_map]
  simp only [StateT.run, Functor.map_map]

/-! ### The global erasure for the pluggable native game -/

section Game
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- The pointed handler of the whole native game: registration commands report their points, coins, BLAKE2b and records report none. -/
noncomputable def pointedWith {L : CacheLens spec₀ (XState KemSK Bk n)} (pair : PointedReg L) :
    (query : Spec.Domain) → StateT (XState KemSK Bk n) ProbComp (Spec.Range query × Option spec₀.Domain)
  | .inr (.create pin keyId) => pair.pointed ⟨.create pin keyId, trivial⟩
  | .inr (.bundle owner) => pair.pointed ⟨.bundle owner, trivial⟩
  | .inr (.accept raw) => pair.pointed ⟨.accept raw, trivial⟩
  | .inr (.build session payload) => pair.pointed ⟨.build session payload, trivial⟩
  | .inr (.finish owner raw) => pair.pointed ⟨.finish owner raw, trivial⟩
  | .inr (.hmac key message) => pair.pointed ⟨.hmac key message, trivial⟩
  | query => (·, none) <$> handlerWith setup codec route pair.reg query

/-- Forgetting the points of the pointed handler gives the handler with the erased registration handler. -/
theorem pointedWith_erased {L : CacheLens spec₀ (XState KemSK Bk n)} (pair : PointedReg L) :
    (fun query => Prod.fst <$> pointedWith setup codec route pair query : QueryImpl Spec _) =
      handlerWith setup codec route pair.erased := by
  funext query
  rcases query with coin | command
  · simp only [pointedWith, handlerWith, Functor.map_map, id_map']
  · cases command <;> simp only [pointedWith, handlerWith, PointedReg.erased, Functor.map_map, id_map'] <;> rfl

/-- The handler with `reg` is, in law, the pointed handler followed by the completion of the reported point. -/
theorem pointedWith_factor {L : CacheLens spec₀ (XState KemSK Bk n)} (pair : PointedReg L) (query : Spec.Domain)
    (state : XState KemSK Bk n) :
    LawEq ((handlerWith setup codec route pair.reg query).run state)
      ((pointedWith setup codec route pair query).run state >>= fun r => (r.1.1, ·) <$> L.completeOpt r.1.2 r.2) := by
  have plain : ∀ (step : StateT (XState KemSK Bk n) ProbComp (Spec.Range query)),
      LawEq (step.run state) ((((·, none) <$> step : StateT (XState KemSK Bk n) ProbComp
        (Spec.Range query × Option spec₀.Domain))).run state >>= fun r => (r.1.1, ·) <$> L.completeOpt r.1.2 r.2) :=
    fun step => LawEq.of_eq (by
      simp only [StateT.run_map, bind_map_left, StateLens.completeOpt, map_pure, Prod.mk.eta, bind_pure])
  rcases query with coin | command
  · exact plain _
  · cases command
    case create pin keyId => exact pair.factor _ state
    case bundle owner => exact pair.factor _ state
    case accept raw => exact pair.factor _ state
    case build session payload => exact pair.factor _ state
    case finish owner raw => exact pair.factor _ state
    case hmac key message => exact pair.factor _ state
    all_goals exact plain _

/-- Every pointed step of the whole native game commutes with completions when the fixed steps do. -/
theorem pointedWith_oblivious {L : CacheLens spec₀ (XState KemSK Bk n)} (pair : PointedReg L)
    (fixed : ∀ query, (∀ command : PqxdhRecordLiftInterface.EnvQuery, query ≠ .inr command.val) →
      Commutes L (handlerWith setup codec route pair.reg query))
    (query : Spec.Domain) : Commutes L (Prod.fst <$> pointedWith setup codec route pair query) := by
  have plain : ∀ query', (∀ command : PqxdhRecordLiftInterface.EnvQuery, query' ≠ .inr command.val) →
      Commutes L (Prod.fst <$> ((·, none) <$> handlerWith setup codec route pair.reg query' :
        StateT (XState KemSK Bk n) ProbComp (Spec.Range query' × Option spec₀.Domain))) := by
    intro query' notEnv
    rw [Functor.map_map]
    simpa only [id_map'] using fixed query' notEnv
  rcases query with coin | command
  · exact plain _ (fun _ same => by cases same)
  · cases command
    case create pin keyId => exact pair.oblivious _
    case bundle owner => exact pair.oblivious _
    case accept raw => exact pair.oblivious _
    case build session payload => exact pair.oblivious _
    case finish owner raw => exact pair.oblivious _
    case hmac key message => exact pair.oblivious _
    all_goals exact plain _ (fun command same => by cases command with | mk command isEnv => cases same; exact isEnv.elim)

/-- The outcome of `gameWith` read through a projection of the final state. -/
def outcomeMap {τ : Type} (proj : XState KemSK Bk n → τ) :
    Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.Ledger × XState KemSK Bk n) × A →
      Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.Ledger × τ) × A :=
  fun outcome => (outcome.1.map fun result => (result.1, result.2.1, result.2.2.1, proj result.2.2.2), outcome.2)

/-- The global erasure for the run phase (generic lens): when the fixed steps commute with completions of the cache focused by `L`, the game with each constructed Server's registration handler and the game with its erased handler have the same law of the Server's public data, the output, the ledger and every projection of the final state that does not see the cache. -/
theorem erase_game {L : CacheLens spec₀ (XState KemSK Bk n)} (pair : PqxdhLiveServerConstruction.Created Unit → PointedReg L)
    (fixed : ∀ created query, (∀ command : PqxdhRecordLiftInterface.EnvQuery, query ≠ .inr command.val) →
      Commutes L (handlerWith setup codec route (pair created).reg query))
    {τ : Type} (proj : XState KemSK Bk n → τ) (proj_set : ∀ state cache, proj (L.set state cache) = proj state)
    (init : PqxdhLiveServerConstruction.Created Unit → Bk) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    LawEq (outcomeMap proj <$> (gameWith setup codec route init (fun created => (pair created).reg) ensureInit
        identityIndex bounds mode adversary).run runtime)
      (outcomeMap proj <$> (gameWith setup codec route init (fun created => (pair created).erased) ensureInit
        identityIndex bounds mode adversary).run runtime) := by
  simp only [gameWith, StateT.run, map_bind]
  refine LawEq.bind (LawEq.refl _) fun born => ?_
  rcases born with ⟨_ | created, after⟩
  · exact LawEq.refl _
  · have erased := LazyOracleDiscard.discard_erase_proj L (handlerWith setup codec route (pair created).reg)
      (pointedWith setup codec route (pair created)) (pointedWith_factor setup codec route (pair created))
      (pointedWith_oblivious setup codec route (pair created) (fixed created)) proj proj_set
      (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode adversary))
      (xinitial created (init created))
    rw [pointedWith_erased] at erased
    have mapped := erased.map (fun result => (some (PqxdhRegistrationJointServerBirth.encode created, result.1.1,
      result.1.2, result.2), after))
    simp only [StateT.run, Functor.map_map] at mapped
    simpa only [Functor.map_map, outcomeMap, Option.map_some, Prod.map_fst, Prod.map_snd, id_eq] using mapped

end Game

/-! ### The LQ-F later game with a pluggable post phase -/

/-- The LQ-F reveal read from an extended state: the Beacon-side reveal of its owners and snapshot, and the constructed Server's identity seed with the ephemeral log. -/
def xreveal (created : PqxdhLiveServerConstruction.Created Unit) (state : XState KemSK Bk n) :
    PqxdhDeploymentLaterServerGame.Reveal :=
  (PqxdhDeploymentLater.revealOf state.base.native.owners state.snap, (some created.seed, state.log))

section Later
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X Out : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- The LQ-F later game with a pluggable registration handler and a pluggable post-phase handler: the run phase of `gameWith`, the reveal of the final state, and the post phase of `second` on the run's output and the reveal, from the run's final state. -/
noncomputable def laterWith (init : PqxdhLiveServerConstruction.Created Unit → Bk)
    (reg : PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK Bk n)
    (postWith : PqxdhLiveServerConstruction.Created Unit →
      QueryImpl PqxdhDeploymentLater.PostSpec (StateT (XState KemSK Bk n) ProbComp))
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PqxdhDeploymentLater.PostSpec Out) :
    StateT A ProbComp (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out ×
      PqxdhDeploymentSecrecy.Ledger × XState KemSK Bk n)) := fun runtime => do
  let born ← (PqxdhLiveServerConstruction.construct setup.joint ensureInit identityIndex setup.serverKeyId none).run runtime
  match born.1 with
  | none => pure (none, born.2)
  | some created =>
    (fun result => (some (PqxdhRegistrationJointServerBirth.encode created, result), born.2)) <$> (do
      let run ← (simulateQ (handlerWith setup codec route (reg created))
        (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first))).run
          (xinitial created (init created))
      let post ← (simulateQ (postWith created) (second run.1.1 (xreveal created run.2))).run run.2
      pure (post.1, run.1.2, post.2))

/-- The post phase of the later game from the run's result, read through a projection of the final state. -/
noncomputable def laterTail {τ : Type}
    (postWith : PqxdhLiveServerConstruction.Created Unit →
      QueryImpl PqxdhDeploymentLater.PostSpec (StateT (XState KemSK Bk n) ProbComp))
    (created : PqxdhLiveServerConstruction.Created Unit)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PqxdhDeploymentLater.PostSpec Out)
    (proj : XState KemSK Bk n → τ) (after : A) (run : (X × PqxdhDeploymentSecrecy.Ledger) × XState KemSK Bk n) :
    ProbComp (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × PqxdhDeploymentSecrecy.Ledger × τ) × A) :=
  (simulateQ (postWith created) (second run.1.1 (xreveal created run.2))).run run.2 >>= fun post =>
    pure (some (PqxdhRegistrationJointServerBirth.encode created, post.1, run.1.2, proj post.2), after)

/-- The post phase cannot observe a completion of the cache before it, when it commutes with completions, the reveal does not see the cache and the projection does not see it either. -/
theorem laterTail_blind {L : CacheLens spec₀ (XState KemSK Bk n)} {τ : Type}
    (postWith : PqxdhLiveServerConstruction.Created Unit →
      QueryImpl PqxdhDeploymentLater.PostSpec (StateT (XState KemSK Bk n) ProbComp))
    (postCommutes : ∀ created query, Commutes L (postWith created query))
    (revealBlind : ∀ created state cache, xreveal created (L.set state cache) = xreveal created state)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PqxdhDeploymentLater.PostSpec Out)
    (proj : XState KemSK Bk n → τ) (proj_set : ∀ state cache, proj (L.set state cache) = proj state) (after : A) :
    LazyOracleDiscard.Blind L (laterTail postWith created second proj after) := by
  intro value point state
  have moved := LazyOracleDiscard.commutes_simulateQ L (postWith created) (postCommutes created)
    (second value.1 (xreveal created state)) point state
  have stepA : (L.complete point state >>= fun later => laterTail postWith created second proj after (value, later)) =
      (L.complete point state >>= (simulateQ (postWith created) (second value.1 (xreveal created state))).run) >>=
        fun post => (pure (some (PqxdhRegistrationJointServerBirth.encode created, post.1, value.2, proj post.2), after) :
          ProbComp _) := by
    simp only [laterTail, StateLens.complete, bind_map_left, revealBlind, bind_assoc]
  have stepC : LawEq (((simulateQ (postWith created) (second value.1 (xreveal created state))).run state >>=
        fun r => (r.1, ·) <$> L.complete point r.2) >>=
          fun post => (pure (some (PqxdhRegistrationJointServerBirth.encode created, post.1, value.2, proj post.2), after) :
            ProbComp _))
      (laterTail postWith created second proj after (value, state)) := by
    simp only [laterTail, bind_assoc, bind_map_left]
    refine LawEq.bind (LawEq.refl _) fun post => ?_
    simp only [StateLens.complete, bind_map_left, proj_set]
    exact LazyOracleDiscard.lawEq_drop _ _
  rw [stepA]
  exact (moved.bind fun _ => LawEq.refl _).trans stepC

/-- The global erasure for the LQ-F later game (generic lens, m7): when the fixed steps and the post phase commute with completions of the cache focused by `L`, and the reveal does not see the cache, the later games with the registration handler and with its erased handler have the same law of the Server's public data, the second adversary's output, the ledger and every projection of the final state that does not see the cache. -/
theorem erase_later {L : CacheLens spec₀ (XState KemSK Bk n)}
    (pair : PqxdhLiveServerConstruction.Created Unit → PointedReg L)
    (fixed : ∀ created query, (∀ command : PqxdhRecordLiftInterface.EnvQuery, query ≠ .inr command.val) →
      Commutes L (handlerWith setup codec route (pair created).reg query))
    (postWith : PqxdhLiveServerConstruction.Created Unit →
      QueryImpl PqxdhDeploymentLater.PostSpec (StateT (XState KemSK Bk n) ProbComp))
    (postCommutes : ∀ created query, Commutes L (postWith created query))
    (revealBlind : ∀ created state cache, xreveal created (L.set state cache) = xreveal created state)
    {τ : Type} (proj : XState KemSK Bk n → τ) (proj_set : ∀ state cache, proj (L.set state cache) = proj state)
    (init : PqxdhLiveServerConstruction.Created Unit → Bk) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PqxdhDeploymentLater.PostSpec Out) (runtime : A) :
    LawEq (outcomeMap proj <$> (laterWith setup codec route init (fun created => (pair created).reg) postWith ensureInit
        identityIndex bounds mode first second).run runtime)
      (outcomeMap proj <$> (laterWith setup codec route init (fun created => (pair created).erased) postWith ensureInit
        identityIndex bounds mode first second).run runtime) := by
  simp only [laterWith, StateT.run, map_bind]
  refine LawEq.bind (LawEq.refl _) fun born => ?_
  rcases born with ⟨_ | created, after⟩
  · exact LawEq.refl _
  · have erased := LazyOracleDiscard.discard_erase L (handlerWith setup codec route (pair created).reg)
      (pointedWith setup codec route (pair created)) (pointedWith_factor setup codec route (pair created))
      (pointedWith_oblivious setup codec route (pair created) (fixed created))
      (laterTail postWith created second proj after)
      (laterTail_blind postWith postCommutes revealBlind created second proj proj_set after)
      (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first))
      (xinitial created (init created))
    rw [pointedWith_erased] at erased
    simp only [map_bind, map_pure, outcomeMap, Option.map_some]
    exact erased

end Later

/-! ### The CTX-cache instance (C7) -/

/-- C7's pair: a registration handler with its pointed form for the CTX cache. -/
abbrev FinishPair (KemSK Bk : Type) (n : Nat) := PointedReg (ctxLens (KemSK := KemSK) (Bk := Bk) (n := n))

/-- The final state with the CTX cache emptied: every coordinate except the CTX cache. -/
def fullX (state : XState KemSK Bk n) : XState KemSK Bk n := ctxLens.set state ∅

/-- Emptying the CTX cache does not see the cache. -/
theorem fullX_set (state : XState KemSK Bk n) (cache : CtxRomAuth.CtxRO.QueryCache) :
    fullX (ctxLens.set state cache) = fullX state := by
  simp only [fullX, StateLens.set_set]

section Ctx
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X Out : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- C7 (run phase, per constructed Server, M2): the game with each Server's registration handler and the game with its erased handler have the same law of the Server's public data, the output, the ledger and the final state with the CTX cache emptied. -/
theorem erase_game_ctx (pair : PqxdhLiveServerConstruction.Created Unit → FinishPair KemSK Bk n)
    (init : PqxdhLiveServerConstruction.Created Unit → Bk) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    LawEq (outcomeMap fullX <$> (gameWith setup codec route init (fun created => (pair created).reg) ensureInit
        identityIndex bounds mode adversary).run runtime)
      (outcomeMap fullX <$> (gameWith setup codec route init (fun created => (pair created).erased) ensureInit
        identityIndex bounds mode adversary).run runtime) :=
  erase_game setup codec route pair
    (fun created query => PqxdhDeploymentBackend.fixed_commute_ctx setup codec route (pair created).reg query)
    fullX fullX_set init ensureInit identityIndex bounds mode adversary runtime

/-- The LQ-F reveal does not see the CTX cache. -/
theorem xreveal_ctx (created : PqxdhLiveServerConstruction.Created Unit) (state : XState KemSK Bk n)
    (cache : CtxRomAuth.CtxRO.QueryCache) : xreveal created (ctxLens.set state cache) = xreveal created state := rfl

/-- C7 with the LQ-F reveal and a pluggable post phase (m7): when the post phase commutes with completions of the CTX cache, the later games with each Server's registration handler and with its erased handler have the same law of the Server's public data, the second adversary's output, the ledger and the final state with the CTX cache emptied. -/
theorem erase_later_ctx (pair : PqxdhLiveServerConstruction.Created Unit → FinishPair KemSK Bk n)
    (postWith : PqxdhLiveServerConstruction.Created Unit →
      QueryImpl PqxdhDeploymentLater.PostSpec (StateT (XState KemSK Bk n) ProbComp))
    (postCommutes : ∀ created query, Commutes ctxLens (postWith created query))
    (init : PqxdhLiveServerConstruction.Created Unit → Bk) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PqxdhDeploymentLater.PostSpec Out) (runtime : A) :
    LawEq (outcomeMap fullX <$> (laterWith setup codec route init (fun created => (pair created).reg) postWith ensureInit
        identityIndex bounds mode first second).run runtime)
      (outcomeMap fullX <$> (laterWith setup codec route init (fun created => (pair created).erased) postWith ensureInit
        identityIndex bounds mode first second).run runtime) :=
  erase_later setup codec route pair
    (fun created query => PqxdhDeploymentBackend.fixed_commute_ctx setup codec route (pair created).reg query)
    postWith postCommutes xreveal_ctx fullX fullX_set init ensureInit identityIndex bounds mode first second runtime

end Ctx

/-! ### The real instance -/

/-- Simulating a handler lifted through a lens runs the handler on the focused coordinate. -/
theorem simulateQ_lift {σ ρ α ι' : Type} {spec' : OracleSpec ι'} (E : StateLens σ ρ)
    (impl : QueryImpl spec' (StateT ρ ProbComp)) (oa : OracleComp spec' α) (s : σ) :
    (simulateQ (fun query => E.lift (impl query) : QueryImpl spec' (StateT σ ProbComp)) oa).run s =
      (fun r => (r.1, E.set s r.2)) <$> (simulateQ impl oa).run (E.get s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, E.set_get]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, map_bind]
      change ((fun r => (r.1, E.set s r.2)) <$> (impl query).run (E.get s)) >>= _ = _
      rw [bind_map_left]
      refine bind_congr fun r => ?_
      rw [ih, E.get_set]
      simp only [E.set_set]

section Real
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X Out : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks)

/-- The real registration handler as a C7 pair with no point: its erased handler is itself. -/
noncomputable def realPair (created : PqxdhLiveServerConstruction.Created Unit) : FinishPair KemSK Unit 0 :=
  PointedReg.ofCommuting (realReg setup codec route checks created)
    (PqxdhDeploymentBackend.realReg_commutes_ctx setup codec route checks created)

/-- The real post phase: LQ's post-run handler (fresh coins, the native HMAC and BLAKE2b) on the deployment state. -/
noncomputable def realPost (created : PqxdhLiveServerConstruction.Created Unit) :
    QueryImpl PqxdhDeploymentLater.PostSpec (StateT (XState KemSK Bk n) ProbComp) :=
  fun query => PqxdhDeploymentBackend.onBase (PqxdhDeploymentLater.postImpl setup codec checks created.seed query)

/-- The real post phase commutes with completions of the CTX cache. -/
theorem realPost_commutes (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhDeploymentLater.PostSpec.Domain) :
    Commutes ctxLens (realPost (Bk := Bk) (n := n) setup codec checks created query) := by
  rcases query with coin | query
  · exact LazyOracleDiscard.commutes_lift PqxdhDeploymentBackend.baseLens PqxdhDeploymentBackend.nativeCtxLens _
      (PqxdhDeploymentBackend.commutes_lift_comp _ _)
  · cases query with
    | hmac key message =>
        show Commutes ctxLens (PqxdhDeploymentBackend.baseLens.lift (PqxdhDeploymentBackend.nativeLens.lift
          (PqxdhDeploymentBackend.scheduleLens.lift (PqxdhServerAuthNative.nativeHmac setup created.seed
            PqxdhRegistrationSchedule.observationScalar key message))))
        exact LazyOracleDiscard.commutes_lift _ _ _ (LazyOracleDiscard.commutes_lift _ _ _
          (LazyOracleDiscard.commutes_lift _ _ _ (PqxdhDeploymentBackend.nativeHmac_frame setup _ _ _ _).commutes))
    | hash bytes =>
        show Commutes ctxLens (PqxdhDeploymentBackend.baseLens.lift (PqxdhDeploymentBackend.nativeLens.lift
          (PqxdhDeploymentBackend.scheduleLens.lift (PqxdhServerAuthNative.nativeHash bytes))))
        refine LazyOracleDiscard.commutes_lift _ _ _ (LazyOracleDiscard.commutes_lift _ _ _
          (LazyOracleDiscard.commutes_lift _ _ _ ?_))
        rw [PqxdhDeploymentBackend.nativeHash_query]
        exact LazyOracleDiscard.commutes_query _ _

/-- The later game with the real registration handler and the real post phase is exactly the LQ-F later game, jointly over the Server's public data, the second adversary's output, the ledger, the snapshot, the final deployment state, the log and the runtime state. -/
theorem laterWith_real (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (bounds : FreshBounds)
    (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PqxdhDeploymentLater.PostSpec Out)
    (runtime : A) :
    (fun outcome => (outcome.1.map fun result =>
        (result.1, result.2.1, (result.2.2.1, PqxdhDeploymentBackend.laterView result.2.2.2)), outcome.2)) <$>
        (laterWith setup codec route (fun _ => ()) (realReg setup codec route checks) (realPost setup codec checks)
          ensureInit identityIndex bounds mode first second).run runtime =
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit identityIndex bounds mode first
        second).run runtime := by
  simp only [laterWith, PqxdhDeploymentLaterServerGame.game, PqxdhDeploymentLaterServerGame.exec, StateT.run, map_bind]
  apply bind_congr
  rintro ⟨_ | created, after⟩
  · simp only [map_pure, Option.map_none]
  · have viewed := OracleComp.map_run_simulateQ_eq_of_query_map_eq
      (handlerWith setup codec route (realReg setup codec route checks created))
      (PqxdhDeploymentLaterServerGame.snapImpl setup codec checks route created.seed) PqxdhDeploymentBackend.laterView
      (fun query state => PqxdhDeploymentBackend.realStep_view setup codec route checks created query state)
      (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first))
      (xinitial created ())
    have wrapped := PqxdhDeploymentLaterServerGame.later_run_wrap setup codec checks route created.seed bounds
      (asModeO mode first) (PqxdhDeploymentLater.Snap.empty, (PqxdhDeploymentNative.initial created, []))
    simp only [StateT.run] at wrapped viewed
    dsimp only
    rw [wrapped, show ((PqxdhDeploymentLater.Snap.empty, (PqxdhDeploymentNative.initial created, [])) :
        PqxdhDeploymentLater.Snap × (PqxdhDeploymentNative.State KemSK × PqxdhDeploymentLaterServerSource.Log)) =
          PqxdhDeploymentBackend.laterView (xinitial created ()) from rfl, ← viewed]
    simp only [map_bind, bind_map_left, Functor.map_map]
    refine bind_congr fun run => ?_
    have post := simulateQ_lift PqxdhDeploymentBackend.baseLens
      (PqxdhDeploymentLater.postImpl setup codec checks created.seed) (second run.1.1 (xreveal created run.2)) run.2
    simp only [StateT.run] at post
    have post' : simulateQ (realPost (Bk := Unit) (n := 0) setup codec checks created)
        (second run.1.1 (xreveal created run.2)) run.2 =
          (fun r => (r.1, PqxdhDeploymentBackend.baseLens.set run.2 r.2)) <$>
            simulateQ (PqxdhDeploymentLater.postImpl setup codec checks created.seed)
              (second run.1.1 (xreveal created run.2)) run.2.base := post
    rw [post', bind_map_left]
    rfl

end Real

end BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.PointedReg.ofCommuting_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.PointedReg.ofCommuting_erased

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.factor_focus' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.factor_focus

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.oblivious_focus' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.oblivious_focus

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.pointedWith_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.pointedWith_erased

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.pointedWith_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.pointedWith_factor

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.pointedWith_oblivious' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.pointedWith_oblivious

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.erase_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.erase_game

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.laterTail_blind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.laterTail_blind

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.erase_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.erase_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.fullX_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.fullX_set

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.erase_game_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.erase_game_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.xreveal_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.xreveal_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.erase_later_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.erase_later_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.simulateQ_lift' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.simulateQ_lift

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.realPost_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.realPost_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.laterWith_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure.laterWith_real
