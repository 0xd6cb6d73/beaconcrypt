-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame
import BeaconcryptCore.Computational.PqxdhRecordLiftWorld

/-!
# The native deployment game with a pluggable registration handler

`gameWith` is the common deployment experiment (CE-2, with the LQ-F ghosts) in which the six registration commands (create, bundle, accept, build, finish, HMAC) are answered by a registration handler `reg` chosen after the Server is constructed (critique M2), while coins, the public BLAKE2b oracle and the four record commands are the native deployment experiment's own steps on the deployment state. The state `XState` extends the native deployment state with a backend for the handler, a lazily sampled hidden-seed table and the LQ-F ghosts (the finish snapshot and the Server ephemeral log). The real registration handler `realReg` answers every registration command as the LQ-F run-phase handler does, and `gameWith_real` shows that the game with it is exactly the LQ-F run phase `PqxdhDeploymentLaterServerGame.runPhase`, and `gameWith_classical` that, with the backend, the seed table and the LQ-F ghosts forgotten, it is the classical common deployment experiment `PqxdhDeploymentSecrecy.game`.

`ctxLens` focuses the shared BLAKE2b cache of the deployment state and `seedLens` the hidden-seed table. The obliviousness facts (critique M5) are proved for the fixed steps: coins, BLAKE2b and records commute, in law, with completing any point of the CTX cache (`fixed_commute_ctx`) and of the seed table (`fixed_commute_seed`), so the whole handler commutes whenever the registration handler does (`handlerWith_commutes_ctx`, `handlerWith_commutes_seed`). Every command of the real registration handler commutes with completions of the CTX cache (`realBuild_commutes_ctx`, `realFinish_commutes_ctx` and `realReg_commutes_ctx` for all six): the build runs the logged response tail on the shared cache, the finish runs its callbacks (including the finish-time receive) on it, and creation, bundle, accept and HMAC are frames of the cache. The proofs use `commutes_focus`: a step that runs an inner program on a focused sub-state, where everything else it reads and writes is a frame of the cache, commutes with completions when the inner program does; and `commutes_dispatch`: a step that first reads a frame of the cache commutes when every branch does.

These are equalities of programs and equalities in law of lazy caches. No security claim is made here.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentBackend
open PqxdhServerAuthExperiment (Setup Codec Checks GameState)
open PqxdhServerAuthNative (NativeState NativeGame)
open PqxdhDeploymentInterface (Spec Command ModeSpec Mode FreshBounds asModeO)
open LazyOracleDiscard (Commutes StateLens CacheLens LawEq)

/-! ### Generic commutation lemmas -/

section Generic
variable {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec ι₀} [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)]

/-- A step that runs an inner program on a sub-state, reading and writing everything else as a frame of the focused cache, commutes with completions of the cache when the inner program does. -/
theorem commutes_focus {σ ρ α β : Type} (L : CacheLens spec₀ σ) (M : CacheLens spec₀ ρ) (step : StateT σ ProbComp α)
    (init : σ → ρ) (inner : σ → StateT ρ ProbComp β) (fin : σ → β → ρ → α × σ)
    (shape : ∀ s, step.run s = (fun r => fin s r.1 r.2) <$> (inner s).run (init s))
    (init_set : ∀ s c, init (L.set s c) = M.set (init s) c)
    (inner_set : ∀ s c, inner (L.set s c) = inner s)
    (fin_set : ∀ s c b r, fin (L.set s c) b r = fin s b r)
    (fin_complete : ∀ s b r c, fin s b (M.set r c) = Prod.map id (fun x => L.set x c) (fin s b r))
    (commutes : ∀ s, Commutes M (inner s)) : Commutes L step := by
  intro t s
  have initGet : M.get (init s) = L.get s := by
    have h := init_set s (L.get s)
    rw [L.set_get] at h
    rw [h, M.get_set]
  have finGet : ∀ b r, L.get (fin s b r).2 = M.get r := by
    intro b r
    have h := fin_complete s b r (M.get r)
    rw [M.set_get] at h
    rw [h]
    exact L.get_set _ _
  have finSet : ∀ b r c, (fin s b r).1 = (fin s b (M.set r c)).1 ∧ L.set (fin s b r).2 c = (fin s b (M.set r c)).2 := by
    intro b r c
    rw [fin_complete]
    exact ⟨rfl, rfl⟩
  have lhs : L.complete t s >>= step.run =
      (fun r => fin s r.1 r.2) <$> (M.complete t (init s) >>= (inner s).run) := by
    simp only [StateLens.complete, bind_map_left, map_bind, shape, inner_set, fin_set, init_set, initGet]
  have rhs : (step.run s >>= fun r => (r.1, ·) <$> L.complete t r.2) =
      (fun r => fin s r.1 r.2) <$> ((inner s).run (init s) >>= fun r => (r.1, ·) <$> M.complete t r.2) := by
    rw [shape, bind_map_left, map_bind]
    refine bind_congr fun r => ?_
    simp only [StateLens.complete, Functor.map_map, finGet]
    congr 1
    funext c
    obtain ⟨first, second⟩ := finSet r.1 r.2 c
    exact Prod.ext first second
  rw [lhs, rhs]
  exact (commutes s t (init s)).map _

/-- A step that first reads a part of the state unchanged by the focused cache, then runs a commuting step chosen by it, commutes with completions of the cache. -/
theorem commutes_dispatch {σ τ α : Type} (L : CacheLens spec₀ σ) (step : StateT σ ProbComp α) (π : σ → τ)
    (π_set : ∀ s c, π (L.set s c) = π s) (choose : τ → StateT σ ProbComp α)
    (shape : ∀ s, step.run s = (choose (π s)).run s) (commutes : ∀ p, Commutes L (choose p)) : Commutes L step := by
  intro t s
  have lhs : L.complete t s >>= step.run = L.complete t s >>= (choose (π s)).run := by
    simp only [StateLens.complete, bind_map_left, shape, π_set]
  rw [lhs, shape]
  exact commutes (π s) t s

/-- A lifted probabilistic computation that does not touch the state commutes with every completion. -/
theorem commutes_lift_comp {σ α : Type} (L : CacheLens spec₀ σ) (work : ProbComp α) :
    Commutes L (StateT.lift work : StateT σ ProbComp α) :=
  LazyOracleDiscard.commutes_frame L _ fun s c => by
    simp only [StateT.run_lift, map_bind, map_pure]

end Generic

/-! ### The extended state and its lenses -/

/-- The native deployment state with the backend of a pluggable registration handler, the lazily sampled hidden-seed table and the LQ-F ghosts: the finish snapshot and the Server ephemeral log. -/
structure XState (KemSK Bk : Type) (n : Nat) where
  base : PqxdhDeploymentNative.State KemSK
  backend : Bk
  seeds : (PqxdhRecordLiftWorld.SeedSpec n).QueryCache
  snap : PqxdhDeploymentLater.Snap
  log : PqxdhDeploymentLaterServerSource.Log

/-- A registration handler: the six environment commands on the extended state. -/
abbrev RegImpl (KemSK Bk : Type) (n : Nat) :=
  QueryImpl PqxdhRecordLiftInterface.EnvSpec (StateT (XState KemSK Bk n) ProbComp)

variable {KemSK Bk : Type} {n : Nat}

/-- The native deployment state inside the extended state. -/
def baseLens : StateLens (XState KemSK Bk n) (PqxdhDeploymentNative.State KemSK) where
  get x := x.base
  set x b := { x with base := b }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- The registration state inside the native deployment state. -/
def nativeLens : StateLens (PqxdhDeploymentNative.State KemSK) (PqxdhRegistrationSchedule.State KemSK) where
  get s := s.native
  set s r := { s with native := r }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- The shared native state inside the registration state. -/
def scheduleLens : StateLens (PqxdhRegistrationSchedule.State KemSK) (NativeState KemSK) where
  get s := s.shared
  set s r := { s with shared := r }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- The shared primitive state (no auxiliary component, the CTX cache) inside the shared native state, as `PqxdhServerAuthNative.nativeCtx` reads and writes it. -/
def gameLens : StateLens (NativeState KemSK) (RawCtxSharedPrimitive.SharedState Unit) where
  get s := ((), s.2.ctx)
  set s r := (s.1, { s.2 with ctx := r.2 })
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- The CTX cache of the shared native state. -/
abbrev gameCtxLens : CacheLens CtxRomAuth.CtxRO (NativeState KemSK) :=
  gameLens.comp (StateLens.snd Unit CtxRomAuth.CtxRO.QueryCache)

/-- The CTX cache of the registration state. -/
abbrev scheduleCtxLens : CacheLens CtxRomAuth.CtxRO (PqxdhRegistrationSchedule.State KemSK) :=
  scheduleLens.comp gameCtxLens

/-- The CTX cache of the native deployment state. -/
abbrev nativeCtxLens : CacheLens CtxRomAuth.CtxRO (PqxdhDeploymentNative.State KemSK) :=
  nativeLens.comp scheduleCtxLens

/-- The CTX cache of the extended state: `base.native.shared.2.ctx`. -/
abbrev ctxLens : CacheLens CtxRomAuth.CtxRO (XState KemSK Bk n) :=
  baseLens.comp nativeCtxLens

/-- The hidden-seed table of the extended state. -/
def seedLens : CacheLens (PqxdhRecordLiftWorld.SeedSpec n) (XState KemSK Bk n) where
  get x := x.seeds
  set x c := { x with seeds := c }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- The CTX cache of the extended state is the shared BLAKE2b cache of the registration state. -/
theorem ctxLens_get (x : XState KemSK Bk n) : ctxLens.get x = x.base.native.shared.2.ctx := rfl

/-! ### The handler and the game -/

/-- Run a step of the native deployment state on the extended state. -/
abbrev onBase {α : Type} (step : StateT (PqxdhDeploymentNative.State KemSK) ProbComp α) :
    StateT (XState KemSK Bk n) ProbComp α :=
  baseLens.lift step

section Game
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- The native handler with a pluggable registration handler: coins, BLAKE2b and the four record commands are the native deployment experiment's own steps on the deployment state; the six registration commands are answered by `reg`. -/
noncomputable def handlerWith (reg : RegImpl KemSK Bk n) : QueryImpl Spec (StateT (XState KemSK Bk n) ProbComp)
  | .inl coin => StateT.lift (unifSpec.query coin : ProbComp _)
  | .inr (.create pin keyId) => reg ⟨.create pin keyId, trivial⟩
  | .inr (.bundle owner) => reg ⟨.bundle owner, trivial⟩
  | .inr (.accept raw) => reg ⟨.accept raw, trivial⟩
  | .inr (.build session payload) => reg ⟨.build session payload, trivial⟩
  | .inr (.finish owner raw) => reg ⟨.finish owner raw, trivial⟩
  | .inr (.hmac key message) => reg ⟨.hmac key message, trivial⟩
  | .inr (.hash bytes) => onBase (PqxdhDeploymentNative.onNative
      (PqxdhRegistrationSchedule.onShared (PqxdhServerAuthNative.nativeHash bytes)))
  | .inr (.serverSend keyId plaintext) => onBase (PqxdhDeploymentNative.serverStep setup codec route (.inl (plaintext, keyId)))
  | .inr (.serverRaw raw) => onBase (PqxdhDeploymentNative.serverStep setup codec route (.inr raw))
  | .inr (.beaconSend owner plaintext) => onBase (PqxdhDeploymentNative.beaconStep setup codec owner (.inl plaintext))
  | .inr (.beaconRaw owner raw) => onBase (PqxdhDeploymentNative.beaconStep setup codec owner (.inr raw))

/-- The initial extended state: the constructed Server's initial deployment state, the backend's initial value, an empty seed table, the empty snapshot and the empty log. -/
def xinitial (created : PqxdhLiveServerConstruction.Created Unit) (backend : Bk) : XState KemSK Bk n :=
  ⟨PqxdhDeploymentNative.initial created, backend, ∅, PqxdhDeploymentLater.Snap.empty, []⟩

/-- The common deployment experiment with a registration handler chosen after construction (M2): the actual Server constructor with a generated seed, then the wrapped adversary (`PqxdhDeploymentSecrecy.wrap`, the secrecy layer as a program) against `handlerWith (reg created)` from the initial extended state. A constructor failure ends the run with no outcome. -/
noncomputable def gameWith (init : PqxdhLiveServerConstruction.Created Unit → Bk)
    (reg : PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK Bk n) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : Nat) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    StateT A ProbComp (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X ×
      PqxdhDeploymentSecrecy.Ledger × XState KemSK Bk n)) := fun runtime => do
  let born ← (PqxdhLiveServerConstruction.construct setup.joint ensureInit identityIndex setup.serverKeyId none).run runtime
  match born.1 with
  | none => pure (none, born.2)
  | some created =>
    (fun result => (some (PqxdhRegistrationJointServerBirth.encode created, result.1.1, result.1.2, result.2), born.2)) <$>
      (simulateQ (handlerWith setup codec route (reg created))
        (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode adversary))).run
          (xinitial created (init created))

/-- The real registration handler: every registration command runs the LQ-F run-phase handler (the logged native accept, every other command the native handler) on the deployment state and the ephemeral log, and a finish first captures the addressed owner's scalars in the snapshot. -/
noncomputable def realReg (checks : Checks) (created : PqxdhLiveServerConstruction.Created Unit) : RegImpl KemSK Unit 0 :=
  fun query state =>
    let snap := PqxdhDeploymentLater.snapshotAt state.snap state.base.native.owners
      (PqxdhDeploymentLater.finishOwner (.inr query.val))
    (fun result => (result.1, { state with base := result.2.1, log := result.2.2, snap := snap })) <$>
      (PqxdhDeploymentLaterServerGame.handler setup codec checks route created.seed (.inr query.val)).run
        (state.base, state.log)

/-- The LQ-F run-phase state of an extended state: snapshot, deployment state and log. -/
def laterView (x : XState KemSK Bk n) : PqxdhDeploymentLater.Snap × (PqxdhDeploymentNative.State KemSK ×
    PqxdhDeploymentLaterServerSource.Log) :=
  (x.snap, (x.base, x.log))

/-- One step of the handler with the real registration handler is one step of the LQ-F logged snapshot handler on the LQ-F view of the state. -/
theorem realStep_view (checks : Checks) (created : PqxdhLiveServerConstruction.Created Unit) (query : Spec.Domain)
    (state : XState KemSK Unit 0) :
    Prod.map id laterView <$> (handlerWith setup codec route (realReg setup codec route checks created) query).run state =
      (PqxdhDeploymentLaterServerGame.snapImpl setup codec checks route created.seed query).run (laterView state) := by
  rcases query with coin | command
  · simp only [handlerWith, StateT.run_lift, laterView]
    rfl
  · cases command <;> simp only [handlerWith, realReg, onBase, StateLens.lift, baseLens, laterView,
      PqxdhDeploymentLaterServerGame.snapImpl, PqxdhDeploymentLaterServerGame.handler, StateT.run, Functor.map_map] <;> rfl

/-- The game with the real registration handler is exactly the LQ-F run phase, jointly over the Server's public data, the adversary's output, the ledger, the snapshot, the deployment state, the log and the runtime state. -/
theorem gameWith_real (checks : Checks) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    (fun outcome => (outcome.1.map fun result => (result.1, result.2.1, (result.2.2.1, laterView result.2.2.2)),
        outcome.2)) <$>
        (gameWith setup codec route (fun _ => ()) (realReg setup codec route checks) ensureInit identityIndex bounds mode
          adversary).run runtime =
      (PqxdhDeploymentLaterServerGame.runPhase setup codec checks route ensureInit identityIndex bounds mode adversary).run
        runtime := by
  simp only [gameWith, PqxdhDeploymentLaterServerGame.runPhase, StateT.run, map_bind]
  apply bind_congr
  rintro ⟨_ | created, after⟩
  · simp only [map_pure, Option.map_none]
  · have viewed := OracleComp.map_run_simulateQ_eq_of_query_map_eq
      (handlerWith setup codec route (realReg setup codec route checks created))
      (PqxdhDeploymentLaterServerGame.snapImpl setup codec checks route created.seed) laterView
      (fun query state => realStep_view setup codec route checks created query state)
      (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode adversary))
      (xinitial created ())
    have wrapped := PqxdhDeploymentLaterServerGame.later_run_wrap setup codec checks route created.seed bounds
      (asModeO mode adversary) (PqxdhDeploymentLater.Snap.empty, (PqxdhDeploymentNative.initial created, []))
    simp only [StateT.run] at wrapped viewed
    simp only [wrapped, Functor.map_map, Option.map_some]
    rw [show ((PqxdhDeploymentLater.Snap.empty, (PqxdhDeploymentNative.initial created, [])) :
        PqxdhDeploymentLater.Snap × (PqxdhDeploymentNative.State KemSK × PqxdhDeploymentLaterServerSource.Log)) =
          laterView (xinitial created ()) from rfl, ← viewed, Functor.map_map]
    rfl

/-- Forgetting the backend, the seed table, the snapshot and the log, the game with the real registration handler is exactly the classical common deployment experiment `PqxdhDeploymentSecrecy.game`. -/
theorem gameWith_classical (checks : Checks) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    (fun outcome => (outcome.1.map fun result => (result.1, result.2.1, (result.2.2.1, result.2.2.2.base)),
        outcome.2)) <$>
        (gameWith setup codec route (fun _ => ()) (realReg setup codec route checks) ensureInit identityIndex bounds mode
          adversary).run runtime =
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run runtime := by
  rw [← PqxdhDeploymentLaterServerGame.runPhase_classical, ← gameWith_real, Functor.map_map]
  congr 1
  funext outcome
  rcases outcome with ⟨_ | result, after⟩ <;> rfl

end Game

/-! ### Obliviousness of the fixed steps (critique M5) -/

/-- The native BLAKE2b oracle is the lazy query on the CTX cache of the shared native state. -/
theorem nativeHash_query (bytes : Pqxdh.Bytes) :
    PqxdhServerAuthNative.nativeHash (KemSK := KemSK) bytes = gameCtxLens.query (spec := CtxRomAuth.CtxRO) ((), bytes) := by
  apply StateT.ext
  intro state
  rfl

section Fixed
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- Every record primitive commutes with completions of the CTX cache. -/
theorem primitives_commutes (query : RawCtxMixedOwner.NativeSpec.Domain) :
    Commutes (StateLens.snd Unit CtxRomAuth.CtxRO.QueryCache) (PqxdhDeploymentNative.primitives setup codec query) :=
  PqxdhDeploymentHiddenEntry.compose_commutes setup.source.crypto setup.source
    (RawCtxMixedShared.sharedAdapter setup.source.crypto codec.frameWrite) query

/-- A record program commutes with completions of the CTX cache of the registration state. -/
theorem record_commutes {Result : Type} (work : OracleComp RawCtxMixedOwner.NativeSpec Result) :
    Commutes scheduleCtxLens (PqxdhDeploymentNative.record (KemSK := KemSK) setup codec work) :=
  LazyOracleDiscard.commutes_lift scheduleLens gameCtxLens _
    (LazyOracleDiscard.commutes_lift gameLens _ _
      (LazyOracleDiscard.commutes_simulateQ _ _ (primitives_commutes setup codec) work))

/-- A Server record step commutes with completions of the CTX cache: the peer map, counters and produced frames are a frame of the cache. -/
theorem serverStep_commutes (query : RawCtxServerMixed.SourceSpec.Domain) :
    Commutes nativeCtxLens (PqxdhDeploymentNative.serverStep (KemSK := KemSK) setup codec route query) := by
  refine commutes_focus nativeCtxLens scheduleCtxLens _ (fun s => s.native)
    (fun s => PqxdhDeploymentNative.record setup codec (PqxdhDeploymentNative.logged
      ((RawCtxServerMixed.serverImpl (PqxdhDeploymentNative.senderId s) route codec.frameRead query).run
        (PqxdhDeploymentNative.serverView s))))
    (fun s b r => (b.1.1, PqxdhDeploymentNative.produce (PqxdhDeploymentNative.serverTag query) b.2
      (PqxdhDeploymentNative.withServer { s with native := r } b.1.2)))
    (fun s => ?_) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun s => record_commutes setup codec _)
  change _ >>= _ = _
  rw [map_eq_bind_pure_comp]
  rfl

/-- The Beacon record step of a present owner, with that owner fixed. -/
noncomputable def ownerStep (index : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (query : RawCtxMixedOwner.SourceSpec.Domain) :
    StateT (PqxdhDeploymentNative.State KemSK) ProbComp (RawCtxMixedOwner.SourceSpec.Range query) := fun state => do
  let result ← (PqxdhDeploymentNative.record setup codec (PqxdhDeploymentNative.logged
    ((RawCtxBeaconLifecycle.beaconImpl codec.frameRead query).run ⟨owner.beacon, state.ownerRaw index⟩))).run state.native
  pure (result.1.1.1, PqxdhDeploymentNative.produce (PqxdhDeploymentNative.beaconTag index) result.1.2 { state with native := { result.2 with owners := result.2.owners.set index { owner with beacon := result.1.1.2.beacon } }, ownerRaw := Function.update state.ownerRaw index result.1.1.2.rawAttempts })

/-- A Beacon record step commutes with completions of the CTX cache: the owner slot is read from a frame of the cache, and the owners, counters and produced frames are a frame of the cache. -/
theorem beaconStep_commutes (index : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain) :
    Commutes nativeCtxLens (PqxdhDeploymentNative.beaconStep (KemSK := KemSK) setup codec index query) := by
  refine commutes_dispatch nativeCtxLens _ (fun s => s.native.owners[index]?) (fun _ _ => rfl)
    (fun found => match found with
      | none => pure (PqxdhDeploymentNative.absent query)
      | some owner => ownerStep setup codec index owner query)
    (fun s => ?_) (fun found => ?_)
  · simp only [PqxdhDeploymentNative.beaconStep, StateT.run]
    split
    next _ found => simp only [found]; rfl
    next _ owner found => simp only [found]; rfl
  · cases found with
    | none => exact LazyOracleDiscard.commutes_pure _ _
    | some owner =>
        refine commutes_focus nativeCtxLens scheduleCtxLens _ (fun s => s.native)
          (fun s => PqxdhDeploymentNative.record setup codec (PqxdhDeploymentNative.logged
            ((RawCtxBeaconLifecycle.beaconImpl codec.frameRead query).run ⟨owner.beacon, s.ownerRaw index⟩)))
          (fun s b r => (b.1.1, PqxdhDeploymentNative.produce (PqxdhDeploymentNative.beaconTag index) b.2 { s with native := { r with owners := r.owners.set index { owner with beacon := b.1.2.beacon } }, ownerRaw := Function.update s.ownerRaw index b.1.2.rawAttempts }))
          (fun s => ?_) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
          (fun s => record_commutes setup codec _)
        change _ >>= _ = _
        rw [map_eq_bind_pure_comp]
        rfl

/-- The coins, the BLAKE2b oracle and the four record commands of the handler commute with completions of the CTX cache, whatever the registration handler. -/
theorem fixed_commute_ctx (reg : RegImpl KemSK Bk n) (query : Spec.Domain)
    (notEnv : ∀ command : PqxdhRecordLiftInterface.EnvQuery, query ≠ .inr command.val) :
    Commutes ctxLens (handlerWith setup codec route reg query) := by
  rcases query with coin | command
  · exact commutes_lift_comp ctxLens _
  · cases command with
    | create pin keyId => exact absurd rfl (notEnv ⟨.create pin keyId, trivial⟩)
    | bundle owner => exact absurd rfl (notEnv ⟨.bundle owner, trivial⟩)
    | accept raw => exact absurd rfl (notEnv ⟨.accept raw, trivial⟩)
    | build session payload => exact absurd rfl (notEnv ⟨.build session payload, trivial⟩)
    | finish owner raw => exact absurd rfl (notEnv ⟨.finish owner raw, trivial⟩)
    | hmac key message => exact absurd rfl (notEnv ⟨.hmac key message, trivial⟩)
    | hash bytes =>
        show Commutes ctxLens (baseLens.lift (nativeLens.lift (scheduleLens.lift
          (PqxdhServerAuthNative.nativeHash bytes))))
        refine LazyOracleDiscard.commutes_lift baseLens nativeCtxLens _
          (LazyOracleDiscard.commutes_lift nativeLens scheduleCtxLens _
            (LazyOracleDiscard.commutes_lift scheduleLens gameCtxLens _ ?_))
        rw [nativeHash_query]
        exact LazyOracleDiscard.commutes_query _ _
    | serverSend keyId plaintext =>
        exact LazyOracleDiscard.commutes_lift baseLens nativeCtxLens _ (serverStep_commutes setup codec route _)
    | serverRaw raw =>
        exact LazyOracleDiscard.commutes_lift baseLens nativeCtxLens _ (serverStep_commutes setup codec route _)
    | beaconSend owner plaintext =>
        exact LazyOracleDiscard.commutes_lift baseLens nativeCtxLens _ (beaconStep_commutes setup codec owner _)
    | beaconRaw owner raw =>
        exact LazyOracleDiscard.commutes_lift baseLens nativeCtxLens _ (beaconStep_commutes setup codec owner _)

/-- The whole handler commutes with completions of the CTX cache whenever the registration handler does. -/
theorem handlerWith_commutes_ctx (reg : RegImpl KemSK Bk n) (regCommutes : ∀ command, Commutes ctxLens (reg command))
    (query : Spec.Domain) : Commutes ctxLens (handlerWith setup codec route reg query) := by
  by_cases env : ∃ command : PqxdhRecordLiftInterface.EnvQuery, query = .inr command.val
  · obtain ⟨⟨command, isEnv⟩, rfl⟩ := env
    cases command <;> first | exact regCommutes _ | exact isEnv.elim
  · exact fixed_commute_ctx setup codec route reg query fun command same => env ⟨command, same⟩

/-- A step of the native deployment state never touches the hidden-seed table. -/
theorem onBase_seed {α : Type} (step : StateT (PqxdhDeploymentNative.State KemSK) ProbComp α) :
    Commutes seedLens (onBase (Bk := Bk) (n := n) step) :=
  LazyOracleDiscard.commutes_frame seedLens _ fun x c => by
    simp only [onBase, StateLens.lift, baseLens, seedLens, StateT.run, Functor.map_map]

/-- The coins, the BLAKE2b oracle and the four record commands of the handler commute with completions of the hidden-seed table, whatever the registration handler. -/
theorem fixed_commute_seed (reg : RegImpl KemSK Bk n) (query : Spec.Domain)
    (notEnv : ∀ command : PqxdhRecordLiftInterface.EnvQuery, query ≠ .inr command.val) :
    Commutes seedLens (handlerWith setup codec route reg query) := by
  rcases query with coin | command
  · exact commutes_lift_comp seedLens _
  · cases command with
    | create pin keyId => exact absurd rfl (notEnv ⟨.create pin keyId, trivial⟩)
    | bundle owner => exact absurd rfl (notEnv ⟨.bundle owner, trivial⟩)
    | accept raw => exact absurd rfl (notEnv ⟨.accept raw, trivial⟩)
    | build session payload => exact absurd rfl (notEnv ⟨.build session payload, trivial⟩)
    | finish owner raw => exact absurd rfl (notEnv ⟨.finish owner raw, trivial⟩)
    | hmac key message => exact absurd rfl (notEnv ⟨.hmac key message, trivial⟩)
    | hash bytes => exact onBase_seed _
    | serverSend keyId plaintext => exact onBase_seed _
    | serverRaw raw => exact onBase_seed _
    | beaconSend owner plaintext => exact onBase_seed _
    | beaconRaw owner raw => exact onBase_seed _

/-- The whole handler commutes with completions of the hidden-seed table whenever the registration handler does. -/
theorem handlerWith_commutes_seed (reg : RegImpl KemSK Bk n) (regCommutes : ∀ command, Commutes seedLens (reg command))
    (query : Spec.Domain) : Commutes seedLens (handlerWith setup codec route reg query) := by
  by_cases env : ∃ command : PqxdhRecordLiftInterface.EnvQuery, query = .inr command.val
  · obtain ⟨⟨command, isEnv⟩, rfl⟩ := env
    cases command <;> first | exact regCommutes _ | exact isEnv.elim
  · exact fixed_commute_seed setup codec route reg query fun command same => env ⟨command, same⟩

end Fixed

/-! ### Obliviousness of the real registration (critique M5) -/

/-- A step of the shared native state that leaves the CTX cache alone, whatever the cache holds. -/
def GameFrame {α : Type} (step : NativeGame KemSK α) : Prop :=
  ∀ s c, step.run (gameCtxLens.set s c) = (fun r => (r.1, gameCtxLens.set r.2 c)) <$> step.run s

/-- A frame of the CTX cache commutes with its completions. -/
theorem GameFrame.commutes {α : Type} {step : NativeGame KemSK α} (frame : GameFrame step) :
    Commutes gameCtxLens step :=
  LazyOracleDiscard.commutes_frame _ _ frame

/-- Reading the shared native state passes its game component to the continuation. -/
theorem nativeGet_bind {β : Type} (next : GameState KemSK → NativeGame KemSK β) (s : NativeState KemSK) :
    (PqxdhServerAuthNative.nativeGet >>= next).run s = (next s.2).run s := rfl

/-- An ordinary probabilistic source computation keeps the state for its continuation. -/
theorem nativeCoins_bind {α β : Type} (work : ProbComp α) (next : α → NativeGame KemSK β) (s : NativeState KemSK) :
    (PqxdhServerAuthNative.nativeCoins work >>= next).run s = work >>= fun value => (next value).run s := by
  rw [StateT.run_bind]
  change ((fun value => (value, s)) <$> work) >>= _ = _
  rw [bind_map_left]

/-- An ordinary probabilistic source computation is a frame of the CTX cache. -/
theorem coins_frame {α : Type} (work : ProbComp α) : GameFrame (PqxdhServerAuthNative.nativeCoins (KemSK := KemSK) work) :=
  fun s c => by
    simp only [PqxdhServerAuthNative.nativeCoins, StateT.run, Functor.map_map]

/-- The actual Beacon root callback reads and writes only the Extract family, a frame of the CTX cache. -/
theorem sourceRoot_frame (hmac : PqxdhSecretInputKdf.HmacSha512) (input : beaconcrypt_core.pqxdh.RootKeyInput) :
    GameFrame (PqxdhServerAuthNative.sourceRoot (KemSK := KemSK) hmac input) :=
  fun s c => by
    simp only [PqxdhServerAuthNative.sourceRoot, StateT.run, Functor.map_map]
    rfl

section Real
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- Every request of the native Beacon tail commutes with completions of the CTX cache. -/
theorem beaconNative_commutes (query : (PqxdhBeaconPhase2Publication.NativeTailSpec Response).Domain) :
    Commutes (StateLens.snd Unit CtxRomAuth.CtxRO.QueryCache) (PqxdhServerAuthExperiment.beaconNative setup codec query) := by
  rcases query with query | (input | request | response)
  · exact PqxdhDeploymentHiddenEntry.nativeImpl_commutes _ _ query
  · exact LazyOracleDiscard.commutes_pure _ _
  · exact LazyOracleDiscard.commutes_pure _ _
  · exact LazyOracleDiscard.commutes_pure _ _

/-- Every finish callback (preparation, root, initial KDF, application getter and the record primitives of the finish-time receive) commutes with completions of the CTX cache. -/
theorem callbacks_commutes (query : (PqxdhBeaconPhase2Publication.NativeSpec PqxdhJointIdentity.IdentitySeed
      PqxdhJointGapDh.ScalarBytes (PqxdhKemIndCca.MlKem768PublicKey × KemSK) PqxdhJointIdentity.IdentitySeed
      Response).Domain) :
    Commutes gameCtxLens (PqxdhRegistrationSchedule.callbacks setup codec query) := by
  rcases query with query | query
  · exact (coins_frame _).commutes
  · rcases query with query | (input | request | response)
    · exact LazyOracleDiscard.commutes_lift gameLens _ _ (beaconNative_commutes setup codec (.inl query))
    · exact (sourceRoot_frame setup.hmac input).commutes
    · exact LazyOracleDiscard.commutes_lift gameLens _ _ (beaconNative_commutes setup codec (.inr (.initial request)))
    · exact LazyOracleDiscard.commutes_lift gameLens _ _
        (beaconNative_commutes setup codec (.inr (.application response)))

/-- The registration finish of a present owner, with that owner fixed. -/
noncomputable def ownerFinish (index : Nat) (raw : Pqxdh.Bytes) (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    PqxdhRegistrationSchedule.Game KemSK (Option Pqxdh.Bytes) := do
  let result ← PqxdhRegistrationSchedule.onShared (simulateQ (PqxdhRegistrationSchedule.callbacks setup codec)
    (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner))
  modify fun current => { current with owners := current.owners.set index result.2 }
  pure result.1

/-- M5: the native registration finish commutes with completions of the CTX cache: the owner slot is a frame, the finish-time receive and every other callback commute, and reinstalling the returned owner is a frame. -/
theorem finish_commutes (index : Nat) (raw : Pqxdh.Bytes) :
    Commutes scheduleCtxLens (PqxdhRegistrationSchedule.finish (KemSK := KemSK) setup codec index raw) := by
  refine commutes_dispatch scheduleCtxLens _ (fun s => s.owners[index]?) (fun _ _ => rfl)
    (fun found => match found with
      | none => pure none
      | some owner => ownerFinish setup codec index raw owner)
    (fun s => ?_) (fun found => ?_)
  · rcases found : s.owners[index]? with _ | owner
    · simp only [PqxdhRegistrationSchedule.finish, StateT.run_bind, StateT.run_get, pure_bind, found]
    · simp only [PqxdhRegistrationSchedule.finish, StateT.run_bind, StateT.run_get, pure_bind, found]
      rfl
  · cases found with
    | none => exact LazyOracleDiscard.commutes_pure _ _
    | some owner =>
        refine LazyOracleDiscard.commutes_bind _ (LazyOracleDiscard.commutes_lift scheduleLens gameCtxLens _
          (LazyOracleDiscard.commutes_simulateQ _ _ (callbacks_commutes setup codec) _)) (fun result => ?_)
        refine LazyOracleDiscard.commutes_bind _ ?_ (fun _ => LazyOracleDiscard.commutes_pure _ _)
        exact LazyOracleDiscard.commutes_frame _ _ fun s c => by
          simp only [StateT.run_modify, map_pure]
          rfl

/-- The native build of a session with a present pending token, in focused form: the logged response tail on the seal log and the CTX cache, then the installation of its result. -/
noncomputable def tokenBuild (session : Nat) (payload : Option Pqxdh.Bytes) (token : PqxdhServerRelatedRootConsumer.Returned) :
    NativeGame KemSK (Option PqxdhServerRegistrationPublication.Response) := fun s =>
  (fun r => ((PqxdhServerAuthExperiment.settle s.2.server r.1).1, (s.1, { s.2 with
      pending := Function.update s.2.pending session none
      server := (PqxdhServerAuthExperiment.settle s.2.server r.1).2
      ctx := r.2.2
      ghost := { s.2.ghost with seals := s.2.ghost.seals ++ r.2.1.map (fun context => (session, context)) } }))) <$>
    (simulateQ (PqxdhServerAuthExperiment.tailImpl setup codec checks)
      (PqxdhServerRegistrationPublication.build setup.source token.pending token.root payload () s.2.server)).run
        ([], s.2.ctx)

/-- M5: the native registration build commutes with completions of the CTX cache: the pending token is a frame, the logged response tail commutes, and the installation is a frame. -/
theorem nativeBuild_commutes (session : Nat) (payload : Option Pqxdh.Bytes) :
    Commutes gameCtxLens (PqxdhServerAuthNative.nativeBuild (KemSK := KemSK) setup codec checks session payload) := by
  refine commutes_dispatch gameCtxLens _ (fun s => s.2.pending session) (fun _ _ => rfl)
    (fun found => match found with
      | none => pure none
      | some token => tokenBuild setup codec checks session payload token)
    (fun s => ?_) (fun found => ?_)
  · change (PqxdhServerAuthNative.nativeGet >>= _).run s = _
    rw [nativeGet_bind]
    rcases found : s.2.pending session with _ | token
    · rfl
    · change (PqxdhServerAuthNative.nativeCoins _ >>= _).run s = _
      rw [nativeCoins_bind]
      simp only [tokenBuild, StateT.run, map_eq_bind_pure_comp]
      rfl
  · cases found with
    | none => exact LazyOracleDiscard.commutes_pure _ _
    | some token =>
        refine commutes_focus gameCtxLens (PqxdhDeploymentHiddenEntry.sharedLens (List RawCtxSourceSend.SealContext)) _
          (fun s => ([], s.2.ctx))
          (fun s => simulateQ (PqxdhServerAuthExperiment.tailImpl setup codec checks)
            (PqxdhServerRegistrationPublication.build setup.source token.pending token.root payload () s.2.server))
          (fun s b r => ((PqxdhServerAuthExperiment.settle s.2.server b).1, (s.1, { s.2 with
            pending := Function.update s.2.pending session none
            server := (PqxdhServerAuthExperiment.settle s.2.server b).2
            ctx := r.2
            ghost := { s.2.ghost with seals := s.2.ghost.seals ++ r.1.map (fun context => (session, context)) } })))
          (fun s => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
          (fun s => LazyOracleDiscard.commutes_simulateQ _ _
            (PqxdhDeploymentHiddenEntry.tailImpl_commutes setup codec checks) _)

end Real

/-! ### Frames of the CTX cache in the native registration -/

/-- A pure step is a frame of the CTX cache. -/
theorem frame_pure {α : Type} (value : α) : GameFrame (pure value : NativeGame KemSK α) :=
  fun _ _ => by simp only [StateT.run_pure, map_pure]

/-- Frames of the CTX cache are closed under `bind`. -/
theorem frame_bind {α β : Type} {first : NativeGame KemSK α} {next : α → NativeGame KemSK β}
    (frame : GameFrame first) (rest : ∀ value, GameFrame (next value)) : GameFrame (first >>= next) :=
  fun s c => by
    simp only [StateT.run_bind, frame s c, bind_map_left, map_bind, rest _ _ c]

/-- A local step of the game state is a frame when it commutes with resetting the cache. -/
theorem frame_local {α : Type} (step : GameState KemSK → α × GameState KemSK)
    (commute : ∀ game c, step { game with ctx := c } = ((step game).1, { (step game).2 with ctx := c })) :
    GameFrame (PqxdhServerAuthNative.localState step) :=
  fun s c => by
    show (pure ((step { s.2 with ctx := c }).1, (s.1, (step { s.2 with ctx := c }).2)) :
        ProbComp (α × NativeState KemSK)) =
      (fun r => (r.1, gameCtxLens.set r.2 c)) <$>
        (pure ((step s.2).1, (s.1, (step s.2).2)) : ProbComp (α × NativeState KemSK))
    rw [commute, map_pure]
    rfl

/-- A step of the Extract family alone is a frame of the CTX cache. -/
theorem frame_family {α : Type} (work : StateT PqxdhJointDhExtractFamily.State ProbComp α) :
    GameFrame (fun state => (fun result => (result.1, (result.2, state.2))) <$> work.run state.1 : NativeGame KemSK α) :=
  fun s c => by
    simp only [StateT.run, Functor.map_map]
    rfl

section Frames
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- The native ROM root of a Server session reads and writes only the Extract family. -/
theorem romRoot_frame {E : Type} (hmac : PqxdhSecretInputKdf.HmacSha512)
    (input : PqxdhServerRootPreparation.Inputs Reader E PqxdhBeaconPhase2Preparation.Word32)
    (original : beaconcrypt_core.pqxdh.PendingServerRegistration) :
    GameFrame (PqxdhServerAuthNative.romRoot (A := GameState KemSK) hmac input original) :=
  fun s c => by
    simp only [PqxdhServerAuthNative.romRoot, PqxdhServerAuthNative.romRootBytes, StateT.run, Functor.map_map]
    rfl

/-- The native Server client (core acceptance, root, touch and consumption) is a frame of the CTX cache. -/
theorem nativeClient_frame (hmac : PqxdhSecretInputKdf.HmacSha512) (index : Nat)
    (control : beaconcrypt_core.pqxdh.ServerState) (serverBinding : beaconcrypt_core.pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes PqxdhBeaconPhase2Preparation.Word32) :
    GameFrame (PqxdhServerAuthNative.nativeClient (KemSK := KemSK) hmac index control serverBinding input) := by
  unfold PqxdhServerAuthNative.nativeClient
  split
  · exact frame_pure _
  · exact frame_pure _
  · exact frame_pure _
  · refine frame_bind ?_ fun root => frame_bind (frame_local _ fun _ _ => rfl) fun _ => frame_pure _
    unfold PqxdhServerAuthNative.loggedRoot
    exact frame_bind (romRoot_frame hmac _ _) fun root =>
      frame_bind (frame_local _ fun _ _ => rfl) fun _ => frame_pure _

/-- The accept tail after the native allocation: the core acceptance, root, touch, consumption and pending publication. -/
noncomputable def acceptRest (publicIdentity : PqxdhJointIdentity.PublicIdentity) (game : GameState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes) : NativeGame KemSK (Option Nat) :=
  match collected.1 with
  | none => pure none
  | some input => do
      let returned ← PqxdhServerAuthNative.nativeClient setup.hmac game.sessions game.server.control
        ⟨PqxdhRootTableInitialization.rootArray publicIdentity.ed25519, setup.serverKeyId⟩ input
      match returned with
      | .ok (some token) => do
          PqxdhServerAuthNative.nativeModify fun current =>
            { current with pending := Function.update current.pending game.sessions (some token) }
          pure (some game.sessions)
      | _ => pure none

/-- The accept tail is the allocation followed by `acceptRest`. -/
theorem tail_eq (publicIdentity : PqxdhJointIdentity.PublicIdentity) (game : GameState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes) :
    PqxdhRegistrationJointServerAccept.tail setup publicIdentity game collected =
      (PqxdhServerAuthNative.nativeSet { game with sessions := game.sessions + 1, server := { game.server with consumed := collected.2 } } >>= fun _ =>
        acceptRest setup publicIdentity game collected) := rfl

/-- The accept tail after the allocation is a frame of the CTX cache. -/
theorem acceptRest_frame (publicIdentity : PqxdhJointIdentity.PublicIdentity) (game : GameState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes) :
    GameFrame (acceptRest setup publicIdentity game collected) := by
  unfold acceptRest
  rcases collected with ⟨_ | input, consumed⟩
  · exact frame_pure _
  · refine frame_bind (nativeClient_frame _ _ _ _ _) fun returned => ?_
    rcases returned with (_ | token) | _ | _
    all_goals first
      | exact frame_pure _
      | exact frame_bind (frame_local _ fun _ _ => rfl) fun _ => frame_pure _

/-- Writing a whole game state passes it to the continuation. -/
theorem nativeSet_run_bind {β : Type} (value : GameState KemSK) (next : Unit → NativeGame KemSK β)
    (s : NativeState KemSK) :
    (PqxdhServerAuthNative.nativeSet value >>= next).run s = (next ()).run (s.1, value) := rfl

/-- The accept tail, from a game state whose cache differs, is that tail with its final cache reset. -/
theorem tail_frame (publicIdentity : PqxdhJointIdentity.PublicIdentity) (game : GameState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes) {β : Type}
    (next : Option Nat → NativeGame KemSK β) (nextFrame : ∀ reply, GameFrame (next reply))
    (family : PqxdhJointDhExtractFamily.State) (other : GameState KemSK) (c : CtxRomAuth.CtxRO.QueryCache) :
    (PqxdhRegistrationJointServerAccept.tail setup publicIdentity { game with ctx := c } collected >>= next).run
        (family, other) =
      (fun r => (r.1, gameCtxLens.set r.2 c)) <$>
        (PqxdhRegistrationJointServerAccept.tail setup publicIdentity game collected >>= next).run (family, other) := by
  rw [tail_eq, tail_eq, bind_assoc, bind_assoc, nativeSet_run_bind, nativeSet_run_bind]
  exact (frame_bind (acceptRest_frame setup publicIdentity game collected) nextFrame)
    (family, { game with sessions := game.sessions + 1, server := { game.server with consumed := collected.2 } }) c

/-- The native logged raw accept is a frame of the CTX cache. -/
theorem acceptLogged_frame (seed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes) :
    GameFrame (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed raw) := by
  intro s c
  unfold PqxdhDeploymentLaterServerNative.acceptLogged
  rw [nativeGet_bind, nativeGet_bind]
  rw [nativeCoins_bind, nativeCoins_bind, map_bind]
  refine bind_congr fun collected => ?_
  exact tail_frame setup _ s.2 _ _ (fun _ => frame_pure _) s.1 _ c

/-- The native public HMAC (with its adversary touch) reads and writes only the Extract family and the touch log. -/
theorem nativeHmac_frame (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) :
    GameFrame (PqxdhServerAuthNative.nativeHmac setup seed scalar key message) := by
  unfold PqxdhServerAuthNative.nativeHmac
  dsimp only
  split
  · exact frame_bind (frame_local _ fun _ _ => rfl) fun _ => frame_family _
  · exact frame_family _

end Frames

/-! ### Obliviousness of every real registration command -/

/-- The CTX cache of the LQ-F view of the deployment state with the ephemeral log. -/
abbrev laterLens : CacheLens CtxRomAuth.CtxRO (PqxdhDeploymentNative.State KemSK × PqxdhDeploymentLaterServerSource.Log) :=
  (StateLens.fst (PqxdhDeploymentNative.State KemSK) PqxdhDeploymentLaterServerSource.Log).comp nativeCtxLens

section RealReg
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks)

/-- The real registration handler commutes with completions of the CTX cache at every command whose LQ-F run-phase step does: the snapshot and the backend are frames. -/
theorem realReg_commutes_of (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhRecordLiftInterface.EnvQuery)
    (step : Commutes laterLens
      (PqxdhDeploymentLaterServerGame.handler setup codec checks route created.seed (.inr query.val))) :
    Commutes ctxLens (realReg setup codec route checks created query) :=
  commutes_focus ctxLens laterLens _ (fun x => (x.base, x.log))
    (fun _ => PqxdhDeploymentLaterServerGame.handler setup codec checks route created.seed (.inr query.val))
    (fun x b r => (b, { x with base := r.1, log := r.2, snap := PqxdhDeploymentLater.snapshotAt x.snap x.base.native.owners (PqxdhDeploymentLater.finishOwner (.inr query.val)) }))
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ => step)

/-- M5: the real registration build commutes with completions of the CTX cache. -/
theorem realBuild_commutes_ctx (created : PqxdhLiveServerConstruction.Created Unit) (session : Nat)
    (payload : Option Pqxdh.Bytes) :
    Commutes ctxLens (realReg setup codec route checks created ⟨.build session payload, trivial⟩) := by
  refine realReg_commutes_of setup codec route checks created _ ?_
  show Commutes laterLens ((StateLens.fst _ _).lift (nativeLens.lift (scheduleLens.lift
    (PqxdhServerAuthNative.nativeBuild setup codec checks session payload))))
  exact LazyOracleDiscard.commutes_lift _ _ _ (LazyOracleDiscard.commutes_lift nativeLens _ _
    (LazyOracleDiscard.commutes_lift scheduleLens _ _ (nativeBuild_commutes setup codec checks session payload)))

/-- M5: the real registration finish (snapshot, then the native finish with its finish-time receive) commutes with completions of the CTX cache. -/
theorem realFinish_commutes_ctx (created : PqxdhLiveServerConstruction.Created Unit) (owner : Nat)
    (raw : Pqxdh.Bytes) :
    Commutes ctxLens (realReg setup codec route checks created ⟨.finish owner raw, trivial⟩) := by
  refine realReg_commutes_of setup codec route checks created _ ?_
  show Commutes laterLens ((StateLens.fst _ _).lift (nativeLens.lift
    (PqxdhRegistrationSchedule.finish setup codec owner raw)))
  exact LazyOracleDiscard.commutes_lift _ _ _ (LazyOracleDiscard.commutes_lift nativeLens _ _
    (finish_commutes setup codec owner raw))

/-- The real Beacon creation commutes with completions of the CTX cache: it draws fresh keys and appends an owner. -/
theorem realCreate_commutes_ctx (created : PqxdhLiveServerConstruction.Created Unit) (pin : Pqxdh.Bytes)
    (keyId : Std.U64) :
    Commutes ctxLens (realReg setup codec route checks created ⟨.create pin keyId, trivial⟩) := by
  refine realReg_commutes_of setup codec route checks created _ ?_
  refine LazyOracleDiscard.commutes_lift (StateLens.fst _ _) nativeCtxLens _ ?_
  show Commutes nativeCtxLens (match PqxdhDeploymentInterface.parsePin pin with
    | none => pure none
    | some word => some <$> nativeLens.lift (PqxdhRegistrationSchedule.create setup word keyId))
  split
  · exact LazyOracleDiscard.commutes_pure _ _
  · refine LazyOracleDiscard.commutes_map _ _ (LazyOracleDiscard.commutes_lift nativeLens _ _ ?_)
    unfold PqxdhRegistrationSchedule.create
    refine LazyOracleDiscard.commutes_bind _ (commutes_lift_comp _ _) fun _ => ?_
    refine LazyOracleDiscard.commutes_bind _ (commutes_lift_comp _ _) fun _ => ?_
    refine LazyOracleDiscard.commutes_bind _ (commutes_lift_comp _ _) fun _ => ?_
    exact LazyOracleDiscard.commutes_frame _ _ fun s c => by
      simp only [StateT.run_bind, StateT.run_get, StateT.run_set, pure_bind, StateT.run_pure, map_pure]
      rfl

/-- The real Beacon bundle commutes with completions of the CTX cache: it reads and rewrites only its owner. -/
theorem realBundle_commutes_ctx (created : PqxdhLiveServerConstruction.Created Unit) (owner : Nat) :
    Commutes ctxLens (realReg setup codec route checks created ⟨.bundle owner, trivial⟩) := by
  refine realReg_commutes_of setup codec route checks created _ ?_
  refine LazyOracleDiscard.commutes_lift (StateLens.fst _ _) nativeCtxLens _
    (LazyOracleDiscard.commutes_lift nativeLens _ _ ?_)
  show Commutes scheduleCtxLens (PqxdhRegistrationSchedule.bundle setup codec owner)
  refine commutes_dispatch scheduleCtxLens _ (fun s => s.owners[owner]?) (fun _ _ => rfl)
    (fun found => match found with
      | none => pure none
      | some current => do
          let result ← StateT.lift (simulateQ (PqxdhRegistrationSchedule.bundleCallbacks setup codec
            current.beacon.identity) (PqxdhLivePhase1Bundle.bundle (PqxdhRegistrationSchedule.projection setup owner)
              current))
          modify fun state => { state with owners := state.owners.set owner result.2 }
          pure result.1)
    (fun s => ?_) (fun found => ?_)
  · rcases found : s.owners[owner]? with _ | current
    · simp only [PqxdhRegistrationSchedule.bundle, StateT.run_bind, StateT.run_get, pure_bind, found]
    · simp only [PqxdhRegistrationSchedule.bundle, StateT.run_bind, StateT.run_get, pure_bind, found]
  · cases found with
    | none => exact LazyOracleDiscard.commutes_pure _ _
    | some current =>
        refine LazyOracleDiscard.commutes_bind _ (commutes_lift_comp _ _) fun result => ?_
        refine LazyOracleDiscard.commutes_bind _ ?_ (fun _ => LazyOracleDiscard.commutes_pure _ _)
        exact LazyOracleDiscard.commutes_frame _ _ fun s c => by
          simp only [StateT.run_modify, map_pure]
          rfl

/-- The real public HMAC commutes with completions of the CTX cache. -/
theorem realHmac_commutes_ctx (created : PqxdhLiveServerConstruction.Created Unit)
    (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) :
    Commutes ctxLens (realReg setup codec route checks created ⟨.hmac key message, trivial⟩) := by
  refine realReg_commutes_of setup codec route checks created _ ?_
  refine LazyOracleDiscard.commutes_lift (StateLens.fst _ _) nativeCtxLens _
    (LazyOracleDiscard.commutes_lift nativeLens _ _ (LazyOracleDiscard.commutes_lift scheduleLens _ _ ?_))
  exact (nativeHmac_frame setup _ _ _ _).commutes

/-- The real logged raw accept commutes with completions of the CTX cache. -/
theorem realAccept_commutes_ctx (created : PqxdhLiveServerConstruction.Created Unit) (raw : Pqxdh.Bytes) :
    Commutes ctxLens (realReg setup codec route checks created ⟨.accept raw, trivial⟩) := by
  refine realReg_commutes_of setup codec route checks created _ ?_
  refine commutes_focus laterLens scheduleCtxLens _ (fun s => s.1.native)
    (fun _ => PqxdhRegistrationSchedule.onShared
      (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks created.seed raw))
    (fun s b r => (b.1, ({ s.1 with native := r }, s.2 ++ [b.2])))
    (fun s => ?_) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ => LazyOracleDiscard.commutes_lift scheduleLens _ _ (acceptLogged_frame setup codec checks _ _).commutes)
  simp only [PqxdhDeploymentLaterServerGame.handler, PqxdhDeploymentLaterServerNative.native, StateT.run,
    Functor.map_map]

/-- M5: every command of the real registration handler commutes with completions of the CTX cache. -/
theorem realReg_commutes_ctx (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhRecordLiftInterface.EnvQuery) :
    Commutes ctxLens (realReg setup codec route checks created query) := by
  obtain ⟨command, isEnv⟩ := query
  cases command with
  | create pin keyId => exact realCreate_commutes_ctx setup codec route checks created pin keyId
  | bundle owner => exact realBundle_commutes_ctx setup codec route checks created owner
  | accept raw => exact realAccept_commutes_ctx setup codec route checks created raw
  | build session payload => exact realBuild_commutes_ctx setup codec route checks created session payload
  | finish owner raw => exact realFinish_commutes_ctx setup codec route checks created owner raw
  | hmac key message => exact realHmac_commutes_ctx setup codec route checks created key message
  | _ => exact isEnv.elim

/-- The handler with the real registration handler commutes with completions of the CTX cache at every query. -/
theorem realHandler_commutes_ctx (created : PqxdhLiveServerConstruction.Created Unit) (query : Spec.Domain) :
    Commutes ctxLens (handlerWith setup codec route (realReg setup codec route checks created) query) :=
  handlerWith_commutes_ctx setup codec route _ (realReg_commutes_ctx setup codec route checks created) query

end RealReg

end BeaconcryptCore.Computational.PqxdhDeploymentBackend

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.commutes_focus' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.commutes_focus

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.commutes_dispatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.commutes_dispatch

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.commutes_lift_comp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.commutes_lift_comp

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.ctxLens_get' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.ctxLens_get

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.realStep_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.realStep_view

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.gameWith_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.gameWith_real

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.gameWith_classical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.gameWith_classical

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.nativeHash_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.nativeHash_query

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.primitives_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.primitives_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.record_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.record_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.serverStep_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.serverStep_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.beaconStep_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.beaconStep_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.fixed_commute_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.fixed_commute_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.handlerWith_commutes_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.handlerWith_commutes_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.onBase_seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.onBase_seed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.fixed_commute_seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.fixed_commute_seed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.handlerWith_commutes_seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.handlerWith_commutes_seed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.GameFrame.commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.GameFrame.commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.nativeGet_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.nativeGet_bind

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.nativeCoins_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.nativeCoins_bind

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.coins_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.coins_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.sourceRoot_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.sourceRoot_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.beaconNative_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.beaconNative_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.callbacks_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.callbacks_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.finish_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.finish_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.nativeBuild_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.nativeBuild_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.frame_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.frame_pure

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.frame_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.frame_bind

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.frame_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.frame_local

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.frame_family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.frame_family

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.romRoot_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.romRoot_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.nativeClient_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.nativeClient_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.tail_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.tail_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.acceptRest_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.acceptRest_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.nativeSet_run_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.nativeSet_run_bind

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.tail_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.tail_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.acceptLogged_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.acceptLogged_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.nativeHmac_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.nativeHmac_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.realReg_commutes_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.realReg_commutes_of

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.realBuild_commutes_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.realBuild_commutes_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.realFinish_commutes_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.realFinish_commutes_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.realCreate_commutes_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.realCreate_commutes_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.realBundle_commutes_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.realBundle_commutes_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.realHmac_commutes_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.realHmac_commutes_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.realAccept_commutes_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.realAccept_commutes_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.realReg_commutes_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.realReg_commutes_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentBackend.realHandler_commutes_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentBackend.realHandler_commutes_ctx
