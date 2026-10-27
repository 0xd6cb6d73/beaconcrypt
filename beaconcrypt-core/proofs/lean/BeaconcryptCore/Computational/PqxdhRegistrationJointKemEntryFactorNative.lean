import BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactorTools
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeletonServices

/-!
# The factored services on the native layer of the skeleton (item 2, stage S3b, native layer)

Stage S3b of the item 2 plan replaces the native services of the services skeleton (`PqxdhRegistrationJointKemPostSkeleton.nativeServices`, whose hidden values are 32-byte roots) by the factored services (`factoredServices`, whose hidden values are the 108-byte key-schedule outputs `PqxdhServerAuthKeySchedule.Output`). On a hidden entry with value `value`, the factored services are the fields of `PqxdhServerAuthEntryFactor.factorServices setup codec checks context value` (plan section 18; `factorHidden_eq`): the logged `PqxdhServerAuthLoggedSendFactor.factored` for the Server's response tail and `PqxdhServerAuthBeaconFactor.factored` with `nativePrim` for the Beacon continuation, both at `PqxdhServerAuthCtxMaterial.factor value`. The root that the Server's pending token holds for the hidden session is the fixed placeholder `PqxdhServerAuthEntryFactor.sentinel`, so the pending token holds no part of the value.

The comparison is a program equality on the native layer, with the hidden values related by `f = PqxdhServerAuthKeySchedule.fromRoot setup.source`:

- `hiddenAfter_factor`: the native Beacon continuation after a root `r` is the factored continuation at `fromRoot source r` (`PqxdhServerAuthBeaconFactor.beacon_afterRoot_factor`, `PqxdhServerAuthCtxMaterial.factor_source`); `hiddenBuild_factor`: the native response tail of a session whose pending token holds root `r` is the factored response tail at `fromRoot source r` on the same Registration (`PqxdhServerAuthLoggedSendFactor.logged_server_send_factor`).
- `proj f` maps a native-layer state of the native skeleton to one of the factored skeleton: the marked hidden value `r` becomes `f r`, and the pending token of the marked session gets the placeholder root (`placeholderAt`, the plan's pending-root placeholder). `Inv` is the invariant under which this projection commutes with every step: the marked session index is below the session counter and its pending token, if any, holds the marked root.
- `Rel f answer P Q native factored` relates a native-layer program of the native skeleton to one of the factored skeleton: from every state satisfying `P`, the native run mapped by `answer` and `proj f` is the factored run from the projected state with its value reads relabelled by `f` (`PqxdhRegistrationJointKemEntryFactor.relabel`), and every native final state satisfies `Q`. `RelC` is the same relation on the exposed encapsulation interface, and `liftT_rel` lifts the first to the second.
- `skelImpl_rel`: every step of the skeleton's native layer is related, under `Inv`.

These are program equalities; they charge nothing.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor

open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhRegistrationJointKemPostSkeleton
open PqxdhSecretInputKdf (HmacBlock HmacOracle RootOutput)

/-- The 108-byte key-schedule output. -/
abbrev Output := PqxdhServerAuthKeySchedule.Output

/-! ### The factored services -/

section Services

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The factored hidden-entry services at a 108-byte value: the fields of `PqxdhServerAuthEntryFactor.factorServices` (plan section 18). -/
noncomputable def factoredHidden (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (value : Output) : Hidden Response where
  hiddenBuild token payload server := PqxdhServerAuthLoggedSendFactor.factored
    (fun entry _ _ => pure (entry, .None))
    (PqxdhServerAuthLoggedSendFactor.loggedPrim setup codec checks) setup.source
    (PqxdhServerAuthLoggedSendFactor.loggedAux setup codec checks)
    (PqxdhServerAuthCtxMaterial.factor value) token.pending payload () server
  hiddenAfter pending := PqxdhServerAuthBeaconFactor.factored
    (PqxdhServerAuthBeaconFactor.nativePrim setup codec)
    (fun entry _ => pure (entry, none)) setup.source (fun response => pure (codec.application response))
    codec.frameRead (PqxdhPhase2DhRootConsumer.cleared pending) (PqxdhServerAuthCtxMaterial.factor value)

/-- The factored hidden-entry services are those of `PqxdhServerAuthEntryFactor.factorServices`, for every context. -/
theorem factorHidden_eq (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : PqxdhServerAuthEntryFactor.Context KemSK) (value : Output) :
    factorHidden setup codec checks context value = factoredHidden setup codec checks value := rfl

/-- The factored services: hidden values are 108-byte outputs, the hidden session's pending token holds the placeholder root, and each hidden entry runs the factored forms. -/
noncomputable def factoredServices (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) :
    Services Output Response where
  rootOf _ := PqxdhServerAuthEntryFactor.sentinel
  hidden := factoredHidden setup codec checks

/-- The native Beacon continuation after a root is the factored continuation at the root's 108-byte output. -/
theorem hiddenAfter_factor (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (root : RootOutput) :
    (nativeHidden setup codec checks root).hiddenAfter =
      (factoredHidden setup codec checks (PqxdhServerAuthKeySchedule.fromRoot setup.source root)).hiddenAfter := by
  funext pending
  change simulateQ (beaconNative setup codec)
      (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead pending (PqxdhRootTableInitialization.rootArray root)) = _
  rw [PqxdhServerAuthBeaconFactor.beacon_afterRoot_factor setup codec (fun entry _ => pure (entry, none)),
    ← PqxdhServerAuthCtxMaterial.factor_source]
  rfl

/-- The native response tail of a session whose pending token holds a root is the factored response tail at that root's 108-byte output, on any token with the same pending Registration. -/
theorem hiddenBuild_factor (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (token other : PqxdhServerRelatedRootConsumer.Returned) (same : other.pending = token.pending)
    (payload : Option Pqxdh.Bytes) (server : PqxdhServerAuthEntryFactor.ServerState) :
    nativeResponse setup codec checks token payload server =
      (factoredHidden setup codec checks (PqxdhServerAuthKeySchedule.fromRoot setup.source token.root)).hiddenBuild
        other payload server := by
  change simulateQ (tailImpl setup codec checks)
      (PqxdhServerRegistrationPublication.build setup.source token.pending token.root payload () server) = _
  rw [PqxdhServerAuthLoggedSendFactor.logged_server_send_factor setup codec checks (fun entry _ _ => pure (entry, .None)),
    ← PqxdhServerAuthCtxMaterial.factor_source]
  change _ = PqxdhServerAuthLoggedSendFactor.factored _ _ _ _ _ other.pending payload () server
  rw [same]

end Services

/-! ### The projection and its invariant -/

section Projection

variable {KemSK : Type}

/-- A pending token with the placeholder root. -/
def placeholderToken (token : Option PqxdhServerRelatedRootConsumer.Returned) :
    Option PqxdhServerRelatedRootConsumer.Returned :=
  token.map fun token => ⟨PqxdhServerAuthEntryFactor.sentinel, token.pending⟩

/-- The game state with the pending token of the marked session holding the placeholder root. -/
def placeholderAt (marked : Option Nat) (game : GameState KemSK) : GameState KemSK :=
  match marked with
  | none => game
  | some index => { game with pending := Function.update game.pending index (placeholderToken (game.pending index)) }

/-- A native-layer state of the native skeleton as one of the factored skeleton: the marked value becomes its image under `f`, and the marked session's pending token holds the placeholder root. -/
def proj (f : RootOutput → Output) (state : SkelState KemSK RootOutput) : SkelState KemSK Output :=
  (placeholderAt (state.2.map Prod.fst) state.1, state.2.map (Prod.map id f))

/-- The marked session is below `bound` and its pending token, if any, holds the marked root. -/
def Good (bound : Nat) (state : SkelState KemSK RootOutput) : Prop :=
  ∀ index root, state.2 = some (index, root) →
    index < bound ∧ ∀ token, state.1.pending index = some token → token.root = root

/-- The invariant of the comparison: `Good` at the session counter. -/
def Inv (state : SkelState KemSK RootOutput) : Prop := Good state.1.sessions state

theorem proj_none (f : RootOutput → Output) (game : GameState KemSK) : proj f (game, none) = (game, none) := rfl

theorem placeholderAt_none (game : GameState KemSK) : placeholderAt none game = game := rfl

theorem placeholderAt_clean (marked : Option Nat) (game : GameState KemSK) :
    placeholderAt marked (clean game) = clean (placeholderAt marked game) := by
  cases marked <;> rfl

theorem placeholderAt_ctx (marked : Option Nat) (game : GameState KemSK) (ctx : CtxRomAuth.CtxRO.QueryCache) :
    placeholderAt marked { game with ctx := ctx } = { placeholderAt marked game with ctx := ctx } := by
  cases marked <;> rfl

theorem placeholderAt_ctx_eq (marked : Option Nat) (game : GameState KemSK) :
    (placeholderAt marked game).ctx = game.ctx := by
  cases marked <;> rfl

theorem placeholderAt_server_eq (marked : Option Nat) (game : GameState KemSK) :
    (placeholderAt marked game).server = game.server := by
  cases marked <;> rfl

theorem placeholderAt_sessions_eq (marked : Option Nat) (game : GameState KemSK) :
    (placeholderAt marked game).sessions = game.sessions := by
  cases marked <;> rfl

theorem placeholderAt_server (marked : Option Nat) (game : GameState KemSK)
    (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) :
    placeholderAt marked { game with server := server } = { placeholderAt marked game with server := server } := by
  cases marked <;> rfl

theorem placeholderAt_sessions (marked : Option Nat) (game : GameState KemSK) (sessions : Nat)
    (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) :
    placeholderAt marked { game with sessions := sessions, server := server } =
      { placeholderAt marked game with sessions := sessions, server := server } := by
  cases marked <;> rfl

/-- The pending token of an unmarked session is unchanged. -/
theorem placeholderAt_pending_ne (marked : Option Nat) (game : GameState KemSK) (session : Nat)
    (other : ∀ index, marked = some index → index ≠ session) :
    (placeholderAt marked game).pending session = game.pending session := by
  cases marked with
  | none => rfl
  | some index =>
      simp only [placeholderAt]
      exact Function.update_of_ne (other index rfl).symm _ _

/-- Writing a pending token of an unmarked session commutes with the placeholder. -/
theorem placeholderAt_update (marked : Option Nat) (game : GameState KemSK) (session : Nat)
    (token : Option PqxdhServerRelatedRootConsumer.Returned) (other : ∀ index, marked = some index → index ≠ session) :
    placeholderAt marked { game with pending := Function.update game.pending session token } =
      { placeholderAt marked game with pending := Function.update (placeholderAt marked game).pending session token } := by
  cases marked with
  | none => rfl
  | some index =>
      have distinct : index ≠ session := other index rfl
      simp only [placeholderAt, Function.update_of_ne distinct]
      rw [Function.update_comm distinct]

/-- Clearing a pending token commutes with the placeholder. -/
theorem placeholderAt_clear (marked : Option Nat) (game : GameState KemSK) (session : Nat) :
    placeholderAt marked { game with pending := Function.update game.pending session none } =
      { placeholderAt marked game with pending := Function.update (placeholderAt marked game).pending session none } := by
  cases marked with
  | none => rfl
  | some index =>
      by_cases same : index = session
      · subst same
        simp only [placeholderAt, Function.update_self, placeholderToken, Option.map_none, Function.update_idem]
      · simp only [placeholderAt, Function.update_of_ne same]
        rw [Function.update_comm same]

end Projection

/-! ### Related programs -/

section Rel

variable {KemSK : Type}

/-- Relabelling at the bottom of the skeleton interface. -/
noncomputable abbrev relabelS (f : RootOutput → Output) :
    QueryImpl (SkelSpec Output) (OracleComp (SkelSpec RootOutput)) :=
  relabel (B := unifSpec) (D := PqxdhCorrelatedExtractFamily.Message) (T := PqxdhExtractRomHiddenSuffix.TableOracle) f

/-- Relabelling on the exposed encapsulation interface with the table oracles. -/
noncomputable abbrev relabelE (f : RootOutput → Output) :
    QueryImpl (Enc KemSK + TSpec Output) (OracleComp (Enc KemSK + TSpec RootOutput)) :=
  relabel (B := Enc KemSK) (D := PqxdhCorrelatedExtractFamily.Message) (T := PqxdhExtractRomHiddenSuffix.TableOracle) f

/-- A native-layer program of the native skeleton and one of the factored skeleton are related: from every state satisfying `P`, the native run mapped by `answer` and the projection is the relabelled factored run from the projected state, and every native final state satisfies `Q`. -/
def Rel {α β : Type} (f : RootOutput → Output) (answer : α → β) (P : SkelState KemSK RootOutput → Prop)
    (Q : α → SkelState KemSK RootOutput → Prop) (native : NGame KemSK RootOutput α) (factored : NGame KemSK Output β) :
    Prop :=
  ∀ state, P state →
    Prod.map answer (proj f) <$> native.run state = simulateQ (relabelS f) (factored.run (proj f state)) ∧
      ∀ result ∈ support (native.run state), Q result.1 result.2

/-- The same relation on the exposed encapsulation interface. -/
def RelC {α β : Type} (f : RootOutput → Output) (answer : α → β) (P : SkelState KemSK RootOutput → Prop)
    (Q : α → SkelState KemSK RootOutput → Prop) (native : SClient KemSK RootOutput α) (factored : SClient KemSK Output β) :
    Prop :=
  ∀ state, P state →
    Prod.map answer (proj f) <$> native.run state = simulateQ (relabelE f) (factored.run (proj f state)) ∧
      ∀ result ∈ support (native.run state), Q result.1 result.2

theorem Rel.bind {α β γ δ : Type} {f : RootOutput → Output} {answer : α → β} {answer' : γ → δ}
    {P : SkelState KemSK RootOutput → Prop} {Q : α → SkelState KemSK RootOutput → Prop}
    {R : γ → SkelState KemSK RootOutput → Prop}
    {native : NGame KemSK RootOutput α} {factored : NGame KemSK Output β}
    {next : α → NGame KemSK RootOutput γ} {nextF : β → NGame KemSK Output δ}
    (first : Rel f answer P Q native factored) (rest : ∀ value, Rel f answer' (Q value) R (next value) (nextF (answer value))) :
    Rel f answer' P R (native >>= next) (factored >>= nextF) := by
  intro state holds
  obtain ⟨same, supported⟩ := first state holds
  refine ⟨?_, ?_⟩
  · simp only [StateT.run_bind, map_bind, simulateQ_bind]
    rw [← same, bind_map_left]
    exact bind_congr_of_forall_mem_support _ fun step member =>
      (rest step.1 step.2 (supported step member)).1
  · intro result member
    simp only [StateT.run_bind, mem_support_bind_iff] at member
    obtain ⟨step, stepMember, member⟩ := member
    exact (rest step.1 step.2 (supported step stepMember)).2 result member

theorem Rel.pure {α β : Type} {f : RootOutput → Output} {answer : α → β}
    {P : SkelState KemSK RootOutput → Prop} {Q : α → SkelState KemSK RootOutput → Prop} (value : α)
    (holds : ∀ state, P state → Q value state) :
    Rel f answer P Q (Pure.pure value) (Pure.pure (answer value)) := by
  intro state start
  refine ⟨?_, ?_⟩
  · simp only [StateT.run_pure, map_pure, simulateQ_pure, Prod.map_apply]
  · intro result member
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact holds state start

theorem Rel.mono {α β : Type} {f : RootOutput → Output} {answer : α → β}
    {P P' : SkelState KemSK RootOutput → Prop} {Q Q' : α → SkelState KemSK RootOutput → Prop}
    {native : NGame KemSK RootOutput α} {factored : NGame KemSK Output β}
    (related : Rel f answer P Q native factored) (pre : ∀ state, P' state → P state)
    (post : ∀ value state, Q value state → Q' value state) : Rel f answer P' Q' native factored :=
  fun state holds => ⟨(related state (pre state holds)).1,
    fun result member => post _ _ ((related state (pre state holds)).2 result member)⟩

/-- Relabelling a lifted probabilistic computation leaves it unchanged. -/
theorem relabelS_liftComp {α : Type} (f : RootOutput → Output) (work : ProbComp α) :
    simulateQ (relabelS f) (OracleComp.liftComp work (SkelSpec Output)) = OracleComp.liftComp work (SkelSpec RootOutput) :=
  relabel_liftComp f work

/-- A direct read is related to itself. -/
theorem Rel.tableRead (f : RootOutput → Output) (P : SkelState KemSK RootOutput → Prop) (point : Pqxdh.Bytes) :
    Rel f id P (fun _ => P) (tableRead point) (tableRead point) := by
  intro state holds
  refine ⟨?_, ?_⟩
  · change Prod.map id (proj f) <$> ((fun reply => (reply, state)) <$>
        ((SkelSpec RootOutput).query (.inr (.inr point)) : OracleComp (SkelSpec RootOutput) _)) =
      simulateQ (relabelS f) ((fun reply => (reply, proj f state)) <$>
        ((SkelSpec Output).query (.inr (.inr point)) : OracleComp (SkelSpec Output) _))
    rw [simulateQ_map, relabel_query_direct, Functor.map_map]
    rfl
  · intro result member
    change result ∈ support ((fun reply => (reply, state)) <$>
      ((SkelSpec RootOutput).query (.inr (.inr point)) : OracleComp (SkelSpec RootOutput) _)) at member
    rw [support_map] at member
    obtain ⟨reply, -, rfl⟩ := member
    exact holds

/-- A hidden read is related to itself, with the answer mapped by `f`. -/
theorem Rel.valueRead (f : RootOutput → Output) (P : SkelState KemSK RootOutput → Prop)
    (point : PqxdhCorrelatedExtractFamily.Message) :
    Rel f f P (fun _ => P) (valueRead point) (valueRead point) := by
  intro state holds
  refine ⟨?_, ?_⟩
  · change Prod.map f (proj f) <$> ((fun reply => (reply, state)) <$>
        ((SkelSpec RootOutput).query (.inr (.inl point)) : OracleComp (SkelSpec RootOutput) _)) =
      simulateQ (relabelS f) ((fun reply => (reply, proj f state)) <$>
        ((SkelSpec Output).query (.inr (.inl point)) : OracleComp (SkelSpec Output) _))
    rw [simulateQ_map, relabel_query_value, Functor.map_map, Functor.map_map]
    rfl
  · intro result member
    change result ∈ support ((fun reply => (reply, state)) <$>
      ((SkelSpec RootOutput).query (.inr (.inl point)) : OracleComp (SkelSpec RootOutput) _)) at member
    rw [support_map] at member
    obtain ⟨reply, -, rfl⟩ := member
    exact holds

/-- A game-state computation that commutes with the placeholder and keeps the pending tokens and the session counter is related to itself. -/
theorem Rel.gameStep {α : Type} (f : RootOutput → Output) (P : SkelState KemSK RootOutput → Prop)
    (work : StateT (GameState KemSK) ProbComp α)
    (commutes : ∀ marked game, Prod.map id (placeholderAt marked) <$> work.run game =
      work.run (placeholderAt marked game))
    (keeps : ∀ game, ∀ result ∈ support (work.run game),
      result.2.pending = game.pending ∧ result.2.sessions = game.sessions)
    (stable : ∀ state game, P state → game.pending = state.1.pending → game.sessions = state.1.sessions →
      P (game, state.2)) :
    Rel f id P (fun _ => P) (PqxdhRegistrationJointKemPostSkeleton.gameStep work)
      (PqxdhRegistrationJointKemPostSkeleton.gameStep work) := by
  intro state holds
  refine ⟨?_, ?_⟩
  · change Prod.map id (proj f) <$> ((fun result => (result.1, (result.2, state.2))) <$>
        OracleComp.liftComp (work.run (clean state.1)) (SkelSpec RootOutput)) =
      simulateQ (relabelS f) ((fun result => (result.1, (result.2, (proj f state).2))) <$>
        OracleComp.liftComp (work.run (clean (proj f state).1)) (SkelSpec Output))
    rw [simulateQ_map, relabelS_liftComp]
    change _ = _ <$> OracleComp.liftComp (work.run (clean (placeholderAt (state.2.map Prod.fst) state.1)))
      (SkelSpec RootOutput)
    rw [← placeholderAt_clean, ← commutes, OracleComp.liftComp_map, Functor.map_map, Functor.map_map]
    rfl
  · intro result member
    change result ∈ support ((fun result => (result.1, (result.2, state.2))) <$>
      OracleComp.liftComp (work.run (clean state.1)) (SkelSpec RootOutput)) at member
    rw [support_map, OracleComp.support_liftComp] at member
    obtain ⟨step, stepMember, rfl⟩ := member
    obtain ⟨pending, sessions⟩ := keeps _ step stepMember
    exact stable state step.2 holds pending sessions

/-- A computation on the shared commitment cache is related to itself. -/
theorem Rel.ctx {α : Type} (f : RootOutput → Output) (P : SkelState KemSK RootOutput → Prop)
    (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp α)
    (stable : ∀ state game, P state → game.pending = state.1.pending → game.sessions = state.1.sessions →
      P (game, state.2)) :
    Rel f id P (fun _ => P) (PqxdhRegistrationJointKemPostSkeleton.gameStep (ctxGame work))
      (PqxdhRegistrationJointKemPostSkeleton.gameStep (ctxGame work)) := by
  refine Rel.gameStep f P _ (fun marked game => ?_) (fun game result member => ?_) stable
  · simp only [ctxGame, StateT.run, Functor.map_map, placeholderAt_ctx_eq]
    congr 1
    funext result
    simp only [Prod.map_apply, id_eq, placeholderAt_ctx]
  · simp only [ctxGame, StateT.run, support_map] at member
    obtain ⟨step, -, rfl⟩ := member
    exact ⟨rfl, rfl⟩

/-- The invariant and `Good` are stable under steps that keep the pending tokens and the session counter. -/
theorem inv_stable (state : SkelState KemSK RootOutput) (game : GameState KemSK) (holds : Inv state)
    (pending : game.pending = state.1.pending) (sessions : game.sessions = state.1.sessions) : Inv (game, state.2) := by
  intro index root marked
  obtain ⟨below, held⟩ := holds index root marked
  exact ⟨sessions ▸ below, fun token found => held token (pending ▸ found)⟩

theorem good_stable (bound : Nat) (state : SkelState KemSK RootOutput) (game : GameState KemSK)
    (holds : Good bound state) (pending : game.pending = state.1.pending) (_sessions : game.sessions = state.1.sessions) :
    Good bound (game, state.2) := by
  intro index root marked
  obtain ⟨below, held⟩ := holds index root marked
  exact ⟨below, fun token found => held token (pending ▸ found)⟩

end Rel

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.factorHidden_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.factorHidden_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.hiddenAfter_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.hiddenAfter_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.hiddenBuild_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.hiddenBuild_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.proj_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.proj_none

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.placeholderAt_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.placeholderAt_none

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.placeholderAt_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.placeholderAt_clean

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.placeholderAt_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.placeholderAt_ctx

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.placeholderAt_ctx_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.placeholderAt_ctx_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.placeholderAt_server_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.placeholderAt_server_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.placeholderAt_sessions_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.placeholderAt_sessions_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.placeholderAt_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.placeholderAt_server

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.placeholderAt_sessions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.placeholderAt_sessions

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.placeholderAt_pending_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.placeholderAt_pending_ne

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.placeholderAt_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.placeholderAt_update

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.placeholderAt_clear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.placeholderAt_clear

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.Rel.bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.Rel.bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.Rel.pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.Rel.pure

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.Rel.mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.Rel.mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.relabelS_liftComp' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.relabelS_liftComp

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.Rel.tableRead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.Rel.tableRead

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.Rel.valueRead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.Rel.valueRead

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.Rel.gameStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.Rel.gameStep

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.Rel.ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.Rel.ctx

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.inv_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.inv_stable

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.good_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.good_stable
