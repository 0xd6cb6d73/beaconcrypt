import BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactorNative
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeletonNative

/-!
# Every native-layer step of the skeleton under the factored services (item 2, stage S3b, steps)

This module proves `skelImpl_rel`: every step of the native layer of the services skeleton with the native services (`nativeServices`, hidden values are 32-byte roots) is related, in the sense of `PqxdhRegistrationJointKemEntryFactor.RelC` and under the invariant `Inv`, to the same step with the factored services (`factoredServices`, hidden values are 108-byte outputs), with the hidden values related by `PqxdhServerAuthKeySchedule.fromRoot setup.source`.

- Steps that touch neither hidden values nor pending tokens (Beacon tail callbacks, public HMAC, BLAKE2b, kernel reveals, forwarded pool requests) are related to themselves.
- The grouped Beacon finish on the challenge marker reads the hidden value of its coordinates; the native continuation at the root is the factored continuation at the root's 108-byte output (`hiddenAfter_factor`).
- The Server build of the marked session: the native response tail reads the root of the session's pending token, which is the marked root by `Inv`; the factored response tail reads the marked 108-byte output and ignores the pending token's placeholder root (`hiddenBuild_factor`).
- The Server's raw accept writes a fresh pending token at the session counter, which by `Inv` is not the marked session.

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

/-! ### Lifting and atomic steps -/

section Atomic

variable {KemSK : Type}

/-- Related native-layer programs are related on the exposed encapsulation interface. -/
theorem liftT_rel {α β : Type} {f : RootOutput → Output} {answer : α → β}
    {P : SkelState KemSK RootOutput → Prop} {Q : α → SkelState KemSK RootOutput → Prop}
    {native : NGame KemSK RootOutput α} {factored : NGame KemSK Output β}
    (related : Rel f answer P Q native factored) : RelC f answer P Q (liftT native) (liftT factored) := by
  intro state holds
  obtain ⟨same, supported⟩ := related state holds
  refine ⟨?_, ?_⟩
  · change Prod.map answer (proj f) <$>
        simulateQ (fwd (T := TSpec RootOutput) (coinLift (KemSK := KemSK))) (native.run state) =
      simulateQ (relabelE f) (simulateQ (fwd (T := TSpec Output) (coinLift (KemSK := KemSK)))
        (factored.run (proj f state)))
    rw [← simulateQ_map, same, relabel_fwd]
  · intro result member
    exact supported result (support_simulateQ_subset _ _ member)

/-- Replacing the game state, with the factored state the placeholder image of the native one. -/
theorem Rel.setGame (f : RootOutput → Output) (P : SkelState KemSK RootOutput → Prop)
    (Q : Unit → SkelState KemSK RootOutput → Prop) (game game' : GameState KemSK)
    (image : ∀ state, P state → placeholderAt (state.2.map Prod.fst) game = game')
    (post : ∀ state, P state → Q () (game, state.2)) :
    Rel f id P Q (PqxdhRegistrationJointKemPostSkeleton.setGame game)
      (PqxdhRegistrationJointKemPostSkeleton.setGame game') := by
  intro state holds
  refine ⟨?_, ?_⟩
  · change (Pure.pure ((), proj f (game, state.2)) : OracleComp (SkelSpec RootOutput) _) =
      simulateQ (relabelS f) (Pure.pure ((), (game', (proj f state).2)))
    rw [simulateQ_pure, proj, image state holds]
    rfl
  · intro result member
    change result ∈ support (Pure.pure ((), (game, state.2)) : OracleComp (SkelSpec RootOutput) _) at member
    rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact post state holds

/-- Changing the game state by a change that commutes with the placeholder. -/
theorem Rel.modifyGame (f : RootOutput → Output) (P : SkelState KemSK RootOutput → Prop)
    (Q : Unit → SkelState KemSK RootOutput → Prop) (change : GameState KemSK → GameState KemSK)
    (commutes : ∀ state, P state →
      placeholderAt (state.2.map Prod.fst) (change state.1) = change (placeholderAt (state.2.map Prod.fst) state.1))
    (post : ∀ state, P state → Q () (change state.1, state.2)) :
    Rel f id P Q (PqxdhRegistrationJointKemPostSkeleton.modifyGame change)
      (PqxdhRegistrationJointKemPostSkeleton.modifyGame change) := by
  intro state holds
  refine ⟨?_, ?_⟩
  · change (Pure.pure ((), proj f (change state.1, state.2)) : OracleComp (SkelSpec RootOutput) _) =
      simulateQ (relabelS f) (Pure.pure ((), (change (proj f state).1, (proj f state).2)))
    rw [simulateQ_pure, proj, commutes state holds]
    rfl
  · intro result member
    change result ∈ support (Pure.pure ((), (change state.1, state.2)) : OracleComp (SkelSpec RootOutput) _) at member
    rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact post state holds

/-- A predicate on the pending tokens, the session counter and the marks. -/
def Framed (P : SkelState KemSK RootOutput → Prop) : Prop :=
  ∀ state game, P state → game.pending = state.1.pending → game.sessions = state.1.sessions → P (game, state.2)

theorem inv_framed : Framed (KemSK := KemSK) Inv := fun state game holds pending sessions =>
  inv_stable state game holds pending sessions

theorem good_framed (bound : Nat) : Framed (KemSK := KemSK) (Good bound) := fun state game holds pending sessions =>
  good_stable bound state game holds pending sessions

theorem framed_and {P P' : SkelState KemSK RootOutput → Prop} (framed : Framed P) (framed' : Framed P') :
    Framed fun state => P state ∧ P' state := fun state game holds pending sessions =>
  ⟨framed state game holds.1 pending sessions, framed' state game holds.2 pending sessions⟩

/-- The source's consumption of a registration ID is related to itself. -/
theorem Rel.consume (f : RootOutput → Output) (P : SkelState KemSK RootOutput → Prop) (framed : Framed P)
    (rid : beaconcrypt_core.pqxdh.RegistrationId) :
    Rel f id P (fun _ => P) (consumeGame rid) (consumeGame rid) := by
  refine Rel.modifyGame f P _ _ (fun state _ => ?_) (fun state holds => framed state _ holds rfl rfl)
  rw [placeholderAt_server, placeholderAt_server_eq]

end Atomic

/-! ### The native-layer handlers -/

section Handlers

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The Beacon tail callbacks are related to themselves. -/
theorem tailStep_rel (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (f : RootOutput → Output)
    (P : SkelState KemSK RootOutput → Prop) (framed : Framed P)
    (query : (PqxdhBeaconPhase2Publication.NativeTailSpec Response).Domain) :
    Rel f id P (fun _ => P) (tailStep (V := RootOutput) setup codec query) (tailStep (V := Output) setup codec query) := by
  rcases query with query | (input | request | response)
  · exact Rel.ctx f P _ framed
  · exact Rel.bind (Rel.tableRead f P _) fun block => Rel.pure _ fun _ holds => holds
  · exact Rel.ctx f P _ framed
  · exact Rel.ctx f P _ framed

/-- The adversary's public HMAC is related to itself. -/
theorem hmacStep_rel (setup : Setup baseSpec KemSK) (f : RootOutput → Output) (P : SkelState KemSK RootOutput → Prop)
    (key : HmacBlock) (message : Pqxdh.Bytes) :
    Rel f id P (fun _ => P) (hmacStep (V := RootOutput) setup key message) (hmacStep (V := Output) setup key message) := by
  by_cases slice : key = PqxdhSecretInputKdf.zeroSalt ∧ message.length = 192
  · simp only [hmacStep, slice, and_self, ite_true]
    exact Rel.tableRead f P message
  · simp only [hmacStep, slice, ite_false]
    exact Rel.pure _ fun _ holds => holds

/-- The BLAKE2b oracle is related to itself. -/
theorem hash_rel (f : RootOutput → Output) (P : SkelState KemSK RootOutput → Prop) (framed : Framed P)
    (bytes : Pqxdh.Bytes) :
    Rel f id P (fun _ => P) (gameStep (V := RootOutput) (hashGame (KemSK := KemSK) bytes))
      (gameStep (V := Output) (hashGame bytes)) := by
  refine Rel.gameStep f P _ (fun marked game => ?_) (fun game result member => ?_) framed
  · simp only [hashGame, StateT.run, Functor.map_map, placeholderAt_ctx_eq]
    congr 1
    funext result
    simp only [Prod.map_apply, id_eq, placeholderAt_ctx]
  · simp only [hashGame, StateT.run, support_map] at member
    obtain ⟨step, -, rfl⟩ := member
    exact ⟨rfl, rfl⟩

/-- A kernel reveal is related to itself: it reads installed kernels, never a pending root. -/
theorem reveal_rel (f : RootOutput → Output) (P : SkelState KemSK RootOutput → Prop) (framed : Framed P)
    (keyId : Std.U64) :
    Rel f id P (fun _ => P)
      (gameStep (V := RootOutput) (fun game : GameState KemSK => Pure.pure (revealKernel keyId game, game)))
      (gameStep (V := Output) (fun game : GameState KemSK => Pure.pure (revealKernel keyId game, game))) := by
  refine Rel.gameStep f P _ (fun marked game => ?_) (fun game result member => ?_) framed
  · change Prod.map id (placeholderAt marked) <$> (Pure.pure (revealKernel keyId game, game) : ProbComp _) =
      Pure.pure (revealKernel keyId (placeholderAt marked game), placeholderAt marked game)
    rw [map_pure, revealKernel, revealKernel, placeholderAt_server_eq]
    rfl
  · change result ∈ support (Pure.pure (revealKernel keyId game, game) : ProbComp _) at member
    rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, rfl⟩

/-- The grouped Beacon finish: a hidden read on the challenge marker, whose native continuation at the root is the factored continuation at the root's 108-byte output. -/
theorem groupStep_rel (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (P : SkelState KemSK RootOutput → Prop) (framed : Framed P) (pending : Pending Response) :
    Rel (PqxdhServerAuthKeySchedule.fromRoot setup.source) id P (fun _ => P)
      (groupStep setup codec (nativeServices setup codec checks) pending)
      (groupStep setup codec (factoredServices setup codec checks) pending) := by
  obtain ⟨response, ciphertext, ephemeral, metadata, ⟨dh1, dh2, dh3, dh4, shared⟩⟩ := pending
  by_cases nonzero : Pqxdh.dhNonZero (absBytes dh1, absBytes dh2, absBytes dh3, absBytes dh4)
  · cases shared with
    | challenge =>
        simp only [groupStep, nonzero, ite_true]
        refine Rel.bind (Rel.valueRead _ P _) fun root => ?_
        change Rel _ id P (fun _ => P) (gameStep (ctxGame ((nativeHidden setup codec checks root).hiddenAfter _)))
          (gameStep (ctxGame ((factoredHidden setup codec checks
            (PqxdhServerAuthKeySchedule.fromRoot setup.source root)).hiddenAfter _)))
        rw [← hiddenAfter_factor]
        exact Rel.ctx _ P _ framed
    | known secret =>
        simp only [groupStep, nonzero, ite_true]
        exact Rel.bind (Rel.tableRead _ P _) fun block => Rel.ctx _ P _ framed
  · simp only [groupStep, nonzero, ite_false]
    exact Rel.pure _ fun _ holds => holds

/-- The response tail of the marked session under the native services is the factored response tail on the projected pending token. -/
theorem buildService_factor (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (session : Nat) (game : GameState KemSK) (marks : Marks RootOutput) (holds : Inv (game, marks))
    (token : PqxdhServerRelatedRootConsumer.Returned) (found : game.pending session = some token) :
    ∃ other, (placeholderAt (marks.map Prod.fst) game).pending session = some other ∧
      buildService setup codec checks (factoredServices setup codec checks)
          (marks.map (Prod.map id (PqxdhServerAuthKeySchedule.fromRoot setup.source))) session other =
        buildService setup codec checks (nativeServices setup codec checks) marks session token := by
  rw [buildService_native]
  rcases marks with _ | ⟨index, root⟩
  · exact ⟨token, found, rfl⟩
  · by_cases same : index = session
    · subst same
      refine ⟨⟨PqxdhServerAuthEntryFactor.sentinel, token.pending⟩, ?_, ?_⟩
      · simp only [Option.map_some, placeholderAt, Function.update_self, found, placeholderToken]
      · have rooted : token.root = root := (holds index root rfl).2 token found
        funext payload server
        simp only [Option.map_some, buildService, Prod.map_apply, id_eq, ite_true]
        rw [← rooted]
        exact (hiddenBuild_factor setup codec checks token _ rfl payload server).symm
    · refine ⟨token, ?_, ?_⟩
      · rw [Option.map_some, placeholderAt_pending_ne _ _ _ fun other equal => by
          cases equal
          exact same]
        exact found
      · simp only [Option.map_some, buildService, Prod.map_apply, id_eq, same, ite_false]

/-- The Server build is related to itself under the invariant. -/
theorem buildStep_rel (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (session : Nat) (payload : Option Pqxdh.Bytes) :
    Rel (PqxdhServerAuthKeySchedule.fromRoot setup.source) id Inv (fun _ => Inv)
      (buildStep setup codec checks (nativeServices setup codec checks) session payload)
      (buildStep setup codec checks (factoredServices setup codec checks) session payload) := by
  intro state holds
  obtain ⟨game, marks⟩ := state
  rcases found : game.pending session with _ | token
  · have projected : (placeholderAt (marks.map Prod.fst) game).pending session = none := by
      rcases marks with _ | ⟨index, root⟩
      · exact found
      · by_cases same : index = session
        · subst same
          simp only [Option.map_some, placeholderAt, Function.update_self, found, placeholderToken, Option.map_none]
        · rw [Option.map_some, placeholderAt_pending_ne _ _ _ fun other equal => by
            cases equal
            exact same]
          exact found
    refine ⟨?_, ?_⟩
    · change Prod.map id (proj _) <$> (match game.pending session with
          | none => Pure.pure (none, (game, marks))
          | some token => _ : OracleComp (SkelSpec RootOutput) _) =
        simulateQ (relabelS _) (match (placeholderAt (marks.map Prod.fst) game).pending session with
          | none => Pure.pure (none, proj _ (game, marks))
          | some token => _)
      rw [found, projected, map_pure, simulateQ_pure]
      rfl
    · intro result member
      change result ∈ support (match game.pending session with
        | none => Pure.pure (none, (game, marks))
        | some token => _ : OracleComp (SkelSpec RootOutput) _) at member
      rw [found, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact holds
  · obtain ⟨other, projected, service⟩ := buildService_factor setup codec checks session game marks holds token found
    refine ⟨?_, ?_⟩
    · change Prod.map id (proj _) <$> (match game.pending session with
          | none => Pure.pure (none, (game, marks))
          | some token => _ : OracleComp (SkelSpec RootOutput) _) =
        simulateQ (relabelS _) (match (placeholderAt (marks.map Prod.fst) game).pending session with
          | none => Pure.pure (none, proj _ (game, marks))
          | some token => _)
      rw [found, projected]
      simp only [proj, placeholderAt_server_eq, placeholderAt_ctx_eq]
      rw [service]
      simp only [simulateQ_bind, relabelS_liftComp, simulateQ_pure, map_bind, map_pure]
      refine bind_congr fun result => ?_
      simp only [Prod.map_apply, id_eq]
      rcases marks with _ | ⟨index, root⟩
      · rfl
      · by_cases same : index = session
        · subst same
          simp only [proj, Option.map_some, placeholderAt, Function.update_self, placeholderToken, Option.map_none,
            Function.update_idem]
        · simp only [proj, Option.map_some, placeholderAt, Function.update_of_ne same]
          rw [Function.update_comm same]
    · intro result member
      change result ∈ support (match game.pending session with
        | none => Pure.pure (none, (game, marks))
        | some token => _ : OracleComp (SkelSpec RootOutput) _) at member
      rw [found] at member
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
      obtain ⟨step, -, rfl⟩ := member
      intro index root marked
      obtain ⟨below, held⟩ := holds index root marked
      refine ⟨below, fun token' found' => ?_⟩
      by_cases same : index = session
      · subst same
        simp at found'
      · simp only [Function.update_of_ne same] at found'
        exact held token' found'

/-- The part of the Server's accept tail after the session allocation. -/
noncomputable def acceptBody {V : Type} (setup : Setup baseSpec KemSK) (publicIdentity : PublicIdentity) (index : Nat)
    (control : beaconcrypt_core.pqxdh.ServerState)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes) : NGame KemSK V (Option Nat) :=
  match collected.1 with
  | none => Pure.pure none
  | some input => do
      let returned ← clientStep setup.hmac control
        ⟨PqxdhRootTableInitialization.rootArray publicIdentity.ed25519, setup.serverKeyId⟩ input
      match returned with
      | .ok (some token) => do
          PqxdhRegistrationJointKemPostSkeleton.modifyGame fun current =>
            { current with pending := Function.update current.pending index (some token) }
          Pure.pure (some index)
      | _ => Pure.pure none

theorem acceptTail_eq {V : Type} (setup : Setup baseSpec KemSK) (publicIdentity : PublicIdentity)
    (before : GameState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes) :
    acceptTail (V := V) setup publicIdentity before collected =
      PqxdhRegistrationJointKemPostSkeleton.setGame
          { before with sessions := before.sessions + 1, server := { before.server with consumed := collected.2 } } >>=
        fun _ => acceptBody setup publicIdentity before.sessions before.server.control collected := rfl

/-- The Server's core acceptance and root of a raw accept is related to itself. -/
theorem clientStep_rel (hmac : PqxdhSecretInputKdf.HmacSha512) (f : RootOutput → Output)
    (P : SkelState KemSK RootOutput → Prop) (framed : Framed P)
    (control : beaconcrypt_core.pqxdh.ServerState) (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes PqxdhBeaconPhase2Preparation.Word32) :
    Rel f id P (fun _ => P) (clientStep (V := RootOutput) hmac control binding input)
      (clientStep (V := Output) hmac control binding input) := by
  unfold clientStep
  cases PqxdhServerRelatedRootInput.accept control binding input with
  | ok result =>
      cases result with
      | Err error => exact Rel.pure _ fun _ holds => holds
      | Ok pair =>
          simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
          exact Rel.bind (Rel.tableRead f P _) fun block => Rel.bind (Rel.consume f P framed _) fun _ =>
            Rel.pure _ fun _ holds => holds
  | fail error => exact Rel.pure _ fun _ holds => holds
  | div => exact Rel.pure _ fun _ holds => holds

/-- The part of the accept tail after the session allocation writes a pending token only at the new session, which is not the marked one. -/
theorem acceptBody_rel (setup : Setup baseSpec KemSK) (publicIdentity : PublicIdentity) (index : Nat)
    (control : beaconcrypt_core.pqxdh.ServerState)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes) :
    Rel (PqxdhServerAuthKeySchedule.fromRoot setup.source) id
      (fun state => Good index state ∧ index < state.1.sessions) (fun _ => Inv)
      (acceptBody (V := RootOutput) setup publicIdentity index control collected)
      (acceptBody (V := Output) setup publicIdentity index control collected) := by
  have inv_of : ∀ state : SkelState KemSK RootOutput, Good index state ∧ index < state.1.sessions → Inv state :=
    fun state holds marked root found =>
      ⟨((holds.1 marked root found).1).trans holds.2, (holds.1 marked root found).2⟩
  have framedP : Framed (KemSK := KemSK) fun state => Good index state ∧ index < state.1.sessions :=
    fun state game holds pending sessions => ⟨good_framed index state game holds.1 pending sessions, sessions ▸ holds.2⟩
  rcases collected with ⟨_ | input, consumed⟩
  · exact Rel.pure _ fun state holds => inv_of state holds
  · refine Rel.bind (clientStep_rel setup.hmac _ _ framedP _ _ input) fun returned => ?_
    rcases returned with (_ | token) | error | _
    · exact Rel.pure _ fun state holds => inv_of state holds
    · refine Rel.bind (Rel.modifyGame _ _ (fun _ => Inv) _ (fun state holds => ?_) (fun state holds => ?_))
        fun _ => Rel.pure _ fun _ holds => holds
      · exact placeholderAt_update _ _ _ _ fun marked equal => by
          obtain ⟨⟨marked', root⟩, found, rfl⟩ := Option.map_eq_some_iff.mp equal
          exact Nat.ne_of_lt (holds.1 _ root found).1
      · intro marked root found
        obtain ⟨below, held⟩ := holds.1 marked root found
        refine ⟨below.trans holds.2, fun token' found' => held token' ?_⟩
        simpa only [Function.update_of_ne (Nat.ne_of_lt below)] using found'
    · exact Rel.pure _ fun state holds => inv_of state holds
    · exact Rel.pure _ fun state holds => inv_of state holds

/-- The Server's accept tail from a state, with the factored side's pre-accept game the placeholder image of the native side's. -/
theorem acceptTail_rel (setup : Setup baseSpec KemSK) (publicIdentity : PublicIdentity)
    (game : GameState KemSK) (marks : Marks RootOutput) (holds : Inv (game, marks))
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes) :
    Rel (PqxdhServerAuthKeySchedule.fromRoot setup.source) id (fun state => state = (game, marks)) (fun _ => Inv)
      (acceptTail (V := RootOutput) setup publicIdentity (clean game) collected)
      (acceptTail (V := Output) setup publicIdentity (placeholderAt (marks.map Prod.fst) (clean game)) collected) := by
  rw [acceptTail_eq, acceptTail_eq, placeholderAt_sessions_eq, placeholderAt_server_eq]
  refine Rel.bind (Rel.setGame _ _ (fun _ state => Good game.sessions state ∧ game.sessions < state.1.sessions) _ _
    (fun state same => ?_) (fun state same => ?_)) fun _ => acceptBody_rel setup publicIdentity _ _ collected
  · subst same
    rcases marks with _ | ⟨index, root⟩ <;> rfl
  · subst same
    refine ⟨fun marked root found => ?_, Nat.lt_succ_self _⟩
    exact holds marked root found

/-- Relabelling a forwarded program of the exposed encapsulation interface leaves it unchanged. -/
theorem relabelE_encLift {α : Type} (f : RootOutput → Output) (work : OracleComp (Enc KemSK) α) :
    simulateQ (relabelE f) (simulateQ (encLift (KemSK := KemSK) (V := Output)) work) =
      simulateQ (encLift (KemSK := KemSK) (V := RootOutput)) work := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1

/-- A forwarded request of the exposed encapsulation interface is related to itself. -/
theorem forward_rel (f : RootOutput → Output) (P : SkelState KemSK RootOutput → Prop) (query : (Enc KemSK).Domain) :
    RelC f id P (fun _ => P)
      (fun state => (fun reply => (reply, state)) <$> encLift (KemSK := KemSK) (V := RootOutput) query)
      (fun state => (fun reply => (reply, state)) <$> encLift (KemSK := KemSK) (V := Output) query) := by
  intro state holds
  refine ⟨?_, ?_⟩
  · change Prod.map id (proj f) <$> ((fun reply => (reply, state)) <$> encLift (V := RootOutput) query) =
      simulateQ (relabelE f) ((fun reply => (reply, proj f state)) <$> encLift (V := Output) query)
    rw [simulateQ_map, encLift, encLift, relabel_query_base, Functor.map_map]
    rfl
  · intro result member
    change result ∈ support ((fun reply => (reply, state)) <$> encLift (V := RootOutput) query) at member
    rw [support_map] at member
    obtain ⟨reply, -, rfl⟩ := member
    exact holds

/-- The Server's raw accept with its encapsulation exposed is related to itself under the invariant. -/
theorem acceptStep_rel (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes) :
    RelC (PqxdhServerAuthKeySchedule.fromRoot setup.source) id Inv (fun _ => Inv)
      (acceptStep (V := RootOutput) setup codec checks identityIndex publicIdentity raw)
      (acceptStep (V := Output) setup codec checks identityIndex publicIdentity raw) := by
  intro state holds
  have stepN : (acceptStep (V := RootOutput) setup codec checks identityIndex publicIdentity raw).run state =
      ((fun result => (result, state)) <$> simulateQ (encLift (V := RootOutput))
        ((simulateQ (PqxdhRegistrationJointKemEncapsulation.prefixImpl setup codec checks raw)
          (PqxdhRegistrationJointServerPrefix.clientPrefix identityIndex raw)).run state.1.server.consumed)) >>=
        fun result => (liftT (acceptTail setup publicIdentity (clean state.1) result.1)).run result.2 := rfl
  have stepF : (acceptStep (V := Output) setup codec checks identityIndex publicIdentity raw).run
      (proj (PqxdhServerAuthKeySchedule.fromRoot setup.source) state) =
      ((fun result => (result, proj (PqxdhServerAuthKeySchedule.fromRoot setup.source) state)) <$>
        simulateQ (encLift (V := Output))
        ((simulateQ (PqxdhRegistrationJointKemEncapsulation.prefixImpl setup codec checks raw)
          (PqxdhRegistrationJointServerPrefix.clientPrefix identityIndex raw)).run state.1.server.consumed)) >>=
        fun result => (liftT (acceptTail setup publicIdentity
          (placeholderAt (state.2.map Prod.fst) (clean state.1)) result.1)).run result.2 := by
    obtain ⟨game, _ | ⟨index, root⟩⟩ := state <;> rfl
  obtain ⟨game, marks⟩ := state
  refine ⟨?_, ?_⟩
  · rw [stepN, stepF, map_bind, simulateQ_bind, simulateQ_map, relabelE_encLift, bind_map_left, bind_map_left]
    exact bind_congr fun collected =>
      (liftT_rel (acceptTail_rel setup publicIdentity game marks holds collected) _ rfl).1
  · intro result member
    rw [stepN, bind_map_left, mem_support_bind_iff] at member
    obtain ⟨collected, -, member⟩ := member
    exact (liftT_rel (acceptTail_rel setup publicIdentity game marks holds collected) _ rfl).2 result member

/-- Every step of the skeleton's native layer is related, under the invariant, for the native and the factored services. -/
theorem skelImpl_rel (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (query : (GSpec KemSK Response).Domain) :
    RelC (PqxdhServerAuthKeySchedule.fromRoot setup.source) id Inv (fun _ => Inv)
      (skelImpl setup codec checks identityIndex publicIdentity (nativeServices setup codec checks) query)
      (skelImpl setup codec checks identityIndex publicIdentity (factoredServices setup codec checks) query) := by
  rcases query with ((pool | tail) | shared) | pending
  · exact forward_rel _ Inv (.inl pool)
  · exact liftT_rel (tailStep_rel setup codec _ Inv inv_framed tail)
  · cases shared with
    | accept raw => exact acceptStep_rel setup codec checks identityIndex publicIdentity raw
    | build session payload => exact liftT_rel (buildStep_rel setup codec checks session payload)
    | hmac key message => exact liftT_rel (hmacStep_rel setup _ Inv key message)
    | hash bytes => exact liftT_rel (hash_rel _ Inv inv_framed bytes)
    | reveal keyId => exact liftT_rel (reveal_rel _ Inv inv_framed keyId)
  · exact liftT_rel (groupStep_rel setup codec checks Inv inv_framed pending)

/-- Every program of the grouped interface: the native layer with the native services, mapped by the projection, is the relabelled native layer with the factored services from the projected state, under the invariant. -/
theorem skelImpl_run {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (work : OracleComp (GSpec KemSK Response) α)
    (state : SkelState KemSK RootOutput) (holds : Inv state) :
    Prod.map id (proj (PqxdhServerAuthKeySchedule.fromRoot setup.source)) <$>
        (simulateQ (skelImpl setup codec checks identityIndex publicIdentity (nativeServices setup codec checks)) work).run
          state =
      simulateQ (relabelE (PqxdhServerAuthKeySchedule.fromRoot setup.source))
        ((simulateQ (skelImpl setup codec checks identityIndex publicIdentity (factoredServices setup codec checks)) work).run
          (proj (PqxdhServerAuthKeySchedule.fromRoot setup.source) state)) ∧
      ∀ result ∈ support
        ((simulateQ (skelImpl setup codec checks identityIndex publicIdentity (nativeServices setup codec checks)) work).run
          state), Inv result.2 := by
  rw [simulateQ_mapRun]
  exact map_run_inv _ _ Inv _ (fun query state holds => (skelImpl_rel setup codec checks identityIndex publicIdentity query
    state holds).2) (fun query state holds => (skelImpl_rel setup codec checks identityIndex publicIdentity query
    state holds).1) work state holds

end Handlers

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.liftT_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.liftT_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.Rel.setGame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.Rel.setGame

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.Rel.modifyGame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.Rel.modifyGame

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.inv_framed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.inv_framed

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.good_framed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.good_framed

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.framed_and' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.framed_and

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.Rel.consume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.Rel.consume

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.tailStep_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.tailStep_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.hmacStep_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.hmacStep_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.hash_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.hash_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.reveal_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.reveal_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.groupStep_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.groupStep_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.buildService_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.buildService_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.buildStep_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.buildStep_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.acceptTail_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.acceptTail_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.clientStep_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.clientStep_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.acceptBody_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.acceptBody_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.acceptTail_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.acceptTail_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.relabelE_encLift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.relabelE_encLift

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.forward_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.forward_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.acceptStep_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.acceptStep_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.skelImpl_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.skelImpl_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.skelImpl_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.skelImpl_run
