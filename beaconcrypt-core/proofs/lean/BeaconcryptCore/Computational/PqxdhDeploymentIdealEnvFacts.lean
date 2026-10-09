-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish

/-!
# Facts about the ideal environment's commands (CE-11b, unit U3)

What CE-11b's ideal environment (design-v2 section 6) needs about each command for its admissibility predicate `PqxdhDeploymentIdealEnv.IdealInv`, beyond the per-command laws of `PqxdhDeploymentIdealEnvStep`, `PqxdhDeploymentIdealEnvBuild` and `PqxdhDeploymentIdealEnvFinish`.

- World runs without a hidden install keep the World's used markers and seed table (`isHidden`, `hidden_admin`, `hiddenFree_of_noAdmin`, `effects_keep`, `run_keep`); every real environment step, the pool create and the selected accept issue none (`coins_free`, `issue_free`, `ownerEffect_free`, `ownerChange_free`, `serverEffect_free`, `realStep_free`, `createPool_free`, `acceptSelected_free`).
- Moves of the registration state: owner `k` is terminal (`terminalAt`, kept by stripping, by setting an owner that stays unchanged if terminal and by appending: `terminal_stripOwner`, `terminalAt_strip`, `terminalAt_set`, `terminalAt_append`, with `finished_keep` and `bundled_keep`); the Server's session counter does not decrease and no session below it gains a pending token (`SessionMove`, `refl`, `trans`, `of_eq`); `RealMove` collects both with an unchanged backend. Every real environment step (`realStep_move`, through `hmacOracle_keeps`, `nativeHmac_move` and `acceptLogged_move`, the latter from `PqxdhServerAuthPendingBudget.accept_pending`) and the pool create (`createPool_move`) make a `RealMove`; `world_support` carries facts about an environment program to its World run.
- The selected accept's allocator and session facts: a slot read (`isRead`), allocator moves (`AllocMove`, `refl`, `trans`), one allocator step (`slotStep_move`), lifted coins (`slot_liftS`, `slot_mapLiftS`), invariants kept at the requests a program issues (`run_keepsGood`); the marker tail issues at most one root request (`isRoot`, `isClientRoot`, `client_root`, `tail_root`) and installs before anything else (`isInstall`, `GoodTail`); its root and auxiliary requests keep the Server's sessions (`romRoot_keeps`, `auxiliary_keeps`); the marker tail with its slot reads answered by the allocator as one handler (`tailSlots`, `tailSlots_run`, `TailInv`, `tailSlots_step`); the native accept tail without input (`serverTail_none`). Together (`acceptInactive_facts`, `acceptActive_facts`, `acceptExposed_facts`, `acceptSelected_move`): the selected accept moves the Server's sessions, raises the allocator's counter by at most one, and its mark is at the old session counter, below the new one, at coordinates holding a slot unless the allocator is full.
- The hidden commands' outcomes with the seed table exact outside the slot (`lazy_other`, `buildHidden_exact`, `hiddenFinish_exact`, copies of `PqxdhDeploymentIdealEnvBuild.buildHidden_outcome` and `PqxdhDeploymentIdealEnvFinish.hiddenFinish_outcome` with that conjunct added), and the moves of the marked build (`builtEnv_move`, `buildHidden_move`) and of owner k's challenge finish (`finishChallenge_move`).

These are support facts about programs; no security claim is made here.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts
open PqxdhServerAuthExperiment (Setup Codec Checks GameState)
open PqxdhServerAuthNative (NativeState NativeGame)
open PqxdhDeploymentEnvironment (EnvState EnvStep strip coins)
open PqxdhDeploymentEnvironmentJoin (merge uncount Good)
open PqxdhDeploymentIdealSlots (Coord)
open PqxdhDeploymentIdealSteps (IdealCore SplitBk initSentAt establishedAt)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhRecordLiftInterface (EnvEffects EffectKind effectKind)

variable {KemSK : Type}

/-! ### World runs without a hidden install -/

section HiddenFree

/-- A hidden install request. -/
def isHidden : (EnvEffects 2).Domain → Bool
  | .inr (.installServer _ _ (.hidden _)) => true
  | .inr (.installBeacon _ _ (.hidden _)) => true
  | _ => false

/-- A hidden install is an administrative effect. -/
theorem hidden_admin (query : (EnvEffects 2).Domain) (hidden : isHidden query = true) :
    effectKind query = .administrative := by
  rcases query with coin | capability
  · simp [isHidden] at hidden
  · cases capability <;> simp_all [isHidden, effectKind]

/-- A program without administrative effect has no hidden install. -/
theorem hiddenFree_of_noAdmin {α : Type} (work : OracleComp (EnvEffects 2) α)
    (noAdmin : work.IsQueryBoundP (fun effect => effectKind effect = .administrative) 0) :
    work.IsQueryBoundP (fun effect => isHidden effect = true) 0 :=
  IsQueryBoundP.of_imp (fun query hidden => hidden_admin query hidden) noAdmin

/-- One World effect that is not a hidden install keeps the used markers and the seed table. -/
theorem effects_keep (query : (EnvEffects 2).Domain) (visible : isHidden query = false)
    (w : PqxdhRecordLiftWorld.State 2) :
    ∀ result ∈ support ((PqxdhRecordLiftWorld.effects query).run w), result.2.used = w.used ∧ result.2.seeds = w.seeds := by
  intro result supported
  rcases query with coin | capability
  · simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.sampled, StateT.run, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨_, _, rfl⟩ := supported
    exact ⟨rfl, rfl⟩
  · cases capability with
    | peerPresent keyId =>
        simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability, StateT.run, support_pure,
          Set.mem_singleton_iff] at supported
        subst supported
        exact ⟨rfl, rfl⟩
    | ownerPresent owner =>
        simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability, StateT.run, support_pure,
          Set.mem_singleton_iff] at supported
        subst supported
        exact ⟨rfl, rfl⟩
    | appendOwner keyId identity phase =>
        simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability, StateT.run, support_pure,
          Set.mem_singleton_iff] at supported
        subst supported
        exact ⟨rfl, rfl⟩
    | advanceOwner owner phase =>
        simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability, StateT.run] at supported
        split at supported
        · split at supported <;>
            (simp only [support_pure, Set.mem_singleton_iff] at supported; subst supported; exact ⟨rfl, rfl⟩)
        · simp only [support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact ⟨rfl, rfl⟩
    | installServer keyId identity ref =>
        cases ref with
        | hidden slot => simp [isHidden] at visible
        | known kernel =>
            change result ∈ support ((PqxdhRecordLiftWorld.installServer keyId identity (.known kernel)).run
              (PqxdhRecordLiftWorld.chargeEffect _ w)) at supported
            unfold PqxdhRecordLiftWorld.installServer at supported
            simp only [StateT.run] at supported
            split at supported
            · simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact ⟨rfl, rfl⟩
            · split_ifs at supported
              · simp only [PqxdhRecordLiftWorld.resolve, PqxdhRecordLiftWorld.markUsed] at supported
                subst supported
                exact ⟨rfl, rfl⟩
              · simp only [support_pure, Set.mem_singleton_iff] at supported
                subst supported
                exact ⟨rfl, rfl⟩
    | installBeacon owner shell ref =>
        cases ref with
        | hidden slot => simp [isHidden] at visible
        | known kernel =>
            change result ∈ support ((PqxdhRecordLiftWorld.installBeacon owner shell (.known kernel)).run
              (PqxdhRecordLiftWorld.chargeEffect _ w)) at supported
            unfold PqxdhRecordLiftWorld.installBeacon at supported
            simp only [StateT.run] at supported
            split_ifs at supported
            · simp only [PqxdhRecordLiftWorld.resolve, PqxdhRecordLiftWorld.markUsed] at supported
              subst supported
              exact ⟨rfl, rfl⟩
            · simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact ⟨rfl, rfl⟩
    | hash bytes =>
        change result ∈ support ((PqxdhRecordLiftWorld.capability (.hash bytes)).run
          (PqxdhRecordLiftWorld.chargeEffect _ w)) at supported
        simp only [PqxdhRecordLiftWorld.capability, PqxdhRecordLiftWorld.sampled, StateT.run, bind_assoc, pure_bind,
          mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
        obtain ⟨_, _, rfl⟩ := supported
        exact ⟨rfl, rfl⟩

/-- A program without hidden install, run by the World, keeps the used markers and the seed table. -/
theorem run_keep {α : Type} (work : OracleComp (EnvEffects 2) α)
    (free : work.IsQueryBoundP (fun effect => isHidden effect = true) 0) (w : PqxdhRecordLiftWorld.State 2) :
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects work).run w),
      result.2.used = w.used ∧ result.2.seeds = w.seeds := by
  induction work using OracleComp.inductionOn generalizing w with
  | pure value =>
      intro result supported
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨rfl, rfl⟩
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at free
      obtain ⟨visible, rest⟩ := free
      have visible' : isHidden query = false := by
        cases hidden : isHidden query
        · rfl
        · simp only [hidden, not_true_eq_false, false_or, lt_self_iff_false] at visible
      simp only [visible', Bool.false_eq_true, ite_false] at rest
      intro result supported
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, first, final⟩ := supported
      obtain ⟨used₁, seeds₁⟩ := effects_keep query visible' w middle first
      obtain ⟨used₂, seeds₂⟩ := ih middle.1 (rest middle.1) middle.2 result final
      exact ⟨used₂.trans used₁, seeds₂.trans seeds₁⟩

end HiddenFree

/-! ### The ideal environment's programs without hidden install -/

section Free
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : ℕ}

/-- Coins have no hidden install. -/
theorem coins_free {α : Type} (work : ProbComp α) :
    (coins (n := 2) work).IsQueryBoundP (fun effect => isHidden effect = true) 0 :=
  hiddenFree_of_noAdmin _ (PqxdhDeploymentEnvironmentReal.coins_noAdmin work)

/-- A capability request that is not a hidden install has none. -/
theorem issue_free (capability : PqxdhRecordLiftInterface.Capability 2) (visible : isHidden (.inr capability) = false) :
    (PqxdhDeploymentEnvironment.issue capability).IsQueryBoundP (fun effect => isHidden effect = true) 0 := by
  unfold PqxdhDeploymentEnvironment.issue PqxdhDeploymentEnvironment.request
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl fun hidden => ?_, fun _ => trivial⟩
  rw [visible] at hidden
  exact Bool.false_ne_true hidden

/-- Publishing one owner's change installs no hidden kernel. -/
theorem ownerEffect_free (index : ℕ) (before after : PqxdhRegistrationSchedule.Owner KemSK) :
    (PqxdhDeploymentEnvironment.ownerEffect (n := 2) index before after).IsQueryBoundP
      (fun effect => isHidden effect = true) 0 := by
  unfold PqxdhDeploymentEnvironment.ownerEffect
  split
  · trivial
  · exact issue_free _ rfl
  · split
    · split
      · trivial
      · exact issue_free _ rfl
    · trivial

/-- Publishing the change of one owner between two owner lists installs no hidden kernel. -/
theorem ownerChange_free (index : ℕ) (before after : List (PqxdhRegistrationSchedule.Owner KemSK)) :
    (PqxdhDeploymentEnvironment.ownerChange (n := 2) index before after).IsQueryBoundP
      (fun effect => isHidden effect = true) 0 := by
  unfold PqxdhDeploymentEnvironment.ownerChange
  split
  · exact ownerEffect_free _ _ _
  · trivial

/-- Publishing a Server build installs no hidden kernel. -/
theorem serverEffect_free (settled : Option PqxdhServerRegistrationPublication.Response ×
    PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) :
    (PqxdhDeploymentEnvironment.serverEffect (n := 2) settled).IsQueryBoundP (fun effect => isHidden effect = true) 0 := by
  unfold PqxdhDeploymentEnvironment.serverEffect
  split
  · trivial
  · split
    · trivial
    · exact issue_free _ rfl

/-- Every real environment step installs no hidden kernel. -/
theorem realStep_free (query : PqxdhRecordLiftInterface.EnvQuery) (e : EnvState KemSK SplitBk) :
    ((PqxdhDeploymentEnvironment.realStep (n := 2) setup codec checks query).run e).IsQueryBoundP
      (fun effect => isHidden effect = true) 0 := by
  rcases query with ⟨command, allowed⟩
  cases command with
  | create pin keyId =>
      change ((PqxdhDeploymentEnvironment.createStep setup pin keyId).run _).IsQueryBoundP _ 0
      unfold PqxdhDeploymentEnvironment.createStep
      split
      · trivial
      · simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
        rw [show (0 : ℕ) = 0 + 0 from rfl]
        refine isQueryBoundP_bind ?_ fun _ _ => ?_
        · change (_ <$> coins _).IsQueryBoundP _ 0
          rw [isQueryBoundP_map_iff]
          exact coins_free _
        · rw [show (0 : ℕ) = 0 + 0 from rfl]
          exact isQueryBoundP_bind (issue_free _ rfl) fun _ _ => trivial
  | bundle owner =>
      change ((PqxdhDeploymentEnvironment.bundleStep setup codec owner).run _).IsQueryBoundP _ 0
      unfold PqxdhDeploymentEnvironment.bundleStep
      rw [show (0 : ℕ) = 0 + 0 from rfl]
      refine isQueryBoundP_bind (coins_free _) fun _ _ => ?_
      rw [show (0 : ℕ) = 0 + 0 from rfl]
      exact isQueryBoundP_bind (ownerChange_free _ _ _) fun _ _ => trivial
  | accept raw =>
      change ((PqxdhDeploymentEnvironment.acceptStep setup codec checks raw).run _).IsQueryBoundP _ 0
      unfold PqxdhDeploymentEnvironment.acceptStep
      change (_ <$> coins _).IsQueryBoundP _ 0
      rw [isQueryBoundP_map_iff]
      exact coins_free _
  | build session payload =>
      change ((PqxdhDeploymentEnvironment.buildStep setup codec checks session payload).run _).IsQueryBoundP _ 0
      unfold PqxdhDeploymentEnvironment.buildStep
      simp only [StateT.run]
      split
      · trivial
      · rename_i token _
        rw [show (0 : ℕ) = 0 + 0 from rfl]
        refine isQueryBoundP_bind (hiddenFree_of_noAdmin _ ?_) fun _ _ => ?_
        · have bound := PqxdhDeploymentEnvironment.build_fwd_bound (n := 2) setup codec checks token.pending token.root
            payload e.native.shared.2.server [] .administrative
          simp only [reduceCtorEq, ite_false] at bound
          exact bound
        · rw [show (0 : ℕ) = 0 + 0 from rfl]
          exact isQueryBoundP_bind (serverEffect_free _) fun _ _ => trivial
  | finish owner raw =>
      change ((PqxdhDeploymentEnvironment.finishStep setup codec owner raw).run _).IsQueryBoundP _ 0
      unfold PqxdhDeploymentEnvironment.finishStep
      simp only [StateT.run]
      split
      · trivial
      · rw [show (0 : ℕ) = 0 + 0 from rfl]
        refine isQueryBoundP_bind (hiddenFree_of_noAdmin _ (PqxdhDeploymentEnvironmentReal.finishFwd_noAdmin setup codec
          _ _)) fun _ _ => ?_
        rw [show (0 : ℕ) = 0 + 0 from rfl]
        exact isQueryBoundP_bind (ownerEffect_free _ _ _) fun _ _ => trivial
  | hmac key message =>
      change ((PqxdhDeploymentEnvironment.hmacStep setup key message).run _).IsQueryBoundP _ 0
      unfold PqxdhDeploymentEnvironment.hmacStep PqxdhDeploymentEnvironment.onEnv
      change (_ <$> coins _).IsQueryBoundP _ 0
      rw [isQueryBoundP_map_iff]
      exact coins_free _
  | hash _ => exact absurd allowed id
  | serverSend _ _ => exact absurd allowed id
  | serverRaw _ => exact absurd allowed id
  | beaconSend _ _ => exact absurd allowed id
  | beaconRaw _ _ => exact absurd allowed id

/-- The pool create in capability form installs no hidden kernel. -/
theorem createPool_free (pool : List (PqxdhLiveKemReservation.Pair KemSK)) (pin : Pqxdh.Bytes) (keyId : Std.U64)
    (e : EnvState KemSK SplitBk) :
    ((PqxdhDeploymentIdealEnvReal.createPoolStep (n := 2) setup pool pin keyId).run e).IsQueryBoundP
      (fun effect => isHidden effect = true) 0 := by
  unfold PqxdhDeploymentIdealEnvReal.createPoolStep
  split
  · trivial
  · simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
    rw [show (0 : ℕ) = 0 + 0 from rfl]
    refine isQueryBoundP_bind ?_ fun _ _ => ?_
    · change (_ <$> coins _).IsQueryBoundP _ 0
      rw [isQueryBoundP_map_iff]
      exact coins_free _
    · rw [show (0 : ℕ) = 0 + 0 from rfl]
      exact isQueryBoundP_bind (issue_free _ rfl) fun _ _ => trivial

/-- The selected accept in capability form installs no hidden kernel. -/
theorem acceptSelected_free (p : Params KemSK count) (raw : Pqxdh.Bytes) (e : EnvState KemSK SplitBk) :
    ((PqxdhDeploymentIdealEnvStep.acceptSelectedEnv setup codec checks p raw).run e).IsQueryBoundP
      (fun effect => isHidden effect = true) 0 := by
  change (_ <$> coins _).IsQueryBoundP _ 0
  rw [isQueryBoundP_map_iff]
  exact coins_free _

end Free

/-! ### Moves of the registration state by the commands without a hidden effect -/

section Moves

/-- Owner `index` is present and terminal (aborted or established). -/
def terminalAt (owners : List (PqxdhRegistrationSchedule.Owner KemSK)) (index : ℕ) : Prop :=
  ∃ owner, owners[index]? = some owner ∧ PqxdhRegistrationSchedule.Terminal owner

/-- Stripping an owner keeps whether it is terminal. -/
theorem terminal_stripOwner (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    PqxdhRegistrationSchedule.Terminal (PqxdhDeploymentEnvironment.stripOwner owner) ↔
      PqxdhRegistrationSchedule.Terminal owner := by
  cases phase : owner.beacon.phase <;>
    simp [PqxdhDeploymentEnvironment.stripOwner, PqxdhRegistrationSchedule.Terminal, phase]

/-- Stripping keeps whether an owner is terminal. -/
theorem terminalAt_strip (state : PqxdhRegistrationSchedule.State KemSK) (index : ℕ) :
    terminalAt (strip state).owners index ↔ terminalAt state.owners index := by
  constructor
  · rintro ⟨owner, found, terminal⟩
    change (state.owners.map PqxdhDeploymentEnvironment.stripOwner)[index]? = some owner at found
    rw [List.getElem?_map] at found
    obtain ⟨original, present, rfl⟩ := Option.map_eq_some_iff.mp found
    exact ⟨original, present, (terminal_stripOwner original).1 terminal⟩
  · rintro ⟨owner, found, terminal⟩
    refine ⟨PqxdhDeploymentEnvironment.stripOwner owner, ?_, (terminal_stripOwner owner).2 terminal⟩
    change (state.owners.map PqxdhDeploymentEnvironment.stripOwner)[index]? = _
    rw [List.getElem?_map, found]
    rfl

/-- Setting one owner keeps owner `index` terminal when the set owner is unchanged if it was terminal. -/
theorem terminalAt_set (owners : List (PqxdhRegistrationSchedule.Owner KemSK)) (position index : ℕ)
    (before after : PqxdhRegistrationSchedule.Owner KemSK) (found : owners[position]? = some before)
    (keep : PqxdhRegistrationSchedule.Terminal before → after = before) (terminal : terminalAt owners index) :
    terminalAt (owners.set position after) index := by
  obtain ⟨owner, present, isTerminal⟩ := terminal
  by_cases same : position = index
  · subst same
    rw [found] at present
    cases present
    rw [keep isTerminal]
    exact ⟨before, List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1, isTerminal⟩
  · exact ⟨owner, by rw [List.getElem?_set_ne same]; exact present, isTerminal⟩

/-- Appending owners keeps owner `index` terminal. -/
theorem terminalAt_append (owners extra : List (PqxdhRegistrationSchedule.Owner KemSK)) (index : ℕ)
    (terminal : terminalAt owners index) : terminalAt (owners ++ extra) index := by
  obtain ⟨owner, present, isTerminal⟩ := terminal
  exact ⟨owner, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp present).1]; exact present, isTerminal⟩

/-- A finish leaves a terminal owner unchanged. -/
theorem finished_keep (before after : PqxdhRegistrationSchedule.Owner KemSK)
    (shape : PqxdhDeploymentEnvironmentReal.Finished before after) (terminal : PqxdhRegistrationSchedule.Terminal before) :
    after = before := by
  rcases shape with same | ⟨initSent, _⟩
  · exact same
  · exfalso
    unfold PqxdhRegistrationSchedule.Terminal at terminal
    cases phase : before.beacon.phase <;> simp_all [PqxdhDeploymentEnvironment.inactiveTag]

/-- A bundle leaves a terminal owner unchanged. -/
theorem bundled_keep (before after : PqxdhRegistrationSchedule.Owner KemSK)
    (shape : PqxdhDeploymentEnvironmentReal.Bundled before after) (terminal : PqxdhRegistrationSchedule.Terminal before) :
    after = before := by
  rcases shape with same | ⟨_, fresh⟩
  · exact same
  · exfalso
    unfold PqxdhRegistrationSchedule.Terminal at terminal
    cases phase : before.beacon.phase <;> simp_all [PqxdhDeploymentEnvironment.inactiveTag]

/-- The Server's session counter does not decrease, and no session below the old counter gains a pending token. -/
def SessionMove (before after : GameState KemSK) : Prop :=
  before.sessions ≤ after.sessions ∧
    ∀ session, session < before.sessions → (after.pending session).isSome = true → (before.pending session).isSome = true

/-- A state moves to itself. -/
theorem SessionMove.refl (state : GameState KemSK) : SessionMove state state :=
  ⟨le_refl _, fun _ _ found => found⟩

/-- Session moves compose. -/
theorem SessionMove.trans {first second third : GameState KemSK} (left : SessionMove first second)
    (right : SessionMove second third) : SessionMove first third :=
  ⟨left.1.trans right.1, fun session below found =>
    left.2 session below (right.2 session (lt_of_lt_of_le below left.1) found)⟩

/-- Equal session counters and pending tokens are a session move. -/
theorem SessionMove.of_eq {before after : GameState KemSK} (sessions : after.sessions = before.sessions)
    (pending : after.pending = before.pending) : SessionMove before after :=
  ⟨sessions.ge, fun _ _ found => by rw [← pending]; exact found⟩

/-- The move of the environment state by a command without a hidden effect, as the ideal admissibility predicate needs it: the backend is unchanged, the Server's sessions move (`SessionMove`), and owner `k` stays terminal. -/
structure RealMove {Bk : Type} (k : ℕ) (e e' : EnvState KemSK Bk) : Prop where
  backend : e'.backend = e.backend
  sessions : SessionMove e.native.shared.2 e'.native.shared.2
  terminal : terminalAt e.native.owners k → terminalAt e'.native.owners k

/-- Every outcome of a World run of an environment program is an outcome of the program. -/
theorem world_support {α : Type} (work : OracleComp (EnvEffects 2) α) (w : PqxdhRecordLiftWorld.State 2)
    (property : α → Prop) (holds : ∀ value ∈ support work, property value) :
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects work).run w), property result.1 :=
  fun result member => holds result.1 (PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ member)

end Moves

section RealMoves
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- The public HMAC oracle keeps the session counter and the pending tokens. -/
theorem hmacOracle_keeps (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) (state : GameState KemSK)
    (result : PqxdhSecretInputKdf.HmacBlock × GameState KemSK)
    (supported : result ∈ support ((PqxdhServerAuthExperiment.hmacOracle key message).run state)) :
    result.2.sessions = state.sessions ∧ result.2.pending = state.pending := by
  simp only [PqxdhServerAuthExperiment.hmacOracle] at supported
  split_ifs at supported
  · obtain ⟨middle, first, rest⟩ := PqxdhServerAuthExperiment.run_bind_support _ _ _ _ supported
    rw [PqxdhServerAuthExperiment.record_run, support_pure, Set.mem_singleton_iff] at first
    subst first
    rw [PqxdhServerAuthExperiment.forward_support _ _ _ rest]
    exact ⟨rfl, rfl⟩
  · rw [PqxdhServerAuthExperiment.forward_support _ _ _ supported]
    exact ⟨rfl, rfl⟩

/-- The native public HMAC moves the Server's sessions. -/
theorem nativeHmac_move (seed : PqxdhJointIdentity.IdentitySeed) (key : PqxdhSecretInputKdf.HmacBlock)
    (message : Pqxdh.Bytes) (shared : NativeState KemSK) :
    ∀ result ∈ support ((PqxdhServerAuthNative.nativeHmac setup seed PqxdhRegistrationSchedule.observationScalar key
      message).run shared), SessionMove shared.2 result.2.2 := by
  intro result supported
  rw [← PqxdhServerAuthNative.hmac_native] at supported
  have inner := PqxdhServerAuthNative.evaluate_support setup seed _ _ shared result supported
  obtain ⟨sessions, pending⟩ := hmacOracle_keeps key message shared.2 _ inner
  exact SessionMove.of_eq sessions pending

/-- The native logged raw accept moves the Server's sessions: the counter grows by one and only the old counter can gain a pending token. -/
theorem acceptLogged_move (seed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes) (shared : NativeState KemSK) :
    ∀ result ∈ support ((PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed raw).run shared),
      SessionMove shared.2 result.2.2 := by
  intro result supported
  have native : ((result.1.1, result.2) : Option ℕ × NativeState KemSK) ∈ support
      ((PqxdhServerAuthNative.nativeAccept setup codec checks seed PqxdhRegistrationSchedule.observationScalar raw).run
        shared) := by
    rw [← PqxdhDeploymentLaterServerNative.acceptLogged_fst, support_map]
    exact ⟨result, supported, rfl⟩
  rw [← PqxdhServerAuthNative.accept_native] at native
  have inner := PqxdhServerAuthNative.evaluate_support setup seed _ _ shared _ native
  obtain ⟨sessions, same | ⟨token, installed⟩⟩ :=
    PqxdhServerAuthPendingBudget.accept_pending setup codec checks _ raw shared.2 _ inner
  · dsimp only at sessions same
    refine ⟨by omega, fun session _ found => ?_⟩
    rwa [same] at found
  · dsimp only at sessions installed
    refine ⟨by omega, fun session below found => ?_⟩
    rwa [installed, Function.update_of_ne (Nat.ne_of_lt below)] at found

/-- Every real environment step moves the environment state without a hidden effect (`RealMove`). -/
theorem realStep_move {Bk : Type} (k : ℕ) (query : PqxdhRecordLiftInterface.EnvQuery) (e : EnvState KemSK Bk) :
    ∀ v ∈ support ((PqxdhDeploymentEnvironment.realStep (n := 2) setup codec checks query).run e), RealMove k e v.2 := by
  rcases query with ⟨command, allowed⟩
  cases command with
  | create pin keyId =>
      intro v member
      change v ∈ support ((PqxdhDeploymentEnvironment.createStep (n := 2) setup pin keyId).run
        (PqxdhDeploymentEnvironment.snapped _ e)) at member
      unfold PqxdhDeploymentEnvironment.createStep at member
      split at member
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
        subst member
        exact ⟨rfl, SessionMove.refl _, id⟩
      · rename_i word _
        rw [StateT.run_bind, mem_support_bind_iff] at member
        obtain ⟨r, rMember, member⟩ := member
        simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind, mem_support_bind_iff,
          support_pure, Set.mem_singleton_iff] at member
        obtain ⟨_, _, rfl⟩ := member
        simp only [PqxdhDeploymentEnvironment.onEnv, StateT.run, support_map, Set.mem_image] at rMember
        obtain ⟨x, xMember, rfl⟩ := rMember
        have inner : x ∈ support ((PqxdhRegistrationSchedule.create setup word keyId).run e.native) :=
          PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ xMember
        rw [PqxdhDeploymentEnvironmentReal.create_run setup word keyId e.native] at inner
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at inner
        obtain ⟨_, _, _, _, _, _, rfl⟩ := inner
        exact ⟨rfl, SessionMove.refl _, fun terminal => by rw [terminalAt_strip]; exact terminalAt_append _ _ k terminal⟩
  | bundle owner =>
      intro v member
      change v ∈ support ((PqxdhDeploymentEnvironment.bundleStep (n := 2) setup codec owner).run
        (PqxdhDeploymentEnvironment.snapped _ e)) at member
      unfold PqxdhDeploymentEnvironment.bundleStep at member
      simp only [StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
      obtain ⟨r, rMember, _, _, rfl⟩ := member
      have inner : r ∈ support ((PqxdhRegistrationSchedule.bundle setup codec owner).run e.native) :=
        PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ rMember
      cases owned : e.native.owners[owner]? with
      | none =>
          rw [PqxdhDeploymentEnvironmentReal.bundle_run_missing setup codec owner _ owned, support_pure,
            Set.mem_singleton_iff] at inner
          subst inner
          exact ⟨rfl, SessionMove.refl _, fun terminal => by rw [terminalAt_strip]; exact terminal⟩
      | some current =>
          rw [PqxdhDeploymentEnvironmentReal.bundle_run_found setup codec owner _ current owned, support_map] at inner
          obtain ⟨b, bMember, rfl⟩ := inner
          have shape := PqxdhDeploymentEnvironmentReal.bundle_shape _ current b
            (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ bMember)
          exact ⟨rfl, SessionMove.refl _, fun terminal => by
            rw [terminalAt_strip]
            exact terminalAt_set _ owner k current b.2 owned (bundled_keep current b.2 shape) terminal⟩
  | accept raw =>
      intro v member
      change v ∈ support ((PqxdhDeploymentEnvironment.acceptStep (n := 2) setup codec checks raw).run
        (PqxdhDeploymentEnvironment.snapped _ e)) at member
      unfold PqxdhDeploymentEnvironment.acceptStep at member
      simp only [StateT.run, support_map, Set.mem_image] at member
      obtain ⟨r, rMember, rfl⟩ := member
      have inner : r ∈ support ((PqxdhRegistrationSchedule.onShared (PqxdhDeploymentLaterServerNative.acceptLogged setup
          codec checks e.created.seed raw)).run e.native) :=
        PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ rMember
      rw [PqxdhDeploymentEnvironmentReal.onShared_run, support_map] at inner
      obtain ⟨x, xMember, rfl⟩ := inner
      exact ⟨rfl, acceptLogged_move setup codec checks e.created.seed raw e.native.shared x xMember,
        fun terminal => by rw [terminalAt_strip]; exact terminal⟩
  | build session payload =>
      intro v member
      change v ∈ support ((PqxdhDeploymentEnvironment.buildStep (n := 2) setup codec checks session payload).run
        (PqxdhDeploymentEnvironment.snapped _ e)) at member
      unfold PqxdhDeploymentEnvironment.buildStep at member
      simp only [StateT.run] at member
      split at member
      · simp only [support_pure, Set.mem_singleton_iff] at member
        subst member
        exact ⟨rfl, SessionMove.refl _, id⟩
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
        obtain ⟨_, _, _, _, rfl⟩ := member
        refine ⟨rfl, ⟨le_refl _, fun s _ found => ?_⟩, fun terminal => by rw [terminalAt_strip]; exact terminal⟩
        by_cases same : s = session
        · subst same
          simp [strip, PqxdhDeploymentEnvironment.snapped] at found
        · simpa [strip, PqxdhDeploymentEnvironment.snapped, Function.update_of_ne same] using found
  | finish owner raw =>
      intro v member
      change v ∈ support ((PqxdhDeploymentEnvironment.finishStep (n := 2) setup codec owner raw).run
        (PqxdhDeploymentEnvironment.snapped _ e)) at member
      unfold PqxdhDeploymentEnvironment.finishStep at member
      simp only [StateT.run] at member
      split at member
      · simp only [support_pure, Set.mem_singleton_iff] at member
        subst member
        exact ⟨rfl, SessionMove.refl _, id⟩
      · rename_i before owned
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
        obtain ⟨result, resultMember, _, _, rfl⟩ := member
        have game := PqxdhDeploymentEnvironmentReal.finishFwd_game setup codec _ _ result resultMember
        have shape := PqxdhDeploymentEnvironmentReal.finish_shape codec.frameRead raw before result.1
          (PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ resultMember)
        refine ⟨rfl, SessionMove.of_eq (congrArg (fun g => g.sessions) game) (congrArg (fun g => g.pending) game),
          fun terminal => ?_⟩
        rw [terminalAt_strip]
        exact terminalAt_set _ owner k before result.1.2 owned (finished_keep before result.1.2 shape) terminal
  | hmac key message =>
      intro v member
      change v ∈ support ((PqxdhDeploymentEnvironment.hmacStep (n := 2) setup key message).run
        (PqxdhDeploymentEnvironment.snapped _ e)) at member
      unfold PqxdhDeploymentEnvironment.hmacStep PqxdhDeploymentEnvironment.onEnv at member
      simp only [StateT.run, support_map, Set.mem_image] at member
      obtain ⟨r, rMember, rfl⟩ := member
      have inner : r ∈ support ((PqxdhRegistrationSchedule.onShared (PqxdhServerAuthNative.nativeHmac setup e.created.seed
          PqxdhRegistrationSchedule.observationScalar key message)).run e.native) :=
        PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ rMember
      rw [PqxdhDeploymentEnvironmentReal.onShared_run, support_map] at inner
      obtain ⟨x, xMember, rfl⟩ := inner
      exact ⟨rfl, nativeHmac_move setup e.created.seed key message e.native.shared x xMember,
        fun terminal => by rw [terminalAt_strip]; exact terminal⟩
  | hash _ => exact absurd allowed id
  | serverSend _ _ => exact absurd allowed id
  | serverRaw _ => exact absurd allowed id
  | beaconSend _ _ => exact absurd allowed id
  | beaconRaw _ _ => exact absurd allowed id

/-- The pool create in capability form moves the environment state without a hidden effect. -/
theorem createPool_move {Bk : Type} (k : ℕ) (pool : List (PqxdhLiveKemReservation.Pair KemSK)) (pin : Pqxdh.Bytes)
    (keyId : Std.U64) (e : EnvState KemSK Bk) :
    ∀ v ∈ support ((PqxdhDeploymentIdealEnvReal.createPoolStep (n := 2) setup pool pin keyId).run e), RealMove k e v.2 := by
  intro v member
  unfold PqxdhDeploymentIdealEnvReal.createPoolStep at member
  split at member
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, SessionMove.refl _, id⟩
  · rename_i word _
    rw [StateT.run_bind, mem_support_bind_iff] at member
    obtain ⟨r, rMember, member⟩ := member
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at member
    obtain ⟨_, _, rfl⟩ := member
    simp only [PqxdhDeploymentEnvironment.onEnv, StateT.run, support_map, Set.mem_image] at rMember
    obtain ⟨x, xMember, rfl⟩ := rMember
    have inner : x ∈ support ((PqxdhDeploymentIdealSteps.createPool setup pool word keyId).run e.native) :=
      PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ xMember
    rw [PqxdhDeploymentIdealEnvReal.createPool_run setup pool word keyId e.native] at inner
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at inner
    obtain ⟨_, _, _, _, _, _, rfl⟩ := inner
    exact ⟨rfl, SessionMove.refl _, fun terminal => by rw [terminalAt_strip]; exact terminalAt_append _ _ k terminal⟩

end RealMoves

/-! ### The selected accept's allocator and session facts -/

section SlotFacts
open PqxdhRegistrationJointKemSecondEntry (Alloc slotImpl)
open PqxdhDeploymentIdealSlots (SlotSpec)

/-- A value request through the allocator (a slot read). -/
def isRead : SlotSpec.Domain → Bool
  | .inl _ => false
  | .inr _ => true

/-- The allocator only grows: the earlier slots are kept, the counter does not decrease, and a counter of at most two with every slot below it stays so. -/
structure AllocMove (a a' : Alloc Coord 2) : Prop where
  keeps : ∀ c j, a.1 c = some j → a'.1 c = some j
  counter : a.2 ≤ a'.2
  bounded : a.2 ≤ 2 → a'.2 ≤ 2
  below : (∀ c (j : PqxdhRecordLiftInterface.Slot 2), a.1 c = some j → j.val < a.2) →
    ∀ c (j : PqxdhRecordLiftInterface.Slot 2), a'.1 c = some j → j.val < a'.2

/-- An allocator moves to itself. -/
theorem AllocMove.refl (a : Alloc Coord 2) : AllocMove a a :=
  ⟨fun _ _ found => found, le_refl _, id, id⟩

/-- Allocator moves compose. -/
theorem AllocMove.trans {a b c : Alloc Coord 2} (left : AllocMove a b) (right : AllocMove b c) : AllocMove a c :=
  ⟨fun point j found => right.keeps point j (left.keeps point j found), left.counter.trans right.counter,
    fun bounded => right.bounded (left.bounded bounded), fun below => right.below (left.below below)⟩

/-- One allocator step: the allocator moves, its counter grows by at most one and only at a slot read, and a slot read leaves its point with a slot unless the allocator was full. -/
theorem slotStep_move {S : Type} (svc : PqxdhDeploymentSeedSplit.SlotService S 2) (query : SlotSpec.Domain)
    (state : Alloc Coord 2 × S) :
    ∀ r ∈ support ((slotImpl svc query).run state), AllocMove state.1 r.2.1 ∧
      r.2.1.2 ≤ state.1.2 + (if isRead query then 1 else 0) ∧
      ∀ point, query = .inr point → (r.2.1.1 point).isSome = true ∨ 2 ≤ state.1.2 := by
  intro r member
  rcases query with coin | point
  · rw [PqxdhRegistrationJointKemSecondEntry.slot_coin, support_map] at member
    obtain ⟨_, _, rfl⟩ := member
    exact ⟨AllocMove.refl _, by simp [isRead], fun _ wrong => by cases wrong⟩
  · rcases found : state.1.1 point with _ | slot
    · by_cases room : state.1.2 < 2
      · rw [PqxdhRegistrationJointKemSecondEntry.slot_none _ _ _ found room, support_map] at member
        obtain ⟨inner, _, rfl⟩ := member
        refine ⟨⟨fun c j present => ?_, Nat.le_succ _, fun _ => room, fun below c j present => ?_⟩,
          by simp [isRead], fun other same => ?_⟩
        · have ne : c ≠ point := by
            rintro rfl
            rw [found] at present
            cases present
          simpa only [Function.update_of_ne ne] using present
        · by_cases same : c = point
          · subst same
            simp only [Function.update_self, Option.some.injEq] at present
            subst present
            exact Nat.lt_succ_self _
          · dsimp only at present ⊢
            rw [Function.update_of_ne same] at present
            exact lt_of_lt_of_le (below c j present) (Nat.le_succ _)
        · cases same
          left
          simp
      · simp only [slotImpl, QueryImpl.add_apply_inr, StateT.run_mk, found, room, _root_.dite_false,
          support_map] at member
        obtain ⟨answer, -, rfl⟩ := member
        exact ⟨AllocMove.refl _, by simp [isRead], fun _ _ => Or.inr (by omega)⟩
    · rw [PqxdhRegistrationJointKemSecondEntry.slot_some _ _ _ _ found, support_map] at member
      obtain ⟨inner, _, rfl⟩ := member
      refine ⟨AllocMove.refl _, by simp [isRead], fun other same => ?_⟩
      cases same
      left
      simp [found]

/-- The allocator passes lifted coins through, keeping the allocator and the service state. -/
theorem slot_liftS {S α : Type} (svc : PqxdhDeploymentSeedSplit.SlotService S 2) (work : ProbComp α)
    (state : Alloc Coord 2 × S) :
    (simulateQ (slotImpl svc) (PqxdhDeploymentIdealSteps.liftS work)).run state = (fun a => (a, state)) <$> work := by
  rw [PqxdhDeploymentIdealSteps.liftS, QueryImpl.simulateQ_liftComp_left_eq_of_apply (slotImpl svc)
    (fun query => StateT.mk fun current => (fun reply => (reply, current)) <$> (unifSpec.query query : ProbComp _))
    (fun query => by funext current; exact PqxdhRegistrationJointKemSecondEntry.slot_coin svc query current)]
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, StateT.run_mk, bind_map_left, map_bind]
      refine bind_congr fun reply => ?_
      exact ih reply state

/-- An invariant kept by every step of a stateful handler at the requests a program may issue (those that are not bad) is kept by the program's simulation. -/
theorem run_keepsGood {ι₁ ι₂ σ α : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (impl : QueryImpl spec₁ (StateT σ (OracleComp spec₂))) (bad : spec₁.Domain → Prop) [DecidablePred bad]
    (inv : σ → Prop)
    (step : ∀ query state, ¬ bad query → inv state → ∀ result ∈ support ((impl query).run state), inv result.2)
    (work : OracleComp spec₁ α) (bounded : work.IsQueryBoundP bad 0) (state : σ) (holds : inv state) :
    ∀ result ∈ support ((simulateQ impl work).run state), inv result.2 := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
      intro result supported
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact holds
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      have good : ¬ bad query := bounded.1.resolve_right (lt_irrefl 0)
      intro result supported
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, first, final⟩ := supported
      exact ih middle.1 (by simpa only [Nat.zero_sub, ite_self] using bounded.2 middle.1) middle.2
        (step query state good holds middle first) result final

end SlotFacts

/-! ### The selected accept's marker tail through the allocator -/

section TailFacts
open PqxdhRegistrationJointKemSecondEntry (Alloc slotImpl)
open PqxdhDeploymentIdealSlots (SlotSpec)
variable {Reader : Type}

/-- A root request of the marker tail. -/
def isRoot : (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).Domain → Bool
  | .inl (.inl _) => true
  | _ => false

/-- A root request of the marker client. -/
def isClientRoot : (PqxdhRegistrationJointKemOpaqueClient.Spec Reader).Domain → Bool
  | .inl _ => true
  | .inr _ => false

/-- An install request of the marker tail. -/
def isInstall : (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).Domain → Bool
  | .inr (.install _) => true
  | _ => false

/-- The marker client issues at most one root request. -/
theorem client_root (control : beaconcrypt_core.pqxdh.ServerState) (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (input : PqxdhRegistrationJointKemOpaqueClient.Input Reader) :
    (PqxdhRegistrationJointKemOpaqueClient.client control binding input).IsQueryBoundP
      (fun query => isClientRoot query = true) 1 := by
  unfold PqxdhRegistrationJointKemOpaqueClient.client
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (by simp [isClientRoot]), fun _ => ?_⟩
  simp only [isClientRoot, Bool.false_eq_true, ↓reduceIte]
  split
  · trivial
  · trivial
  · trivial
  · rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr Nat.zero_lt_one, fun _ => ?_⟩
    simp only [↓reduceIte, Nat.sub_self]
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (by simp), fun _ => ?_⟩
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp), fun _ => trivial⟩

/-- The marker tail issues at most one root request. -/
theorem tail_root (serverKeyId : Std.U64) (publicIdentity : PqxdhJointIdentity.PublicIdentity) (state : GameState KemSK)
    (collected : Option (PqxdhRegistrationJointKemOpaqueClient.Input Reader) × List Pqxdh.Bytes) :
    (PqxdhRegistrationJointKemOpaqueTail.tail serverKeyId publicIdentity state collected).IsQueryBoundP
      (fun query => isRoot query = true) 1 := by
  unfold PqxdhRegistrationJointKemOpaqueTail.tail
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (by simp [isRoot]), fun _ => ?_⟩
  simp only [isRoot, Bool.false_eq_true, ↓reduceIte]
  split
  · trivial
  · rw [show (1 : ℕ) = 1 + 0 from rfl]
    refine isQueryBoundP_bind (IsQueryBoundP.simulateQ_of_step (client_root _ _ _) (fun query root => ?_)
      (fun query notRoot => ?_)) fun returned _ => ?_
    · rcases query with input | aux
      · simp [PqxdhRegistrationJointKemOpaqueTail.forward, isQueryBoundP_query_iff]
      · simp [isClientRoot] at root
    · rcases query with input | aux
      · simp [isClientRoot] at notRoot
      · simp [PqxdhRegistrationJointKemOpaqueTail.forward, isQueryBoundP_query_iff]
    · split
      · rw [isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by simp), fun _ => trivial⟩
      · trivial

/-- A marker tail request that keeps the Server's sessions moving from `start`: an install of a state `start` moves to, a publication at an index not below `start`'s counter, and every client request. -/
def GoodTail (start : GameState KemSK) : (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).Domain → Prop
  | .inr (.install state) => SessionMove start state
  | .inr (.publish index _) => start.sessions ≤ index
  | _ => True

/-- The native root of a known decapsulation result keeps the Server's sessions and pending tokens. -/
theorem romRoot_keeps (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : PqxdhRegistrationJointKemOpaqueClient.Input Reader) (s : NativeState KemSK) :
    ∀ r ∈ support ((PqxdhRegistrationJointKemOpaqueClient.romRoot KemSK hmac index candidate input).run s),
      r.2.2.sessions = s.2.sessions ∧ r.2.2.pending = s.2.pending := by
  intro r member
  simp only [PqxdhRegistrationJointKemOpaqueClient.romRoot, PqxdhServerAuthNative.nativeTouch, StateT.run_bind,
    StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
  obtain ⟨root, rootMember, _, touched, rfl⟩ := member
  unfold PqxdhServerAuthNative.romRootBytes at rootMember
  simp only [StateT.run, support_map, Set.mem_image] at rootMember
  obtain ⟨_, _, rfl⟩ := rootMember
  simp only [PqxdhServerAuthNative.localState, StateT.run, support_pure, Set.mem_singleton_iff] at touched
  subst touched
  exact ⟨rfl, rfl⟩

/-- The marker client's auxiliary requests keep the Server's sessions and pending tokens. -/
theorem auxiliary_keeps (query : PqxdhServerRelatedRootConsumer.Auxiliary) (s : NativeState KemSK) :
    ∀ r ∈ support ((PqxdhRegistrationJointKemOpaqueClient.auxiliary KemSK query).run s),
      r.2.2.sessions = s.2.sessions ∧ r.2.2.pending = s.2.pending := by
  intro r member
  cases query <;>
    simp [PqxdhRegistrationJointKemOpaqueClient.auxiliary, PqxdhServerAuthNative.nativeConsume,
      PqxdhServerAuthNative.localState, StateT.run] at member <;>
    subst member <;> exact ⟨rfl, rfl⟩

/-- A lifted probabilistic step of a slot client, mapped, keeps the allocator and the service state. -/
theorem slot_mapLiftS {S α β : Type} (svc : PqxdhDeploymentSeedSplit.SlotService S 2) (f : α → β) (work : ProbComp α)
    (state : Alloc Coord 2 × S) :
    ∀ y ∈ support ((simulateQ (slotImpl svc) (f <$> PqxdhDeploymentIdealSteps.liftS work)).run state),
      ∃ x ∈ support work, y = (f x, state) := by
  intro y member
  rw [simulateQ_map, StateT.run_map, slot_liftS, Functor.map_map, support_map] at member
  obtain ⟨x, xMember, rfl⟩ := member
  exact ⟨x, xMember, rfl⟩

/-- The selected accept's marker tail with its slot reads answered by the allocator in front of a slot service, as one stateful handler on the native state with the mark, and the allocator with the service state. -/
noncomputable def tailSlots {S : Type} (svc : PqxdhDeploymentSeedSplit.SlotService S 2)
    (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ) :
    QueryImpl (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK)
      (StateT ((NativeState KemSK × Option (ℕ × Coord)) × (Alloc Coord 2 × S)) ProbComp) :=
  ((slotImpl svc).mapStateTBase (PqxdhDeploymentIdealSteps.tailCE hmac index)).flattenStateT

/-- One step of `tailSlots`: the marker tail's step, its slot reads answered by the allocator. -/
theorem tailSlots_run {S : Type} (svc : PqxdhDeploymentSeedSplit.SlotService S 2) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (index : ℕ) (query : (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).Domain) (s : NativeState KemSK)
    (mark : Option (ℕ × Coord)) (state : Alloc Coord 2 × S) :
    (tailSlots svc hmac index query).run ((s, mark), state) =
      (fun z => (z.1.1, (z.1.2, z.2))) <$>
        (simulateQ (slotImpl svc) ((PqxdhDeploymentIdealSteps.tailCE hmac index query).run (s, mark))).run state :=
  rfl

/-- What the selected accept's marker tail keeps from the start: the Server's sessions move from the start's game state, the allocator moves from the start's allocator, and a mark is at the accept's session index with its coordinates holding a slot unless the allocator is full. -/
def TailInv {S : Type} (start : GameState KemSK) (index : ℕ) (origin : Alloc Coord 2)
    (z : (NativeState KemSK × Option (ℕ × Coord)) × (Alloc Coord 2 × S)) : Prop :=
  SessionMove start z.1.1.2 ∧ AllocMove origin z.2.1 ∧
    ∀ i c, z.1.2 = some (i, c) → i = index ∧ ((z.2.1.1 c).isSome = true ∨ 2 ≤ z.2.1.2)

/-- One step of `tailSlots`: it raises the allocator's counter by at most one and only at a root request; it keeps `TailInv` at a request that keeps the sessions moving; every request other than an install does not lower the session counter; and an install sets the game state, keeping the mark, the allocator and the service state. -/
theorem tailSlots_step {S : Type} (svc : PqxdhDeploymentSeedSplit.SlotService S 2)
    (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ) (start : GameState KemSK) (origin : Alloc Coord 2)
    (query : (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).Domain)
    (z : (NativeState KemSK × Option (ℕ × Coord)) × (Alloc Coord 2 × S)) :
    ∀ r ∈ support ((tailSlots svc hmac index query).run z),
      r.2.2.1.2 ≤ z.2.1.2 + (if isRoot query then 1 else 0) ∧
        (GoodTail start query → TailInv start index origin z → TailInv start index origin r.2) ∧
        (isInstall query = false → z.1.1.2.sessions ≤ r.2.1.1.2.sessions) ∧
        (∀ game, query = .inr (.install game) → r.2.1.1.2 = game ∧ r.2.1.2 = z.1.2 ∧ r.2.2 = z.2) := by
  obtain ⟨⟨s, mark⟩, state⟩ := z
  intro r member
  rw [tailSlots_run, support_map] at member
  obtain ⟨y, yMember, rfl⟩ := member
  rcases query with (input | aux) | mutation
  · cases shared : input.shared with
    | challenge =>
        have left : (PqxdhDeploymentIdealSteps.tailCE (KemSK := KemSK) hmac index (.inl (.inl input))).run (s, mark) =
            ((SlotSpec.query (.inr (PqxdhDeploymentIdealSteps.coordsOf input)) : OracleComp SlotSpec _) >>= fun _ =>
              pure (PqxdhServerAuthEntryFactor.sentinel, (s, some (index, PqxdhDeploymentIdealSteps.coordsOf input)))) := by
          simp only [PqxdhDeploymentIdealSteps.tailCE, StateT.run, shared]
        rw [left, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at yMember
        obtain ⟨x, xMember, final⟩ := yMember
        rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at final
        subst final
        obtain ⟨move, count, read⟩ := slotStep_move svc _ state x xMember
        refine ⟨by simpa [isRoot, isRead] using count, fun _ holds => ⟨holds.1, holds.2.1.trans move, fun i c found => ?_⟩,
          fun _ => le_refl _, fun _ wrong => by cases wrong⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, rfl⟩ := found
        exact ⟨rfl, (read _ rfl).imp id (fun full => le_trans full move.counter)⟩
    | known secret =>
        simp only [PqxdhDeploymentIdealSteps.tailCE, shared] at yMember
        obtain ⟨x, xMember, rfl⟩ := slot_mapLiftS svc _ _ state y yMember
        obtain ⟨sessions, pending⟩ := romRoot_keeps hmac index _ input s x xMember
        exact ⟨by simp, fun _ holds => ⟨holds.1.trans (SessionMove.of_eq sessions pending), holds.2.1, holds.2.2⟩,
          fun _ => sessions.ge, fun _ wrong => by cases wrong⟩
  · simp only [PqxdhDeploymentIdealSteps.tailCE] at yMember
    obtain ⟨x, xMember, rfl⟩ := slot_mapLiftS svc _ _ state y yMember
    obtain ⟨sessions, pending⟩ := auxiliary_keeps aux s x xMember
    exact ⟨by simp, fun _ holds => ⟨holds.1.trans (SessionMove.of_eq sessions pending), holds.2.1, holds.2.2⟩,
      fun _ => sessions.ge, fun _ wrong => by cases wrong⟩
  · simp only [PqxdhDeploymentIdealSteps.tailCE] at yMember
    obtain ⟨x, xMember, rfl⟩ := slot_mapLiftS svc _ _ state y yMember
    cases mutation with
    | install game =>
        simp [PqxdhRegistrationJointKemOpaqueTail.mutation, PqxdhServerAuthNative.nativeSet,
          PqxdhServerAuthNative.localState, StateT.run] at xMember
        subst xMember
        exact ⟨by simp, fun good holds => ⟨good, holds.2.1, holds.2.2⟩, fun wrong => by simp [isInstall] at wrong,
          fun other same => by cases same; exact ⟨rfl, rfl, rfl⟩⟩
    | publish at_ token =>
        simp [PqxdhRegistrationJointKemOpaqueTail.mutation, PqxdhServerAuthNative.nativeModify,
          PqxdhServerAuthNative.localState, StateT.run] at xMember
        subst xMember
        refine ⟨by simp, fun good holds => ⟨⟨holds.1.1, fun session below found => holds.1.2 session below ?_⟩,
          holds.2.1, holds.2.2⟩, fun _ => le_refl _, fun _ wrong => by cases wrong⟩
        have ne : session ≠ at_ := Nat.ne_of_lt (lt_of_lt_of_le below good)
        simpa [Function.update_of_ne ne] using found

end TailFacts

/-! ### The selected accept's facts -/

section AcceptFacts
open PqxdhRegistrationJointKemSecondEntry (Alloc slotImpl)
open PqxdhDeploymentIdealSlots (SlotSpec)
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : ℕ}

/-- The native accept tail without a collected input allocates the next session index and publishes no token. -/
theorem serverTail_none (publicIdentity : PqxdhJointIdentity.PublicIdentity) (state : GameState KemSK)
    (consumed : List Pqxdh.Bytes) (s : NativeState KemSK) :
    ∀ r ∈ support ((PqxdhRegistrationJointServerAccept.tail (Reader := Reader) setup publicIdentity state
      (none, consumed)).run s), SessionMove state r.2.2 := by
  intro r member
  simp [PqxdhRegistrationJointServerAccept.tail, PqxdhServerAuthNative.nativeSet, StateT.run] at member
  subst member
  exact ⟨Nat.le_succ _, fun _ _ found => found⟩

/-- The LQ-F logged accept as a slot client keeps the allocator and the service state, sets no mark, and moves the Server's sessions. -/
theorem acceptInactive_facts {S : Type} (svc : PqxdhDeploymentSeedSplit.SlotService S 2)
    (seed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes) (shared : NativeState KemSK)
    (origin : Alloc Coord 2) (service : S) :
    ∀ r ∈ support ((simulateQ (slotImpl svc) ((PqxdhDeploymentIdealSteps.acceptInactive setup codec checks seed
      raw).run shared)).run (origin, service)),
      SessionMove shared.2 r.1.2.2 ∧ r.2 = (origin, service) ∧ r.1.1.2.2 = none := by
  intro r member
  obtain ⟨x, xMember, rfl⟩ := slot_mapLiftS svc _ _ _ r member
  exact ⟨acceptLogged_move setup codec checks seed raw shared x xMember, rfl, rfl⟩

open Classical in
/-- The active selected accept as a slot client: the Server's sessions move, the allocator moves with its counter raised by at most one, and a mark is at the accept's session index with its coordinates holding a slot unless the allocator is full. -/
theorem acceptActive_facts {S : Type} (svc : PqxdhDeploymentSeedSplit.SlotService S 2)
    (seed : PqxdhJointIdentity.IdentitySeed) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (verified : PqxdhServerRootPreparation.Verified Reader) (shared : NativeState KemSK)
    (origin : Alloc Coord 2) (service : S) :
    ∀ r ∈ support ((simulateQ (slotImpl svc) ((PqxdhDeploymentIdealSteps.acceptActive setup codec checks seed challenge
      verified).run shared)).run (origin, service)),
      SessionMove shared.2 r.1.2.2 ∧ AllocMove origin r.2.1 ∧ r.2.1.2 ≤ origin.2 + 1 ∧
        ∀ i c, r.1.1.2.2 = some (i, c) → i = shared.2.sessions ∧ shared.2.sessions < r.1.2.2.sessions ∧
          ((r.2.1.1 c).isSome = true ∨ 2 ≤ r.2.1.2) := by
  intro r member
  rw [show (PqxdhDeploymentIdealSteps.acceptActive setup codec checks seed challenge verified).run shared =
    PqxdhDeploymentIdealSteps.acceptActive setup codec checks seed challenge verified shared from rfl] at member
  unfold PqxdhDeploymentIdealSteps.acceptActive at member
  rw [simulateQ_bind, StateT.run_bind, slot_liftS, bind_map_left, mem_support_bind_iff] at member
  obtain ⟨pre, _, member⟩ := member
  split at member
  · rw [simulateQ_bind, StateT.run_bind, slot_liftS, bind_map_left, mem_support_bind_iff] at member
    obtain ⟨x, xMember, final⟩ := member
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at final
    subst final
    exact ⟨serverTail_none setup _ shared.2 _ shared x xMember, AllocMove.refl _, Nat.le_succ _,
      fun _ _ wrong => by cases wrong⟩
  · rw [simulateQ_bind, StateT.run_bind, slot_liftS, bind_map_left, mem_support_bind_iff] at member
    obtain ⟨prepared, _, member⟩ := member
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at member
    obtain ⟨answer, answerMember, final⟩ := member
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at final
    subst final
    rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, support_map] at answerMember
    obtain ⟨z, zMember, rfl⟩ := answerMember
    change z ∈ support ((simulateQ (tailSlots svc setup.hmac shared.2.sessions) _).run _) at zMember
    have counted := PqxdhServerAuthExperiment.run_count (tailSlots svc setup.hmac shared.2.sessions)
      (fun query => isRoot query = true) (fun state => state.2.1.2)
      (fun query state result member => (tailSlots_step svc setup.hmac shared.2.sessions shared.2 origin query state
        result member).1) _ 1 (tail_root _ _ _ _) _ z zMember
    unfold PqxdhRegistrationJointKemOpaqueTail.tail at zMember
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at zMember
    obtain ⟨installed, installedMember, zMember⟩ := zMember
    obtain ⟨_, _, _, installFacts⟩ := tailSlots_step svc setup.hmac shared.2.sessions shared.2 origin _ _ installed
      installedMember
    obtain ⟨game, mark, slots⟩ := installFacts _ rfl
    have kept := run_keepsGood (tailSlots svc setup.hmac shared.2.sessions)
      (fun query => ¬ GoodTail shared.2 query ∨ isInstall query = true)
      (fun state => TailInv shared.2 shared.2.sessions origin state ∧ shared.2.sessions < state.1.1.2.sessions)
      (fun query state bad holds result member => by
        obtain ⟨_, keeps, grows, _⟩ := tailSlots_step svc setup.hmac shared.2.sessions shared.2 origin query state
          result member
        have good : GoodTail shared.2 query ∧ isInstall query = false := by
          simp only [not_or, not_not, Bool.not_eq_true] at bad
          exact bad
        exact ⟨keeps good.1 holds.1, lt_of_lt_of_le holds.2 (grows good.2)⟩) _ ?_ installed.2
      ⟨⟨by rw [game]; exact ⟨Nat.le_succ _, fun _ _ found => found⟩, by rw [slots]; exact AllocMove.refl _,
        fun _ _ found => by rw [mark] at found; cases found⟩, by rw [game]; exact Nat.lt_succ_self _⟩ z zMember
    · exact ⟨kept.1.1, kept.1.2.1, counted, fun i c found => by
        obtain ⟨same, slotted⟩ := kept.1.2.2 i c found
        exact ⟨same, same ▸ kept.2, slotted⟩⟩
    · split
      · trivial
      · rw [show (0 : ℕ) = 0 + 0 from rfl]
        refine isQueryBoundP_bind (IsQueryBoundP.simulateQ_of_step (p := fun _ => False)
          (isQueryBoundP_false _ _) (fun _ wrong => absurd wrong id) (fun query _ => ?_)) fun returned _ => ?_
        · exact (isQueryBoundP_query_iff _ _ _).2 (fun bad => by simp [GoodTail, isInstall] at bad)
        · split
          · rw [isQueryBoundP_query_bind_iff]
            exact ⟨Or.inl (by simp [GoodTail, isInstall]), fun _ => trivial⟩
          · trivial

/-- The selected accept with its encapsulation exposed, as a slot client from an allocator: the Server's sessions move, the allocator moves with its counter raised by at most one, and a mark is at the accept's session index with its coordinates holding a slot unless the allocator is full. -/
theorem acceptExposed_facts {S : Type} (svc : PqxdhDeploymentSeedSplit.SlotService S 2) (p : Params KemSK count)
    (seed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes) (shared : NativeState KemSK)
    (origin : Alloc Coord 2) (service : S) :
    ∀ r ∈ support ((simulateQ (slotImpl svc) ((PqxdhDeploymentIdealSteps.acceptExposed setup codec checks seed p.chosen
      p.challenge raw).run shared)).run (origin, service)),
      SessionMove shared.2 r.1.2.2 ∧ AllocMove origin r.2.1 ∧ r.2.1.2 ≤ origin.2 + 1 ∧
        ∀ i c, r.1.1.2.2 = some (i, c) → i = shared.2.sessions ∧ shared.2.sessions < r.1.2.2.sessions ∧
          ((r.2.1.1 c).isSome = true ∨ 2 ≤ r.2.1.2) := by
  have inactive : ∀ r ∈ support ((simulateQ (slotImpl svc) ((PqxdhDeploymentIdealSteps.acceptInactive setup codec checks
      seed raw).run shared)).run (origin, service)),
      SessionMove shared.2 r.1.2.2 ∧ AllocMove origin r.2.1 ∧ r.2.1.2 ≤ origin.2 + 1 ∧
        ∀ i c, r.1.1.2.2 = some (i, c) → i = shared.2.sessions ∧ shared.2.sessions < r.1.2.2.sessions ∧
          ((r.2.1.1 c).isSome = true ∨ 2 ≤ r.2.1.2) := by
    intro r member
    obtain ⟨sessions, same, marked⟩ := acceptInactive_facts setup codec checks svc seed raw shared origin service r member
    rw [same]
    exact ⟨sessions, AllocMove.refl _, Nat.le_succ _, fun _ _ wrong => by rw [marked] at wrong; cases wrong⟩
  intro r member
  unfold PqxdhDeploymentIdealSteps.acceptExposed at member
  split at member
  · split_ifs at member
    · exact acceptActive_facts setup codec checks svc seed p.challenge _ shared origin service r member
    · exact inactive r member
  · exact inactive r member

end AcceptFacts

/-! ### The hidden commands' outcomes with the seed table exact -/

section Exact
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : ℕ}
open PqxdhDeploymentEnvironment (ctxEffects)
open PqxdhDeploymentEnvironmentReal (ctxAdmin effects_then_free coins_noAdmin CountFree countFree_bind countFree_pure
  withCache)
open PqxdhDeploymentIdealKernel (MatCache SeedCache lazyDummy)
open PqxdhDeploymentIdealEnvStep (SlotState)
open PqxdhRegistrationJointKemSecondEntry (slotImpl)
open PqxdhRegistrationJointKemPostSkeleton (Pending embed message)
open PqxdhDeploymentIdealSteps (publishedKey)
open PqxdhDeploymentSeedSplit (MaterialSpec)
open PqxdhDeploymentSplitFactor (freeBuild)
open PqxdhDeploymentIdealEnvBuild
open PqxdhDeploymentIdealEnvFinish

/-- One lazy seed-table step changes the table only at the requested slot. -/
theorem lazy_other (j : PqxdhRecordLiftInterface.Slot 2)
    (s : PqxdhRecordLiftLazyTable.State (PqxdhRecordLiftWorld.SeedSpec 2))
    (z : (PqxdhRecordLiftWorld.SeedSpec 2).Range j × PqxdhRecordLiftLazyTable.State (PqxdhRecordLiftWorld.SeedSpec 2))
    (supported : z ∈ support ((PqxdhRecordLiftLazyTable.impl j).run s)) : ∀ k, k ≠ j → z.2.1 k = s.1 k := by
  intro k other
  cases hit : s.1 j with
  | some answer =>
      simp only [PqxdhRecordLiftLazyTable.run_hit j s answer hit, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl
  | none =>
      simp only [PqxdhRecordLiftLazyTable.run_miss j s hit, support_map] at supported
      obtain ⟨answer, _, rfl⟩ := supported
      exact QueryCache.cacheQuery_of_ne _ _ other

open PqxdhDeploymentEnvironmentReal (worldCopies run_support Built installPeer) in
/-- `PqxdhDeploymentIdealEnvBuild.buildHidden_outcome` with the seed table exact: every outcome of the marked build in capability form at an allocated slot with a pending token, with the World's counts forgotten, from an admissible state whose World Server marker of the slot is unused: either nothing was published (the token consumed, the seals logged, the World's CTX cache advanced) or one peer was published at a key ID vacant before, the World installed it with its Server kernel of the slot's seed, which its seed table now holds, and set the slot's Server marker. -/
theorem buildHidden_exact (created : PqxdhLiveServerConstruction.Created Unit) (session : ℕ)
    (payload : Option Pqxdh.Bytes) (coords : Coord) (e : EnvState KemSK SplitBk) (w : PqxdhRecordLiftWorld.State 2)
    (good : Good created e w) (j : PqxdhRecordLiftInterface.Slot 2) (token : PqxdhServerRelatedRootConsumer.Returned)
    (allocated : e.backend.2.1.1 coords = some j) (pending : e.native.shared.2.pending session = some token)
    (unused : w.used j .server = false) (world : PqxdhRecordLiftWorld.Server) (found : w.server = some world) :
    ∀ result ∈ support (Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((buildHiddenEnv setup codec checks session payload coords).run e)).run w),
      ∃ material log cache,
        (result.1.1 = none ∧ result.1.2 = builtEnv e session coords material ((none, e.native.shared.2.server), log) ∧
          result.2 = uncount (withCache w cache)) ∨
        (∃ response candidate seed table, response.keyId = candidate.key_id ∧
          e.native.shared.2.server.server.peers candidate.key_id = none ∧ table.1 j = some seed ∧
          w.seeds.1 ≤ table.1 ∧ (∀ k, k ≠ j → table.1 k = w.seeds.1 k) ∧ result.1.1 = some response ∧
          result.1.2 = builtEnv e session coords material ((some response, PqxdhServerRegistrationPublication.publish
            e.native.shared.2.server candidate PqxdhDeploymentHiddenSplit.placeholderKernel ()), log) ∧
          result.2 = uncount { withCache w cache with
            seeds := table
            used := Function.update w.used j (Function.update (w.used j) .server true)
            server := some (installPeer world candidate.key_id candidate.beacon_identity_public_key
              (PqxdhRecordLiftWorld.kernel .server seed)) }) := by
  obtain ⟨world', found', _, _, peersRaw⟩ := good.server
  rw [found] at found'
  cases found'
  intro result supported
  rw [buildHidden_effects setup codec checks session payload coords e w j token allocated pending,
    mem_support_bind_iff] at supported
  obtain ⟨drawn, _, supported⟩ := supported
  rw [mem_support_bind_iff, PqxdhDeploymentSplitFactor.buildSplitFwd_free, StateT.run_map, simulateQ_map,
    StateT.run_map, support_map] at supported
  obtain ⟨_, ⟨⟨⟨rust, log⟩, cache⟩, member, rfl⟩, final⟩ := supported
  have built : Built e.native.shared.2.server () rust :=
    freeBuild_shape _ _ _ _ _ rust (run_support _ _ [] (rust, log) (run_support _ _ w.primitive.2 ((rust, log), cache) member))
  refine ⟨drawn.2, log, cache, ?_⟩
  have effect : PqxdhDeploymentEnvironment.hiddenServerEffect (n := 2) j (none, e.native.shared.2.server) = pure () :=
    rfl
  rcases rust with ⟨_ | response, after⟩ | error | _
  · have same : after = e.native.shared.2.server := built
    subst same
    change result ∈ support (Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
      (PqxdhDeploymentEnvironment.hiddenServerEffect j (none, e.native.shared.2.server) >>= fun _ =>
        pure (none, builtEnv e session coords drawn.2 ((none, e.native.shared.2.server), log)))).run
          (withCache w cache)) at final
    rw [effect, pure_bind, simulateQ_pure, StateT.run_pure, map_pure, support_pure, Set.mem_singleton_iff] at final
    subst final
    exact Or.inl ⟨rfl, rfl, rfl⟩
  · obtain ⟨candidate, kernel, keyEq, vacant, published⟩ := built
    subst published
    have vacantWorld : world.records.server.peers candidate.key_id = none := by
      have mapped := peersRaw candidate.key_id
      rw [vacant] at mapped
      cases hworld : world.records.server.peers candidate.key_id with
      | none => rfl
      | some peer => rw [hworld] at mapped; cases mapped
    have replaced : PqxdhServerAuthExperiment.settle e.native.shared.2.server
        (PqxdhDeploymentHiddenSplit.replaceRaw PqxdhDeploymentHiddenSplit.placeholderKernel <$>
          RustM.ok (some response, PqxdhServerRegistrationPublication.publish e.native.shared.2.server candidate kernel ())) =
        (some response, PqxdhServerRegistrationPublication.publish e.native.shared.2.server candidate
          PqxdhDeploymentHiddenSplit.placeholderKernel ()) := by
      change (some response, PqxdhDeploymentHiddenSplit.setPeerKernel (PqxdhServerRegistrationPublication.publish
        e.native.shared.2.server candidate kernel ()) response.keyId PqxdhDeploymentHiddenSplit.placeholderKernel) = _
      rw [keyEq, PqxdhDeploymentHiddenSplit.publish_setPeerKernel]
    have peerAt := (PqxdhServerRegistrationPublication.publish_fields e.native.shared.2.server candidate
      PqxdhDeploymentHiddenSplit.placeholderKernel ()).1
    have effect : PqxdhDeploymentEnvironment.hiddenServerEffect (n := 2) j (some response,
        PqxdhServerRegistrationPublication.publish e.native.shared.2.server candidate
          PqxdhDeploymentHiddenSplit.placeholderKernel ()) =
        PqxdhDeploymentEnvironment.issue (.installServer response.keyId candidate.beacon_identity_public_key (.hidden j)) := by
      unfold PqxdhDeploymentEnvironment.hiddenServerEffect
      simp only [keyEq, peerAt]
    rw [replaced, effect, PqxdhDeploymentEnvironmentReal.effects_issue_then,
      effects_hiddenServer response.keyId candidate.beacon_identity_public_key j (withCache w cache) world found
        (by rw [keyEq]; exact vacantWorld) unused, Functor.map_map, support_map] at final
    obtain ⟨⟨seed, table⟩, inTable, rfl⟩ := final
    have facts := PqxdhRecordLiftLazyTable.step_facts j w.seeds (seed, table) inTable
    refine Or.inr ⟨response, candidate, seed, table, keyEq, vacant, facts.1, facts.2.1,
      lazy_other j w.seeds (seed, table) inTable, rfl, rfl, ?_⟩
    rw [keyEq]
    rfl
  · change result ∈ support (Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
      (PqxdhDeploymentEnvironment.hiddenServerEffect j (none, e.native.shared.2.server) >>= fun _ =>
        pure (none, builtEnv e session coords drawn.2 ((none, e.native.shared.2.server), log)))).run
          (withCache w cache)) at final
    rw [effect, pure_bind, simulateQ_pure, StateT.run_pure, map_pure, support_pure, Set.mem_singleton_iff] at final
    subst final
    exact Or.inl ⟨rfl, rfl, rfl⟩
  · change result ∈ support (Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
      (PqxdhDeploymentEnvironment.hiddenServerEffect j (none, e.native.shared.2.server) >>= fun _ =>
        pure (none, builtEnv e session coords drawn.2 ((none, e.native.shared.2.server), log)))).run
          (withCache w cache)) at final
    rw [effect, pure_bind, simulateQ_pure, StateT.run_pure, map_pure, support_pure, Set.mem_singleton_iff] at final
    subst final
    exact Or.inl ⟨rfl, rfl, rfl⟩

open PqxdhDeploymentEnvironmentReal (commit_shape effects_issue_then effects_advance) in
/-- `PqxdhDeploymentIdealEnvFinish.hiddenFinish_outcome` with the seed table exact: every outcome of owner k's hidden finish in capability form at an allocated slot, with the World's counts forgotten, from a World whose owner is in the `initSent` phase and whose Beacon marker of the slot is unused: the owner aborted (its World phase advanced, nothing else changed in the World), or established with the World's Beacon kernel of the slot's seed, which the seed table now holds, the slot's Beacon marker set. -/
theorem hiddenFinish_exact (e : EnvState KemSK SplitBk) (owner : ℕ) (control : beaconcrypt_core.pqxdh.BeaconInitSent)
    (before : PqxdhRegistrationSchedule.Owner KemSK) (pending : Pending Response) (coords : Coord)
    (read : PqxdhServerAuthKeySchedule.Output × SlotState) (j : PqxdhRecordLiftInterface.Slot 2)
    (w : PqxdhRecordLiftWorld.State 2) (cache : CtxRomAuth.CtxRO.QueryCache)
    (initSent : PqxdhDeploymentEnvironment.inactiveTag before.beacon.phase = some .initSent)
    (worldPhase : w.owners[owner]? = some (.inactive .initSent)) (unused : w.used j .beacon = false) :
    ∀ result ∈ support (Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((fun committed => (committed.1, finishedEnv e owner e.native.shared committed.2
          (hiddenBackend e owner committed.2 coords read.2))) <$>
          PqxdhDeploymentEnvironment.finishSplitEnv setup codec (PqxdhDeploymentHiddenLayout.splitOutput read.1).1 j
            owner control before (embed pending))).run (withCache w cache)),
      ∃ staged cache',
        (PqxdhDeploymentEnvironment.inactiveTag (PqxdhBeaconPhase2Publication.finish control before staged).2.beacon.phase =
            some .aborted ∧
          result = (((PqxdhBeaconPhase2Publication.finish control before staged).1, finishedEnv e owner e.native.shared
            (PqxdhBeaconPhase2Publication.finish control before staged).2 (hiddenBackend e owner
              (PqxdhBeaconPhase2Publication.finish control before staged).2 coords read.2)),
            uncount { withCache w cache' with owners := w.owners.set owner (.inactive .aborted) })) ∨
        (∃ control' associatedData kernel seed table,
          (PqxdhBeaconPhase2Publication.finish control before staged).2.beacon.phase =
            .established control' associatedData kernel ∧ table.1 j = some seed ∧ w.seeds.1 ≤ table.1 ∧
          (∀ k, k ≠ j → table.1 k = w.seeds.1 k) ∧
          result = (((PqxdhBeaconPhase2Publication.finish control before staged).1, finishedEnv e owner e.native.shared
            (PqxdhBeaconPhase2Publication.finish control before staged).2 (hiddenBackend e owner
              (PqxdhBeaconPhase2Publication.finish control before staged).2 coords read.2)),
            uncount { withCache w cache' with
              seeds := table
              used := Function.update w.used j (Function.update (w.used j) .beacon true)
              owners := w.owners.set owner (.established ⟨(PqxdhBeaconPhase2Publication.finish control before
                staged).2.beacon.identityKeyId, control', associatedData⟩ (PqxdhRecordLiftWorld.kernel .beacon seed)) })) := by
  intro result supported
  have program : (fun committed => (committed.1, finishedEnv e owner e.native.shared committed.2
      (hiddenBackend e owner committed.2 coords read.2))) <$>
      PqxdhDeploymentEnvironment.finishSplitEnv setup codec (PqxdhDeploymentHiddenLayout.splitOutput read.1).1 j
        owner control before (embed pending) =
      PqxdhDeploymentEnvironment.finishSplitFwd setup codec (PqxdhDeploymentHiddenLayout.splitOutput read.1).1
        (embed pending) >>= fun staged =>
        PqxdhDeploymentEnvironment.hiddenOwnerEffect j owner before
          (PqxdhBeaconPhase2Publication.finish control before staged).2 >>= fun _ =>
          pure ((PqxdhBeaconPhase2Publication.finish control before staged).1, finishedEnv e owner e.native.shared
            (PqxdhBeaconPhase2Publication.finish control before staged).2
            (hiddenBackend e owner (PqxdhBeaconPhase2Publication.finish control before staged).2 coords read.2)) := by
    simp only [PqxdhDeploymentEnvironment.finishSplitEnv, map_bind, map_pure]
  rw [program, PqxdhDeploymentEnvironmentReal.effects_then_free PqxdhDeploymentEnvironmentReal.ctxAdmin _
    (finishSplitFwd_noAdmin setup codec _ _) _ (fun staged => countFree_bind (countFree_hiddenOwnerEffect _ _ _ _)
      fun _ => countFree_pure _) _, mem_support_bind_iff] at supported
  obtain ⟨⟨staged, cache'⟩, _, final⟩ := supported
  refine ⟨staged, cache', ?_⟩
  rw [show withCache (withCache w cache) cache' = withCache w cache' from rfl] at final
  rcases commit_shape control before staged with aborted | ⟨control', associatedData, kernel, established⟩
  · rw [hiddenOwnerEffect_abort j owner before _ initSent aborted, effects_issue_then,
      effects_advance owner .initSent .aborted (withCache w cache') worldPhase trivial, map_pure, support_pure,
      Set.mem_singleton_iff] at final
    exact Or.inl ⟨aborted, final⟩
  · rw [hiddenOwnerEffect_establish j owner before _ initSent control' associatedData kernel established,
      effects_issue_then, effects_hiddenBeacon owner _ j (withCache w cache') worldPhase unused, Functor.map_map,
      support_map] at final
    obtain ⟨⟨seed, table⟩, inTable, rfl⟩ := final
    have facts := PqxdhRecordLiftLazyTable.step_facts j w.seeds (seed, table) inTable
    exact Or.inr ⟨control', associatedData, kernel, seed, table, established, facts.1, facts.2.1,
      lazy_other j w.seeds (seed, table) inTable, rfl⟩

/-- The selected accept in capability form: the Server's sessions move; the allocator moves with its counter raised by at most one; a mark is at the old session counter, below the new one, with its coordinates holding a slot unless the allocator is full; the accept counter is advanced, the install ghosts are unchanged, and the owners are the stripped owners. -/
theorem acceptSelected_move (p : Params KemSK count) (raw : Pqxdh.Bytes) (e : EnvState KemSK SplitBk) :
    ∀ v ∈ support ((PqxdhDeploymentIdealEnvStep.acceptSelectedEnv setup codec checks p raw).run e),
      SessionMove e.native.shared.2 v.2.native.shared.2 ∧ AllocMove e.backend.2.1 v.2.backend.2.1 ∧
        v.2.backend.2.1.2 ≤ e.backend.2.1.2 + 1 ∧
        (∀ i c, v.2.backend.2.2.marks = some (i, c) → i = e.native.shared.2.sessions ∧
          e.native.shared.2.sessions < v.2.native.shared.2.sessions ∧
          ((v.2.backend.2.1.1 c).isSome = true ∨ 2 ≤ v.2.backend.2.1.2)) ∧
        v.2.backend.2.2.accepts = e.backend.2.2.accepts + 1 ∧ v.2.backend.2.2.peer = e.backend.2.2.peer ∧
        v.2.backend.2.2.beacon = e.backend.2.2.beacon ∧ v.2.native.owners = (strip e.native).owners := by
  intro v member
  change v ∈ support ((fun r => (r.1.1.1.1, PqxdhDeploymentIdealEnvStep.acceptedEnv e r)) <$> coins (n := 2)
    ((PqxdhDeploymentIdealEnvStep.acceptGame setup codec checks p e.created.seed raw
      (e.backend.2.1, (e.backend.1, ∅))).run e.native.shared)) at member
  rw [support_map] at member
  obtain ⟨r, rMember, rfl⟩ := member
  have inner : r ∈ support ((fun r => ((r.1.1, r.2), r.1.2)) <$> (simulateQ (slotImpl (lazyDummy (n := 2)))
      ((PqxdhDeploymentIdealSteps.acceptExposed setup codec checks e.created.seed p.chosen p.challenge raw).run
        e.native.shared)).run (e.backend.2.1, (e.backend.1, ∅))) :=
    PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ rMember
  rw [support_map] at inner
  obtain ⟨x, xMember, rfl⟩ := inner
  obtain ⟨sessions, alloc, counter, marked⟩ := acceptExposed_facts setup codec checks lazyDummy p e.created.seed raw
    e.native.shared e.backend.2.1 (e.backend.1, ∅) x xMember
  exact ⟨sessions, alloc, counter, marked, rfl, rfl, rfl, rfl⟩

/-- The marked build's environment state: the session's token consumed and the Server's sessions moved. -/
theorem builtEnv_move (e : EnvState KemSK SplitBk) (session : ℕ) (coords : Coord) (material : MatCache 2)
    (result : (Option PqxdhServerRegistrationPublication.Response × PqxdhServerAuthEntryFactor.ServerState) ×
      List RawCtxSourceSend.SealContext) :
    SessionMove e.native.shared.2 (builtEnv e session coords material result).native.shared.2 ∧
      (builtEnv e session coords material result).native.shared.2.pending session = none := by
  refine ⟨⟨le_refl _, fun s _ present => ?_⟩, by simp [builtEnv, builtSettled, strip]⟩
  by_cases same : s = session
  · subst same
    simp [builtEnv, builtSettled, strip] at present
  · simpa [builtEnv, builtSettled, strip, Function.update_of_ne same] using present

/-- The marked build in capability form, from an admissible state at an allocated slot with a pending token whose World Server marker of the slot is unused: the session's token is consumed and the Server's sessions move; the owners are the stripped owners; the allocator and every ideal backend field but the Server install ghost are unchanged; and either nothing was installed (the ghost, the used markers and the seed table unchanged) or the ghost is at the marked coordinates, the slot's Server marker is set and its seed present, the table unchanged at every other slot. -/
theorem buildHidden_move (created : PqxdhLiveServerConstruction.Created Unit) (session : ℕ)
    (payload : Option Pqxdh.Bytes) (coords : Coord) (e : EnvState KemSK SplitBk) (w : PqxdhRecordLiftWorld.State 2)
    (good : Good created e w) (j : PqxdhRecordLiftInterface.Slot 2) (token : PqxdhServerRelatedRootConsumer.Returned)
    (allocated : e.backend.2.1.1 coords = some j) (pending : e.native.shared.2.pending session = some token)
    (unused : w.used j .server = false) :
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((buildHiddenEnv setup codec checks session payload coords).run e)).run w),
      SessionMove e.native.shared.2 result.1.2.native.shared.2 ∧ result.1.2.native.shared.2.pending session = none ∧
        result.1.2.native.owners = (strip e.native).owners ∧ result.1.2.backend.2.1 = e.backend.2.1 ∧
        result.1.2.backend.2.2 = { e.backend.2.2 with peer := result.1.2.backend.2.2.peer } ∧
        ((result.1.2.backend.2.2.peer = e.backend.2.2.peer ∧ result.2.used = w.used ∧ result.2.seeds.1 = w.seeds.1) ∨
          (∃ key, result.1.2.backend.2.2.peer = some (key, coords) ∧
            result.2.used = Function.update w.used j (Function.update (w.used j) .server true) ∧
            (result.2.seeds.1 j).isSome = true ∧ ∀ k, k ≠ j → result.2.seeds.1 k = w.seeds.1 k)) := by
  intro result member
  obtain ⟨world, found, _, _, _⟩ := good.server
  have mapped : (result.1, uncount result.2) ∈ support (Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
      ((buildHiddenEnv setup codec checks session payload coords).run e)).run w) := by
    rw [support_map]
    exact ⟨result, member, rfl⟩
  obtain ⟨material, log, cache, ⟨_, envEq, worldEq⟩ |
      ⟨response, candidate, seed, table, keyEq, _, seeded, _, other, _, envEq, worldEq⟩⟩ :=
    buildHidden_exact setup codec checks created session payload coords e w good j token allocated pending unused world
      found _ mapped
  · dsimp only at envEq
    rw [envEq]
    exact ⟨(builtEnv_move e session coords material _).1, (builtEnv_move e session coords material _).2, rfl, rfl, rfl,
      Or.inl ⟨rfl, congrArg (fun x => x.used) worldEq, congrArg (fun x => x.seeds.1) worldEq⟩⟩
  · dsimp only at envEq
    rw [envEq]
    have peerAt := (PqxdhServerRegistrationPublication.publish_fields e.native.shared.2.server candidate
      PqxdhDeploymentHiddenSplit.placeholderKernel ()).1
    refine ⟨(builtEnv_move e session coords material _).1, (builtEnv_move e session coords material _).2, rfl, rfl, rfl,
      Or.inr ⟨response.keyId, ?_, congrArg (fun x => x.used) worldEq, ?_, fun k ne => ?_⟩⟩
    · simp [builtEnv, publishedKey, keyEq, peerAt]
    · rw [show result.2.seeds = table from congrArg (fun x => x.seeds) worldEq, seeded]
      rfl
    · rw [show result.2.seeds = table from congrArg (fun x => x.seeds) worldEq]
      exact other k ne

open PqxdhDeploymentEnvironmentReal (fill_inactive good_matched) in
/-- Owner k's challenge finish in capability form, from an admissible state whose owner is in the `initSent` phase and whose World holds no Beacon marker: the Server's session counter and pending tokens are unchanged; the owner is terminal; the allocator moves with its counter raised by at most one; every ideal backend field but the Beacon install ghost is unchanged; and either nothing was installed (the ghost, the used markers and the seed table unchanged) or the ghost is at coordinates with a slot whose Beacon marker is set and whose seed is present, the table unchanged at every other slot. -/
theorem finishChallenge_move (created : PqxdhLiveServerConstruction.Created Unit) (p : Params KemSK count) (owner : ℕ)
    (raw : Pqxdh.Bytes) (e : EnvState KemSK SplitBk) (w : PqxdhRecordLiftWorld.State 2) (good : Good created e w)
    (initSentOwner : initSentAt e.native.owners owner = true) (unused : ∀ j, w.used j .beacon = false) :
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((finishChallengeEnv setup codec p owner raw).run e)).run w),
      result.1.2.native.shared.2.sessions = e.native.shared.2.sessions ∧
        result.1.2.native.shared.2.pending = e.native.shared.2.pending ∧
        terminalAt result.1.2.native.owners owner ∧
        AllocMove e.backend.2.1 result.1.2.backend.2.1 ∧ result.1.2.backend.2.1.2 ≤ e.backend.2.1.2 + 1 ∧
        result.1.2.backend.2.2 = { e.backend.2.2 with beacon := result.1.2.backend.2.2.beacon } ∧
        ((result.1.2.backend.2.2.beacon = e.backend.2.2.beacon ∧ result.2.used = w.used ∧
            result.2.seeds.1 = w.seeds.1) ∨
          (∃ c j, result.1.2.backend.2.2.beacon = some c ∧ result.1.2.backend.2.1.1 c = some j ∧
            result.2.used = Function.update w.used j (Function.update (w.used j) .beacon true) ∧
            (result.2.seeds.1 j).isSome = true ∧ ∀ k, k ≠ j → result.2.seeds.1 k = w.seeds.1 k)) := by
  rcases owned : e.native.owners[owner]? with _ | before
  · simp only [initSentAt, owned, Bool.false_eq_true] at initSentOwner
  rcases phase : before.beacon.phase with _ | _ | ⟨control, prekey, oneTime, kem⟩ | _ | _
  all_goals try (simp only [initSentAt, owned, phase, Bool.false_eq_true] at initSentOwner)
  have inactive : ¬ RawCtxBeaconLifecycle.Established before.beacon.phase := by
    rw [phase]
    simp only [RawCtxBeaconLifecycle.Established, not_false_eq_true]
  have initSent : PqxdhDeploymentEnvironment.inactiveTag before.beacon.phase = some .initSent := by rw [phase]; rfl
  obtain ⟨tag, worldPhase, projected, _⟩ := fill_inactive w _ (good_matched created e w good) owner before owned inactive
  have tagEq : tag = .initSent := by
    simp only [PqxdhRecordLiftBeacon.projectPhase, phase, PqxdhRecordLiftBeacon.Phase.inactive.injEq] at projected
    exact projected.symm
  subst tagEq
  have below : owner < e.native.owners.length := (List.getElem?_eq_some_iff.mp owned).1
  have terminalSet : ∀ (after : PqxdhRegistrationSchedule.Owner KemSK), PqxdhRegistrationSchedule.Terminal after →
      ∀ shared : NativeState KemSK, terminalAt (strip ⟨shared, e.native.owners.set owner after⟩).owners owner :=
    fun after terminal shared => (terminalAt_strip _ owner).2
      ⟨after, List.getElem?_set_self below, terminal⟩
  intro result member
  have mapped : (result.1, uncount result.2) ∈ support (Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
      ((finishChallengeEnv setup codec p owner raw).run e)).run w) := by
    rw [support_map]
    exact ⟨result, member, rfl⟩
  rcases finishChallenge_outcome setup codec p owner raw e w before control prekey oneTime kem owned phase worldPhase
    _ mapped with ⟨shared, staged, cache, _, game, _, _, outcome⟩ | ⟨pending, coords, read, j, readMember, slotted, hidden⟩
  · simp only [Prod.mk.injEq] at outcome
    obtain ⟨envEq, worldEq⟩ := outcome
    rw [envEq]
    exact ⟨congrArg (fun g => g.sessions) game, congrArg (fun g => g.pending) game,
      terminalSet _ (PqxdhRegistrationSchedule.finish_terminal control before staged) shared, AllocMove.refl _,
      Nat.le_succ _, rfl, Or.inl ⟨rfl, congrArg (fun x => x.used) worldEq, congrArg (fun x => x.seeds.1) worldEq⟩⟩
  · obtain ⟨move, counter, _⟩ := slotStep_move (lazyDummy (n := 2)) (.inr coords) (e.backend.2.1, (e.backend.1, ∅))
      read readMember
    obtain ⟨staged, cache', ⟨aborted, outcome⟩ | ⟨control', associatedData, kernel, seed, table, established, seeded, _,
        other, outcome⟩⟩ :=
      hiddenFinish_exact setup codec e owner control before pending coords read j w w.primitive.2 initSent worldPhase
        (unused j) _ hidden
    · simp only [Prod.mk.injEq] at outcome
      obtain ⟨envEq, worldEq⟩ := outcome
      rw [envEq]
      have closed : establishedAt (e.native.owners.set owner (PqxdhBeaconPhase2Publication.finish control before
          staged).2) owner = false := by
        simp only [establishedAt, List.getElem?_set_self below]
        cases afterPhase : (PqxdhBeaconPhase2Publication.finish control before staged).2.beacon.phase <;>
          simp_all [PqxdhDeploymentEnvironment.inactiveTag]
      refine ⟨rfl, rfl, terminalSet _ (PqxdhRegistrationSchedule.finish_terminal control before staged) _, move,
        counter, ?_, Or.inl ⟨?_, congrArg (fun x => x.used) worldEq, congrArg (fun x => x.seeds.1) worldEq⟩⟩
      · simp only [finishedEnv, hiddenBackend, closed, Bool.false_eq_true, ↓reduceIte]
      · simp only [finishedEnv, hiddenBackend, closed, Bool.false_eq_true, ↓reduceIte]
    · simp only [Prod.mk.injEq] at outcome
      obtain ⟨envEq, worldEq⟩ := outcome
      rw [envEq]
      have opened : establishedAt (e.native.owners.set owner (PqxdhBeaconPhase2Publication.finish control before
          staged).2) owner = true := by
        simp only [establishedAt, List.getElem?_set_self below, established]
      refine ⟨rfl, rfl, terminalSet _ (PqxdhRegistrationSchedule.finish_terminal control before staged) _, move,
        counter, ?_, Or.inr ⟨coords, j, ?_, slotted, congrArg (fun x => x.used) worldEq, ?_, fun k ne => ?_⟩⟩
      · simp only [finishedEnv, hiddenBackend, opened, ↓reduceIte]
      · simp only [finishedEnv, hiddenBackend, opened, ↓reduceIte, Option.some_or]
      · rw [show result.2.seeds = table from congrArg (fun x => x.seeds) worldEq, seeded]
        rfl
      · rw [show result.2.seeds = table from congrArg (fun x => x.seeds) worldEq]
        exact other k ne

end Exact

end BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.hidden_admin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.hidden_admin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.hiddenFree_of_noAdmin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.hiddenFree_of_noAdmin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.effects_keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.effects_keep

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.run_keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.run_keep

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.coins_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.coins_free

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.issue_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.issue_free

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.ownerEffect_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.ownerEffect_free

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.ownerChange_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.ownerChange_free

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.serverEffect_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.serverEffect_free

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.realStep_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.realStep_free

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.createPool_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.createPool_free

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.acceptSelected_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.acceptSelected_free

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.terminal_stripOwner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.terminal_stripOwner

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.terminalAt_strip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.terminalAt_strip

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.terminalAt_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.terminalAt_set

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.terminalAt_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.terminalAt_append

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.finished_keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.finished_keep

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.bundled_keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.bundled_keep

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.SessionMove.refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.SessionMove.refl

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.SessionMove.trans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.SessionMove.trans

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.SessionMove.of_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.SessionMove.of_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.world_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.world_support

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.hmacOracle_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.hmacOracle_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.nativeHmac_move' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.nativeHmac_move

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.acceptLogged_move' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.acceptLogged_move

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.realStep_move' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.realStep_move

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.createPool_move' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.createPool_move

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.AllocMove.refl' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.AllocMove.refl

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.AllocMove.trans' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.AllocMove.trans

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.slotStep_move' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.slotStep_move

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.slot_liftS' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.slot_liftS

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.run_keepsGood' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.run_keepsGood

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.client_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.client_root

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.tail_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.tail_root

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.romRoot_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.romRoot_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.auxiliary_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.auxiliary_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.slot_mapLiftS' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.slot_mapLiftS

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.tailSlots_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.tailSlots_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.tailSlots_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.tailSlots_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.serverTail_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.serverTail_none

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.acceptInactive_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.acceptInactive_facts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.acceptActive_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.acceptActive_facts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.acceptExposed_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.acceptExposed_facts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.lazy_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.lazy_other

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.buildHidden_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.buildHidden_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.hiddenFinish_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.hiddenFinish_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.acceptSelected_move' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.acceptSelected_move

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.builtEnv_move' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.builtEnv_move

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.buildHidden_move' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.buildHidden_move

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.finishChallenge_move' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts.finishChallenge_move
