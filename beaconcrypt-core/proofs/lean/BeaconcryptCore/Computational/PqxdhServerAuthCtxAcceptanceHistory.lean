import BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology
import BeaconcryptCore.Computational.PqxdhServerAuthStopTrace

/-! Chronology of the first actual acceptance in the factor-side source execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhJointIdentity PqxdhJointGapDh

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response τ : Type}

/-- The original acceptance observation is first-only and freezes actual log prefixes ending at the sole Beacon touch. This is execution instrumentation, not saved or restored protocol state. -/
structure History (game : GameState KemSK) : Prop where
  fresh : InitSent game → game.ghost.acceptance = none
  frozen : ∀ snap, game.ghost.acceptance = some snap →
    snap.touches <+: game.ghost.touches ∧ snap.seals <+: game.ghost.seals
  atomic : ∀ snap, game.ghost.acceptance = some snap →
    ∃ before message, snap.touches = before ++ [Touch.beacon message] ∧
      ∀ other, Touch.beacon other ∉ before

/-- A reached prepared finish captures exactly the current logs, even if its optional opening or final publication later fails. -/
theorem History.finishTouched (control : pqxdh.BeaconInitSent) (game : GameState KemSK)
    (history : History game) (shape : PqxdhServerAuthCtxStop.Shape game) (active : InitSent game)
    (message : PqxdhJointDhExtractFamily.Message) (cache : CtxRomAuth.CtxRO.QueryCache)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    History (finishOutcome control { game with
      ctx := cache
      ghost := { game.ghost with touches := game.ghost.touches ++ [.beacon message] } } staged).2 := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨control', prekey, oneTime, kem, phase⟩
    exact (finish_phase control game.beacon staged control' prekey oneTime kem phase).elim
  · intro snap found
    obtain ⟨fields, _, equal⟩ := Ghost.accept_new _ _ snap found (history.fresh active)
    simp only [equal, finishOutcome, Ghost.accept_touches, Ghost.accept_seals, List.prefix_refl, and_self]
  · intro snap found
    obtain ⟨fields, _, equal⟩ := Ghost.accept_new _ _ snap found (history.fresh active)
    exact ⟨game.ghost.touches, message, congrArg Snapshot.touches equal, shape.clean active⟩

/-- A step that retains the acceptance and extends its logs preserves the captured observation. -/
theorem History.transport (before after : GameState KemSK) (history : History before)
    (active : InitSent after → InitSent before)
    (acceptance : after.ghost.acceptance = before.ghost.acceptance)
    (touches : before.ghost.touches <+: after.ghost.touches)
    (seals : before.ghost.seals <+: after.ghost.seals) : History after := by
  exact ⟨fun live => acceptance.trans (history.fresh (active live)),
    fun snap found => let prior := history.frozen snap (acceptance.symm.trans found)
      ⟨prior.1.trans touches, prior.2.trans seals⟩,
    fun snap found => history.atomic snap (acceptance.symm.trans found)⟩

/-- Preparation failure finishes the phase without manufacturing an acceptance. -/
theorem History.finishNone (control : pqxdh.BeaconInitSent) (game : GameState KemSK)
    (history : History game) : History (finishOutcome control game none).2 := by
  apply History.transport game (finishOutcome control game none).2 history
    (fun active => by
      obtain ⟨control', prekey, oneTime, kem, phase⟩ := active
      exact (finish_phase control game.beacon none control' prekey oneTime kem phase).elim)
    rfl (List.prefix_refl _) (List.prefix_refl _)

/-- Actual raw finish establishes acceptance chronology on every preparation, derivation, opening and publication branch. -/
theorem finish_history (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (services : Services Response τ)
    (raw : Pqxdh.Bytes) (state : FlatState KemSK τ) (shape : PqxdhServerAuthCtxStop.Shape state.1) (history : History state.1)
    (result : Option Pqxdh.Bytes × FlatState KemSK τ)
    (supported : result ∈ support ((finishStep setup codec publicValue beaconSeed services raw).run state)) :
    History result.2.1 := by
  simp only [finishStep, StateT.run] at supported
  cases phase : state.1.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [phase, mem_support_bind_iff] at supported
      obtain ⟨prepared, _, supported⟩ := supported
      cases found : prepared with
      | none =>
          simp only [found, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact History.finishNone control state.1 history
      | some pending =>
          simp only [found, mem_support_bind_iff] at supported
          obtain ⟨derived, _, supported⟩ := supported
          cases reply : derived.1 with
          | rejected =>
              simp only [reply, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact History.finishTouched control state.1 history shape ⟨control, prekey, oneTime, kem, phase⟩ _ state.1.ctx none
          | root root =>
              simp only [reply, mem_support_bind_iff] at supported
              obtain ⟨staged, _, supported⟩ := supported
              simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact History.finishTouched control state.1 history shape ⟨control, prekey, oneTime, kem, phase⟩ _ staged.2.2 staged.1
          | hidden =>
              simp only [reply, mem_support_bind_iff] at supported
              obtain ⟨staged, _, supported⟩ := supported
              simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact History.finishTouched control state.1 history shape ⟨control, prekey, oneTime, kem, phase⟩ _ staged.2.2 staged.1
  | _ =>
      simp only [phase, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact history

/-- Reaching another Server allocation preserves the original acceptance and both logs. -/
theorem History.prefix (game : GameState KemSK) (history : History game) (consumed : List Pqxdh.Bytes) :
    History (acceptedPrefix game consumed) := by
  exact ⟨history.fresh, history.frozen, history.atomic⟩

/-- A completed Server derivation appends its source touch and retains the previous accepted observation. -/
theorem History.derived (setup : Setup baseSpec KemSK) (publicValue : PublicChallenge)
    (game : GameState KemSK) (history : History game) (index : Nat)
    (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding) (reply : Reply) :
    History (afterDerive setup publicValue index input reply game).2 := by
  cases reply <;> exact History.transport game _ history (fun active => active) rfl ⟨_, rfl⟩ (List.prefix_refl _)

/-- Every actual API branch preserves first-only acceptance and its source-log prefixes, without any assumptions on tail success or returned key bytes. -/
theorem skeleton_history (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (services : Services Response τ)
    (query : ServerAuthSpec.Domain) (state : FlatState KemSK τ) (shape : PqxdhServerAuthCtxStop.Shape state.1) (history : History state.1)
    (result : ServerAuthSpec.Range query × FlatState KemSK τ)
    (supported : result ∈ support ((skeleton setup codec checks publicValue beaconSeed services query).run state)) :
    History result.2.1 := by
  cases query with
  | inl coin =>
      simp only [skeleton, StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨value, _, rfl⟩ := supported
      exact history
  | inr query =>
      cases query with
      | accept raw =>
          simp only [skeleton, acceptStep, StateT.run, mem_support_bind_iff] at supported
          obtain ⟨collected, _, supported⟩ := supported
          cases found : collected.1 with
          | none =>
              simp only [found, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact History.prefix state.1 history collected.2
          | some input =>
              simp only [found] at supported
              split_ifs at supported with nonzero
              · obtain ⟨derived, _, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
                simp only [support_pure, Set.mem_singleton_iff] at supported
                subst supported
                exact History.derived setup publicValue (acceptedPrefix state.1 collected.2) (History.prefix state.1 history collected.2) state.1.sessions input derived.1
              · simp only [support_pure, Set.mem_singleton_iff] at supported
                subst supported
                exact History.prefix state.1 history collected.2
      | build session payload =>
          simp only [skeleton, buildStep, StateT.run] at supported
          cases found : state.1.pending session with
          | none =>
              simp only [found, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact history
          | some token =>
              simp only [found, mem_support_bind_iff] at supported
              obtain ⟨built, _, supported⟩ := supported
              simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact History.transport state.1 _ history (fun active => active) rfl (List.prefix_refl _) ⟨_, rfl⟩
      | finish raw =>
          exact finish_history setup codec publicValue beaconSeed services raw state shape history result supported
      | hmac key bytes =>
          simp only [skeleton, hmacStep, StateT.run] at supported
          split_ifs at supported with inside
          · obtain ⟨read, _, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
            simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            exact History.transport state.1 _ history (fun active => active) rfl ⟨_, rfl⟩ (List.prefix_refl _)
          · simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            exact history
      | hash bytes =>
          simp only [skeleton, hashStep, StateT.run, mem_support_bind_iff] at supported
          obtain ⟨read, _, supported⟩ := supported
          simp only [support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact ⟨history.fresh, history.frozen, history.atomic⟩
      | reveal key =>
          simp only [skeleton, StateT.run, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact history

/-- The exact designation latch and sticky table refusal preserve the original acceptance history. -/
theorem handler_history (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (services : Services Response HiddenTable)
    (query : ServerAuthSpec.Domain) (state : HiddenState KemSK) (shape : PqxdhServerAuthCtxStop.Shape state.1.1) (history : History state.1.1)
    (result : ServerAuthSpec.Range query × HiddenState KemSK)
    (supported : result ∈ support ((hiddenHandler setup codec checks context Q j services query).run state)) :
    History result.2.1.1 := by
  simp only [hiddenHandler, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨middle, supported, rfl⟩ := supported
  rw [keepHiddenBad_game]
  simp only [once, StateT.run] at supported
  split_ifs at supported
  all_goals
    simp only [latch, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨step, supported, rfl⟩ := supported
    exact skeleton_history setup codec checks (context.publicValue setup) context.beaconSeed _ query state.1 shape history step supported

/-- Every reply-dependent source continuation preserves the acceptance observation and actual chronology. -/
theorem program_history {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1))
    (services : Services Response HiddenTable) (program : OracleComp ServerAuthSpec α)
    (state : HiddenState KemSK) (shape : PqxdhServerAuthCtxStop.Shape state.1.1)
    (history : History state.1.1) (result : α × HiddenState KemSK)
    (supported : result ∈ support ((simulateQ (hiddenHandler setup codec checks context Q j services) program).run state)) :
    History result.2.1.1 := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact history
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨step, reached, supported⟩ := supported
    exact ih step.1 step.2
      (PqxdhServerAuthCtxStop.hidden_shape setup codec checks context Q j services query state shape step reached)
      (handler_history setup codec checks context Q j services query state shape history step reached) supported

/-- Literal empty acceptance instrumentation supplies the history invariant for every sampled context. -/
theorem History.initial (setup : Setup baseSpec KemSK) (context : Context KemSK) :
    History (contextState setup context) := by
  exact ⟨fun _ => rfl, (fun _ found => by cases found), (fun _ found => by cases found)⟩

/-- The complete original factor-side run has a first-only acceptance ending at the actual sole Beacon touch, with both captured logs retained as prefixes. -/
theorem run_history (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (revealSeed : Bool) (context : Context KemSK)
    (value : PqxdhServerAuthKeySchedule.Output) (Q : Nat) (j : Fin (Q + 1)) (result : HiddenState KemSK)
    (supported : result ∈ support (hiddenRun setup codec checks adversary revealSeed context Q j
      (factorServices setup codec checks context value))) : History result.1.1 := by
  simp only [hiddenRun, support_map, Set.mem_image] at supported
  obtain ⟨final, reached, rfl⟩ := supported
  exact program_history setup codec checks context Q j _ _ _
    (PqxdhServerAuthCtxStop.TraceInvariant.initial setup context Q j).shape
    (History.initial setup context) final reached

/-- The literal first Beacon request is identical in the recorded acceptance and in the current extended source log. -/
theorem History.first (game : GameState KemSK) (history : History game) (snap : Snapshot)
    (found : game.ghost.acceptance = some snap) :
    ∃ before message, snap.touches = before ++ [Touch.beacon message] ∧
      (∀ other, Touch.beacon other ∉ before) ∧ firstBeacon snap.touches = some message ∧
      firstBeacon game.ghost.touches = some message := by
  obtain ⟨before, message, equal, clean⟩ := history.atomic snap found
  have first : firstBeacon snap.touches = some message := by
    rw [equal]
    exact firstBeacon_after before [] message clean
  exact ⟨before, message, equal, clean, first,
    firstBeacon_prefix _ _ message first (history.frozen snap found).1⟩

/-- The full byte input observed at acceptance equals the final source input without root, key or encoding injectivity. -/
theorem History.input (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (game : GameState KemSK) (history : History game) (snap : Snapshot)
    (found : game.ghost.acceptance = some snap) :
    beaconInput setup context.seed context.scalar snap.touches =
      beaconInput setup context.seed context.scalar game.ghost.touches := by
  obtain ⟨_, message, _, _, first, later⟩ := history.first game snap found
  simp only [beaconInput, first, later]

/-- The concrete final acceptance observer preserves previous observations and both current logs. -/
theorem finish_grows (control : pqxdh.BeaconInitSent) (game : GameState KemSK)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    Grows game (finishOutcome control game staged).2 := by
  refine ⟨?_, ?_, fun snap found => Ghost.accept_keeps _ _ snap found, le_refl _⟩
  · rw [finishOutcome_touches]
  · change game.ghost.seals <+: (game.ghost.accept _).seals
    rw [Ghost.accept_seals]

/-- Touching the reached Beacon derivation and finishing retain the exact earlier source history. -/
theorem finishTouched_grows (control : pqxdh.BeaconInitSent) (game : GameState KemSK)
    (message : PqxdhJointDhExtractFamily.Message) (cache : CtxRomAuth.CtxRO.QueryCache)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    Grows game (finishOutcome control { game with
      ctx := cache
      ghost := { game.ghost with touches := game.ghost.touches ++ [.beacon message] } } staged).2 := by
  exact (show Grows game { game with
      ctx := cache
      ghost := { game.ghost with touches := game.ghost.touches ++ [.beacon message] } } from
      ⟨⟨_, rfl⟩, List.prefix_refl _, (fun _ found => found), le_refl _⟩).trans
    (finish_grows control _ staged)

/-- Every complete raw finish retains earlier touch/seal entries and an existing accepted observation. -/
theorem finish_step_grows (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (services : Services Response τ)
    (raw : Pqxdh.Bytes) (state : FlatState KemSK τ)
    (result : Option Pqxdh.Bytes × FlatState KemSK τ)
    (supported : result ∈ support ((finishStep setup codec publicValue beaconSeed services raw).run state)) :
    Grows state.1 result.2.1 := by
  simp only [finishStep, StateT.run] at supported
  cases phase : state.1.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [phase, mem_support_bind_iff] at supported
      obtain ⟨prepared, _, supported⟩ := supported
      cases found : prepared with
      | none =>
          simp only [found, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact finish_grows control state.1 none
      | some pending =>
          simp only [found, mem_support_bind_iff] at supported
          obtain ⟨derived, _, supported⟩ := supported
          cases reply : derived.1 with
          | rejected =>
              simp only [reply, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact finishTouched_grows control state.1 _ state.1.ctx none
          | root root =>
              simp only [reply, mem_support_bind_iff] at supported
              obtain ⟨staged, _, supported⟩ := supported
              simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact finishTouched_grows control state.1 _ staged.2.2 staged.1
          | hidden =>
              simp only [reply, mem_support_bind_iff] at supported
              obtain ⟨staged, _, supported⟩ := supported
              simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact finishTouched_grows control state.1 _ staged.2.2 staged.1
  | _ =>
      simp only [phase, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact Grows.refl state.1

/-- The actual complete source API only appends logs and never overwrites an accepted observation; the actual session-attempt counter never decreases. -/
theorem skeleton_grows (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (services : Services Response τ)
    (query : ServerAuthSpec.Domain) (state : FlatState KemSK τ)
    (result : ServerAuthSpec.Range query × FlatState KemSK τ)
    (supported : result ∈ support ((skeleton setup codec checks publicValue beaconSeed services query).run state)) :
    Grows state.1 result.2.1 := by
  cases query with
  | inl coin =>
      simp only [skeleton, StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨value, _, rfl⟩ := supported
      exact Grows.refl state.1
  | inr query =>
      cases query with
      | accept raw =>
          simp only [skeleton, acceptStep, StateT.run, mem_support_bind_iff] at supported
          obtain ⟨collected, _, supported⟩ := supported
          cases found : collected.1 with
          | none =>
              simp only [found, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact ⟨List.prefix_refl _, List.prefix_refl _, (fun _ found => found), Nat.le_succ _⟩
          | some input =>
              simp only [found] at supported
              split_ifs at supported with nonzero
              · obtain ⟨derived, _, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
                simp only [support_pure, Set.mem_singleton_iff] at supported
                subst supported
                cases derived.1 <;> exact ⟨⟨_, rfl⟩, List.prefix_refl _, (fun _ found => found), Nat.le_succ _⟩
              · simp only [support_pure, Set.mem_singleton_iff] at supported
                subst supported
                exact ⟨List.prefix_refl _, List.prefix_refl _, (fun _ found => found), Nat.le_succ _⟩
      | build session payload =>
          simp only [skeleton, buildStep, StateT.run] at supported
          cases found : state.1.pending session with
          | none =>
              simp only [found, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact Grows.refl state.1
          | some token =>
              simp only [found, mem_support_bind_iff] at supported
              obtain ⟨built, _, supported⟩ := supported
              simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact ⟨List.prefix_refl _, ⟨_, rfl⟩, (fun _ found => found), le_refl _⟩
      | finish raw =>
          exact finish_step_grows setup codec publicValue beaconSeed services raw state result supported
      | hmac key bytes =>
          simp only [skeleton, hmacStep, StateT.run] at supported
          split_ifs at supported with inside
          · obtain ⟨read, _, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
            simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            exact ⟨⟨_, rfl⟩, List.prefix_refl _, (fun _ found => found), le_refl _⟩
          · simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            exact Grows.refl state.1
      | hash bytes =>
          simp only [skeleton, hashStep, StateT.run, mem_support_bind_iff] at supported
          obtain ⟨read, _, supported⟩ := supported
          simp only [support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact ⟨List.prefix_refl _, List.prefix_refl _, (fun _ found => found), le_refl _⟩
      | reveal key =>
          simp only [skeleton, StateT.run, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact Grows.refl state.1

/-- Actual one-shot selection and sticky refusal retain the exact monotone source observations. -/
theorem handler_grows (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (services : Services Response HiddenTable)
    (query : ServerAuthSpec.Domain) (state : HiddenState KemSK)
    (result : ServerAuthSpec.Range query × HiddenState KemSK)
    (supported : result ∈ support ((hiddenHandler setup codec checks context Q j services query).run state)) :
    Grows state.1.1 result.2.1.1 := by
  simp only [hiddenHandler, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨middle, supported, rfl⟩ := supported
  rw [keepHiddenBad_game]
  simp only [once, StateT.run] at supported
  split_ifs at supported
  all_goals
    simp only [latch, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨step, supported, rfl⟩ := supported
    exact skeleton_grows setup codec checks (context.publicValue setup) context.beaconSeed _ query state.1 step supported

/-- Every adaptive source suffix preserves previous source receipts and the existing acceptance. -/
theorem program_grows {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1))
    (services : Services Response HiddenTable) (program : OracleComp ServerAuthSpec α)
    (state : HiddenState KemSK) (result : α × HiddenState KemSK)
    (supported : result ∈ support ((simulateQ (hiddenHandler setup codec checks context Q j services) program).run state)) :
    Grows state.1.1 result.2.1.1 := by
  exact run_rel _ (fun (before after : HiddenState KemSK) => Grows before.1.1 after.1.1)
    (fun state => Grows.refl state.1.1) (fun _ _ _ first second => first.trans second)
    (fun query before after reached => handler_grows setup codec checks context Q j services query before after reached)
    program state result supported

/-- Later source traffic cannot change W1/W2 once the actual accepted observation has been recorded. -/
theorem accepted_suffix {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1))
    (services : Services Response HiddenTable) (program : OracleComp ServerAuthSpec α)
    (state : HiddenState KemSK) (snap : Snapshot) (accepted : state.1.1.ghost.acceptance = some snap)
    (result : α × HiddenState KemSK)
    (supported : result ∈ support ((simulateQ (hiddenHandler setup codec checks context Q j services) program).run state)) :
    (W1 setup context.seed context.scalar result.2.1.1.ghost ∨ W2 setup context.seed context.scalar result.2.1.1.ghost) ↔
      (W1 setup context.seed context.scalar state.1.1.ghost ∨ W2 setup context.seed context.scalar state.1.1.ghost) := by
  have kept := (program_grows setup codec checks context Q j services program state result supported).acceptance snap accepted
  simp only [W1, W2, kept, accepted]

end BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.History.finishTouched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.History.finishTouched
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.History.transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.History.transport
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.History.finishNone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.History.finishNone
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.finish_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.finish_history
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.History.prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.History.prefix
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.History.derived' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.History.derived
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.skeleton_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.skeleton_history
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.handler_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.handler_history
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.program_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.program_history
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.History.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.History.initial
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.run_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.run_history
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.History.first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.History.first
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.History.input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.History.input
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.finish_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.finish_grows
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.finishTouched_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.finishTouched_grows
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.finish_step_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.finish_step_grows
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.skeleton_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.skeleton_grows
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.handler_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.handler_grows
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.program_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.program_grows
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.accepted_suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory.accepted_suffix
