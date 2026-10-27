import BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame

/-! The concrete protocol services do not read their private analysis ghost. The projection retains every protocol, table, component-interface and control field. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhJointIdentity PqxdhJointGapDh
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader WireResponse Table Result : Type}

/-- Only the analysis ghost is removed; all original protocol state remains. -/
def game (state : GameState KemSK) : GameState KemSK := { state with ghost := Ghost.empty }

/-- The table, session marks and every non-ghost field are retained. -/
def flat (state : FlatState KemSK Table) : FlatState KemSK Table := (game state.1, state.2)

/-- The designation latch is retained alongside the full projected source state. -/
def project (state : Local KemSK) : Local KemSK := (flat state.1, state.2)

/-- Ghost projection is idempotent. -/
theorem game_idempotent (state : GameState KemSK) : game (game state) = game state := rfl

/-- Projecting the complete local source state twice has no additional effect. -/
theorem project_idempotent (state : Local KemSK) : project (project state) = project state := rfl

/-- The actual source accept callback retains identical replies and every non-ghost field for any initial ghost. -/
theorem accept_flat (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (publicValue : PublicChallenge) (services : Services WireResponse Table)
    (raw : Pqxdh.Bytes) (state : FlatState KemSK Table) :
    Prod.map id flat <$> (acceptStep setup codec checks publicValue services raw).run state =
      Prod.map id flat <$> (acceptStep setup codec checks publicValue services raw).run (flat state) := by
  simp only [acceptStep, StateT.run, flat, game, map_bind]
  refine bind_congr fun collected => ?_
  cases collected.1 with
  | none => rfl
  | some input =>
      simp only []
      split
      · simp only [map_bind]
        refine bind_congr fun derived => ?_
        cases derived.1 <;> rfl
      · rfl

/-- Ghost projection of a whole probabilistic flat callback lifts through the unchanged actual coin interpreter. -/
theorem flat_coins (work : StateT (FlatState KemSK HiddenTable) ProbComp Result)
    (same : ∀ state, Prod.map id flat <$> work.run state = Prod.map id flat <$> work.run (flat state))
    (state : Local KemSK) :
    Prod.map id project <$> (flatCoins work).run state =
      Prod.map id project <$> (flatCoins work).run (project state) := by
  have lifted := congrArg (fun program => simulateQ PqxdhServerAuthCtxAmbient.coin
    ((fun result => (result.1, (result.2, state.2))) <$> program)) (same state.1)
  simpa only [flatCoins, localCoins, StateT.run, simulateQ_map, Functor.map_map,
    project, Prod.map_def, Function.comp_def] using lifted

/-- The executable acceptance compiler depends on every source field except its private ghost. -/
theorem accept_project (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (select : Bool) (raw : Pqxdh.Bytes)
    (state : Local KemSK) :
    Prod.map id project <$> (PqxdhServerAuthCtxState.accept setup codec checks context select raw).run state =
      Prod.map id project <$> (PqxdhServerAuthCtxState.accept setup codec checks context select raw).run (project state) :=
  flat_coins _ (accept_flat setup codec checks (context.publicValue setup) _ raw) state

/-- Actual public HMAC replies and complete table effects ignore the existing analysis ghost. -/
theorem hmac_flat (setup : Setup baseSpec KemSK) (services : Services WireResponse Table)
    (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) (state : FlatState KemSK Table) :
    Prod.map id flat <$> (hmacStep setup services key message).run state =
      Prod.map id flat <$> (hmacStep setup services key message).run (flat state) := by
  simp only [hmacStep, StateT.run, flat, game]
  split <;> simp only [map_bind, map_pure]
  · refine bind_congr fun result => ?_
    rfl
  · rfl

/-- The literal public-HMAC compiler retains the same source draws and reply under ghost projection. -/
theorem hmac_project (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) (state : Local KemSK) :
    Prod.map id project <$> (PqxdhServerAuthCtxState.hmac setup context key message).run state =
      Prod.map id project <$> (PqxdhServerAuthCtxState.hmac setup context key message).run (project state) :=
  flat_coins _ (hmac_flat setup (tableServices (WireResponse := Unit) setup context false) key message) state

/-- The actual builder settlement never reads prior source seal history or prior acceptance annotations. Native outcomes and component refusal retain every non-ghost field. -/
theorem build_post (session : Nat) (state : Local KemSK)
    (result : Option PqxdhServerAuthCtxBuild.Outcome × PqxdhServerAuthCtxBuild.Log) :
    Prod.map id project (PqxdhServerAuthCtxBuild.post session state result) =
      Prod.map id project (PqxdhServerAuthCtxBuild.post session (project state) result) := by
  rcases result with ⟨_ | outcome, log⟩ <;> rfl

/-- Whole native or selected builder callbacks preserve the same component program under ghost projection. -/
theorem build_after (session : Nat)
    (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec
      (Option PqxdhServerAuthCtxBuild.Outcome × PqxdhServerAuthCtxBuild.Log)) (state : Local KemSK) :
    Prod.map id project <$> (PqxdhServerAuthCtxBuild.after session work).run.run state =
      Prod.map id project <$> (PqxdhServerAuthCtxBuild.after session work).run.run (project state) := by
  simp only [PqxdhServerAuthCtxBuild.after, OptionT.run_mk, StateT.run, Functor.map_map]
  congr 1
  funext result
  exact build_post session state result

/-- Pending lookup, marked/ordinary routing and full source settlement ignore the old ghost. -/
theorem build_project (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (codec : Codec Reader WireResponse) (checks : Checks) (rest : PqxdhServerAuthCtxCalls.Residual)
    (session : Nat) (payload : Option Pqxdh.Bytes) (state : Local KemSK) :
    Prod.map id project <$> (PqxdhServerAuthCtxBuild.build source codec checks rest session payload).run.run state =
      Prod.map id project <$> (PqxdhServerAuthCtxBuild.build source codec checks rest session payload).run.run (project state) := by
  simp only [PqxdhServerAuthCtxBuild.build, OptionT.run_mk, StateT.run, project, flat, game]
  cases state.1.1.pending session with
  | none => rfl
  | some token =>
      simp only []
      split <;> exact build_after session _ state

/-- The literal Beacon final checks depend on the actual staged plaintext and phase, while old ghost contents affect only the new ghost. -/
theorem finish_complete (control : pqxdh.BeaconInitSent) (state : Local KemSK)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    Prod.map id project (PqxdhServerAuthCtxFinish.complete control state staged) =
      Prod.map id project (PqxdhServerAuthCtxFinish.complete control (project state) staged) := rfl

/-- The full post-root callback keeps every original component effect and optional plaintext before projected native completion. -/
theorem finish_after (control : pqxdh.BeaconInitSent)
    (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Option PqxdhBeaconPhase2Publication.Staged))
    (state : Local KemSK) :
    Prod.map id project <$> (PqxdhServerAuthCtxFinish.after control work).run state =
      Prod.map id project <$> (PqxdhServerAuthCtxFinish.after control work).run (project state) := by
  simp only [PqxdhServerAuthCtxFinish.after, StateT.run, Functor.map_map]
  congr 1

/-- Actual raw preparation, omitted-table routing and both optional post-root continuations never read the private analysis ghost. -/
theorem finish_project (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) (select : Bool)
    (raw : Pqxdh.Bytes) (state : Local KemSK) :
    Prod.map id project <$> (PqxdhServerAuthCtxFinish.finish setup codec context rest select raw).run state =
      Prod.map id project <$> (PqxdhServerAuthCtxFinish.finish setup codec context rest select raw).run (project state) := by
  simp only [PqxdhServerAuthCtxFinish.finish, StateT.run, project, flat, game]
  cases state.1.1.beacon.beacon.phase <;> simp only [map_pure]
  all_goals try rfl
  simp only [map_bind]
  refine bind_congr fun prepared => ?_
  cases prepared with
  | none => rfl
  | some pending =>
      simp only [map_bind]
      refine bind_congr fun derived => ?_
      cases derived.1 <;> simp only [PqxdhServerAuthCtxFinish.known, PqxdhServerAuthCtxFinish.selected,
        PqxdhServerAuthCtxFinish.after, Functor.map_map, map_pure] <;> rfl

/-- Optional lifting preserves a proved complete callback ghost projection. -/
theorem lifted_project (work : Program KemSK Result) (state : Local KemSK)
    (same : Prod.map id project <$> work.run state = Prod.map id project <$> work.run (project state)) :
    Prod.map id project <$> (OptionT.lift work).run.run state =
      Prod.map id project <$> (OptionT.lift work).run.run (project state) := by
  have mapped := congrArg (Functor.map (fun result => (some result.1, result.2))) same
  simpa only [OptionT.run_lift, bind_pure_comp, StateT.run_map, Functor.map_map,
    Prod.map_def, Function.comp_def, id_eq] using mapped

/-- Every literal API route ignores the private ghost, including failed native callbacks and arbitrary component replies. -/
theorem route_project (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (select : Bool) (query : ServerAuthSpec.Domain) (state : Local KemSK) :
    Prod.map id project <$> (PqxdhServerAuthCtxHandler.route setup codec checks context rest select query).run.run state =
      Prod.map id project <$> (PqxdhServerAuthCtxHandler.route setup codec checks context rest select query).run.run (project state) := by
  cases query with
  | inl coin =>
      apply lifted_project
      simp only [coins, StateT.run_lift]
      rfl
  | inr query =>
      cases query with
      | accept raw => exact lifted_project _ state (accept_project setup codec checks context select raw state)
      | hmac key message => exact lifted_project _ state (hmac_project setup context key message state)
      | build session payload => exact build_project setup.source codec checks rest session payload state
      | finish raw => exact lifted_project _ state (finish_project setup codec context rest select raw state)
      | hash bytes =>
          apply lifted_project
          simp only [PqxdhServerAuthCtxState.hash, StateT.run_lift]
          rfl
      | reveal keyId =>
          apply lifted_project
          rfl

/-- The source designation uses the original session counter and Beacon phase, never analysis history. -/
theorem designated_project (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (state : Local KemSK) : hiddenDesignated Q j query (project state).1 =
      hiddenDesignated Q j query state.1 := by
  cases query with
  | inl _ => rfl
  | inr query => cases query <;> rfl

/-- Sticky refusal and the one-shot designation latch preserve every non-ghost field and do not consult either the old or resulting ghost. -/
theorem settle_project (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (before : Local KemSK) (result : Result × Local KemSK) :
    Prod.map id project (PqxdhServerAuthCtxHandler.settle Q j query before result) =
      PqxdhServerAuthCtxHandler.settle Q j query (project before) (Prod.map id project result) := by
  simp only [PqxdhServerAuthCtxHandler.settle]
  rw [designated_project]
  by_cases bad : before.1.2.2.bad = true <;>
    simp only [keepHiddenBad, project, flat, bad, ite_true] <;> rfl

/-- The entire actual optional handler preserves the complete ghost-erased source state and all component requests for arbitrary replies. -/
theorem handler_project (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain) (state : Local KemSK) :
    Prod.map id project <$> (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j query).run.run state =
      Prod.map id project <$> (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j query).run.run (project state) := by
  have flag : (project state).2 = state.2 := rfl
  have same := congrArg (Functor.map (PqxdhServerAuthCtxHandler.settle Q j query (project state)))
    (route_project setup codec checks context rest (!state.2 && hiddenDesignated Q j query state.1) query state)
  simpa only [PqxdhServerAuthCtxHandler.handler, OptionT.run_mk, StateT.run, Functor.map_map,
    settle_project, designated_project, project_idempotent, flag] using same

/-- Keep the source-derived selected-session checkpoint while removing only the analysis ghost. -/
def tracked (state : Local KemSK × Option Nat) : Local KemSK × Option Nat := (project state.1, state.2)

/-- The checkpoint-preserving projection is idempotent. -/
theorem tracked_idempotent (state : Local KemSK × Option Nat) : tracked (tracked state) = tracked state := rfl

/-- The actual second-selected-session stop inspects only source counters and marks, not the private ghost. -/
theorem observe_project (query : ServerAuthSpec.Domain) (before : Local KemSK × Option Nat)
    (result : Option (ServerAuthSpec.Range query) × Local KemSK) :
    Prod.map id tracked (PqxdhServerAuthCtxStop.observe
      (fun state : Local KemSK => state.1.1.sessions) (fun state => state.1.2.1) query before result) =
      PqxdhServerAuthCtxStop.observe
        (fun state : Local KemSK => state.1.1.sessions) (fun state => state.1.2.1)
        query (tracked before) (Prod.map id project result) := by
  rcases result with ⟨_ | reply, after⟩ <;> rfl

/-- The complete executable stop wrapper keeps identical replies, optional refusals, counters, marks and component effects under ghost projection. -/
theorem stopped_project (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain) (state : Local KemSK × Option Nat) :
    Prod.map id tracked <$> (PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run.run state =
      Prod.map id tracked <$> (PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run.run (tracked state) := by
  have same := congrArg (Functor.map (PqxdhServerAuthCtxStop.observe
    (fun state : Local KemSK => state.1.1.sessions) (fun state => state.1.2.1) query (tracked state)))
      (handler_project setup codec checks context rest Q j query state.1)
  simpa only [PqxdhServerAuthCtxReserve.stopped, PqxdhServerAuthCtxStop.stopped,
    OptionT.run_mk, StateT.run, bind_pure_comp, Functor.map_map, observe_project,
    tracked_idempotent, show (tracked state).1 = project state.1 from rfl] using same

/-- Complete optional continuations preserve a proved idempotent state projection, before choosing any component interpreter. -/
theorem optional_project {Input Output State Answer : Type} {spec : OracleSpec Input}
    {target : OracleSpec Output} (eraseState : State → State)
    (idempotent : ∀ state, eraseState (eraseState state) = eraseState state)
    (handler : QueryImpl spec (OptionT (StateT State (OracleComp target))))
    (same : ∀ query state, Prod.map id eraseState <$> (handler query).run.run state =
      Prod.map id eraseState <$> (handler query).run.run (eraseState state))
    (work : OracleComp spec Answer) (state : State) :
    Prod.map id eraseState <$> (simulateQ handler work).run.run state =
      Prod.map id eraseState <$> (simulateQ handler work).run.run (eraseState state) := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, map_pure, Prod.map_apply, idempotent]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
        StateT.run_bind, map_bind]
      let resume : Option (spec.Range query) × State → OracleComp target (Option Answer × State) :=
        fun result => match result.1 with
          | none => pure (none, result.2)
          | some value => Prod.map id eraseState <$> (simulateQ handler (next value)).run.run result.2
      have factor (start : State) :
          (do
            let result ← (handler query).run.run start
            Prod.map id eraseState <$> (result.1.elim (pure none)
              (fun value => (simulateQ handler (next value)).run)).run result.2) =
            (Prod.map id eraseState <$> (handler query).run.run start) >>= resume := by
        rw [bind_map_left]
        refine bind_congr fun ⟨reply, after⟩ => ?_
        cases reply with
        | none => rfl
        | some value => exact ih value after
      rw [factor state, factor (eraseState state), same query state]

/-- The complete actual stopped adaptive client has the same public result and non-ghost state from the projected source state, with every component query unchanged. -/
theorem program_project (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result)
    (state : Local KemSK × Option Nat) :
    Prod.map id tracked <$> (simulateQ (PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) work).run.run state =
      Prod.map id tracked <$> (simulateQ (PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) work).run.run (tracked state) :=
  optional_project tracked tracked_idempotent _ (stopped_project setup codec checks context rest Q j) work state

/-- Two complete source states with the same operational fields give identical component programs and public client outputs after private ghost erasure. No source-origin, freshness, success or key-independence premise is used. -/
theorem program_congr (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result)
    (left right : Local KemSK × Option Nat) (same : tracked left = tracked right) :
    Prod.map id tracked <$> (simulateQ (PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) work).run.run left =
      Prod.map id tracked <$> (simulateQ (PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) work).run.run right := by
  rw [program_project setup codec checks context rest Q j work left,
    program_project setup codec checks context rest Q j work right, same]

/-- The concrete whole-client projection preserves every generalized all-replies component budget, including weighted bytes. Pure ghost bookkeeping is not claimed to have zero runtime cost. -/
theorem program_budget_iff {Budget : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result)
    (left right : Local KemSK × Option Nat) (same : tracked left = tracked right)
    (budget : Budget) (canQuery : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Budget → Prop)
    (cost : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Budget → Budget) :
    ((simulateQ (PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) work).run.run left).IsQueryBound budget canQuery cost ↔
      ((simulateQ (PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) work).run.run right).IsQueryBound budget canQuery cost := by
  have equation := program_congr setup codec checks context rest Q j work left right same
  have bills := congrArg (fun program => program.IsQueryBound budget canQuery cost) equation
  simpa only [isQueryBound_map_iff, eq_iff_iff] using bills

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.game_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.game_idempotent

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.project_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.project_idempotent

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.accept_flat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.accept_flat

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.flat_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.flat_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.accept_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.accept_project

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.hmac_flat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.hmac_flat

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.hmac_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.hmac_project

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.build_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.build_post

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.build_after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.build_after

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.build_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.build_project

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.finish_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.finish_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.finish_after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.finish_after

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.finish_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.finish_project

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.lifted_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.lifted_project

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.route_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.route_project

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.designated_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.designated_project

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.settle_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.settle_project

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.handler_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.handler_project

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.tracked_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.tracked_idempotent

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.observe_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.observe_project

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.stopped_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.stopped_project

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.optional_project' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.optional_project

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.program_project

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.program_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.program_congr

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.program_budget_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost.program_budget_iff

