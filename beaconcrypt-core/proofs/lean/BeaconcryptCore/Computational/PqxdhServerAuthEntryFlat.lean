import BeaconcryptCore.Computational.PqxdhServerAuthEntrySimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment
open PqxdhJointIdentity PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhJointGapDh (DhInterface ScalarBytes PublicChallenge)
open PqxdhJointDhExtractRoot (RootSpec)
open PqxdhRootTableInitialization (rootArray)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response φ τ : Type}

/-! ## Interpreting game computations under a family handler -/

section Interp
variable (family : QueryImpl RootSpec (StateT φ ProbComp))

/-- A game computation interpreted under a family handler, as one computation on the pair of the game state and the family state. -/
def interp {α : Type} (work : Game KemSK α) : StateT (GameState KemSK × φ) ProbComp α :=
  fun state => (fun result => (result.1.1, (result.1.2, result.2))) <$> (simulateQ family (work.run state.1)).run state.2

/-- Interpretation keeps `pure`. -/
theorem interp_pure {α : Type} (value : α) : interp family (pure value : Game KemSK α) = pure value := by
  funext state
  simp [interp, StateT.run_pure]
  rfl

/-- Interpretation keeps `bind`. -/
theorem interp_bind {α β : Type} (first : Game KemSK α) (next : α → Game KemSK β) :
    interp family (first >>= next) = interp family first >>= fun value => interp family (next value) := by
  funext state
  simp only [interp, StateT.run_bind, simulateQ_bind, map_bind]
  change _ = (fun result => (result.1.1, (result.1.2, result.2))) <$> (simulateQ family (first.run state.1)).run state.2 >>= _
  simp only [bind_map_left]
  rfl

/-- Interpretation of a game-state read. -/
theorem interp_get : interp family (get : Game KemSK (GameState KemSK)) = fun state => pure (state.1, state) := by
  funext state
  simp [interp]

/-- Interpretation of a game-state write. -/
theorem interp_set (game : GameState KemSK) :
    interp family (set game : Game KemSK Unit) = fun state => pure ((), (game, state.2)) := by
  funext state
  simp [interp]

/-- Interpretation of a game-state update. -/
theorem interp_modify (update : GameState KemSK → GameState KemSK) :
    interp family (modify update : Game KemSK Unit) = fun state => pure ((), (update state.1, state.2)) := by
  funext state
  simp [interp]

/-- Interpretation of one forwarded family request. -/
theorem interp_forward (query : RootSpec.Domain) :
    interp family (forwardFamily query : Game KemSK (RootSpec.Range query)) =
      fun state => (fun result => (result.1, (state.1, result.2))) <$> (family query).run state.2 := by
  funext state
  simp [interp, forwardFamily]

/-- A family handler forwards coin queries: it samples uniformly and leaves the family state unchanged. -/
def CoinForward : Prop :=
  ∀ coin state, (family (.inl coin)).run state = (fun value => (value, state)) <$> (unifSpec.query coin : ProbComp _)

variable {family}

/-- Under a coin-forwarding family, lifted coins run the probabilistic computation itself. -/
theorem family_coins (forward : CoinForward family) {α : Type} (work : ProbComp α) (state : φ) :
    (simulateQ family (familyCoins work)).run state = (fun value => (value, state)) <$> work := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp [familyCoins]
  | query_bind query next ih =>
      simp only [familyCoins, simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at ih ⊢
      rw [forward query state]
      simp only [bind_map_left, ih, map_bind]

/-- Interpretation of lifted coins. -/
theorem interp_liftCoins (forward : CoinForward family) {α : Type} (work : ProbComp α) :
    interp family (liftCoins work : Game KemSK α) = fun state => (fun value => (value, state)) <$> work := by
  funext state
  simp only [interp, liftCoins, StateT.run_lift, simulateQ_bind, simulateQ_pure, StateT.run_bind,
    family_coins forward, bind_map_left, StateT.run_pure, map_bind, map_pure]
  simp [map_eq_bind_pure_comp]

/-- Interpretation commutes with simulation: an interpreted simulation is the simulation of the interpreted handler. -/
theorem interp_simulateQ {ι' : Type} {spec : OracleSpec ι'} {α : Type} (impl : QueryImpl spec (Game KemSK))
    (work : OracleComp spec α) :
    interp family (simulateQ impl work) = simulateQ (fun query => interp family (impl query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, interp_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, interp_bind, ih]

/-- Interpretation of work on the shared BLAKE2b cache. -/
theorem interp_onCtx (forward : CoinForward family) {α : Type}
    (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp α) :
    interp family (onCtx work : Game KemSK α) = fun state =>
      (fun result => (result.1, ({ state.1 with ctx := result.2.2 }, state.2))) <$> work.run ((), state.1.ctx) := by
  funext state
  change (fun result => (result.1.1, (result.1.2, result.2))) <$> (simulateQ family
    (familyCoins (work.run ((), state.1.ctx)) >>= fun result =>
      pure (result.1, { state.1 with ctx := result.2.2 }))).run state.2 = _
  rw [simulateQ_bind, StateT.run_bind, family_coins forward]
  simp only [bind_map_left, simulateQ_pure, StateT.run_pure, map_bind, map_pure]
  rw [map_eq_bind_pure_comp]
  rfl

end Interp

/-- The composed Extract random-oracle family forwards coins. -/
theorem rom_coinForward (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed)
    (scalar : ScalarBytes) :
    CoinForward (PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar ∘ₛ PqxdhJointDhExtractRoot.reduction) := by
  intro coin state
  rw [(PqxdhExtractRomFamily.rom_forward hmac joint dh seed scalar).1 coin]
  simp [PqxdhExtractRomFamily.romImpl, StateT.run, map_eq_bind_pure_comp]

/-! ## The real experiment as a skeleton run -/

/-- The projection of a flat real state onto a skeleton state: no marks, and the family's table without its history. -/
def project (state : GameState KemSK × PqxdhJointDhExtractFamily.State) : FlatState KemSK HmacOracle.QueryCache :=
  (state.1, fun _ => false, state.2.cache)

theorem derive_project (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (message : PqxdhJointDhExtractFamily.Message) (state : PqxdhJointDhExtractFamily.State) :
    (fun result => (result.1, result.2.cache)) <$>
      ((PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ
        PqxdhJointDhExtractRoot.reduction) (.inr (.derive message))).run state =
      (fun result => (result.1.value, result.2)) <$>
        (realDerive setup.hmac setup.joint setup.dh seed scalar message).run state.cache := by
  rw [PqxdhExtractRomFamily.rom_root]
  unfold realDerive
  cases PqxdhJointDhExtractFamily.input setup.joint setup.dh seed scalar message with
  | none => simp [Reply.value, StateT.run]
  | some bytes => simp [Functor.map_map, Reply.value, StateT.run]

section RunForms
variable (family : QueryImpl RootSpec (StateT PqxdhJointDhExtractFamily.State ProbComp))

theorem interp_run_pure {α : Type} (value : α) (state : GameState KemSK × PqxdhJointDhExtractFamily.State) :
    (interp family (pure value : Game KemSK α)).run state = pure (value, state) := by
  rw [interp_pure]; rfl

theorem interp_run_forward (query : RootSpec.Domain) (state : GameState KemSK × PqxdhJointDhExtractFamily.State) :
    (interp family (forwardFamily query : Game KemSK (RootSpec.Range query))).run state =
      (fun result => (result.1, (state.1, result.2))) <$> (family query).run state.2 := by
  rw [interp_forward]; rfl

theorem interp_run_modify (update : GameState KemSK → GameState KemSK)
    (state : GameState KemSK × PqxdhJointDhExtractFamily.State) :
    (interp family (modify update : Game KemSK Unit)).run state = pure ((), (update state.1, state.2)) := by
  rw [interp_modify]; rfl

theorem interp_run_get (state : GameState KemSK × PqxdhJointDhExtractFamily.State) :
    (interp family (get : Game KemSK (GameState KemSK))).run state = pure (state.1, state) := by
  rw [interp_get]; rfl

theorem interp_run_set (game : GameState KemSK) (state : GameState KemSK × PqxdhJointDhExtractFamily.State) :
    (interp family (set game : Game KemSK Unit)).run state = pure ((), (game, state.2)) := by
  rw [interp_set]; rfl

theorem interp_run_liftCoins (forward : CoinForward family) {α : Type} (work : ProbComp α)
    (state : GameState KemSK × PqxdhJointDhExtractFamily.State) :
    (interp family (liftCoins work : Game KemSK α)).run state = (fun value => (value, state)) <$> work := by
  rw [interp_liftCoins forward]; rfl

theorem interp_run_map {α β : Type} (update : α → β) (work : Game KemSK α)
    (state : GameState KemSK × PqxdhJointDhExtractFamily.State) :
    (interp family (update <$> work)).run state =
      (fun result => (update result.1, result.2)) <$> (interp family work).run state := by
  rw [map_eq_bind_pure_comp, interp_bind, StateT.run_bind, map_eq_bind_pure_comp]
  refine bind_congr fun result => ?_
  simp only [Function.comp_apply, interp_run_pure]

theorem client_run_flat (index : Nat) (serverBinding : pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding)
    (state : GameState KemSK × PqxdhJointDhExtractFamily.State) :
    (simulateQ (fun query => interp family (sessionImpl index query))
      (PqxdhServerRelatedRootConsumer.client serverBinding input)).run state = by
      classical
      exact if PqxdhServerRelatedRootInput.localNonzero input then
        (do
          let derived ← (family (.inr (.derive (PqxdhServerRelatedRootInput.message input)))).run state.2
          let touched : GameState KemSK := { state.1 with ghost := { state.1.ghost with touches :=
            state.1.ghost.touches ++ [Touch.session index (PqxdhServerRelatedRootInput.message input) derived.1] } }
          match derived.1 with
          | none => pure (ok none, (touched, derived.2))
          | some root =>
              let token := PqxdhServerClearedRoot.pending serverBinding input
              pure (ok (some ⟨root, token⟩), ({ touched with server := { touched.server with
                consumed := touched.server.consumed ++ [absBytes token.registration_id.bytes] } }, derived.2)))
      else pure (ok none, state) := by
  unfold PqxdhServerRelatedRootConsumer.client
  by_cases valid : PqxdhServerRelatedRootInput.localNonzero input
  · simp only [valid, not_true_eq_false, ite_false, ite_true, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    simp only [sessionImpl, sessionFamily, recordTouch, interp_bind, StateT.run_bind, interp_run_pure,
      interp_run_forward, interp_run_modify, pure_bind, bind_map_left, bind_assoc]
    refine bind_congr fun derived => ?_
    rcases derived with ⟨_ | root, after⟩
    · simp only [simulateQ_pure, StateT.run_pure]
    · simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure]
      rfl
  · simp only [valid, not_false_eq_true, ite_true, ite_false, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
      StateT.run_bind, StateT.run_pure, sessionImpl, interp_run_pure, pure_bind]

end RunForms

open OracleComp.ProgramLogic.Relational in
theorem derive_couple (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (message : PqxdhJointDhExtractFamily.Message) (state : PqxdhJointDhExtractFamily.State) :
    RelTriple (((PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ
        PqxdhJointDhExtractRoot.reduction) (.inr (.derive message))).run state)
      ((realDerive setup.hmac setup.joint setup.dh seed scalar message).run state.cache)
      (fun left right => left.1 = right.1.value ∧ left.2.cache = right.2 ∧ right.1.isHidden = false) := by
  rw [PqxdhExtractRomFamily.rom_root]
  unfold realDerive
  cases PqxdhJointDhExtractFamily.input setup.joint setup.dh seed scalar message with
  | none => exact relTriple_pure_pure ⟨rfl, rfl, rfl⟩
  | some bytes =>
      change RelTriple (_ <$> _) (_ <$> _) _
      exact relTriple_map_same _ _ _ _ fun read _ => ⟨rfl, rfl, rfl⟩

open OracleComp.ProgramLogic.Relational in
theorem accept_couple (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (seed : IdentitySeed) (scalar : ScalarBytes) (raw : Pqxdh.Bytes)
    (state : GameState KemSK × PqxdhJointDhExtractFamily.State) :
    RelTriple ((interp (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ
        PqxdhJointDhExtractRoot.reduction) (acceptOracle setup codec checks publicValue raw)).run state)
      ((acceptStep setup codec checks publicValue (realServices seed scalar setup codec checks) raw).run
        (project state))
      (fun left right => left.1 = right.1 ∧ right.2 = project left.2) := by
  have forward := rom_coinForward setup.hmac setup.joint setup.dh seed scalar
  unfold acceptOracle
  simp only [interp_bind, StateT.run_bind, interp_run_get, interp_run_liftCoins _ forward, interp_run_set,
    pure_bind, bind_map_left, project]
  refine relTriple_bind (relTriple_refl _) fun collected other same => ?_
  cases same
  rcases collected with ⟨_ | input, consumed⟩
  · simp only [interp_run_pure]
    exact relTriple_pure_pure ⟨rfl, rfl⟩
  · simp only [interp_bind, StateT.run_bind, interp_simulateQ, client_run_flat]
    by_cases valid : PqxdhServerRelatedRootInput.localNonzero input
    · simp only [valid, ite_true, bind_assoc]
      refine relTriple_bind (derive_couple setup seed scalar _ state.2) fun left right related => ?_
      obtain ⟨replyEq, cacheEq, visible⟩ := related
      rcases left with ⟨leftReply, leftFamily⟩
      rcases right with ⟨reply, cache⟩
      dsimp only at replyEq cacheEq visible ⊢
      subst replyEq cacheEq
      cases reply with
      | rejected =>
          simp only [Reply.value, Reply.isHidden, afterDerive]
          exact relTriple_pure_pure ⟨rfl, rfl⟩
      | root value =>
          simp only [Reply.value, Reply.isHidden, afterDerive]
          exact relTriple_pure_pure ⟨rfl, rfl⟩
      | hidden => simp [Reply.isHidden] at visible
    · simp only [valid, ite_false, pure_bind, interp_run_pure]
      exact relTriple_pure_pure ⟨rfl, rfl⟩

theorem interp_run {φ α : Type} (family : QueryImpl RootSpec (StateT φ ProbComp)) (work : Game KemSK α)
    (state : GameState KemSK × φ) :
    (interp family work).run state =
      (fun result => (result.1.1, (result.1.2, result.2))) <$> (simulateQ family (work.run state.1)).run state.2 :=
  rfl

theorem hmacStep_run {τ : Type} (setup : Setup baseSpec KemSK) (svc : Services Response τ) (key : HmacBlock)
    (message : Pqxdh.Bytes) (state : FlatState KemSK τ) :
    (hmacStep setup svc key message).run state =
      if key = zeroSalt ∧ message.length = 192 then do
        let read ← (svc.table message).run state.2.2
        pure (read.1, ({ state.1 with ghost := { state.1.ghost with
          touches := state.1.ghost.touches ++ [Touch.adversary message] } }, state.2.1, read.2))
      else pure (setup.hmac.eval key message, state) :=
  rfl

theorem buildStep_run {τ : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (svc : Services Response τ) (session : Nat) (payload : Option Pqxdh.Bytes) (state : FlatState KemSK τ) :
    (buildStep setup codec checks svc session payload).run state =
      (match state.1.pending session with
      | none => pure (none, state)
      | some token => do
          let result ← (if state.2.1 session then svc.hiddenBuild token payload state.1.server
            else simulateQ (tailImpl setup codec checks)
              (PqxdhServerRegistrationPublication.build setup.source token.pending token.root payload ()
                state.1.server)).run ([], state.1.ctx)
          let after := afterBuild session state.1 result
          pure (after.1, (after.2, state.2))) :=
  rfl

theorem interp_run_onCtx_simulateQ (family : QueryImpl RootSpec (StateT PqxdhJointDhExtractFamily.State ProbComp))
    (forward : CoinForward family) {ι' : Type} {spec : OracleSpec ι'} {α : Type}
    (impl : QueryImpl spec (StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp)) (work : OracleComp spec α)
    (state : GameState KemSK × PqxdhJointDhExtractFamily.State) :
    (interp family (simulateQ (fun query => (onCtx (impl query) : Game KemSK _)) work)).run state =
      (fun result => (result.1, ({ state.1 with ctx := result.2.2 }, state.2))) <$>
        (simulateQ impl work).run ((), state.1.ctx) := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, interp_run_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, interp_bind, StateT.run_bind, map_bind]
      rw [interp_onCtx forward]
      change ((fun result => (result.1, ({ state.1 with ctx := result.2.2 }, state.2))) <$>
        (impl query).run ((), state.1.ctx)) >>= _ = _
      rw [bind_map_left]
      refine bind_congr fun result => ?_
      rw [ih]

theorem stage_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (beaconSeed : IdentitySeed)
    (publicValue : PublicChallenge) (control : pqxdh.BeaconInitSent) (identity : Unit) (oneTime : Unit ⊕ ScalarBytes)
    (kem : KemSK) (raw : Pqxdh.Bytes) :
    simulateQ (stageImpl setup codec beaconSeed)
        (PqxdhPhase2DhStage.stage publicValue codec.frameRead control identity oneTime kem raw) =
      liftCoins ((beaconPrefix setup codec beaconSeed control identity oneTime kem raw).run' ()) >>= fun prepared =>
        match prepared with
        | none => pure none
        | some pending =>
            recordTouch (Touch.beacon (PqxdhJointDhExtractRoot.beaconMessage publicValue pending.collected)) >>= fun _ =>
            forwardFamily (.inr (.derive (PqxdhJointDhExtractRoot.beaconMessage publicValue pending.collected))) >>=
              fun reply =>
            match reply with
            | none => pure none
            | some root => simulateQ (fun query => onCtx (beaconNative setup codec query))
                (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead pending (rootArray root)) := by
  simp only [PqxdhPhase2DhStage.stage, simulateQ_bind]
  rw [← QueryImpl.simulateQ_compose]
  have prefixEq : stageImpl setup codec beaconSeed ∘ₛ PqxdhPhase2DhStage.prefixLift =
      liftUnit (PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain (beaconAuxUnit setup codec beaconSeed)
        (fun _ => pure ())) := by
    funext query
    exact simulateQ_spec_query (stageImpl setup codec beaconSeed) _
  rw [prefixEq, simulateQ_liftUnit]
  refine bind_congr fun prepared => ?_
  cases prepared with
  | none => simp only [simulateQ_pure]
  | some pending =>
      dsimp only
      rw [← QueryImpl.simulateQ_compose]
      simp only [PqxdhPhase2DhRootConsumer.tail, simulateQ_bind]
      rw [← QueryImpl.simulateQ_compose]
      have rootEq : (stageImpl setup codec beaconSeed ∘ₛ PqxdhPhase2DhStage.tailLift) ∘ₛ
          PqxdhPhase2DhRootConsumer.rootLift = beaconFamily := by
        funext query
        simp only [QueryImpl.apply_compose, PqxdhPhase2DhRootConsumer.rootLift, PqxdhPhase2DhStage.tailLift,
          simulateQ_spec_query]
        rfl
      rw [rootEq]
      simp only [PqxdhPhase2DhRootConsumer.root, simulateQ_map, simulateQ_spec_query, beaconFamily, bind_map_left,
        bind_assoc]
      refine bind_congr fun _ => bind_congr fun reply => ?_
      cases reply with
      | none => simp only [Option.map_none, simulateQ_pure]
      | some root =>
          simp only [Option.map_some]
          rw [← QueryImpl.simulateQ_compose]
          have nativeEq : (stageImpl setup codec beaconSeed ∘ₛ PqxdhPhase2DhStage.tailLift) ∘ₛ
              PqxdhPhase2DhRootConsumer.nativeLift = fun query => onCtx (beaconNative setup codec query) := by
            funext query
            simp only [QueryImpl.apply_compose, PqxdhPhase2DhRootConsumer.nativeLift, PqxdhPhase2DhStage.tailLift,
              simulateQ_spec_query]
            rfl
          rw [nativeEq]

theorem finishStep_run {τ : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (svc : Services Response τ) (raw : Pqxdh.Bytes)
    (state : FlatState KemSK τ) :
    (finishStep setup codec publicValue beaconSeed svc raw).run state =
      (match state.1.beacon.beacon.phase with
      | .initSent control _ oneTime kem => do
          let prepared ← (beaconPrefix setup codec beaconSeed control state.1.beacon.beacon.identity oneTime kem
            raw).run' ()
          match prepared with
          | none =>
              let outcome := finishOutcome control state.1 none
              pure (outcome.1, (outcome.2, state.2))
          | some pending => do
              let message := PqxdhJointDhExtractRoot.beaconMessage publicValue pending.collected
              let game : GameState KemSK := { state.1 with ghost := { state.1.ghost with
                touches := state.1.ghost.touches ++ [Touch.beacon message] } }
              let derived ← (svc.derive message).run state.2.2
              match derived.1 with
              | .rejected =>
                  let outcome := finishOutcome control game none
                  pure (outcome.1, (outcome.2, state.2.1, derived.2))
              | .root root => do
                  let staged ← (simulateQ (beaconNative setup codec)
                    (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead pending (rootArray root))).run ((), game.ctx)
                  let outcome := finishOutcome control { game with ctx := staged.2.2 } staged.1
                  pure (outcome.1, (outcome.2, state.2.1, derived.2))
              | .hidden => do
                  let staged ← (svc.hiddenAfter pending).run ((), game.ctx)
                  let outcome := finishOutcome control { game with ctx := staged.2.2 } staged.1
                  pure (outcome.1, (outcome.2, state.2.1, derived.2))
      | _ => pure (none, state)) :=
  rfl

section FlatSteps
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (seed : IdentitySeed) (scalar : ScalarBytes)

theorem coin_couple (coin : ℕ) (state : GameState KemSK × PqxdhJointDhExtractFamily.State) :
    RelTriple ((interp (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ
        PqxdhJointDhExtractRoot.reduction) (authHandler setup codec checks publicValue beaconSeed (.inl coin))).run state)
      ((skeleton setup codec checks publicValue beaconSeed (realServices seed scalar setup codec checks) (.inl coin)).run
        (project state))
      (fun left right => left.1 = right.1 ∧ right.2 = project left.2) := by
  change RelTriple ((interp _ (forwardFamily (.inl coin))).run state) _ _
  rw [interp_run_forward, rom_coinForward, Functor.map_map]
  exact relTriple_map_same _ _ _ _ fun value _ => ⟨rfl, rfl⟩

theorem reveal_couple (keyId : Std.U64) (state : GameState KemSK × PqxdhJointDhExtractFamily.State) :
    RelTriple ((interp (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ
        PqxdhJointDhExtractRoot.reduction)
          (authHandler setup codec checks publicValue beaconSeed (.inr (.reveal keyId)))).run state)
      ((skeleton setup codec checks publicValue beaconSeed (realServices seed scalar setup codec checks)
        (.inr (.reveal keyId))).run (project state))
      (fun left right => left.1 = right.1 ∧ right.2 = project left.2) := by
  have handler : authHandler setup codec checks publicValue beaconSeed (.inr (.reveal keyId)) =
      (fun state => pure (revealKernel keyId state, state) : Game KemSK _) := rfl
  rw [handler]
  simp only [interp, StateT.run, simulateQ_pure, skeleton]
  exact relTriple_pure_pure ⟨rfl, rfl⟩

theorem hash_couple (bytes : Pqxdh.Bytes) (state : GameState KemSK × PqxdhJointDhExtractFamily.State) :
    RelTriple ((interp (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ
        PqxdhJointDhExtractRoot.reduction)
          (authHandler setup codec checks publicValue beaconSeed (.inr (.hash bytes)))).run state)
      ((skeleton setup codec checks publicValue beaconSeed (realServices seed scalar setup codec checks)
        (.inr (.hash bytes))).run (project state))
      (fun left right => left.1 = right.1 ∧ right.2 = project left.2) := by
  have handler : authHandler setup codec checks publicValue beaconSeed (.inr (.hash bytes)) =
      hashOracle bytes := rfl
  rw [handler, interp_run]
  rw [show (hashOracle bytes : Game KemSK _).run state.1 = (familyCoins ((CtxRomAuth.ctxRandomOracle ((), bytes)).run
      state.1.ctx) >>= fun result => pure (result.1, { state.1 with ctx := result.2 })) from rfl]
  rw [simulateQ_bind, StateT.run_bind, family_coins (rom_coinForward setup.hmac setup.joint setup.dh seed scalar)]
  simp only [bind_map_left, simulateQ_pure, StateT.run_pure, map_bind, map_pure]
  change RelTriple _ ((CtxRomAuth.ctxRandomOracle ((), bytes)).run state.1.ctx >>= fun result =>
    pure (result.1, ({ state.1 with ctx := result.2 }, (project state).2))) _
  refine relTriple_bind (relTriple_refl _) fun left right same => ?_
  cases same
  exact relTriple_pure_pure ⟨rfl, rfl⟩

theorem hmac_couple (key : HmacBlock) (message : Pqxdh.Bytes) (state : GameState KemSK × PqxdhJointDhExtractFamily.State) :
    RelTriple ((interp (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ
        PqxdhJointDhExtractRoot.reduction)
          (authHandler setup codec checks publicValue beaconSeed (.inr (.hmac key message)))).run state)
      ((skeleton setup codec checks publicValue beaconSeed (realServices seed scalar setup codec checks)
        (.inr (.hmac key message))).run (project state))
      (fun left right => left.1 = right.1 ∧ right.2 = project left.2) := by
  have handler : authHandler setup codec checks publicValue beaconSeed (.inr (.hmac key message)) =
      hmacOracle key message := rfl
  rw [handler]
  unfold hmacOracle
  simp only [skeleton]
  by_cases table : key = zeroSalt ∧ message.length = 192
  · rw [ite_eq_left table, hmacStep_run, ite_eq_left table]
    simp only [interp_bind, StateT.run_bind, recordTouch, interp_run_modify, pure_bind]
    rw [interp_run_forward, (PqxdhExtractRomFamily.rom_forward setup.hmac setup.joint setup.dh seed scalar).2.2 key message,
      PqxdhExtractRomFamily.rom_public_oracle _ _ _ _ _ _ _ table, Functor.map_map]
    simp only [realServices, project]
    rw [map_eq_bind_pure_comp]
    refine relTriple_bind (relTriple_refl _) fun left right same => ?_
    cases same
    exact relTriple_pure_pure ⟨rfl, rfl⟩
  · rw [ite_eq_right table, hmacStep_run, ite_eq_right table]
    rw [interp_run_forward, (PqxdhExtractRomFamily.rom_forward setup.hmac setup.joint setup.dh seed scalar).2.2 key message,
      PqxdhExtractRomFamily.rom_public_real _ _ _ _ _ (PqxdhJointDhExtractFamily.actualExtract setup.hmac) _ _ table]
    rw [show (PqxdhJointDhExtractFamily.impl setup.hmac setup.joint setup.dh seed scalar
        (PqxdhJointDhExtractFamily.actualExtract setup.hmac) (.inr (.publicHmac key message))).run state.2 =
        pure (setup.hmac.eval key message, { state.2 with history := state.2.history ++
          [.publicHmac key message (setup.hmac.eval key message)] }) from rfl, map_pure]
    exact relTriple_pure_pure ⟨rfl, rfl⟩

theorem build_couple (session : Nat) (payload : Option Pqxdh.Bytes)
    (state : GameState KemSK × PqxdhJointDhExtractFamily.State) :
    RelTriple ((interp (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ
        PqxdhJointDhExtractRoot.reduction)
          (authHandler setup codec checks publicValue beaconSeed (.inr (.build session payload)))).run state)
      ((skeleton setup codec checks publicValue beaconSeed (realServices seed scalar setup codec checks)
        (.inr (.build session payload))).run (project state))
      (fun left right => left.1 = right.1 ∧ right.2 = project left.2) := by
  have forward := rom_coinForward setup.hmac setup.joint setup.dh seed scalar
  have handler : authHandler setup codec checks publicValue beaconSeed (.inr (.build session payload)) =
      buildOracle setup codec checks session payload := rfl
  rw [handler]
  unfold buildOracle
  simp only [skeleton, interp_bind, StateT.run_bind, interp_run_get, pure_bind, project]
  rw [buildStep_run]
  cases found : state.1.pending session with
  | none =>
      simp only [interp_run_pure]
      exact relTriple_pure_pure ⟨rfl, rfl⟩
  | some token =>
      simp only [interp_bind, StateT.run_bind, interp_run_liftCoins _ forward, interp_run_set, interp_run_pure,
        bind_map_left, pure_bind, Bool.false_eq_true, ite_false]
      refine relTriple_bind (relTriple_refl _) fun left right same => ?_
      cases same
      exact relTriple_pure_pure ⟨rfl, rfl⟩

theorem finish_couple (raw : Pqxdh.Bytes) (state : GameState KemSK × PqxdhJointDhExtractFamily.State) :
    RelTriple ((interp (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ
        PqxdhJointDhExtractRoot.reduction)
          (authHandler setup codec checks publicValue beaconSeed (.inr (.finish raw)))).run state)
      ((skeleton setup codec checks publicValue beaconSeed (realServices seed scalar setup codec checks)
        (.inr (.finish raw))).run (project state))
      (fun left right => left.1 = right.1 ∧ right.2 = project left.2) := by
  have forward := rom_coinForward setup.hmac setup.joint setup.dh seed scalar
  have handler : authHandler setup codec checks publicValue beaconSeed (.inr (.finish raw)) =
      finishOracle setup codec publicValue beaconSeed raw := rfl
  rw [handler]
  unfold finishOracle
  simp only [skeleton, interp_bind, StateT.run_bind, interp_run_get, pure_bind]
  rw [finishStep_run]
  simp only [project]
  cases phase : state.1.beacon.beacon.phase
  case initSent control prekey oneTime kem =>
      simp only [stage_game, interp_bind, StateT.run_bind, interp_run_liftCoins _ forward, bind_map_left, bind_assoc]
      refine relTriple_bind (relTriple_refl _) fun prepared other same => ?_
      cases same
      cases prepared with
      | none =>
          simp only [interp_run_pure, pure_bind, interp_run_get, interp_run_set]
          exact relTriple_pure_pure ⟨rfl, rfl⟩
      | some pending =>
          simp only [recordTouch, interp_bind, StateT.run_bind, interp_run_modify, pure_bind, interp_run_forward,
            bind_map_left, bind_assoc]
          refine relTriple_bind (derive_couple setup seed scalar _ state.2) fun left right related => ?_
          obtain ⟨replyEq, cacheEq, visible⟩ := related
          rcases left with ⟨leftReply, leftFamily⟩
          rcases right with ⟨reply, cache⟩
          dsimp only at replyEq cacheEq visible ⊢
          subst replyEq cacheEq
          cases reply with
          | rejected =>
              simp only [Reply.value, interp_run_pure, pure_bind, interp_run_get,
                interp_run_set]
              exact relTriple_pure_pure ⟨rfl, rfl⟩
          | root value =>
              simp only [Reply.value, interp_run_onCtx_simulateQ _ forward, bind_map_left,
                interp_run_get, interp_run_set, interp_run_pure, pure_bind]
              refine relTriple_bind (relTriple_refl _) fun staged other same => ?_
              cases same
              exact relTriple_pure_pure ⟨rfl, rfl⟩
          | hidden => simp [Reply.isHidden] at visible
  all_goals
    simp only [interp_run_pure]
    exact relTriple_pure_pure ⟨rfl, rfl⟩

end FlatSteps

/-- The real experiment's handler interpreted under the Extract random-oracle family. -/
noncomputable def flatReal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (seed : IdentitySeed) (scalar : ScalarBytes) :
    QueryImpl ServerAuthSpec (StateT (GameState KemSK × PqxdhJointDhExtractFamily.State) ProbComp) :=
  fun query => interp (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ
    PqxdhJointDhExtractRoot.reduction) (authHandler setup codec checks publicValue beaconSeed query)

theorem flat_couple (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (seed : IdentitySeed) (scalar : ScalarBytes)
    (query : ServerAuthSpec.Domain) (state : GameState KemSK × PqxdhJointDhExtractFamily.State) :
    RelTriple ((flatReal setup codec checks publicValue beaconSeed seed scalar query).run state)
      ((skeleton setup codec checks publicValue beaconSeed (realServices seed scalar setup codec checks) query).run
        (project state))
      (fun left right => left.1 = right.1 ∧ right.2 = project left.2) := by
  rcases query with coin | query
  · exact coin_couple setup codec checks publicValue beaconSeed seed scalar coin state
  cases query with
  | accept raw => exact accept_couple setup codec checks publicValue seed scalar raw state
  | build session payload => exact build_couple setup codec checks publicValue beaconSeed seed scalar session payload state
  | finish raw => exact finish_couple setup codec checks publicValue beaconSeed seed scalar raw state
  | hmac key message => exact hmac_couple setup codec checks publicValue beaconSeed seed scalar key message state
  | hash bytes => exact hash_couple setup codec checks publicValue beaconSeed seed scalar bytes state
  | reveal keyId => exact reveal_couple setup codec checks publicValue beaconSeed seed scalar keyId state

theorem run_interp {φ α : Type} (family : QueryImpl RootSpec (StateT φ ProbComp)) (work : Game KemSK α)
    (game : GameState KemSK) (state : φ) :
    (simulateQ family (work.run game)).run state =
      (fun result => ((result.1, result.2.1), result.2.2)) <$> (interp family work).run (game, state) := by
  rw [interp_run, Functor.map_map]
  simp

/-- The flat real run is coupled with the real skeleton run: equal outputs, and the skeleton state is the projection. -/
theorem flatReal_couple (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (seed : IdentitySeed) (scalar : ScalarBytes)
    {α : Type} (work : OracleComp ServerAuthSpec α) (state : GameState KemSK × PqxdhJointDhExtractFamily.State) :
    RelTriple ((simulateQ (flatReal setup codec checks publicValue beaconSeed seed scalar) work).run state)
      ((simulateQ (skeleton setup codec checks publicValue beaconSeed (realServices seed scalar setup codec checks))
        work).run (project state))
      (UntilBad (fun left right => right = project left) (fun _ => False) (fun _ => False)) :=
  relTriple_until_bad _ _ _ _ _ (fun _ _ bad => bad.elim) (fun _ _ bad => bad.elim)
    (fun query left right related => by
      subst related
      exact relTriple_post_mono (flat_couple setup codec checks publicValue beaconSeed seed scalar query left)
        fun _ _ post => Or.inl ⟨post.1, post.2⟩)
    work state (project state) (Or.inl rfl)

/-- Everything the experiment samples before the adversary runs: the two Gap-DH secrets, the Beacon's identity seed, one-time scalar and ML-KEM key pair, and the published Phase 1 with the Beacon state. -/
structure Context (KemSK : Type) where
  seed : IdentitySeed
  scalar : ScalarBytes
  beaconSeed : IdentitySeed
  oneTime : ScalarBytes
  keys : PqxdhKemIndCca.MlKem768PublicKey × KemSK
  published : Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK

/-- The public challenge of a context's two secrets. -/
def Context.publicValue (setup : Setup baseSpec KemSK) (context : Context KemSK) : PublicChallenge :=
  PqxdhJointGapDh.challenge setup.joint setup.dh context.seed context.scalar

/-- The experiment's samples before the adversary runs, in the order of `gameState` and `body`. -/
noncomputable def contextSample (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    ProbComp (Context KemSK) := do
  let seed ← sampleSeed
  let scalar ← PqxdhJointGapDh.sampleScalar
  let beaconSeed ← sampleSeed
  let oneTime ← PqxdhJointGapDh.sampleScalar
  let keys ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let published ← phase1Run setup codec beaconSeed (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
    oneTime keys.1 keys.2
  pure ⟨seed, scalar, beaconSeed, oneTime, keys, published⟩

/-- The adversary's public input for a context. -/
def contextInput (setup : Setup baseSpec KemSK) (revealSeed : Bool) (context : Context KemSK) : AuthInput :=
  ⟨(context.publicValue setup).identity, setup.serverKeyId, context.published.1,
    if revealSeed then some context.seed else none⟩

/-- The initial game state of a context. -/
def contextState (setup : Setup baseSpec KemSK) (context : Context KemSK) : GameState KemSK :=
  initialGameState setup (context.publicValue setup) context.published.2

/-- A flattened run of the adversary from a context, with no marks and the given initial table state. -/
noncomputable def flatRun (setup : Setup baseSpec KemSK) (adversary : Adversary) (revealSeed : Bool)
    (context : Context KemSK) (handler : QueryImpl ServerAuthSpec (StateT (FlatState KemSK τ) ProbComp)) (table : τ) :
    ProbComp (FlatState KemSK τ) :=
  Prod.snd <$> (simulateQ handler (adversary (contextInput setup revealSeed context))).run
    (contextState setup context, fun _ => false, table)

/-- The real experiment as a skeleton game: the context, then the adversary against the real table services. -/
noncomputable def realGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) : ProbComp (Context KemSK × FlatState KemSK HmacOracle.QueryCache) := do
  let context ← contextSample setup codec
  let final ← flatRun setup adversary revealSeed context
    (skeleton setup codec checks (context.publicValue setup) context.beaconSeed
      (realServices context.seed context.scalar setup codec checks)) ∅
  pure (context, final)

set_option linter.deprecated false in
theorem gameState_le_real (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) (event : IdentitySeed → ScalarBytes → Ghost → Prop) :
    Pr[fun result => event result.1 result.2.1 result.2.2.1.ghost | gameState setup codec checks revealSeed adversary] ≤
      Pr[fun result => event result.1.seed result.1.scalar result.2.1.ghost |
        realGame setup codec checks revealSeed adversary] := by
  apply probEvent_le_of_relTriple (R := fun left right => left.1 = right.1.seed ∧ left.2.1 = right.1.scalar ∧
    left.2.2.1 = right.2.1)
  · simp only [gameState, realGame, contextSample, body, simulateQ_bind, StateT.run_bind, bind_assoc, pure_bind,
      family_coins (rom_coinForward setup.hmac setup.joint setup.dh _ _), bind_map_left]
    refine relTriple_bind (relTriple_refl _) fun seed other same => ?_
    cases same
    refine relTriple_bind (relTriple_refl _) fun scalar other same => ?_
    cases same
    refine relTriple_bind (relTriple_refl _) fun beaconSeed other same => ?_
    cases same
    refine relTriple_bind (relTriple_refl _) fun oneTime other same => ?_
    cases same
    refine relTriple_bind (relTriple_refl _) fun keys other same => ?_
    cases same
    refine relTriple_bind (relTriple_refl _) fun published other same => ?_
    cases same
    simp only [simulateQ_map, StateT.run_map, run_interp, interp_simulateQ, flatRun, bind_map_left]
    refine relTriple_bind (flatReal_couple setup codec checks (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
      beaconSeed seed scalar _ _) fun left right post => ?_
    rcases post with ⟨_, related⟩ | ⟨bad, _⟩
    · exact relTriple_pure_pure ⟨rfl, rfl, by rw [related]; rfl⟩
    · exact bad.elim
  · rintro left right ⟨seedEq, scalarEq, gameEq⟩ holds
    rw [← seedEq, ← scalarEq, ← gameEq]
    exact holds

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_pure
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_bind
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_get' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_get
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_set
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_modify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_modify
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_forward
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.family_coins' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.family_coins
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_liftCoins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_liftCoins
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_simulateQ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_simulateQ
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_onCtx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_onCtx
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.rom_coinForward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.rom_coinForward
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.derive_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.derive_project
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_run_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_run_pure
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_run_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_run_forward
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_run_modify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_run_modify
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_run_get' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_run_get
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_run_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_run_set
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_run_liftCoins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_run_liftCoins
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_run_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_run_map
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.client_run_flat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.client_run_flat
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.derive_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.derive_couple
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.accept_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.accept_couple
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_run
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hmacStep_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hmacStep_run
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.buildStep_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.buildStep_run
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_run_onCtx_simulateQ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.interp_run_onCtx_simulateQ
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.stage_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.stage_game
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.finishStep_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.finishStep_run
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.coin_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.coin_couple
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.reveal_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.reveal_couple
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hash_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hash_couple
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hmac_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hmac_couple
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.build_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.build_couple
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.finish_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.finish_couple
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.flat_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.flat_couple
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.run_interp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.run_interp
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.flatReal_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.flatReal_couple
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.gameState_le_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.gameState_le_real
