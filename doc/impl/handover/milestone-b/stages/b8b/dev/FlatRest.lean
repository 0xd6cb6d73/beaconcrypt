import B8bScratch.Flat

open OracleComp OracleSpec ENNReal
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
open OracleComp.ProgramLogic.Relational

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment
open PqxdhJointIdentity PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhJointGapDh (DhInterface ScalarBytes PublicChallenge)
open PqxdhJointDhExtractRoot (RootSpec)
open PqxdhRootTableInitialization (rootArray)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

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
  simp only [interp, StateT.run, simulateQ_pure, map_pure, skeleton]
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
  simp only [skeleton, hmacStep]
  by_cases table : key = zeroSalt ∧ message.length = 192
  · rw [if_pos table, hmacStep_run, if_pos table]
    simp only [interp_bind, StateT.run_bind, recordTouch, interp_run_modify, pure_bind]
    rw [interp_run_forward, (PqxdhExtractRomFamily.rom_forward setup.hmac setup.joint setup.dh seed scalar).2.2 key message,
      PqxdhExtractRomFamily.rom_public_oracle _ _ _ _ _ _ _ table, Functor.map_map]
    simp only [realServices, project]
    rw [map_eq_bind_pure_comp]
    refine relTriple_bind (relTriple_refl _) fun left right same => ?_
    cases same
    exact relTriple_pure_pure ⟨rfl, rfl⟩
  · rw [if_neg table, hmacStep_run, if_neg table]
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
          simp only [interp_run_pure, pure_bind, interp_bind, StateT.run_bind, interp_run_get, interp_run_set]
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
              simp only [Reply.value, interp_run_pure, pure_bind, interp_bind, StateT.run_bind, interp_run_get,
                interp_run_set]
              exact relTriple_pure_pure ⟨rfl, rfl⟩
          | root value =>
              simp only [Reply.value, interp_run_onCtx_simulateQ _ forward, bind_map_left, interp_bind,
                StateT.run_bind, interp_run_get, interp_run_set, interp_run_pure, pure_bind]
              refine relTriple_bind (relTriple_refl _) fun staged other same => ?_
              cases same
              exact relTriple_pure_pure ⟨rfl, rfl⟩
          | hidden => simp [Reply.isHidden] at visible
  all_goals
    simp only [interp_run_pure]
    exact relTriple_pure_pure ⟨rfl, rfl⟩

end FlatSteps

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
