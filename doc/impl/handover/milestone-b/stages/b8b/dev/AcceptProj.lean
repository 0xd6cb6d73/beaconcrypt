import B8bScratch.Flat

open OracleComp OracleSpec ENNReal
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

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Project. -/
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
    pure_bind, bind_map_left, acceptStep, project]
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
          simp only [Reply.value, Reply.isHidden, afterDerive, interp_run_pure]
          exact relTriple_pure_pure ⟨rfl, rfl⟩
      | root value =>
          simp only [Reply.value, Reply.isHidden, afterDerive, interp_run_map, interp_run_modify, map_pure]
          exact relTriple_pure_pure ⟨rfl, rfl⟩
      | hidden => simp [Reply.isHidden] at visible
    · simp only [valid, ite_false, pure_bind, interp_run_pure]
      exact relTriple_pure_pure ⟨rfl, rfl⟩

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
