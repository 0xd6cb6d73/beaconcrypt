import BeaconcryptCore.Computational.PqxdhServerAuthObservedNative
import BeaconcryptCore.Computational.PqxdhServerAuthIntermediate

/-! The actual R1 game with a chronological public API journal, for the enclosing accepted-observation partition. -/
open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthObservedGame
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor
open PqxdhJointIdentity PqxdhJointGapDh PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhJointDhExtractRoot (RootSpec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Original source body retaining only the extra public query/reply journal. All private native and family state stays present. -/
noncomputable def body (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (revealed : Option IdentitySeed) (publicValue : PublicChallenge) :
    OracleComp RootSpec (QueryLog ServerAuthSpec × GameState KemSK) := do
  let beaconSeed ← familyCoins sampleSeed
  let oneTime ← familyCoins PqxdhJointGapDh.sampleScalar
  let keys ← familyCoins (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen)
  let published ← familyCoins (phase1Run setup codec beaconSeed publicValue oneTime keys.1 keys.2)
  let input : AuthInput := ⟨publicValue.identity, setup.serverKeyId, published.1, revealed⟩
  (fun result => (result.1.2, result.2)) <$>
    (simulateQ (authHandler setup codec checks publicValue beaconSeed)
      (PqxdhServerAuthApiJournal.record (adversary input))).run
        (initialGameState setup publicValue published.2)

/-- Erasing the external journal recovers the complete original source body as an oracle-program equality. -/
theorem body_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (revealed : Option IdentitySeed) (publicValue : PublicChallenge) :
    Prod.snd <$> body setup codec checks adversary revealed publicValue =
      PqxdhServerAuthExperiment.body setup codec checks adversary revealed publicValue := by
  unfold body PqxdhServerAuthExperiment.body
  simp only [map_bind, Functor.map_map]
  refine bind_congr fun beaconSeed => bind_congr fun oneTime => bind_congr fun keys => bind_congr fun published => ?_
  simpa only [Functor.map_map] using congrArg (Functor.map Prod.snd)
    (PqxdhServerAuthApiJournal.interpreted_erase (authHandler setup codec checks publicValue beaconSeed)
      (adversary ⟨publicValue.identity, setup.serverKeyId, published.1, revealed⟩)
      (initialGameState setup publicValue published.2))

/-- Exact original result with the chronological public history retained beside the native state. -/
abbrev Result (KemSK : Type) := IdentitySeed × ScalarBytes ×
  (QueryLog ServerAuthSpec × GameState KemSK) × PqxdhJointDhExtractFamily.State

/-- Projection to the original R1 experiment result. -/
def erase (result : Result KemSK) : IdentitySeed × ScalarBytes × GameState KemSK × PqxdhJointDhExtractFamily.State :=
  (result.1, result.2.1, result.2.2.1.2, result.2.2.2)

/-- The actual source experiment and original family interpreter, with the extra external journal. Secrets are sampled inside the unchanged game. -/
noncomputable def game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) : ProbComp (Result KemSK) := do
  let seed ← sampleSeed
  let scalar ← PqxdhJointGapDh.sampleScalar
  let publicValue := PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar
  let result ← (simulateQ (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ
      PqxdhJointDhExtractRoot.reduction)
    (body setup codec checks adversary (if revealSeed then some seed else none) publicValue)).run
      PqxdhJointDhExtractFamily.empty
  pure (seed, scalar, result)

/-- The complete original R1 source game is recovered exactly by erasing the public journal, including its family cache and history. -/
theorem game_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) :
    erase <$> game setup codec checks revealSeed adversary =
      gameState setup codec checks revealSeed adversary := by
  simp only [game, erase, gameState, ← body_erase, simulateQ_map, StateT.run_map,
    map_bind, map_pure, bind_map_left]

/-- Every observed run inherits the original source invariant and accept-attempt session bound, through exact erasure rather than a caller promise. -/
theorem reachable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) (result : Result KemSK)
    (supported : result ∈ support (game setup codec checks revealSeed adversary)) :
    GameInv Reader Response setup (challenge setup.joint setup.dh result.1 result.2.1) result.2.2.1.2 ∧
      ∀ Q qH qHash, AuthBudget adversary Q qH qHash → result.2.2.1.2.sessions ≤ Q := by
  have original : erase result ∈ support (gameState setup codec checks revealSeed adversary) := by
    rw [← game_erase, support_map]
    exact ⟨result, supported, rfl⟩
  exact gameState_reachable setup codec checks revealSeed adversary (erase result) original

open PqxdhServerAuthAcceptedEntry PqxdhServerAuthObservedEntry

/-- A concrete observation on an actually accepted run, before any owner or bad-event selection. -/
def Accepted (observer : Observer) (result : Result KemSK) : Prop :=
  (∃ snap, result.2.2.1.2.ghost.acceptance = some snap) ∧
    observer (eraseGhost result.2.2.1.2.ghost) result.2.2.1.1 = true

/-- The same observation in one exact accepted-owner coordinate. -/
def Owned (setup : Setup baseSpec KemSK) (Q : Nat) (j : Fin (Q + 1))
    (observer : Observer) (result : Result KemSK) : Prop :=
  Gate setup result.1 result.2.1 Q j result.2.2.1.2.ghost ∧
    observer (eraseGhost result.2.2.1.2.ghost) result.2.2.1.1 = true

/-- The actual observed source support supplies the full partition for any accepted observation, with the original Q+1 coordinates and no new freshness or honesty premise. -/
theorem accepted_cases (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) (Q qH qHash : Nat)
    (budget : AuthBudget adversary Q qH qHash) (observer : Observer) (result : Result KemSK)
    (supported : result ∈ support (game setup codec checks revealSeed adversary))
    (accepted : Accepted observer result) :
    BadB setup result.1 result.2.1 result.2.2.1.2.ghost ∨
      CollB setup result.1 result.2.1 result.2.2.1.2.ghost ∨
      ∃ j ∈ (Finset.univ : Finset (Fin (Q + 1))), Owned setup Q j observer result := by
  have actual := reachable setup codec checks revealSeed adversary result supported
  rcases PqxdhServerAuthAcceptedEntry.accepted_cases setup result.1 result.2.1 Q result.2.2.1.2.ghost
    result.2.2.1.2.sessions actual.1.touched (actual.2 Q qH qHash budget) accepted.1 with
    bad | coll | ⟨j, owned⟩
  · exact Or.inl bad
  · exact Or.inr (Or.inl coll)
  · exact Or.inr (Or.inr ⟨j, Finset.mem_univ j, owned, accepted.2⟩)

/-- The chronological observed event is charged to the original source disclosure/collision games and the same finite family of owner events. Observation conditions are dropped only on those two explicitly charged bad branches. -/
theorem accepted_probability (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) (Q qH qHash : Nat)
    (budget : AuthBudget adversary Q qH qHash) (observer : Observer) :
    Pr{let x ← game setup codec checks revealSeed adversary}[(Accepted observer) x] ≤
      Pr{let result ← gameState setup codec checks revealSeed adversary}[BadB setup result.1 result.2.1 result.2.2.1.ghost] +
      Pr{let result ← gameState setup codec checks revealSeed adversary}[CollB setup result.1 result.2.1 result.2.2.1.ghost] +
      ∑ j : Fin (Q + 1), Pr{let x ← game setup codec checks revealSeed adversary}[(Owned setup Q j observer) x] := by
  classical
  simp only [← game_erase setup codec checks revealSeed adversary, prEvent_map, erase]
  refine le_trans (prEvent_mono_of_support _ _ (fun result : Result KemSK =>
    BadB setup result.1 result.2.1 result.2.2.1.2.ghost ∨
      (CollB setup result.1 result.2.1 result.2.2.1.2.ghost ∨
        ∃ j ∈ (Finset.univ : Finset (Fin (Q + 1))), Owned setup Q j observer result))
    (fun result supported accepted => accepted_cases setup codec checks revealSeed adversary Q qH qHash
      budget observer result supported accepted)) ?_
  refine le_trans (prEvent_or_le (game setup codec checks revealSeed adversary) _ _) ?_
  rw [add_assoc]
  exact add_le_add le_rfl (le_trans (prEvent_or_le (game setup codec checks revealSeed adversary) _ _)
    (add_le_add le_rfl (prEvent_exists_finset_le (Finset.univ : Finset (Fin (Q + 1)))
      (game setup codec checks revealSeed adversary) _)))

/-- Any seed/scalar-indexed Boolean observation of actual source ghost and public history, used only for exact source-game correspondence. The later key-schedule reduction still uses its separate root-erased observer interface. -/
abbrev Observation := IdentitySeed → ScalarBytes → Ghost → QueryLog ServerAuthSpec → Bool

/-- Keep one arbitrary actual final observation on the journaled source game. -/
noncomputable def observed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) (observation : Observation) : ProbComp Bool :=
  (fun result => observation result.1 result.2.1 result.2.2.1.2.ghost result.2.2.1.1) <$>
    game setup codec checks revealSeed adversary

/-- Same complete observation under the original real-service table skeleton. -/
noncomputable def flatObserved (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) (observation : Observation) : ProbComp Bool := do
  let context ← contextSample setup codec
  (fun result => observation context.seed context.scalar result.2.1.ghost result.1.2) <$>
    (simulateQ (skeleton setup codec checks (context.publicValue setup) context.beaconSeed
      (realServices context.seed context.scalar setup codec checks))
      (PqxdhServerAuthApiJournal.record (adversary (contextInput setup revealSeed context)))).run
        (contextState setup context, fun _ => false, ∅)

/-- Full-game correspondence retains the whole journal jointly with all observed source fields. The same original family interpreter and context samples are used on both sides. -/
theorem observed_flat (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) (observation : Observation) :
    EvalDistEq (observed setup codec checks revealSeed adversary observation)
      (flatObserved setup codec checks revealSeed adversary observation) := by
  apply evalDistEq_of_relTriple_eqRel
  simp only [observed, game, flatObserved, contextSample, body, simulateQ_bind, StateT.run_bind,
    bind_assoc, pure_bind, family_coins (rom_coinForward setup.hmac setup.joint setup.dh _ _),
    map_bind, map_pure, bind_map_left]
  refine relTriple_bind (R := Eq) (relTriple_refl _) ?_
  rintro seed _ rfl
  refine relTriple_bind (R := Eq) (relTriple_refl _) ?_
  rintro scalar _ rfl
  refine relTriple_bind (R := Eq) (relTriple_refl _) ?_
  rintro beaconSeed _ rfl
  refine relTriple_bind (R := Eq) (relTriple_refl _) ?_
  rintro oneTime _ rfl
  refine relTriple_bind (R := Eq) (relTriple_refl _) ?_
  rintro keys _ rfl
  refine relTriple_bind (R := Eq) (relTriple_refl _) ?_
  rintro published _ rfl
  simp only [simulateQ_map, StateT.run_map, run_interp, interp_simulateQ,
    bind_pure_comp, Functor.map_map]
  apply relTriple_map
  apply relTriple_post_mono (flatReal_couple setup codec checks (challenge setup.joint setup.dh seed scalar)
    beaconSeed seed scalar _
    (initialGameState setup (challenge setup.joint setup.dh seed scalar) published.2, PqxdhJointDhExtractFamily.empty))
  rintro left right (⟨same, related⟩ | ⟨bad, _⟩)
  · simp only [related, project, same]
    rfl
  · exact bad.elim

end BeaconcryptCore.Computational.PqxdhServerAuthObservedGame

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedGame.body_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedGame.body_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedGame.game_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedGame.game_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedGame.reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedGame.reachable

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedGame.accepted_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedGame.accepted_cases

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedGame.accepted_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedGame.accepted_probability

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedGame.observed_flat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedGame.observed_flat
