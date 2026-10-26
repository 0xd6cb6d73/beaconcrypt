import B8bScratch.Flat

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

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response τ : Type}

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
    simp only [simulateQ_map, StateT.run_map, run_interp, interp_simulateQ, flatRun, map_bind, bind_map_left]
    refine relTriple_bind (flatReal_couple setup codec checks (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
      beaconSeed seed scalar _ _) fun left right post => ?_
    rcases post with ⟨_, related⟩ | ⟨bad, _⟩
    · exact relTriple_pure_pure ⟨rfl, rfl, by rw [related]; rfl⟩
    · exact bad.elim
  · rintro left right ⟨seedEq, scalarEq, gameEq⟩ holds
    rw [← seedEq, ← scalarEq, ← gameEq]
    exact holds

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
