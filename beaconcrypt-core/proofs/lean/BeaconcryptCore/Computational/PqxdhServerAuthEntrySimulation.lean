import BeaconcryptCore.Computational.PqxdhServerAuthExperiment
import BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule
import VCVio.ProgramLogic.Relational.Basic
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import BeaconcryptCore.Computational.VCVioForwardProgramLogic

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

/-! ## Generic simulation lemmas: couplings until a bad event and eager sampling -/

section Generic
variable {ι : Type} {spec : OracleSpec ι}

/-- Two continuations with equal output distributions on the support of a common first computation give equal output distributions after it. -/
theorem evalSPMF_bind_congr_support {α β : Type} (first : ProbComp α) (left right : α → ProbComp β)
    (same : ∀ value ∈ support first, EvalDistEq (left value) (right value)) :
    EvalDistEq (first >>= left) (first >>= right) :=
  OracleComp.EvalDistEq.bind_congr_of_support first same

/-- Two images of one computation are coupled by any relation that holds between the two images of each supported value. -/
theorem relTriple_map_same {α β γ : Type} (work : ProbComp α) (left : α → β) (right : α → γ)
    (relation : β → γ → Prop) (related : ∀ value ∈ support work, relation (left value) (right value)) :
    RelTriple (left <$> work) (right <$> work) relation := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  refine relTriple_bind (R := fun a b => a = b ∧ a ∈ support work)
    (relTriple_refl_of_mem_support work fun value member => ⟨rfl, member⟩) fun a b same => ?_
  obtain ⟨rfl, member⟩ := same
  exact relTriple_pure_pure (related a member)

/-- Two support properties combine into a coupling of any two computations: the product coupling, given by VCVio's `relTriple_prod`. -/
theorem relTriple_support {α β : Type} (left : ProbComp α) (right : ProbComp β) (first : α → Prop)
    (second : β → Prop) (leftHolds : ∀ value ∈ support left, first value)
    (rightHolds : ∀ value ∈ support right, second value) :
    RelTriple left right (fun a b => first a ∧ second b) :=
  relTriple_prod leftHolds rightHolds

/-- The coupling postcondition of an identical-until-bad argument: equal answers with related states, or both runs bad. -/
def UntilBad {α σ₁ σ₂ : Type} (related : σ₁ → σ₂ → Prop) (bad₁ : σ₁ → Prop) (bad₂ : σ₂ → Prop)
    (left : α × σ₁) (right : α × σ₂) : Prop :=
  (left.1 = right.1 ∧ related left.2 right.2) ∨ (bad₁ left.2 ∧ bad₂ right.2)

/-- A bad predicate that every step keeps holds on every final state of a simulation that starts bad. -/
theorem support_run_bad {α σ : Type} (impl : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Prop)
    (keeps : ∀ query state, bad state → ∀ result ∈ support ((impl query).run state), bad result.2)
    (work : OracleComp spec α) (state : σ) (start : bad state) :
    ∀ result ∈ support ((simulateQ impl work).run state), bad result.2 := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
      intro result member
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact start
  | query_bind query next ih =>
      intro result member
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at member
      obtain ⟨step, stepMember, member⟩ := member
      exact ih step.1 step.2 (keeps query state start step stepMember) result member

/-- Identical until bad, as a coupling of two stateful simulations of the same program: if from related states every query is coupled so that the answers agree and the states stay related, or both runs become bad, and bad states are kept by both handlers, then the whole simulations are coupled in the same way. -/
theorem relTriple_until_bad {α σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp)) (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (related : σ₁ → σ₂ → Prop) (bad₁ : σ₁ → Prop) (bad₂ : σ₂ → Prop)
    (keeps₁ : ∀ query state, bad₁ state → ∀ result ∈ support ((impl₁ query).run state), bad₁ result.2)
    (keeps₂ : ∀ query state, bad₂ state → ∀ result ∈ support ((impl₂ query).run state), bad₂ result.2)
    (step : ∀ query state₁ state₂, related state₁ state₂ →
      RelTriple ((impl₁ query).run state₁) ((impl₂ query).run state₂) (UntilBad related bad₁ bad₂))
    (work : OracleComp spec α) (state₁ : σ₁) (state₂ : σ₂)
    (start : related state₁ state₂ ∨ (bad₁ state₁ ∧ bad₂ state₂)) :
    RelTriple ((simulateQ impl₁ work).run state₁) ((simulateQ impl₂ work).run state₂)
      (UntilBad related bad₁ bad₂) := by
  have bothBad : ∀ (left right : OracleComp spec α) (first : σ₁) (second : σ₂), bad₁ first → bad₂ second →
      RelTriple ((simulateQ impl₁ left).run first) ((simulateQ impl₂ right).run second)
        (UntilBad related bad₁ bad₂) := fun left right first second firstBad secondBad =>
    relTriple_post_mono (relTriple_support _ _ _ _ (support_run_bad impl₁ bad₁ keeps₁ left first firstBad)
      (support_run_bad impl₂ bad₂ keeps₂ right second secondBad)) fun _ _ both => Or.inr both
  rcases start with start | start
  swap
  · exact bothBad work work state₁ state₂ start.1 start.2
  induction work using OracleComp.inductionOn generalizing state₁ state₂ with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure (Or.inl ⟨rfl, start⟩)
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind]
      refine relTriple_bind (step query state₁ state₂ start) fun left right post => ?_
      rcases post with ⟨same, rel⟩ | ⟨leftBad, rightBad⟩
      · rw [same]
        exact ih right.1 left.2 right.2 rel
      · exact bothBad _ _ left.2 right.2 leftBad rightBad

/-- Transport of an event through an identical-until-bad coupling: an event of the first run that excludes the first bad predicate, and that implies an event of the second run on related final states with equal outputs, has at most the probability of the second event. -/
theorem probEvent_le_until_bad {α σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp)) (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (related : σ₁ → σ₂ → Prop) (bad₁ : σ₁ → Prop) (bad₂ : σ₂ → Prop)
    (keeps₁ : ∀ query state, bad₁ state → ∀ result ∈ support ((impl₁ query).run state), bad₁ result.2)
    (keeps₂ : ∀ query state, bad₂ state → ∀ result ∈ support ((impl₂ query).run state), bad₂ result.2)
    (step : ∀ query state₁ state₂, related state₁ state₂ →
      RelTriple ((impl₁ query).run state₁) ((impl₂ query).run state₂) (UntilBad related bad₁ bad₂))
    (work : OracleComp spec α) (state₁ : σ₁) (state₂ : σ₂) (start : related state₁ state₂)
    (event₁ : α × σ₁ → Prop) (event₂ : α × σ₂ → Prop)
    (excludes : ∀ result, event₁ result → ¬ bad₁ result.2)
    (implies : ∀ left right, left.1 = right.1 → related left.2 right.2 → event₁ left → event₂ right) :
    Pr{let x ← (simulateQ impl₁ work).run state₁}[event₁ x] ≤ Pr{let x ← (simulateQ impl₂ work).run state₂}[event₂ x] :=
  prEvent_le_of_relTriple
    (relTriple_until_bad impl₁ impl₂ related bad₁ bad₂ keeps₁ keeps₂ step work state₁ state₂ (Or.inl start))
    fun left right post holds => by
      rcases post with ⟨same, rel⟩ | ⟨leftBad, _⟩
      · exact implies left right same rel holds
      · exact absurd leftBad (excludes left holds)

/-- Once the eager value has been consumed, the eager and lazy handlers agree on every simulation. -/
theorem done_run {α σ V : Type} (lazy : QueryImpl spec (StateT σ ProbComp))
    (eager : V → QueryImpl spec (StateT σ ProbComp)) (done : σ → Prop)
    (doneStep : ∀ query state, done state →
      (∀ value, (eager value query).run state = (lazy query).run state) ∧
        ∀ result ∈ support ((lazy query).run state), done result.2)
    (work : OracleComp spec α) (state : σ) (finished : done state) (value : V) :
    (simulateQ (eager value) work).run state = (simulateQ lazy work).run state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure result => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind]
      rw [(doneStep query state finished).1 value]
      exact OracleComp.bind_congr_of_forall_mem_support _ fun step member =>
        ih step.1 step.2 ((doneStep query state finished).2 step member)

/-- Eager sampling of one value: a lazy handler that, at a single designated step, samples a value and runs the eager step with it has the output distribution of sampling the value first and running the eager handler throughout. At every other step the eager handler does not use its value, and after the designated step (`done`) it never does again. -/
theorem eager_run {α σ V : Type} (sampler : ProbComp V) (lazy : QueryImpl spec (StateT σ ProbComp))
    (eager : V → QueryImpl spec (StateT σ ProbComp)) (done : σ → Prop)
    (doneStep : ∀ query state, done state →
      (∀ value, (eager value query).run state = (lazy query).run state) ∧
        ∀ result ∈ support ((lazy query).run state), done result.2)
    (freshStep : ∀ query state, ¬ done state →
      (∀ value, (eager value query).run state = (lazy query).run state) ∨
        (EvalDistEq ((lazy query).run state) (do let value ← sampler; (eager value query).run state) ∧
          ∀ value, ∀ result ∈ support ((eager value query).run state), done result.2))
    (work : OracleComp spec α) (state : σ) :
    EvalDistEq ((simulateQ lazy work).run state) (do let value ← sampler; (simulateQ (eager value) work).run state) := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure result =>
      simp only [simulateQ_pure, StateT.run_pure]
      exact (OracleComp.EvalDistEq.bind_const sampler _).symm
  | query_bind query next ih =>
      by_cases finished : done state
      · have same : ∀ value, (simulateQ (eager value) (liftM (spec.query query) >>= next)).run state =
            (simulateQ lazy (liftM (spec.query query) >>= next)).run state := fun value =>
          done_run lazy eager done doneStep _ state finished value
        simp only [same]
        exact (OracleComp.EvalDistEq.bind_const sampler _).symm
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind]
      rcases freshStep query state finished with independent | ⟨designated, consumed⟩
      · simp only [independent]
        refine (EvalDistEq.bind_right ((lazy query).run state) fun step => ih step.1 step.2).trans ?_
        exact OracleComp.EvalDistEq.bind_bind_swap ((lazy query).run state) sampler
          (fun step value => (simulateQ (eager value) (next step.1)).run step.2)
      · have after : ∀ value, (eager value query).run state >>= (fun step =>
            (simulateQ (eager value) (next step.1)).run step.2) =
            (eager value query).run state >>= (fun step => (simulateQ lazy (next step.1)).run step.2) :=
          fun value => OracleComp.bind_congr_of_forall_mem_support _ fun step member =>
            done_run lazy eager done doneStep _ step.2 (consumed value step member) value
        simp only [after]
        rw [show (sampler >>= fun value => (eager value query).run state >>= fun step =>
            (simulateQ lazy (next step.1)).run step.2) =
            ((sampler >>= fun value => (eager value query).run state) >>= fun step =>
              (simulateQ lazy (next step.1)).run step.2) from (bind_assoc _ _ _).symm]
        exact designated.bind_left _

end Generic

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

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

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response τ : Type}

/-! ## The flattened experiment with table services -/

/-- The answer of a table read for a root derivation: rejected (no actual input), a root derived from a table entry, or the hidden entry of the analysis games. -/
inductive Reply where
  | rejected
  | root (value : RootOutput)
  | hidden

/-- The fixed placeholder root that stands for the hidden entry's root in a pending token and in the touch log. -/
def sentinel : RootOutput := List.Vector.replicate 32 0

/-- The root a derivation reply shows to the Server's consumer and the touch log: none for a rejected input, the derived root, or the placeholder for the hidden entry. -/
def Reply.value : Reply → Option RootOutput
  | .rejected => none
  | .root value => some value
  | .hidden => some sentinel

/-- Whether a reply is the hidden entry. -/
def Reply.isHidden : Reply → Bool
  | .hidden => true
  | _ => false

/-- The Server state of the experiment. -/
abbrev ServerState := PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)

/-- The shared BLAKE2b cache with the seal log, the state of the Server's response tail. -/
abbrev SealState := RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)

/-- Per-session marks: a marked session's pending token stands for the hidden entry. -/
abbrev Marks := Nat → Bool

/-- The state of a flattened experiment: the game state, the session marks and the table state. -/
abbrev FlatState (KemSK τ : Type) := GameState KemSK × Marks × τ

/-- The table services a flattened experiment uses: the table read of a root derivation, the adversary's table query, the response tail of a marked session and the Beacon's continuation after a hidden reply. -/
structure Services (Response τ : Type) where
  derive : PqxdhJointDhExtractFamily.Message → StateT τ ProbComp Reply
  table : Pqxdh.Bytes → StateT τ ProbComp HmacBlock
  hiddenBuild : PqxdhServerRelatedRootConsumer.Returned → Option Pqxdh.Bytes → ServerState →
    StateT SealState ProbComp (RustM (Option PqxdhServerRegistrationPublication.Response × ServerState))
  hiddenAfter : PqxdhPhase2DhMetadata.Prepared Response →
    StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp (Option PqxdhBeaconPhase2Publication.Staged)

section Steps
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (svc : Services Response τ)

/-- The game state after a session's root derivation, as `PqxdhServerRelatedRootConsumer.client` and `acceptOracle` leave it: the touch is logged, and on a root the registration ID is consumed and the pending token is stored. -/
def afterDerive (index : Nat) (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding)
    (reply : Reply) (game : GameState KemSK) : Option Nat × GameState KemSK :=
  let touched : GameState KemSK := { game with ghost := { game.ghost with touches := game.ghost.touches ++
    [Touch.session index (PqxdhServerRelatedRootInput.message input) reply.value] } }
  match reply.value with
  | none => (none, touched)
  | some root =>
      let token := PqxdhServerClearedRoot.pending (binding setup publicValue) input
      let consumed : GameState KemSK := { touched with server := { touched.server with
        consumed := touched.server.consumed ++ [absBytes token.registration_id.bytes] } }
      (some index, { consumed with pending := Function.update consumed.pending index (some ⟨root, token⟩) })

/-- The flattened accept step (`acceptOracle`): the Phase 1 prefix, then one table read for the root derivation. A hidden reply marks the session. -/
noncomputable def acceptStep (raw : Pqxdh.Bytes) : StateT (FlatState KemSK τ) ProbComp (Option Nat) :=
  fun state => by
    classical
    exact do
      let index := state.1.sessions
      let collected ← (serverPrefix setup codec checks raw).run state.1.server.consumed
      let game : GameState KemSK :=
        { state.1 with sessions := index + 1, server := { state.1.server with consumed := collected.2 } }
      match collected.1 with
      | none => pure (none, (game, state.2))
      | some input =>
          if PqxdhServerRelatedRootInput.localNonzero input then do
            let derived ← (svc.derive (PqxdhServerRelatedRootInput.message input)).run state.2.2
            let result := afterDerive setup publicValue index input derived.1 game
            pure (result.1, (result.2,
              (if derived.1.isHidden then Function.update state.2.1 index true else state.2.1), derived.2))
          else pure (none, (game, state.2))

/-- The Server state and game fields after a build, as `buildOracle` leaves them. -/
def afterBuild (session : Nat) (game : GameState KemSK)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response × ServerState) × SealState) :
    Option PqxdhServerRegistrationPublication.Response × GameState KemSK :=
  let settled := settle game.server result.1
  (settled.1, { game with
    pending := Function.update game.pending session none
    server := settled.2
    ctx := result.2.2
    ghost := { game.ghost with seals := game.ghost.seals ++ result.2.1.map (fun context => (session, context)) } })

/-- The flattened build step (`buildOracle`): an unmarked session runs the native builder with its stored root; a marked session runs the service's response tail. -/
noncomputable def buildStep (session : Nat) (payload : Option Pqxdh.Bytes) :
    StateT (FlatState KemSK τ) ProbComp (Option PqxdhServerRegistrationPublication.Response) :=
  fun state =>
    match state.1.pending session with
    | none => pure (none, state)
    | some token => do
        let result ← (if state.2.1 session then svc.hiddenBuild token payload state.1.server
          else simulateQ (tailImpl setup codec checks)
            (PqxdhServerRegistrationPublication.build setup.source token.pending token.root payload ()
              state.1.server)).run ([], state.1.ctx)
        let after := afterBuild session state.1 result
        pure (after.1, (after.2, state.2))

/-- The outcome of a finish from a staged result, as `finishOracle` leaves it: the final checks, the new Beacon state and the acceptance snapshot. -/
noncomputable def finishOutcome (control : pqxdh.BeaconInitSent) (game : GameState KemSK)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) : Option Pqxdh.Bytes × GameState KemSK :=
  let result := PqxdhBeaconPhase2Publication.finish control game.beacon staged
  (result.1, { game with beacon := result.2, ghost := game.ghost.accept (acceptedOf staged result.1) })

/-- The flattened finish step (`finishOracle`): in the InitSent phase, the Beacon's preparation, its touch, one table read for its root derivation, then the native continuation on the root or the service's continuation on a hidden reply, and the final checks. -/
noncomputable def finishStep (raw : Pqxdh.Bytes) : StateT (FlatState KemSK τ) ProbComp (Option Pqxdh.Bytes) :=
  fun state =>
    match state.1.beacon.beacon.phase with
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
    | _ => pure (none, state)

/-- The flattened public HMAC (`hmacOracle`): a query inside the table domain is logged and read from the table service; any other query is the real HMAC. -/
noncomputable def hmacStep (key : HmacBlock) (message : Pqxdh.Bytes) : StateT (FlatState KemSK τ) ProbComp HmacBlock :=
  fun state =>
    if key = zeroSalt ∧ message.length = 192 then do
      let read ← (svc.table message).run state.2.2
      pure (read.1, ({ state.1 with ghost := { state.1.ghost with
        touches := state.1.ghost.touches ++ [Touch.adversary message] } }, state.2.1, read.2))
    else pure (setup.hmac.eval key message, state)

/-- The flattened BLAKE2b oracle (`hashOracle`). -/
noncomputable def hashStep (bytes : Pqxdh.Bytes) : StateT (FlatState KemSK τ) ProbComp CtxRomAuth.CtxDigest :=
  fun state => do
    let result ← (CtxRomAuth.ctxRandomOracle ((), bytes)).run state.1.ctx
    pure (result.1, ({ state.1 with ctx := result.2 }, state.2))

/-- The flattened experiment handler over a table service. -/
noncomputable def skeleton : QueryImpl ServerAuthSpec (StateT (FlatState KemSK τ) ProbComp)
  | .inl coin => fun state => (fun value => (value, state)) <$> (unifSpec.query coin : ProbComp _)
  | .inr (.accept raw) => acceptStep setup codec checks publicValue svc raw
  | .inr (.build session payload) => buildStep setup codec checks svc session payload
  | .inr (.finish raw) => finishStep setup codec publicValue beaconSeed svc raw
  | .inr (.hmac key message) => hmacStep setup svc key message
  | .inr (.hash bytes) => hashStep bytes
  | .inr (.reveal keyId) => fun state => pure (revealKernel keyId state.1, state)

end Steps

/-! ## The real table service -/

section Real
variable (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed)
  (scalar : ScalarBytes)

/-- The real derivation: a rejected input, or the table read at the actual input bytes followed by the real root Expand. -/
noncomputable def realDerive (message : PqxdhJointDhExtractFamily.Message) :
    StateT HmacOracle.QueryCache ProbComp Reply := fun cache =>
  match PqxdhJointDhExtractFamily.input joint dh seed scalar message with
  | none => pure (.rejected, cache)
  | some bytes => (fun read => (.root (expandRoot hmac read.1), read.2)) <$> (HmacOracle.randomOracle bytes).run cache

/-- The real services: the lazily sampled table for derivations and adversary queries, and the native builder and continuation (never used, as no reply is hidden). -/
noncomputable def realServices (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) :
    Services Response HmacOracle.QueryCache where
  derive := realDerive setup.hmac setup.joint setup.dh seed scalar
  table message := HmacOracle.randomOracle message
  hiddenBuild token payload server := simulateQ (tailImpl setup codec checks)
    (PqxdhServerRegistrationPublication.build setup.source token.pending token.root payload () server)
  hiddenAfter _ := pure none

end Real

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.evalSPMF_bind_congr_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.evalSPMF_bind_congr_support
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.relTriple_map_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.relTriple_map_same
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.relTriple_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.relTriple_support
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.support_run_bad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.support_run_bad
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.relTriple_until_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.relTriple_until_bad
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.probEvent_le_until_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.probEvent_le_until_bad
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.done_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.done_run
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.eager_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.eager_run
