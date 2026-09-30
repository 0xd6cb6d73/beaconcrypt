import B8bScratch.Generic

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
