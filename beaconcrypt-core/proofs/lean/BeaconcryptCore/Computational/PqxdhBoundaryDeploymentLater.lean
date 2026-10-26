-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep
import BeaconcryptCore.Computational.PqxdhBoundaryLoggedAccept

/-! PB-D LQ-F source join (item 7, increment I4; survey row PB-13). `laterStep` is the adaptive source step of the LQ-F run phase on the run state of `PqxdhDeploymentLaterServerGame.snapImpl` (finish snapshot, complete deployment state, private ephemeral log): a `finish` first captures the addressed owner's prekey and one-time fields from the pre-command owners (`snapshotAt`, the cut that `PqxdhDeploymentLater.snapImpl` uses) and then runs the classical source finish; a raw accept runs the source-collected logged acceptance `PqxdhBoundaryLoggedAccept.deployment` (PB-03 under LQ-F, which appends one optional Server-ephemeral entry to the log) and keeps the snapshot; every other command runs the classical source step `PqxdhBoundaryDeploymentStep.sourceStep` (increment I3, whose commands are CE's approved interface under its deviations D1-D5, classification E) on the deployment state and keeps the snapshot and the log (`laterStep_finish`, `laterStep_accept`, `laterStep_quiet`). `laterStep_exact` equates it, for every command and every run state, with the lifted LQ-F snapshot handler at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`; it cites only the published `PqxdhBoundaryLoggedAccept.deployment_exact` and `PqxdhBoundaryDeploymentStep.step_exact` and the frozen LQ-F lemma `PqxdhDeploymentLaterServerGame.handler_quiet`, all quantified over every state, so no reachability invariant, success premise or new contract is needed. `laterSourceGame` is the adaptive LQ-F source execution: the source-ordered Server birth of `PqxdhBoundaryBirth.serverBirth`, then `PqxdhBoundaryProgram.execute` of `laterStep` on `A₁` wrapped by CE's own secrecy layer `PqxdhDeploymentSecrecy.wrap` from the empty snapshot and log, and, only after a successful run (`PqxdhBoundaryProgram.resume`), the modeled reveal `(revealOf owners snapshot, (some seed, log))` and the post phase of `A₂` under `PqxdhDeploymentLater.postImpl` (fresh coins, the public HMAC and the BLAKE2b oracle on the final caches). `later` equates it with the LQ-F game `PqxdhDeploymentLaterServerGame.game` at the production instance on the full returned value (created Server, `A₂`'s output, the run's ledger, the finish snapshot, the complete final deployment state, the ephemeral log and the runtime), up to the `ok` wrapper `okMap`; no ghost is projected away and no event premise or success conditioning is introduced. `unwrap` reads a source value back, so every observation, evaluation measure and event transfers (`later_observe`, `later_evalDist`, and the event form `later_probEvent`). The identity index is arbitrary (`later_zero` is the index-0 instance of the PB-D pin #415) and `checks` is a free parameter (PB-14). The reveal and the post phase are the approved modeled post-run interface (classification E): a modeled disclosure, not physical erasure or a source getter, with classical post-run queries (no quantum or QROM adversary) and no later authentication claim; the secrecy layer and the model oracles are CE's own (E). The ghost capture sites (the Server seed at birth, the Beacon keys at creation, the one-time scalar at `beaconcrypt/src/beacon.rs:302`, the finish snapshot at its cut, the Server ephemeral at `beaconcrypt/src/server.rs:368`, and the two approved exceptions: (a) one-time scalars of failed bundle attempts and (b) Server ephemerals of accepts that fail KEM-key admission inside `encapsulate` at `beaconcrypt/src/server.rs:373`) stay reviewed transcription (RT) under the proposed check PB-GHOST, which is not implemented. Persistence and Cap'n Proto are out of scope. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhDeploymentInterface (Spec FreshBounds Mode ModeSpec asModeO)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentLater (Snap PostSpec postImpl snapshotAt finishOwner revealOf)
open PqxdhDeploymentLaterServerSource (Log)
open PqxdhDeploymentLaterServerGame (Reveal LaterState)
open PqxdhBoundaryProgram (Step liftStep)
open PqxdhBoundaryDeploymentStep (sourceStep)
variable {ι KemSK Reader Response Message Root A X Out Y : Type} {baseSpec : OracleSpec ι}

/-- The run-phase state of the LQ-F source execution: the finish snapshot, the complete deployment state and the private ephemeral log, the state of `PqxdhDeploymentLaterServerGame.snapImpl`. -/
abbrev RunState (KemSK : Type) := Snap × (PqxdhDeploymentNative.State KemSK × Log)

/-- The logged source step: a raw accept runs the source-collected logged acceptance `PqxdhBoundaryLoggedAccept.deployment` (PB-03 under LQ-F), which reinstalls the accepted shared state and appends one optional ephemeral-scalar entry to the log; every other command runs the classical source step `PqxdhBoundaryDeploymentStep.sourceStep` on the deployment state and keeps the log. -/
noncomputable def loggedStep (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 357#usize)
    (checks : Checks) (serverSeed : IdentitySeed) : Step Spec (PqxdhDeploymentNative.State KemSK × Log)
  | .inr (.accept raw) => fun state => (fun result => (RustM.ok result.1, result.2)) <$>
      (PqxdhBoundaryLoggedAccept.deployment setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks serverSeed
        raw).run state
  | query => fun state => (fun result => (result.1, (result.2, state.2))) <$>
      sourceStep setup codec reader erased checks serverSeed query state.1

/-- The adaptive LQ-F source step: a `finish` first captures the addressed owner's prekey and one-time fields from the pre-command owners (`snapshotAt`, the cut of `PqxdhDeploymentLater.snapImpl`), then every command runs the logged source step. -/
noncomputable def laterStep (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 357#usize)
    (checks : Checks) (serverSeed : IdentitySeed) : Step Spec (RunState KemSK) := fun query state =>
  (fun result => (result.1, (snapshotAt state.1 state.2.1.native.owners (finishOwner query), result.2))) <$>
    loggedStep setup codec reader erased checks serverSeed query state.2

/-- The modeled LQ-F post phase after a successful run: the reveal of the final state (the Beacon-side reveal `revealOf` of the final owners and snapshot, the Server identity seed and the ephemeral log) is given to `A₂` with the run's output, and `A₂` runs against `PqxdhDeploymentLater.postImpl` (fresh coins, the public HMAC and the BLAKE2b oracle on the final caches). The ledger, the snapshot and the log of the run are kept. -/
noncomputable def postPhase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (second : X → Reveal → OracleComp PostSpec Out) (value : X × Ledger)
    (after : RunState KemSK) : ProbComp (RustM (Out × Ledger) × RunState KemSK) :=
  (fun post => (RustM.ok (post.1, value.2), (after.1, (post.2, after.2.2)))) <$>
    (simulateQ (postImpl setup codec checks serverSeed)
      (second value.1 (revealOf after.2.1.native.owners after.1, (some serverSeed, after.2.2)))).run after.2.1

/-- The LQ-F source execution from a deployment state: adaptive source execution of `laterStep` on `A₁` wrapped by CE's secrecy layer at the production codec, from the empty snapshot and log; only a successful run enters the modeled reveal and post phase (`PqxdhBoundaryProgram.resume`). -/
noncomputable def laterSourceExec (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 357#usize) (checks : Checks)
    (serverSeed : IdentitySeed) (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → Reveal → OracleComp PostSpec Out) (start : PqxdhDeploymentNative.State KemSK) :
    ProbComp (RustM (Out × Ledger) × RunState KemSK) :=
  PqxdhBoundaryProgram.execute (laterStep setup codec reader erased checks serverSeed)
      (PqxdhDeploymentSecrecy.wrap setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
        setup.serverKeyId bounds (asModeO mode first)) (Snap.empty, (start, [])) >>=
    PqxdhBoundaryProgram.resume
      (postPhase setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks serverSeed second)

/-- The returned value of the LQ-F source game: on a successful Server birth, the encoded created Server, the literal Rust result (on success `A₂`'s output with the run's final ledger) and the run state (snapshot, final deployment state after the post phase, ephemeral log); `none` when initialization fails. -/
abbrev Outcome (KemSK Out : Type) :=
  Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × RustM (Out × Ledger) × RunState KemSK)

/-- The returned value of the LQ-F game `PqxdhDeploymentLaterServerGame.game`. -/
abbrev GameOutcome (KemSK Out : Type) :=
  Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × LaterState KemSK)

/-- The adaptive LQ-F source game: source-ordered Server birth, then the LQ-F source execution from the initial deployment state of the created Server. A failed initialization ends the run with no outcome and its returned runtime. -/
noncomputable def laterSourceGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 357#usize) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) :
    StateT A ProbComp (Outcome KemSK Out) := fun runtime => do
  let born ← (PqxdhBoundaryBirth.serverBirth setup.joint ensureInit identityIndex setup.serverKeyId).run runtime
  match born.1 with
  | none => pure (none, born.2)
  | some created =>
    (fun result => (some (PqxdhRegistrationJointServerBirth.encode created, result), born.2)) <$>
      laterSourceExec setup codec reader erased checks created.seed bounds mode first second
        (PqxdhDeploymentNative.initial created)

/-- An LQ-F game value as a source value: `A₂`'s output and the final ledger are wrapped in Rust `ok`; the created Server, the snapshot, the final deployment state, the ephemeral log and the runtime are unchanged. -/
def okMap (outcome : GameOutcome KemSK Out × A) : Outcome KemSK Out × A :=
  (outcome.1.map fun result => (result.1, RustM.ok (result.2.1, result.2.2.1), result.2.2.2), outcome.2)

/-- A source value read back as an LQ-F game value: an `ok` result moves the ledger back beside the run state; a `fail` or `div` result, which `later` shows is never produced, reads as no outcome. -/
def unwrap (outcome : Outcome KemSK Out × A) : GameOutcome KemSK Out × A :=
  (outcome.1.bind fun result => match result.2.1 with
    | .ok value => some (result.1, value.1, (value.2, result.2.2))
    | _ => none, outcome.2)

/-- A command other than a raw accept runs the classical source step on the deployment state and keeps the log. -/
theorem loggedStep_quiet (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 357#usize)
    (checks : Checks) (serverSeed : IdentitySeed) (query : Spec.Domain)
    (notAccept : ∀ raw, query ≠ .inr (.accept raw)) (state : PqxdhDeploymentNative.State KemSK) (log : Log) :
    loggedStep setup codec reader erased checks serverSeed query (state, log) =
      (fun result => (result.1, (result.2, log))) <$>
        sourceStep setup codec reader erased checks serverSeed query state := by
  rcases query with coin | command
  · rfl
  · cases command
    case accept raw => exact absurd rfl (notAccept raw)
    all_goals rfl

/-- Per-command logged join: for every command and every complete deployment state and log, the logged source step equals the lifted LQ-F logged handler `PqxdhDeploymentLaterServerGame.handler` at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`; the raw accept by the published `PqxdhBoundaryLoggedAccept.deployment_exact`, every other command by `PqxdhBoundaryDeploymentStep.step_exact` and `PqxdhDeploymentLaterServerGame.handler_quiet`. -/
theorem loggedStep_exact (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 357#usize)
    (checks : Checks) (serverSeed : IdentitySeed) :
    ∀ query state, loggedStep setup codec reader erased checks serverSeed query state =
      liftStep (PqxdhDeploymentLaterServerGame.handler setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) serverSeed) query state := by
  rintro query ⟨state, log⟩
  have quiet : ∀ query : Spec.Domain, (∀ raw, query ≠ .inr (.accept raw)) →
      loggedStep setup codec reader erased checks serverSeed query (state, log) =
        liftStep (PqxdhDeploymentLaterServerGame.handler setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          checks (RawCtxFrameDecoding.sender reader.model) serverSeed) query (state, log) := by
    intro query notAccept
    rw [loggedStep_quiet setup codec reader erased checks serverSeed query notAccept state log,
      PqxdhBoundaryDeploymentStep.step_exact]
    simp only [liftStep]
    rw [PqxdhDeploymentLaterServerGame.handler_quiet _ _ _ _ _ query notAccept, Functor.map_map, Functor.map_map]
  rcases query with coin | command
  · exact quiet (.inl coin) (fun raw same => by cases same)
  · cases command
    case accept raw =>
      change (fun result => (RustM.ok result.1, result.2)) <$>
          (PqxdhBoundaryLoggedAccept.deployment setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            serverSeed raw).run (state, log) = _
      rw [PqxdhBoundaryLoggedAccept.deployment_exact setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) serverSeed raw (state, log)]
      rfl
    all_goals exact quiet _ (fun raw same => by cases same)

/-- The source `finish` step captures the addressed owner's prekey and one-time fields from the pre-command owners, then runs the classical source finish (PB-06) on the deployment state and keeps the log. -/
theorem laterStep_finish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 357#usize)
    (checks : Checks) (serverSeed : IdentitySeed) (index : Nat) (raw : Pqxdh.Bytes) (state : RunState KemSK) :
    laterStep setup codec reader erased checks serverSeed (.inr (.finish index raw)) state =
      (fun result => (result.1, (snapshotAt state.1 state.2.1.native.owners (some index), (result.2, state.2.2)))) <$>
        sourceStep setup codec reader erased checks serverSeed (.inr (.finish index raw)) state.2.1 := by
  rcases state with ⟨snap, deployment, log⟩
  simp only [laterStep, finishOwner]
  rw [loggedStep_quiet setup codec reader erased checks serverSeed _ (fun raw same => by cases same), Functor.map_map]

/-- The source raw-accept step runs the source-collected logged acceptance (W4) on the deployment state and log and keeps the snapshot. -/
theorem laterStep_accept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 357#usize)
    (checks : Checks) (serverSeed : IdentitySeed) (raw : Pqxdh.Bytes) (state : RunState KemSK) :
    laterStep setup codec reader erased checks serverSeed (.inr (.accept raw)) state =
      (fun result => (RustM.ok result.1, (state.1, result.2))) <$>
        (PqxdhBoundaryLoggedAccept.deployment setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks serverSeed
          raw).run state.2 := by
  simp only [laterStep, loggedStep, finishOwner, Functor.map_map]
  rfl

/-- Every command other than a `finish` and a raw accept runs the classical source step on the deployment state and keeps the snapshot and the log. -/
theorem laterStep_quiet (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 357#usize)
    (checks : Checks) (serverSeed : IdentitySeed) (query : Spec.Domain)
    (notAccept : ∀ raw, query ≠ .inr (.accept raw)) (notFinish : finishOwner query = none) (state : RunState KemSK) :
    laterStep setup codec reader erased checks serverSeed query state =
      (fun result => (result.1, (state.1, (result.2, state.2.2)))) <$>
        sourceStep setup codec reader erased checks serverSeed query state.2.1 := by
  rcases state with ⟨snap, deployment, log⟩
  simp only [laterStep, notFinish, loggedStep_quiet setup codec reader erased checks serverSeed query notAccept,
    Functor.map_map]
  rfl

/-- PB-13 per-command join: for every command and every run state (snapshot, complete deployment state, ephemeral log), the LQ-F source step equals the lifted LQ-F snapshot handler `PqxdhDeploymentLaterServerGame.snapImpl` at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, for every `checks`. This is the operational premise of `PqxdhBoundaryProgram.source_exact`. -/
theorem laterStep_exact (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 357#usize)
    (checks : Checks) (serverSeed : IdentitySeed) :
    ∀ query state, laterStep setup codec reader erased checks serverSeed query state =
      liftStep (PqxdhDeploymentLaterServerGame.snapImpl setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) serverSeed) query state := by
  intro query state
  change (fun result => (result.1, (snapshotAt state.1 state.2.1.native.owners (finishOwner query), result.2))) <$>
      loggedStep setup codec reader erased checks serverSeed query state.2 =
    (fun result => (RustM.ok result.1, result.2)) <$>
      ((fun result => (result.1, (snapshotAt state.1 state.2.1.native.owners (finishOwner query), result.2))) <$>
        (PqxdhDeploymentLaterServerGame.handler setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) serverSeed query).run state.2)
  rw [loggedStep_exact setup codec reader erased checks serverSeed query state.2]
  simp only [liftStep, Functor.map_map]

/-- Every supported outcome of every LQ-F source step is `ok` with a supported reply and complete poststate of the LQ-F snapshot handler; the entry-state placeholder of the adapted record and finish executors is never observed. -/
theorem laterStep_normal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 357#usize)
    (checks : Checks) (serverSeed : IdentitySeed) (query : Spec.Domain) (state : RunState KemSK)
    (result : RustM (Spec.Range query) × RunState KemSK)
    (supported : result ∈ support (laterStep setup codec reader erased checks serverSeed query state)) :
    ∃ reply ∈ support ((PqxdhDeploymentLaterServerGame.snapImpl setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
        checks (RawCtxFrameDecoding.sender reader.model) serverSeed query).run state),
      result = (.ok reply.1, reply.2) := by
  rw [laterStep_exact setup codec reader erased checks serverSeed query state, liftStep, support_map] at supported
  obtain ⟨reply, member, rfl⟩ := supported
  exact ⟨reply, member, rfl⟩

/-- Whole-program LQ-F source join: for every native-interface program and every run state, adaptive source execution of `laterStep` is the simulation under the LQ-F snapshot handler at the production instance, with each reply and the complete poststate, by `PqxdhBoundaryProgram.source_exact` and `laterStep_exact`. -/
theorem execute_exact {Z : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 357#usize)
    (checks : Checks) (serverSeed : IdentitySeed) (work : OracleComp Spec Z) (state : RunState KemSK) :
    PqxdhBoundaryProgram.execute (laterStep setup codec reader erased checks serverSeed) work state =
      (fun result => (RustM.ok result.1, result.2)) <$>
        (simulateQ (PqxdhDeploymentLaterServerGame.snapImpl setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          checks (RawCtxFrameDecoding.sender reader.model) serverSeed) work).run state :=
  PqxdhBoundaryProgram.source_exact _ _ (laterStep_exact setup codec reader erased checks serverSeed) work state

/-- The LQ-F source execution from any deployment state is the LQ-F later execution `PqxdhDeploymentLaterServerGame.exec` at the production instance, with `A₂`'s output and the run's ledger wrapped in `ok` and the snapshot, the final deployment state and the log unchanged. -/
theorem exec_exact (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 357#usize) (checks : Checks)
    (serverSeed : IdentitySeed) (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → Reveal → OracleComp PostSpec Out) (start : PqxdhDeploymentNative.State KemSK) :
    laterSourceExec setup codec reader erased checks serverSeed bounds mode first second start =
      (fun result => (RustM.ok (result.1, result.2.1), result.2.2)) <$>
        PqxdhDeploymentLaterServerGame.exec setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) serverSeed bounds mode first second start := by
  simp only [laterSourceExec, execute_exact, PqxdhDeploymentLaterServerGame.exec,
    PqxdhDeploymentLaterServerGame.later_run_wrap, map_bind, bind_map_left, PqxdhBoundaryProgram.resume, postPhase,
    bind_pure_comp, Functor.map_map]

/-- `unwrap` is a left inverse of `okMap`: no part of an LQ-F game value is lost. -/
theorem unwrap_okMap (outcome : GameOutcome KemSK Out × A) : unwrap (okMap outcome) = outcome := by
  rcases outcome with ⟨_ | ⟨created, value, ledger, rest⟩, runtime⟩ <;> rfl

/-- PB-13 LQ-F join: for every setup, codec, frame reader, buffer, `checks`, initialization, identity index, bounds, mode, run-phase adversary `A₁`, post-phase adversary `A₂` and runtime, the LQ-F source game equals the LQ-F game `PqxdhDeploymentLaterServerGame.game` at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model` on the full returned value (created Server, `A₂`'s output, the run's ledger, the finish snapshot, the complete final deployment state and the ephemeral log, runtime), up to the `ok` wrapper `okMap`. -/
theorem later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 357#usize) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (runtime : A) :
    (laterSourceGame setup codec reader erased checks ensureInit identityIndex bounds mode first second).run runtime =
      okMap <$> (PqxdhDeploymentLaterServerGame.game setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit identityIndex bounds mode first second).run runtime := by
  simp only [laterSourceGame, PqxdhDeploymentLaterServerGame.game, StateT.run, PqxdhBoundaryBirth.server_source,
    map_bind]
  apply bind_congr
  rintro ⟨_ | created, after⟩
  · simp only [map_pure]
    rfl
  · simp only [exec_exact, Functor.map_map]
    rfl

/-- The index-0 instance of `later`, the identity index of the CE-12-L headline game (PB-D pin #415). -/
theorem later_zero (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 357#usize) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (runtime : A) :
    (laterSourceGame setup codec reader erased checks ensureInit 0 bounds mode first second).run runtime =
      okMap <$> (PqxdhDeploymentLaterServerGame.game setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit 0 bounds mode first second).run runtime :=
  later setup codec reader erased checks ensureInit 0 bounds mode first second runtime

/-- Every supported outcome of the LQ-F source game is the `okMap` image of a supported outcome of the LQ-F game at the production instance; in particular the source game never returns a `fail` or `div` result. -/
theorem later_normal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 357#usize) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (runtime : A)
    (outcome : Outcome KemSK Out × A)
    (supported : outcome ∈ support
      ((laterSourceGame setup codec reader erased checks ensureInit identityIndex bounds mode first second).run
        runtime)) :
    ∃ value ∈ support ((PqxdhDeploymentLaterServerGame.game setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
        checks (RawCtxFrameDecoding.sender reader.model) ensureInit identityIndex bounds mode first second).run runtime),
      outcome = okMap value := by
  rw [later, support_map] at supported
  obtain ⟨value, member, rfl⟩ := supported
  exact ⟨value, member, rfl⟩

/-- Any continuation of the LQ-F source game sees exactly the LQ-F game's returned value through `okMap`; no projection, success conditioning or event premise is introduced, and no ghost (snapshot or log) is forgotten. -/
theorem later_continuation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 357#usize) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (runtime : A)
    (next : Outcome KemSK Out × A → ProbComp Y) :
    ((laterSourceGame setup codec reader erased checks ensureInit identityIndex bounds mode first second).run runtime >>=
        next) =
      ((PqxdhDeploymentLaterServerGame.game setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit identityIndex bounds mode first second).run runtime >>=
          fun outcome => next (okMap outcome)) := by
  rw [later, bind_map_left]

/-- Generic observation transfer for item 8: for every observation `observe` of the LQ-F game's returned value, observing the LQ-F source game through `unwrap` is the same computation as observing the LQ-F game at the production instance. -/
theorem later_observe {Z : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 357#usize) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (runtime : A)
    (observe : GameOutcome KemSK Out × A → Z) :
    (fun outcome => observe (unwrap outcome)) <$>
        (laterSourceGame setup codec reader erased checks ensureInit identityIndex bounds mode first second).run runtime =
      observe <$> (PqxdhDeploymentLaterServerGame.game setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit identityIndex bounds mode first second).run runtime := by
  rw [later, Functor.map_map]
  simp only [unwrap_okMap]

/-- Generic distribution transfer for item 8 in the evaluation-measure form `𝒟[·]`: for every observation `observe` of the LQ-F game's returned value into a measurable space, the evaluation measure of observing the LQ-F source game through `unwrap` equals that of observing the LQ-F game at the production instance. -/
theorem later_evalDist {Z : Type} [MeasurableSpace Z] (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 357#usize) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (runtime : A)
    (observe : GameOutcome KemSK Out × A → Z) :
    𝒟[(fun outcome => observe (unwrap outcome)) <$>
        (laterSourceGame setup codec reader erased checks ensureInit identityIndex bounds mode first second).run
          runtime] =
      𝒟[observe <$> (PqxdhDeploymentLaterServerGame.game setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
        checks (RawCtxFrameDecoding.sender reader.model) ensureInit identityIndex bounds mode first second).run
          runtime] := by
  rw [later_observe]

/-- Generic event transfer for item 8: for every event `event` of the LQ-F game's returned value, its probability in the LQ-F game at the production instance equals the probability of `event ∘ unwrap` in the LQ-F source game. -/
theorem later_probEvent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 357#usize) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (runtime : A)
    (event : GameOutcome KemSK Out × A → Prop) :
    Pr{let x ← ((laterSourceGame setup codec reader erased checks ensureInit identityIndex bounds mode first
        second).run runtime)}[(event ∘ unwrap) x] =
      Pr{let x ← ((PqxdhDeploymentLaterServerGame.game setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit identityIndex bounds mode first second).run runtime)}[
        event x] := by
  rw [later, prEvent_map]
  simp only [Function.comp_apply, unwrap_okMap]

end BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.loggedStep_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.loggedStep_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.loggedStep_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.loggedStep_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.laterStep_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.laterStep_finish

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.laterStep_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.laterStep_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.laterStep_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.laterStep_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.laterStep_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.laterStep_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.laterStep_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.laterStep_normal

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.execute_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.execute_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.exec_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.exec_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.unwrap_okMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.unwrap_okMap

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.later

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.later_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.later_zero

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.later_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.later_normal

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.later_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.later_continuation

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.later_observe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.later_observe

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.later_evalDist' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.later_evalDist

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.later_probEvent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater.later_probEvent
