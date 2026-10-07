-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLater
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative

/-! LQ-F: the later-quantum game of the common deployment experiment for the exact profile. The game `game` constructs the Server from a generated seed (never a supplied one), runs a first adversary `A₁` against the run-phase handler `laterHandler`, computes the reveal from the final state, and runs a second adversary `A₂` on the run's output and the reveal with post-run coins, the public HMAC and the BLAKE2b oracle as its only queries, exactly as the Beacon-side game `PqxdhDeploymentLater.laterGame` does. The run-phase handler is the Beacon-side one with one more ghost change: a raw accept runs the native logged accept `LaterServerNative.acceptLogged` and appends its entry to an ephemeral log kept beside the deployment state (`handler`); every other command runs the unchanged native handler of the deployment experiment, with the finish snapshot of LQ (`snapImpl`) and the secrecy ledger on top. The reveal (`Reveal`) is the Beacon-side reveal of LQ, `revealOf` of the final owners and snapshot, together with the Server reveal `(some seed, log)`: the constructed Server's Ed25519 identity seed (its X25519 identity secret is the production conversion of the seed) and the log, which holds, per raw accept in raw-accept order, the secret of the Server ephemeral the accept generated whenever its generation step was reached and returned one (`none` otherwise). This is the owner's exact profile: every honest Ed25519 identity secret and every honest X25519 secret except the one-time scalars of failed Beacon bundle attempts, which LQ excludes (design recommendation 2) and whose public keys are never output; Diffie-Hellman outputs are derived from the revealed scalars and public points, not listed. ML-KEM secret keys and shared secrets, the Extract family and R1 cache, ghost touches, roots, chains, kernels, skipped keys and plaintexts are never revealed; the reveal's type holds only identity seeds and scalars. Forgetting the log gives back the native handler of the experiment exactly (`handler_erase`, `run_erase`) and the Beacon-side run-phase handler (`snapImpl_erase`, `later_erase`), so the run phase of this game with the log forgotten is the run phase of the Beacon-side game (`runPhase_erase`) and, with the snapshot forgotten too, the classical common deployment experiment (`runPhase_classical`). The post phase changes only the caches and keeps the ledger, the snapshot and the log (`game_frame`), so an event of the Server's public data, the ledger and the deployment state that ignores the caches has the same distribution at the end of this game as at the end of the classical game (`game_classical_event`), and the run-phase terms carry over unchanged. The post-run queries are classical: this is a classical adversary with a post-run disclosure, not a quantum or QROM adversary. Authentication is not claimed in this mode. No security claim is made here. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity PqxdhJointGapDh
open PqxdhDeploymentInterface (Spec Command ModeSpec Mode FreshBounds asModeO)
open PqxdhDeploymentSecrecy (Ledger ledgerImpl wrap)
open PqxdhDeploymentLater (Snap PostSpec postImpl finishOwner snapshotAt revealOf Caches post_frame)
open PqxdhDeploymentLaterServerSource (Log)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Out : Type}

/-- The LQ-F reveal: the Beacon-side reveal of LQ and the Server reveal (the Server identity seed and the ephemeral log). -/
abbrev Reveal := PqxdhDeploymentLater.Reveal × PqxdhDeploymentLaterServerSource.Reveal

/-- The native handler of the deployment experiment with the logged Server accept: a raw accept runs the native logged accept on the registration state and appends its entry to the log; every other command runs the unchanged native handler and keeps the log. -/
noncomputable def handler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) :
    QueryImpl Spec (StateT (PqxdhDeploymentNative.State KemSK × Log) ProbComp)
  | .inr (.accept raw) => fun state => (fun result => (result.1, ({ state.1 with native := result.2.1 }, result.2.2))) <$>
      (PqxdhDeploymentLaterServerNative.native setup codec checks serverSeed (.inl (.inl (.inr (.accept raw))))).run
        (state.1.native, state.2)
  | query => fun state => (fun result => (result.1, (result.2, state.2))) <$>
      (PqxdhDeploymentNative.handler setup codec checks route serverSeed query).run state.1

/-- Forgetting the log of one logged step gives the native step of the deployment experiment. -/
theorem handler_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (query : Spec.Domain)
    (state : PqxdhDeploymentNative.State KemSK) (log : Log) :
    Prod.map id Prod.fst <$> (handler setup codec checks route serverSeed query).run (state, log) =
      (PqxdhDeploymentNative.handler setup codec checks route serverSeed query).run state := by
  rcases query with coin | command
  · simp only [handler, StateT.run, Functor.map_map, Prod.map_apply, id_eq]
    exact id_map _
  · cases command
    case accept raw =>
      have projected := PqxdhDeploymentLaterServerNative.query_projection setup codec checks serverSeed
        (.inl (.inr (.accept raw))) state.native log
      change Prod.map id Prod.fst <$> ((fun result => (result.1, ({ state with native := result.2.1 }, result.2.2))) <$>
        (PqxdhDeploymentLaterServerNative.native setup codec checks serverSeed (.inl (.inl (.inr (.accept raw))))).run
          (state.native, log)) = (fun result => (result.1, { state with native := result.2 })) <$>
        (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr (.accept raw))).run state.native
      rw [show (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr (.accept raw))).run state.native =
        (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed (.inl (.inr (.accept raw)))).run
          state.native from rfl, ← projected, Functor.map_map, Functor.map_map]
      rfl
    all_goals simp only [handler, StateT.run, Functor.map_map, Prod.map_apply, id_eq]; exact id_map _

/-- A command other than a raw accept runs the unchanged native handler and keeps the log. -/
theorem handler_quiet (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (query : Spec.Domain)
    (notAccept : ∀ raw, query ≠ .inr (.accept raw)) (state : PqxdhDeploymentNative.State KemSK) (log : Log) :
    (handler setup codec checks route serverSeed query).run (state, log) =
      (fun result => (result.1, (result.2, log))) <$>
        (PqxdhDeploymentNative.handler setup codec checks route serverSeed query).run state := by
  rcases query with coin | command
  · rfl
  · cases command
    case accept raw => exact absurd rfl (notAccept raw)
    all_goals rfl

/-- Forgetting the log of a whole logged run gives the native run of the deployment experiment: the log changes no reply and no deployment state. -/
theorem run_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) {Result : Type}
    (program : OracleComp Spec Result) (state : PqxdhDeploymentNative.State KemSK) (log : Log) :
    Prod.map id Prod.fst <$> (simulateQ (handler setup codec checks route serverSeed) program).run (state, log) =
      (simulateQ (PqxdhDeploymentNative.handler setup codec checks route serverSeed) program).run state :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (fun query state => handler_erase setup codec checks route serverSeed query state.1 state.2) program (state, log)

/-- The logged handler with the finish snapshot of LQ: a `finish` first captures the addressed owner's current prekey and one-time fields, then every command runs the logged handler. -/
noncomputable def snapImpl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) :
    QueryImpl Spec (StateT (Snap × (PqxdhDeploymentNative.State KemSK × Log)) ProbComp) := fun query state =>
  (fun result => (result.1, (snapshotAt state.1 state.2.1.native.owners (finishOwner query), result.2))) <$>
    (handler setup codec checks route serverSeed query).run state.2

/-- Forgetting the log of one snapshot step gives the Beacon-side snapshot step of LQ. -/
theorem snapImpl_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (query : Spec.Domain)
    (state : Snap × (PqxdhDeploymentNative.State KemSK × Log)) :
    (fun result => (result.1, (result.2.1, result.2.2.1))) <$>
        (snapImpl setup codec checks route serverSeed query).run state =
      (PqxdhDeploymentLater.snapImpl setup codec checks route serverSeed query).run (state.1, state.2.1) := by
  change (fun result => (result.1, (result.2.1, result.2.2.1))) <$>
      ((fun result => (result.1, (snapshotAt state.1 state.2.1.native.owners (finishOwner query), result.2))) <$>
        (handler setup codec checks route serverSeed query).run state.2) =
    (fun result => (result.1, (snapshotAt state.1 state.2.1.native.owners (finishOwner query), result.2))) <$>
      (PqxdhDeploymentNative.handler setup codec checks route serverSeed query).run state.2.1
  rw [← handler_erase setup codec checks route serverSeed query state.2.1 state.2.2, Functor.map_map,
    Functor.map_map]
  rfl

/-- A command other than a raw accept runs the Beacon-side snapshot step of LQ and keeps the log. -/
theorem snapImpl_quiet (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (query : Spec.Domain)
    (notAccept : ∀ raw, query ≠ .inr (.accept raw)) (snap : Snap) (state : PqxdhDeploymentNative.State KemSK)
    (log : Log) :
    (snapImpl setup codec checks route serverSeed query).run (snap, (state, log)) =
      (fun result => (result.1, (result.2.1, (result.2.2, log)))) <$>
        (PqxdhDeploymentLater.snapImpl setup codec checks route serverSeed query).run (snap, state) := by
  change (fun result => (result.1, (snapshotAt snap state.native.owners (finishOwner query), result.2))) <$>
      (handler setup codec checks route serverSeed query).run (state, log) =
    (fun result => (result.1, (result.2.1, (result.2.2, log)))) <$>
      ((fun result => (result.1, (snapshotAt snap state.native.owners (finishOwner query), result.2))) <$>
        (PqxdhDeploymentNative.handler setup codec checks route serverSeed query).run state)
  rw [handler_quiet setup codec checks route serverSeed query notAccept, Functor.map_map, Functor.map_map]

/-- The run-phase state: the secrecy ledger, the snapshot, the deployment state and the ephemeral log. -/
abbrev LaterState (KemSK : Type) := Ledger × (Snap × (PqxdhDeploymentNative.State KemSK × Log))

/-- The run-phase handler: the secrecy layer composed with the logged snapshot handler. -/
noncomputable def laterHandler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (bounds : FreshBounds) :
    QueryImpl PqxdhDeploymentInterface.FullSpec (StateT (LaterState KemSK) ProbComp) :=
  ((snapImpl setup codec checks route serverSeed).mapStateTBase
    (ledgerImpl setup.source.crypto codec setup.serverKeyId bounds)).flattenStateT

/-- Running a complete-interface adversary under the run-phase handler is running the wrapped adversary under the logged snapshot handler, with the ledger moved into the state. -/
theorem later_run_wrap (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (bounds : FreshBounds)
    (adversary : OracleComp PqxdhDeploymentInterface.FullSpec X)
    (state : Snap × (PqxdhDeploymentNative.State KemSK × Log)) :
    (simulateQ (laterHandler setup codec checks route serverSeed bounds) adversary).run (Ledger.empty, state) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (snapImpl setup codec checks route serverSeed)
          (wrap setup.source.crypto codec setup.serverKeyId bounds adversary)).run state := by
  rw [wrap, OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  simp only [laterHandler]
  exact (id_map _).symm

/-- Forgetting the log of the run phase from any start gives the Beacon-side run phase of LQ, jointly over the output, the ledger, the snapshot and the deployment state. -/
theorem later_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (bounds : FreshBounds)
    (adversary : OracleComp PqxdhDeploymentInterface.FullSpec X) (snap : Snap)
    (state : PqxdhDeploymentNative.State KemSK) (log : Log) :
    (fun result => (result.1, (result.2.1, (result.2.2.1, result.2.2.2.1)))) <$>
        (simulateQ (laterHandler setup codec checks route serverSeed bounds) adversary).run
          (Ledger.empty, (snap, (state, log))) =
      (simulateQ (PqxdhDeploymentLater.laterHandler setup codec checks route serverSeed bounds) adversary).run
        (Ledger.empty, (snap, state)) := by
  rw [later_run_wrap, PqxdhDeploymentLater.later_run_wrap, Functor.map_map]
  have erased := OracleComp.map_run_simulateQ_eq_of_query_map_eq (snapImpl setup codec checks route serverSeed)
    (PqxdhDeploymentLater.snapImpl setup codec checks route serverSeed) (fun state => (state.1, state.2.1))
    (fun query state => snapImpl_erase setup codec checks route serverSeed query state)
    (wrap setup.source.crypto codec setup.serverKeyId bounds adversary) (snap, (state, log))
  rw [← erased, Functor.map_map]
  rfl

/-- The run phase alone, from the constructed Server: `A₁` against the run-phase handler from the empty ledger, snapshot and log. -/
noncomputable def runPhase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    StateT A ProbComp (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × LaterState KemSK)) :=
  fun runtime => do
  let born ← (PqxdhLiveServerConstruction.construct setup.joint ensureInit identityIndex setup.serverKeyId none).run runtime
  match born.1 with
  | none => pure (none, born.2)
  | some created =>
    (fun result => (some (PqxdhRegistrationJointServerBirth.encode created, result), born.2)) <$>
      (simulateQ (laterHandler setup codec checks route created.seed bounds) (asModeO mode adversary)).run
        (Ledger.empty, (Snap.empty, (PqxdhDeploymentNative.initial created, [])))

/-- Forgetting the log of the run phase gives the run phase of the Beacon-side later game, jointly over the Server's public data, the output, the ledger, the snapshot, the deployment state and the runtime state. -/
theorem runPhase_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    (fun outcome => (outcome.1.map fun result => (result.1, result.2.1, (result.2.2.1, (result.2.2.2.1,
        result.2.2.2.2.1))), outcome.2)) <$>
        (runPhase setup codec checks route ensureInit identityIndex bounds mode adversary).run runtime =
      (PqxdhDeploymentLater.laterRun setup codec checks route ensureInit identityIndex bounds mode adversary).run
        runtime := by
  simp only [runPhase, PqxdhDeploymentLater.laterRun, StateT.run, map_bind]
  apply bind_congr
  rintro ⟨_ | created, after⟩
  · simp only [map_pure, Option.map_none]
  · have erased := later_erase setup codec checks route created.seed bounds (asModeO mode adversary) Snap.empty
      (PqxdhDeploymentNative.initial created) []
    simp only [StateT.run] at erased
    simp only [← erased, Functor.map_map, Option.map_some]

/-- Theorem `runPhase_classical`: forgetting the log and the snapshot of the run phase gives exactly the classical common deployment experiment, jointly over the Server's public data, the adversary's output, the ledger, the complete deployment state and the runtime state. -/
theorem runPhase_classical (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    (fun outcome => (outcome.1.map fun result => (result.1, result.2.1, (result.2.2.1, result.2.2.2.2.1)),
        outcome.2)) <$>
        (runPhase setup codec checks route ensureInit identityIndex bounds mode adversary).run runtime =
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run
        runtime := by
  rw [← PqxdhDeploymentLater.snap_erase setup codec checks route ensureInit identityIndex bounds mode adversary
    runtime, ← runPhase_erase setup codec checks route ensureInit identityIndex bounds mode adversary runtime,
    Functor.map_map]
  congr 1
  funext outcome
  rcases outcome with ⟨_ | result, after⟩ <;> rfl

/-- The LQ-F later execution from a deployment state: the run phase of `A₁` with the ephemeral log, the reveal of the final state (the Beacon-side reveal of the final owners and snapshot, and the Server seed with the log), and the post phase of `A₂` on the run's output and the reveal. The ledger, the snapshot and the log of the run are returned with the deployment state after the post phase. -/
noncomputable def exec (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (start : PqxdhDeploymentNative.State KemSK) : ProbComp (Out × LaterState KemSK) := do
  let run ← (simulateQ (laterHandler setup codec checks route serverSeed bounds) (asModeO mode first)).run
    (Ledger.empty, (Snap.empty, (start, [])))
  let post ← (simulateQ (postImpl setup codec checks serverSeed)
    (second run.1 (revealOf run.2.2.2.1.native.owners run.2.2.1, (some serverSeed, run.2.2.2.2)))).run run.2.2.2.1
  pure (post.1, (run.2.1, (run.2.2.1, (post.2, run.2.2.2.2))))

/-- The LQ-F later-quantum game: the actual Server constructor with a generated seed (never a supplied one), then the LQ-F later execution of `A₁` and `A₂` from the initial deployment state. A constructor failure ends the run with no outcome. -/
noncomputable def game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → Reveal → OracleComp PostSpec Out) :
    StateT A ProbComp (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × LaterState KemSK)) :=
  fun runtime => do
  let born ← (PqxdhLiveServerConstruction.construct setup.joint ensureInit identityIndex setup.serverKeyId none).run runtime
  match born.1 with
  | none => pure (none, born.2)
  | some created =>
    (fun result => (some (PqxdhRegistrationJointServerBirth.encode created, result), born.2)) <$>
      exec setup codec checks route created.seed bounds mode first second (PqxdhDeploymentNative.initial created)

/-- Every outcome of the LQ-F later execution keeps the run phase's ledger, snapshot and log, and its final deployment state differs from the run phase's final state at most in the caches. -/
theorem game_frame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (start : PqxdhDeploymentNative.State KemSK) (result : Out × LaterState KemSK)
    (supported : result ∈ support (exec setup codec checks route serverSeed bounds mode first second start)) :
    ∃ run ∈ support ((simulateQ (laterHandler setup codec checks route serverSeed bounds) (asModeO mode first)).run
        (Ledger.empty, (Snap.empty, (start, [])))),
      result.2.1 = run.2.1 ∧ result.2.2.1 = run.2.2.1 ∧ result.2.2.2.2 = run.2.2.2.2 ∧
        Caches run.2.2.2.1 result.2.2.2.1 := by
  simp only [exec, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨run, runSupport, post, postSupport, rfl⟩ := supported
  exact ⟨run, runSupport, rfl, rfl, rfl, post_frame setup codec checks serverSeed _ _ post postSupport⟩

/-- Run-phase events: an event of the Server's public data, the ledger, the snapshot, the deployment state and the log that ignores the caches (the Extract family, the BLAKE2b cache and the ghost touch list) has the same distribution at the end of the LQ-F game as at the end of its run phase. -/
theorem game_event (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → Reveal → OracleComp PostSpec Out)
    (event : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × LaterState KemSK) → Bool)
    (invariant : ∀ created ledger snap state result log, Caches state result →
      event (some (created, (ledger, (snap, (result, log))))) = event (some (created, (ledger, (snap, (state, log))))))
    (runtime : A) :
    𝒟[(fun outcome => event (outcome.1.map fun result => (result.1, result.2.2))) <$>
        (game setup codec checks route ensureInit identityIndex bounds mode first second).run runtime] =
      𝒟[(fun outcome => event (outcome.1.map fun result => (result.1, result.2.2))) <$>
        (runPhase setup codec checks route ensureInit identityIndex bounds mode first).run runtime] := by
  simp only [game, runPhase, StateT.run, map_bind]
  apply evalDist_bind_congr
  rintro ⟨_ | created, after⟩
  · rfl
  · simp only [exec, Functor.map_map, map_bind, map_pure, Option.map_some]
    rw [map_eq_bind_pure_comp]
    apply evalDist_bind_congr
    intro run
    simp only [Function.comp_apply]
    conv_rhs => rw [← OracleComp.evalDist_bind_const ((simulateQ (postImpl setup codec checks created.seed)
      (second run.1 (revealOf run.2.2.2.1.native.owners run.2.2.1, (some created.seed, run.2.2.2.2)))).run
        run.2.2.2.1)]
    apply OracleComp.evalDist_bind_congr_of_support
    intro post member
    simp only [invariant _ _ _ _ _ _ (post_frame setup codec checks created.seed _ _ post member)]

/-- Run-phase events against the classical game: an event of the Server's public data, the ledger and the deployment state that ignores the caches has the same distribution at the end of the LQ-F game as at the end of the classical common deployment experiment. This is how the run-phase terms carry over unchanged. -/
theorem game_classical_event (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → Reveal → OracleComp PostSpec Out)
    (event : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × PqxdhDeploymentSecrecy.State KemSK) → Bool)
    (invariant : ∀ created ledger state result, Caches state result →
      event (some (created, (ledger, result))) = event (some (created, (ledger, state))))
    (runtime : A) :
    𝒟[(fun outcome => event (outcome.1.map fun result => (result.1, (result.2.2.1, result.2.2.2.2.1)))) <$>
        (game setup codec checks route ensureInit identityIndex bounds mode first second).run runtime] =
      𝒟[(fun outcome => event (outcome.1.map fun result => (result.1, result.2.2))) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode first).run
          runtime] := by
  have later := game_event setup codec checks route ensureInit identityIndex bounds mode first second
    (fun outcome => event (outcome.map fun result => (result.1, (result.2.1, result.2.2.2.1))))
    (fun created ledger snap state result log caches => by
      simp only [Option.map_some, invariant created ledger state result caches])
    runtime
  rw [← runPhase_classical setup codec checks route ensureInit identityIndex bounds mode first runtime,
    Functor.map_map]
  convert later using 2 <;> (congr 1; funext outcome; rcases outcome with ⟨_ | result, after⟩ <;> rfl)

end BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame.handler_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame.handler_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame.handler_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame.handler_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame.run_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame.run_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame.snapImpl_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame.snapImpl_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame.snapImpl_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame.snapImpl_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame.later_run_wrap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame.later_run_wrap

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame.later_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame.later_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame.runPhase_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame.runPhase_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame.runPhase_classical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame.runPhase_classical

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame.game_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame.game_frame

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame.game_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame.game_event

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame.game_classical_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame.game_classical_event
