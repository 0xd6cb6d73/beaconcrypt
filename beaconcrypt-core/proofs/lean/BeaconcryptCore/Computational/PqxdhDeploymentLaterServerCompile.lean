-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame
import BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile

/-! LQ-F: CE-COMPILE for the LQ-F later game of the common deployment experiment. The compiled LQ-F program `compileServer A₁ A₂` is a program of the logged source in four parts: the run part is the compiled run part of the Beacon-side mode (the CE-3 compiler with the finish pre-read, `PqxdhDeploymentLaterCompile.compileSnapImpl`, on the wrapped run-phase adversary), the terminal reads are the identity, prekey and one-time reads of every created owner, then the Server read `.inr ()`, and the post part runs `A₂` on the run's output and the reveal (the Beacon-side reveal and the Server reveal) through the unchanged compiler; the source14 parts are embedded unchanged. The native side is the native logged handler of `PqxdhDeploymentLaterServerNative`, so the compile simulation has to carry "native log equals source log" through the raw-accept case. The native logged accept commutes with the merge of the compiled program's local copies, because the core acceptance and root processing never read the peer map (`Commutes`, `tail_override`, `acceptLogged_override`, `accept_merge`); every other command issues no raw accept (`snap_quiet`), so under the native logged handler it runs as in the Beacon-side mode and keeps the log (`LaterServerNative.program_quiet`), and the per-step relation of the Beacon-side mode applies (`server_step`, which reuses `PqxdhDeploymentLaterCompile.snap_step`). The invariant of CE-3 is preserved (`server_good`), the run part simulates the logged run phase (`server_run`), and the continuation (terminal reads, Server read and post part, which issue no raw accept) gives exactly the LQ-F reveal and the native post phase on the merged state with the log kept (`server_continuation`). `compile_server_native`, `compile_server_game` and `compile_server_source` state that the LQ-F later game equals the merged execution of the compiled program, jointly over the Server's public data, `A₂`'s output, the ledger, the snapshot, the complete final deployment state, the ephemeral log and the runtime state, at the native level and at the level of the logged annotated source that the LQ-F KEM theorems use, under exactly the two approved codec contracts `Phase1ReadBack` and `Phase2ReadBack`. The Server read of the compiled program is an identity-pool reveal of the Server's slot in the annotated execution, so `revealedAt` holds for the Server identity: A2 and T5 must never be cited for this program, and authentication is not claimed in this mode. No security claim is made here. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity PqxdhJointGapDh PqxdhSecretInputKdf
open PqxdhDeploymentInterface (Spec Command ModeSpec Mode FreshBounds Budget asModeO)
open PqxdhDeploymentSecrecy (Ledger ledgerImpl wrap)
open PqxdhDeploymentCompile (Local merge compileImpl)
open PqxdhDeploymentCompileRegistration (overrideGame overrideShared)
open PqxdhDeploymentCompileInvariant (Good)
open PqxdhDeploymentLater (Snap PostSpec PostBudget postClass postEmbed postImpl finishOwner snapshotAt revealOf)
open PqxdhDeploymentLaterCompile (compileSnapImpl terminal)
open PqxdhDeploymentLaterServerSource (Log embed)
open PqxdhDeploymentLaterServerGame (Reveal LaterState)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Out Result Next : Type}

/-- A native game computation commutes with the Server override of the compiled program's local copies from every shared state. -/
def Commutes (copies : Local) (work : NativeGame KemSK Result) : Prop :=
  ∀ shared, work (overrideShared copies shared) =
    (fun result => (result.1, overrideShared copies result.2)) <$> work shared

/-- Pure results commute with the override. -/
theorem pure_commutes (copies : Local) (value : Result) : Commutes (KemSK := KemSK) copies (pure value) := by
  intro shared
  rfl

/-- Sequencing preserves commuting with the override. -/
theorem bind_commutes (copies : Local) (work : NativeGame KemSK Result) (next : Result → NativeGame KemSK Next)
    (first : Commutes copies work) (rest : ∀ value, Commutes copies (next value)) :
    Commutes copies (work >>= next) := by
  intro shared
  change (work (overrideShared copies shared) >>= fun result => next result.1 result.2) =
    (fun result => (result.1, overrideShared copies result.2)) <$> (work shared >>= fun result => next result.1 result.2)
  rw [first shared, bind_map_left, map_bind]
  exact bind_congr fun result => rest result.1 result.2

/-- A local game step commutes with the override when it commutes on the game state. -/
theorem local_commutes (copies : Local) (step : GameState KemSK → Result × GameState KemSK)
    (same : ∀ game, step (overrideGame copies game) = ((step game).1, overrideGame copies (step game).2)) :
    Commutes copies (localState step) := by
  intro shared
  change (pure ((step (overrideGame copies shared.2)).1, (shared.1, (step (overrideGame copies shared.2)).2)) :
    ProbComp _) = (fun result => (result.1, overrideShared copies result.2)) <$>
      (pure ((step shared.2).1, (shared.1, (step shared.2).2)) : ProbComp _)
  rw [same, map_pure]
  rfl

/-- The native ROM root reads and writes only the Extract family; it commutes with the override. -/
theorem romRoot_commutes (copies : Local) (hmac : HmacSha512) (input : PqxdhServerRootPreparation.Inputs Reader
    ScalarBytes PqxdhBeaconPhase2Preparation.Word32) (original : beaconcrypt_core.pqxdh.PendingServerRegistration) :
    Commutes (KemSK := KemSK) copies (romRoot hmac input original) := by
  intro shared
  simp only [romRoot, romRootBytes, Functor.map_map]
  rfl

/-- The literal native core acceptance and root processing commute with the override: they never read the peer map. -/
theorem nativeClient_commutes (copies : Local) (hmac : HmacSha512) (index : Nat)
    (control : beaconcrypt_core.pqxdh.ServerState) (serverBinding : beaconcrypt_core.pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PqxdhBeaconPhase2Preparation.Word32) :
    Commutes (KemSK := KemSK) copies (nativeClient hmac index control serverBinding input) := by
  unfold nativeClient
  split
  · exact pure_commutes copies _
  · exact pure_commutes copies _
  · exact pure_commutes copies _
  · refine bind_commutes copies _ _ ?_ fun root => bind_commutes copies _ _ ?_ fun _ => pure_commutes copies _
    · refine bind_commutes copies _ _ (romRoot_commutes copies hmac input _) fun root =>
        bind_commutes copies _ _ (local_commutes copies _ fun _ => rfl) fun _ => pure_commutes copies _
    · exact local_commutes copies _ fun _ => rfl

/-- The accept tail after the prefix commutes with the override when it starts from the overridden captured state: the published state is the overridden one, and the core acceptance and root processing never read the peer map. -/
theorem tail_override (setup : Setup baseSpec KemSK) (publicIdentity : PublicIdentity) (copies : Local)
    (game : GameState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader ScalarBytes PqxdhBeaconPhase2Preparation.Word32) ×
      List Pqxdh.Bytes) (shared : NativeState KemSK) :
    (PqxdhRegistrationJointServerAccept.tail setup publicIdentity (overrideGame copies game) collected).run
        (overrideShared copies shared) =
      (fun result => (result.1, overrideShared copies result.2)) <$>
        (PqxdhRegistrationJointServerAccept.tail setup publicIdentity game collected).run shared := by
  have rest : Commutes copies (match collected.1 with
      | none => pure none
      | some input => do
          let returned ← nativeClient setup.hmac game.sessions game.server.control
            ⟨PqxdhRootTableInitialization.rootArray publicIdentity.ed25519, setup.serverKeyId⟩ input
          match returned with
          | .ok (some token) => do
              nativeModify fun current =>
                { current with pending := Function.update current.pending game.sessions (some token) }
              pure (some game.sessions)
          | _ => pure none : NativeGame KemSK (Option Nat)) := by
    rcases collected with ⟨_ | input, consumed⟩
    · exact pure_commutes copies _
    · refine bind_commutes copies _ _ (nativeClient_commutes copies _ _ _ _ input) fun returned => ?_
      rcases returned with (_ | token) | _ | _
      all_goals first
        | exact pure_commutes copies _
        | exact bind_commutes copies _ _ (local_commutes copies _ fun _ => rfl) fun _ => pure_commutes copies _
  simp only [PqxdhRegistrationJointServerAccept.tail, StateT.run]
  exact rest (shared.1, { game with sessions := game.sessions + 1, server := { game.server with consumed := collected.2 } })

/-- The native logged accept commutes with the override of the compiled program's local copies. -/
theorem acceptLogged_override (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (raw : Pqxdh.Bytes) (copies : Local) (shared : NativeState KemSK) :
    (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed raw).run (overrideShared copies shared) =
      (fun result => (result.1, overrideShared copies result.2)) <$>
        (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed raw).run shared := by
  rw [PqxdhDeploymentLaterServerNative.acceptLogged_run, PqxdhDeploymentLaterServerNative.acceptLogged_run, map_bind]
  change (do
      let collected ← (PqxdhDeploymentLaterServerNative.prefixLogged setup codec checks seed raw).run
        shared.2.server.consumed
      let answer ← (PqxdhRegistrationJointServerAccept.tail setup (setup.joint.publicKeys seed)
        (overrideGame copies shared.2) (collected.1.1, collected.2)).run (overrideShared copies shared)
      pure ((answer.1, collected.1.2), answer.2)) = _
  apply bind_congr
  intro collected
  rw [tail_override, bind_map_left, map_bind]
  simp only [map_pure]

/-- The merged native logged accept: running the native logged accept on the merged registration state is merging after running it on the source14 state. -/
theorem accept_merge (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (raw : Pqxdh.Bytes) (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) :
    (PqxdhRegistrationSchedule.onShared (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed raw)).run
        (merge copies native).native =
      (fun result => (result.1, (merge copies result.2).native)) <$>
        (PqxdhRegistrationSchedule.onShared (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed
          raw)).run native :=
  PqxdhDeploymentCompileRegistration.onShared_merge copies _ native
    (acceptLogged_override setup codec checks seed raw copies native.shared)

/-- The source14 requests of the compiled program, answered by the native logged handler. -/
noncomputable def base (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) :
    QueryImpl (PqxdhRegistrationJointRevealSchedule.Spec KemSK)
      (StateT (PqxdhRegistrationSchedule.State KemSK × Log) ProbComp) :=
  (PqxdhDeploymentLaterServerNative.native setup codec checks serverSeed) ∘ₛ embed

/-- The compiled handler with the finish snapshot under the native logged handler, on the product of snapshot and local state with the source14 state and the log. -/
noncomputable def compiledImpl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) :
    QueryImpl Spec (StateT ((Snap × Local) × (PqxdhRegistrationSchedule.State KemSK × Log)) ProbComp) :=
  ((base setup codec checks serverSeed).mapStateTBase (compileSnapImpl setup codec route)).flattenStateT

/-- One compiled step is the compiled command with the finish pre-read run under the native logged handler, reassociated. -/
theorem compiledImpl_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (query : Spec.Domain) (snap : Snap)
    (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) (log : Log) :
    (compiledImpl setup codec checks route serverSeed query).run ((snap, copies), (native, log)) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (PqxdhDeploymentLaterServerNative.native setup codec checks serverSeed)
          (simulateQ embed ((compileSnapImpl setup codec route query).run (snap, copies)))).run (native, log) := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$> (simulateQ (base setup codec checks serverSeed)
    ((compileSnapImpl setup codec route query).run (snap, copies))).run (native, log) = _
  rw [base, QueryImpl.simulateQ_compose]

/-- Forgetting the log of one compiled step gives the compiled step of the Beacon-side mode. -/
theorem compiled_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (query : Spec.Domain) (snap : Snap)
    (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) (log : Log) :
    (fun result => (result.1, (result.2.1, result.2.2.1))) <$>
        (compiledImpl setup codec checks route serverSeed query).run ((snap, copies), (native, log)) =
      (PqxdhDeploymentLaterCompile.compiledSnapImpl setup codec checks route serverSeed query).run
        ((snap, copies), native) := by
  rw [compiledImpl_run, Functor.map_map]
  change _ = (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
      ((compileSnapImpl setup codec route query).run (snap, copies))).run native
  rw [← PqxdhDeploymentLaterServerNative.program_projection setup codec checks serverSeed _ native log,
    Functor.map_map]

/-- A deployment command other than a raw accept issues no raw accept, with or without the finish pre-read. -/
theorem snap_quiet (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : Spec.Domain) (notAccept : ∀ raw, query ≠ .inr (.accept raw))
    (state : Snap × Local) :
    ((compileSnapImpl setup codec route query).run state).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = .inl 3) 0 := by
  have bound := PqxdhDeploymentLaterCompile.snap_step_bound setup codec route (.inl 3) query state
  have zero : PqxdhDeploymentLaterCompile.laterCost (.inl 3) (PqxdhDeploymentCompileBudget.commandKind query) = 0 := by
    rcases query with coin | command
    · simp [PqxdhDeploymentLaterCompile.laterCost, PqxdhDeploymentCompileBudget.commandKind,
        PqxdhDeploymentCompileBudget.cost, PqxdhDeploymentCompileBudget.unit]
    · cases command
      case accept raw => exact absurd rfl (notAccept raw)
      all_goals simp [PqxdhDeploymentLaterCompile.laterCost, PqxdhDeploymentCompileBudget.commandKind,
        PqxdhDeploymentCompileBudget.cost, PqxdhDeploymentCompileBudget.unit]
  rwa [zero] at bound

/-- The compiled raw accept under the native logged handler: one native logged accept on the source14 state, its entry appended to the log and its reply recorded in the compiled program's public log. -/
theorem accept_compiled (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (raw : Pqxdh.Bytes) (snap : Snap)
    (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) (log : Log) :
    (compiledImpl setup codec checks route serverSeed (.inr (.accept raw))).run ((snap, copies), (native, log)) =
      (fun result => (result.1.1, ((snap, { copies with log := (PqxdhDeploymentCompile.logReply copies.log
          (.accept raw) result.1.1) }), (result.2, log ++ [result.1.2])))) <$>
        (PqxdhRegistrationSchedule.onShared (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks
          serverSeed raw)).run native := by
  have program : (compileSnapImpl setup codec route (.inr (.accept raw))).run (snap, copies) =
      (fun answer => (answer, (snap, { copies with log := (PqxdhDeploymentCompile.logReply copies.log (.accept raw)
        answer) }))) <$> ((PqxdhRegistrationJointRevealSchedule.Spec KemSK).query (.inl (.inr (.accept raw))) :
          OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) _) := by
    simp only [compileSnapImpl, finishOwner, PqxdhDeploymentLaterCompile.preRead, compileImpl,
      PqxdhDeploymentCompile.forwardLogged, PqxdhDeploymentCompile.forward, StateT.run, pure_bind, bind_assoc,
      map_eq_bind_pure_comp]
    rfl
  have answered : (PqxdhDeploymentLaterServerNative.native setup codec checks serverSeed
      (.inl (.inl (.inr (.accept raw))))).run (native, log) =
      (fun result => (result.1.1, (result.2, log ++ [result.1.2]))) <$>
        (PqxdhRegistrationSchedule.onShared (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks
          serverSeed raw)).run native := rfl
  rw [compiledImpl_run, program, simulateQ_map, simulateQ_spec_query]
  simp only [embed, simulateQ_map, simulateQ_spec_query, StateT.run_map]
  rw [answered, Functor.map_map, Functor.map_map]

/-- One step of the compile lemma for the LQ-F game: under the CE-3 invariant, merging after the compiled step with the finish snapshot under the native logged handler is the logged snapshot step from the merged state, with the same log. -/
theorem server_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (query : Spec.Domain) (snap : Snap)
    (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) (log : Log)
    (inv : PqxdhDeploymentCompileStep.Inv setup codec copies native) :
    (fun result => (result.1, (result.2.1.1, (merge result.2.1.2 result.2.2.1, result.2.2.2)))) <$>
        (compiledImpl setup codec checks route serverSeed query).run ((snap, copies), (native, log)) =
      (PqxdhDeploymentLaterServerGame.snapImpl setup codec checks route serverSeed query).run
        (snap, (merge copies native, log)) := by
  by_cases accept : ∃ raw, query = .inr (.accept raw)
  · obtain ⟨raw, rfl⟩ := accept
    have answered : (PqxdhDeploymentLaterServerGame.snapImpl setup codec checks route serverSeed (.inr (.accept raw))).run
        (snap, (merge copies native, log)) = (fun result => (result.1.1, (snap, ({ merge copies native with
          native := result.2 }, log ++ [result.1.2])))) <$>
        (PqxdhRegistrationSchedule.onShared (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks
          serverSeed raw)).run (merge copies native).native := by
      change (fun result => (result.1, (snap, result.2))) <$> ((fun result => (result.1, ({ merge copies native with
        native := result.2.1 }, result.2.2))) <$> ((fun result => (result.1.1, (result.2, log ++ [result.1.2]))) <$>
          (PqxdhRegistrationSchedule.onShared (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks
            serverSeed raw)).run (merge copies native).native)) = _
      simp only [Functor.map_map]
    rw [accept_compiled, answered, accept_merge, Functor.map_map, Functor.map_map]
    rfl
  · have notAccept : ∀ raw, query ≠ .inr (.accept raw) := fun raw same => accept ⟨raw, same⟩
    have unfolded : (PqxdhDeploymentLaterCompile.compiledSnapImpl setup codec checks route serverSeed query).run
        ((snap, copies), native) = (fun result => (result.1.1, (result.1.2, result.2))) <$>
          (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
            ((compileSnapImpl setup codec route query).run (snap, copies))).run native := rfl
    rw [compiledImpl_run, PqxdhDeploymentLaterServerNative.program_quiet setup codec checks serverSeed _
      (snap_quiet setup codec route query notAccept (snap, copies)) native log,
      PqxdhDeploymentLaterServerGame.snapImpl_quiet setup codec checks route serverSeed query notAccept,
      ← PqxdhDeploymentLaterCompile.snap_step setup codec checks route serverSeed query snap copies native inv,
      unfolded]
    simp only [Functor.map_map]
    rfl

/-- Every compiled step under the native logged handler keeps the CE-3 simulation invariant. -/
theorem server_good (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (query : Spec.Domain)
    (state : (Snap × Local) × (PqxdhRegistrationSchedule.State KemSK × Log)) (good : Good setup codec state.1.2 state.2.1)
    (result : Spec.Range query × ((Snap × Local) × (PqxdhRegistrationSchedule.State KemSK × Log)))
    (supported : result ∈ support ((compiledImpl setup codec checks route serverSeed query).run state)) :
    Good setup codec result.2.1.2 result.2.2.1 := by
  obtain ⟨⟨snap, copies⟩, native, log⟩ := state
  have erased : (result.1, (result.2.1, result.2.2.1)) ∈ support
      ((PqxdhDeploymentLaterCompile.compiledSnapImpl setup codec checks route serverSeed query).run
        ((snap, copies), native)) := by
    rw [← compiled_erase, support_map]
    exact ⟨result, supported, rfl⟩
  exact PqxdhDeploymentLaterCompile.snap_good setup codec checks route serverSeed phase1 phase2 query
    ((snap, copies), native) good _ erased

/-- The run part of CE-COMPILE for the LQ-F game: from a state with the CE-3 invariant, the compiled program with the finish snapshot under the native logged handler, merged at the end, has exactly the distribution of the logged snapshot run from the merged state, jointly with the output, the snapshot and the log. -/
theorem server_run {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (program : OracleComp Spec Result) (snap : Snap)
    (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) (log : Log) (good : Good setup codec copies native) :
    (fun result => (result.1, (result.2.1.1, (merge result.2.1.2 result.2.2.1, result.2.2.2)))) <$>
        (simulateQ (compiledImpl setup codec checks route serverSeed) program).run ((snap, copies), (native, log)) =
      (simulateQ (PqxdhDeploymentLaterServerGame.snapImpl setup codec checks route serverSeed) program).run
        (snap, (merge copies native, log)) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv' _ _ (fun state => Good setup codec state.1.2 state.2.1)
    (fun state => (state.1.1, (merge state.1.2 state.2.1, state.2.2)))
    (fun query state good result supported =>
      server_good setup codec checks route serverSeed phase1 phase2 query state good result supported)
    (fun query state good => server_step setup codec checks route serverSeed query state.1.1 state.1.2 state.2.1
      state.2.2 (PqxdhDeploymentCompileInvariant.good_inv setup codec _ _ good))
    program ((snap, copies), (native, log)) good

/-- The compiled LQ-F program: the run part (the CE-3 compiler with the finish pre-read on the wrapped run-phase adversary), the terminal reads of every created owner, the Server read, and the post part (`A₂` on the run's output and the reveal, through the unchanged compiler), all as requests of the logged source. -/
noncomputable def compileServer (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) :
    OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) (Out × (Ledger × (Snap × Local))) := do
  let run ← simulateQ embed ((simulateQ (compileSnapImpl setup codec route)
    (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first))).run (Snap.empty, Local.empty))
  let beacons ← simulateQ embed (terminal run.2.1 (List.range run.2.2.log.owners.length))
  let server ← (PqxdhDeploymentLaterServerSource.Spec KemSK).query (.inr ())
  let post ← simulateQ embed ((simulateQ (compileImpl setup codec route)
    (simulateQ postEmbed (second run.1.1 (beacons, server)))).run run.2.2)
  pure (post.1, (run.1.2, (run.2.1, post.2)))

/-- The terminal reads issue no raw accept. -/
theorem terminal_quiet (snap : Snap) (indices : List Nat) :
    (terminal (KemSK := KemSK) snap indices).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = .inl 3) 0 := by
  simpa [PqxdhDeploymentLaterCompile.readCost, PqxdhDeploymentCompileBudget.unit] using
    PqxdhDeploymentLaterCompile.terminal_bound (KemSK := KemSK) (.inl 3) snap indices

/-- The post part issues no raw accept. -/
theorem post_quiet (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (adversary : OracleComp PostSpec Out) (copies : Local) :
    ((simulateQ (compileImpl setup codec route) (simulateQ postEmbed adversary)).run copies).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = .inl 3) 0 := by
  rw [← QueryImpl.simulateQ_compose]
  refine PqxdhDeploymentCompileSecrecy.simulate_zero ((compileImpl setup codec route) ∘ₛ postEmbed) _
    (fun query state => ?_) _ copies
  rcases query with coin | (⟨key, message⟩ | bytes)
  · simp only [QueryImpl.apply_compose, postEmbed, simulateQ_spec_query]
    simpa [PqxdhDeploymentCompileBudget.commandKind, PqxdhDeploymentCompileBudget.cost,
      PqxdhDeploymentCompileBudget.unit] using
      PqxdhDeploymentCompileBudget.step_bound setup codec route (.inl 3) (.inl coin) state
  · simp only [QueryImpl.apply_compose, postEmbed, simulateQ_spec_query]
    simpa [PqxdhDeploymentCompileBudget.commandKind, PqxdhDeploymentCompileBudget.cost,
      PqxdhDeploymentCompileBudget.unit] using
      PqxdhDeploymentCompileBudget.step_bound setup codec route (.inl 3) (.inr (.hmac key message)) state
  · simp only [QueryImpl.apply_compose, postEmbed, simulateQ_spec_query]
    simpa [PqxdhDeploymentCompileBudget.commandKind, PqxdhDeploymentCompileBudget.cost,
      PqxdhDeploymentCompileBudget.unit] using
      PqxdhDeploymentCompileBudget.step_bound setup codec route (.inl 3) (.inr (.hash bytes)) state

/-- The continuation after the run part: the terminal reads, the Server read and the post part, from a state with the CE-3 invariant, merged at the end, are the LQ-F reveal of the merged state (the Beacon-side reveal and the Server seed with the log) and the native post phase on the merged state; the log is kept. -/
theorem server_continuation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (second : X → Reveal → OracleComp PostSpec Out)
    (output : X) (ledger : Ledger) (snap : Snap) (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (log : Log) (good : Good setup codec copies native) :
    (fun result => (result.1.1, (result.1.2.1, (result.1.2.2.1, (merge result.1.2.2.2 result.2.1, result.2.2))))) <$>
        (simulateQ (PqxdhDeploymentLaterServerNative.native setup codec checks serverSeed)
          (simulateQ embed (terminal snap (List.range copies.log.owners.length)) >>= fun beacons =>
            (PqxdhDeploymentLaterServerSource.Spec KemSK).query (.inr ()) >>= fun server =>
              simulateQ embed ((simulateQ (compileImpl setup codec route)
                (simulateQ postEmbed (second output (beacons, server)))).run copies) >>= fun post =>
                  pure (post.1, (ledger, (snap, post.2))))).run (native, log) =
      (simulateQ (postImpl setup codec checks serverSeed)
          (second output (revealOf (merge copies native).native.owners snap, (some serverSeed, log)))).run
          (merge copies native) >>=
        fun post => pure (post.1, (ledger, (snap, (post.2, log)))) := by
  rw [simulateQ_bind, StateT.run_bind, PqxdhDeploymentLaterServerNative.program_quiet setup codec checks serverSeed _
    (terminal_quiet snap _) native log, PqxdhDeploymentLaterCompile.terminal_merge setup codec checks serverSeed snap
    copies native good.count, map_pure, pure_bind]
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  change (fun result => _) <$> (pure ((some serverSeed, log), (native, log)) >>= _) = _
  rw [pure_bind, PqxdhDeploymentLaterServerNative.program_quiet setup codec checks serverSeed _
    (post_quiet setup codec route _ copies) native log,
    ← PqxdhDeploymentLaterCompile.compile_post setup codec checks route serverSeed phase1 phase2 _ copies native good]
  simp only [bind_map_left, map_bind, simulateQ_pure, StateT.run_pure, map_pure]

/-- CE-COMPILE for the LQ-F game at the native level: under the approved Phase 1 and Phase 2 read-back contracts, the compiled LQ-F program run under the native logged handler from a fresh source14 state and the empty log, with the compiled program's final local copies merged into the final source14 state, has exactly the distribution of the LQ-F later execution (run phase with the finish snapshot and the ephemeral log, the reveal of the final state, post phase) from the same state with zero raw-attempt counters, jointly over the post-run output, the ledger, the snapshot, the final deployment state and the log. -/
theorem compile_server_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (native : PqxdhRegistrationSchedule.State KemSK)
    (keyId : native.shared.2.server.identityKeyId = setup.serverKeyId)
    (peers : ∀ kid, native.shared.2.server.server.peers kid = none) (owners : native.owners = [])
    (pending : ∀ session, native.shared.2.pending session = none) :
    (fun result => (result.1.1, (result.1.2.1, (result.1.2.2.1, (merge result.1.2.2.2 result.2.1, result.2.2))))) <$>
        (simulateQ (PqxdhDeploymentLaterServerNative.native setup codec checks serverSeed)
          (compileServer setup codec route bounds mode first second)).run (native, []) =
      PqxdhDeploymentLaterServerGame.exec setup codec checks route serverSeed bounds mode first second
        ⟨native, 0, fun _ => 0, []⟩ := by
  have start := PqxdhDeploymentCompileInvariant.good_initial setup codec native keyId peers owners pending
  have composed : ∀ {Value : Type} (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Value),
      simulateQ (PqxdhDeploymentLaterServerNative.native setup codec checks serverSeed) (simulateQ embed program) =
        simulateQ (base setup codec checks serverSeed) program := fun program => by
    rw [base, QueryImpl.simulateQ_compose]
  have flattened := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (base setup codec checks serverSeed) (compileSnapImpl setup codec route)
    (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first)) (Snap.empty, Local.empty) (native, [])
  change _ = (fun z => ((z.1, z.2.1), z.2.2)) <$> (simulateQ (compiledImpl setup codec checks route serverSeed)
    (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first))).run
      ((Snap.empty, Local.empty), (native, [])) at flattened
  have run := server_run setup codec checks route serverSeed phase1 phase2
    (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first)) Snap.empty Local.empty native []
    start
  rw [PqxdhDeploymentCompile.merge_empty] at run
  simp only [compileServer, simulateQ_bind, StateT.run_bind, composed, flattened, bind_map_left, map_bind]
  simp only [PqxdhDeploymentLaterServerGame.exec, PqxdhDeploymentLaterServerGame.later_run_wrap, ← run,
    bind_map_left, Functor.map_map]
  apply bind_congr_of_forall_mem_support
  rintro ⟨⟨output, ledger⟩, ⟨⟨snap, copies⟩, reached, log⟩⟩ member
  have good := OracleComp.simulateQ_run_preserves_inv_of_query _ (fun state => Good setup codec state.1.2 state.2.1)
    (fun query state good result supported =>
      server_good setup codec checks route serverSeed phase1 phase2 query state good result supported)
    _ _ start _ member
  have cont := server_continuation setup codec checks route serverSeed phase1 phase2 second output ledger snap copies
    reached log good
  simp only [← composed, simulateQ_bind, StateT.run_bind, map_bind, simulateQ_pure, StateT.run_pure,
    map_pure] at cont ⊢
  exact cont

/-- The merged outcome of the native logged initialized execution of the compiled LQ-F program. -/
def mergeServer (outcome : Option (PqxdhRegistrationJointInitializedSchedule.NativeOutcome KemSK
    (Out × (Ledger × (Snap × Local))) × Log) × A) :
    Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × LaterState KemSK) × A :=
  (outcome.1.map fun result => (result.1.1, result.1.2.1.1, (result.1.2.1.2.1, (result.1.2.1.2.2.1,
    (merge result.1.2.1.2.2.2 result.1.2.2, result.2)))), outcome.2)

/-- Theorem CE-COMPILE for the LQ-F game: under the approved Phase 1 and Phase 2 read-back contracts, the LQ-F later-quantum game with a generated Server seed is exactly the native logged initialized execution of the compiled LQ-F program with the merged final state, jointly over the constructed Server's public data, the post-run output, the ledger, the snapshot, the complete final deployment state, the ephemeral log and the runtime state. -/
theorem compile_server_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (runtime : A) :
    mergeServer <$> (PqxdhDeploymentLaterServerNative.initialized setup codec checks ensureInit identityIndex none
        (compileServer setup codec route bounds mode first second)).run runtime =
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit identityIndex bounds mode first
        second).run runtime := by
  simp only [PqxdhDeploymentLaterServerNative.initialized, PqxdhDeploymentLaterServerGame.game, StateT.run, map_bind]
  apply bind_congr_of_forall_mem_support
  rintro ⟨_ | created, after⟩ born
  · simp only [map_pure, mergeServer, Option.map_none]
  · obtain ⟨sender, peers⟩ := PqxdhDeploymentCompileGame.construct_fields setup.joint ensureInit identityIndex
      setup.serverKeyId runtime created after born
    have compiled := compile_server_native setup codec checks route created.seed phase1 phase2 bounds mode first
      second (PqxdhRegistrationSchedule.initial created) sender peers rfl (fun _ => rfl)
    simp only [PqxdhDeploymentNative.initial]
    rw [← compiled, Functor.map_map, Functor.map_map]
    rfl

/-- CE-COMPILE for the LQ-F game at the level of the logged annotated source, the source of the LQ-F KEM theorems: erasing the private service annotations and merging the compiled program's local copies maps the logged initialized source execution of the compiled LQ-F program exactly onto the LQ-F later-quantum game, whose Server identity index is the private identity pool's current size, jointly with the ephemeral log. The Server read of the compiled program is the identity-pool reveal of the Server's slot in this execution, so `revealedAt` holds for the Server identity: A2 and T5 must not be cited for this program. -/
theorem compile_server_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A) :
    (fun result => mergeServer (result.1.map fun outcome =>
        (PqxdhRegistrationJointInitializedSchedule.eraseOutcome outcome.1, outcome.2), result.2.2)) <$>
        (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit none
          (compileServer setup codec route bounds mode first second)).run state =
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit state.1.1.seeds.length bounds mode first
        second).run state.2 := by
  rw [← compile_server_game setup codec checks route ensureInit state.1.1.seeds.length phase1 phase2 bounds mode first
    second state.2, ← PqxdhDeploymentLaterServerNative.initialized_native setup codec checks ensureInit none
      (compileServer setup codec route bounds mode first second) state, Functor.map_map]

end BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.pure_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.pure_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.bind_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.bind_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.local_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.local_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.romRoot_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.romRoot_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.nativeClient_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.nativeClient_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.tail_override' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.tail_override

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.acceptLogged_override' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.acceptLogged_override

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.accept_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.accept_merge

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.compiledImpl_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.compiledImpl_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.compiled_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.compiled_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.snap_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.snap_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.accept_compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.accept_compiled

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.server_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.server_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.server_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.server_good

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.server_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.server_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.terminal_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.terminal_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.post_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.post_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.server_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.server_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.compile_server_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.compile_server_native

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.compile_server_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.compile_server_game

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.compile_server_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile.compile_server_source
