-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhBoundaryProgram
import BeaconcryptCore.Computational.PqxdhBoundaryBirth
import BeaconcryptCore.Computational.PqxdhBoundaryPhase1Buffers
import BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept
import BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuildNative
import BeaconcryptCore.Computational.PqxdhBoundaryRegistrationFinish
import BeaconcryptCore.Computational.PqxdhBoundaryRecordSend
import BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl

/-! PB-D per-command source join (item 7, increment I3). `sourceStep` is one adaptive source step for every command of the common deployment experiment's native interface: each command runs the published source program of its boundary row, at the production codec `withReader codec reader` and the production route `RawCtxFrameDecoding.sender reader.model` (the raw-receive equalities are stated at both, the finish equality fixes the frame reader to `RawCtxFrameDecoding.decode reader.model` for every route, and the create, bundle, accept, build and send equalities hold for every codec and route). `create` runs the source-ordered Beacon creation (PB-01), `bundle` the owner program over the extracted unsigned builder (PB-02), `accept` the raw adapter acceptance (PB-03), `build` the extracted Server builder under the native token wrapper (PB-05), `finish` the candidate-local receive executor (PB-06), the two sends the send transcriptions (PB-09) and the two raw receives the receive execution transcriptions over extracted local steps (PB-07, PB-08). These commands are the common deployment experiment's approved interface under its deviations D1-D5 (classification E: the survey's deviation table, collected in the PB-E ledger), not every Rust entry point: in particular `create` is `Beacon::try_new` after D1, with no second `ensure_init`, and generation failures of the native key generators are not modeled, and the `build` payload is the adversary's choice (D4), so no source adversary is claimed to have a literal build-payload network oracle. Coins, the public HMAC and the BLAKE2b oracle are the CE model oracles, unchanged (classification E: adversary coins, public HMAC with the Extract ROM point, BLAKE2b ROM). Each per-command theorem cites one published boundary equality, which holds for every deployment state, so `step_exact` needs no reachability invariant, no success premise and no new contract; `checks` is a free parameter throughout (PB-14). The record and finish executors return `RustM (reply × state)` and are adapted with `PqxdhBoundaryProgram.outcome`; their published equalities show every result is `ok`, so the adapter's entry-state placeholder for `fail`/`div` is never a supported outcome (`step_normal`). The premise lemmas `route_agreement`, `phase1_withReader` and `phase2_withReader` record what the production instance discharges for item 8 (decision D-2, message #511). The Rust adapter transcriptions behind each published equality stay reviewed transcription (RT); persistence, snapshots and Cap'n Proto are out of scope. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhDeploymentInterface (Spec)
open PqxdhBoundaryProgram (Step liftStep outcome)
variable {ι KemSK Reader Response Message Root : Type} {baseSpec : OracleSpec ι}

/-- A state program whose literal Rust result is a normal return: its reply wrapped in `ok`, with its complete poststate. -/
def normal {S Y : Type} (work : StateT S ProbComp Y) (state : S) : ProbComp (RustM Y × S) :=
  (fun result => (RustM.ok result.1, result.2)) <$> work.run state

/-- The Phase-1 bundle source program (PB-02) on the complete deployment state: a missing owner returns `none` with the state unchanged; otherwise the owner program over the extracted unsigned builder `pqxdh.beacon_start` (`PqxdhBoundaryPhase1Buffers.coreOwnerProgram`: local Fresh coins, extracted builder, attached signatures, optional writer) runs and exactly its returned owner is reinstalled; counters, produced frames, the Server and every other owner are the entry state's. -/
noncomputable def bundleSource (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat) :
    StateT (PqxdhDeploymentNative.State KemSK) ProbComp (Option Pqxdh.Bytes) := fun state =>
  match state.native.owners[index]? with
  | none => pure (none, state)
  | some owner => (fun result => (result.1,
      { state with native := { state.native with owners := state.native.owners.set index result.2 } })) <$>
    PqxdhBoundaryPhase1Buffers.coreOwnerProgram setup codec owner

/-- The adaptive source step of the deployment: every command runs its published source program at the production codec `withReader codec reader` and the production route, on the complete deployment state (owners, Server, pending tokens, both caches, raw-attempt counters, produced frames). Record and finish executors are adapted with `outcome`; coins, HMAC and BLAKE2b are the CE model oracles unchanged. -/
noncomputable def sourceStep (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize)
    (checks : Checks) (serverSeed : IdentitySeed) : Step Spec (PqxdhDeploymentNative.State KemSK)
  | .inl coin => normal (StateT.lift (unifSpec.query coin : ProbComp _))
  | .inr (.create pin keyId) => normal (PqxdhBoundaryBirth.beaconCreate setup pin keyId)
  | .inr (.bundle index) => normal (bundleSource setup (PqxdhBoundaryRecordPrelude.withReader codec reader) index)
  | .inr (.accept raw) => normal (PqxdhBoundaryRegistrationAccept.deploymentAccept setup
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks serverSeed raw)
  | .inr (.build session payload) => normal (PqxdhDeploymentNative.onNative (PqxdhRegistrationSchedule.onShared
      (PqxdhBoundaryRegistrationBuildNative.executeNativeBuild setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
        checks session payload)))
  | .inr (.finish index raw) => fun state =>
      outcome state <$> PqxdhBoundaryRegistrationFinish.executeNativeFinish setup codec reader erased index raw state
  | .inr (.hmac key message) => normal (PqxdhDeploymentNative.onNative (PqxdhRegistrationSchedule.onShared
      (PqxdhServerAuthNative.nativeHmac setup serverSeed PqxdhRegistrationSchedule.observationScalar key message)))
  | .inr (.hash bytes) => normal (PqxdhDeploymentNative.onNative (PqxdhRegistrationSchedule.onShared
      (PqxdhServerAuthNative.nativeHash bytes)))
  | .inr (.serverSend keyId plaintext) => fun state =>
      outcome state <$> PqxdhBoundaryRecordSend.executeServerSend setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
        keyId plaintext state
  | .inr (.serverRaw raw) => fun state =>
      outcome state <$> PqxdhBoundaryRecordExecution.executeServerRaw setup codec reader erased raw state
  | .inr (.beaconSend index plaintext) => fun state =>
      outcome state <$> PqxdhBoundaryRecordSend.executeBeaconSend setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
        index plaintext state
  | .inr (.beaconRaw index raw) => fun state =>
      outcome state <$> PqxdhBoundaryRecordExecution.executeBeaconRaw setup codec reader erased index raw state

/-- PB-01: the source `create` step is the CE `create` command at the production instance, by the published `PqxdhBoundaryBirth.create_source` (wrong-width rejection and every admitted creation, any state). -/
theorem step_create (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize)
    (checks : Checks) (serverSeed : IdentitySeed) (pin : Pqxdh.Bytes) (keyId : Std.U64)
    (state : PqxdhDeploymentNative.State KemSK) :
    sourceStep setup codec reader erased checks serverSeed (.inr (.create pin keyId)) state =
      liftStep (PqxdhDeploymentNative.handler setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) serverSeed) (.inr (.create pin keyId)) state := by
  simp only [sourceStep, normal, liftStep]
  rw [PqxdhBoundaryBirth.create_source]

/-- PB-02: the source `bundle` step is the CE `bundle` command at the production instance, by the published `PqxdhBoundaryPhase1Native.native_bundle` and `PqxdhBoundaryPhase1Buffers.owner_core` (missing owner, every phase, writer failure). -/
theorem step_bundle (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize)
    (checks : Checks) (serverSeed : IdentitySeed) (index : Nat) (state : PqxdhDeploymentNative.State KemSK) :
    sourceStep setup codec reader erased checks serverSeed (.inr (.bundle index)) state =
      liftStep (PqxdhDeploymentNative.handler setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) serverSeed) (.inr (.bundle index)) state := by
  simp only [sourceStep, normal, liftStep]
  rw [PqxdhBoundaryPhase1Native.native_bundle]
  change _ <$> bundleSource setup (PqxdhBoundaryRecordPrelude.withReader codec reader) index state = _
  unfold bundleSource
  cases state.native.owners[index]? with
  | none => rfl
  | some owner => simp only [PqxdhBoundaryPhase1Buffers.owner_core]

/-- PB-03: the source `accept` step is the CE `accept` command at the production instance, by the published `PqxdhBoundaryRegistrationAccept.deployment_accept`. -/
theorem step_accept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize)
    (checks : Checks) (serverSeed : IdentitySeed) (raw : Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK) :
    sourceStep setup codec reader erased checks serverSeed (.inr (.accept raw)) state =
      liftStep (PqxdhDeploymentNative.handler setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) serverSeed) (.inr (.accept raw)) state := by
  simp only [sourceStep, normal, liftStep]
  rw [PqxdhBoundaryRegistrationAccept.deployment_accept]

/-- PB-05: the source `build` step is the CE `build` command at the production instance, by the published `PqxdhBoundaryRegistrationBuildNative.deployment_build` (present and missing tokens, every rejection and both writer failures). -/
theorem step_build (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize)
    (checks : Checks) (serverSeed : IdentitySeed) (session : Nat) (payload : Option Pqxdh.Bytes)
    (state : PqxdhDeploymentNative.State KemSK) :
    sourceStep setup codec reader erased checks serverSeed (.inr (.build session payload)) state =
      liftStep (PqxdhDeploymentNative.handler setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) serverSeed) (.inr (.build session payload)) state := by
  simp only [sourceStep, normal, liftStep]
  rw [PqxdhBoundaryRegistrationBuildNative.deployment_build]

/-- PB-06: the adapted source `finish` step is the CE `finish` command at the production instance, by the published `PqxdhBoundaryRegistrationFinish.native_finish_exact` and `PqxdhBoundaryProgram.outcome_ok`. -/
theorem step_finish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize)
    (checks : Checks) (serverSeed : IdentitySeed) (index : Nat) (raw : Pqxdh.Bytes)
    (state : PqxdhDeploymentNative.State KemSK) :
    sourceStep setup codec reader erased checks serverSeed (.inr (.finish index raw)) state =
      liftStep (PqxdhDeploymentNative.handler setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) serverSeed) (.inr (.finish index raw)) state := by
  simp only [sourceStep, liftStep]
  rw [PqxdhBoundaryRegistrationFinish.native_finish_exact setup codec checks (RawCtxFrameDecoding.sender reader.model)
    serverSeed reader erased index raw state]
  exact PqxdhBoundaryProgram.outcome_ok state _

/-- PB-09: the adapted source Server-send step is the CE `serverSend` command at the production instance, by the published `PqxdhBoundaryRecordSend.handler_serverSend` and `PqxdhBoundaryProgram.outcome_ok`. -/
theorem step_serverSend (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize)
    (checks : Checks) (serverSeed : IdentitySeed) (keyId : Std.U64) (plaintext : Pqxdh.Bytes)
    (state : PqxdhDeploymentNative.State KemSK) :
    sourceStep setup codec reader erased checks serverSeed (.inr (.serverSend keyId plaintext)) state =
      liftStep (PqxdhDeploymentNative.handler setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) serverSeed) (.inr (.serverSend keyId plaintext)) state := by
  simp only [sourceStep, liftStep]
  rw [PqxdhBoundaryRecordSend.handler_serverSend setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
    (RawCtxFrameDecoding.sender reader.model) serverSeed keyId plaintext state]
  exact PqxdhBoundaryProgram.outcome_ok state _

/-- PB-09: the adapted source Beacon-send step is the CE `beaconSend` command at the production instance, by the published `PqxdhBoundaryRecordSend.handler_beaconSend` and `PqxdhBoundaryProgram.outcome_ok`. -/
theorem step_beaconSend (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize)
    (checks : Checks) (serverSeed : IdentitySeed) (index : Nat) (plaintext : Pqxdh.Bytes)
    (state : PqxdhDeploymentNative.State KemSK) :
    sourceStep setup codec reader erased checks serverSeed (.inr (.beaconSend index plaintext)) state =
      liftStep (PqxdhDeploymentNative.handler setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) serverSeed) (.inr (.beaconSend index plaintext)) state := by
  simp only [sourceStep, liftStep]
  rw [PqxdhBoundaryRecordSend.handler_beaconSend setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
    (RawCtxFrameDecoding.sender reader.model) serverSeed index plaintext state]
  exact PqxdhBoundaryProgram.outcome_ok state _

/-- PB-07/PB-08: the adapted source raw Server-receive step is the CE `serverRaw` command at the production instance, by the published `PqxdhBoundaryRecordExecution.handler_serverRaw` and `PqxdhBoundaryProgram.outcome_ok`. -/
theorem step_serverRaw (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize)
    (checks : Checks) (serverSeed : IdentitySeed) (raw : Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK) :
    sourceStep setup codec reader erased checks serverSeed (.inr (.serverRaw raw)) state =
      liftStep (PqxdhDeploymentNative.handler setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) serverSeed) (.inr (.serverRaw raw)) state := by
  simp only [sourceStep, liftStep]
  rw [PqxdhBoundaryRecordExecution.handler_serverRaw setup codec reader erased checks serverSeed raw state]
  exact PqxdhBoundaryProgram.outcome_ok state _

/-- PB-07/PB-08: the adapted source raw Beacon-receive step is the CE `beaconRaw` command at the production instance, for every owner handle, by the published `PqxdhBoundaryRecordExecution.handler_beaconRaw` and `PqxdhBoundaryProgram.outcome_ok`. -/
theorem step_beaconRaw (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize)
    (checks : Checks) (serverSeed : IdentitySeed) (index : Nat) (raw : Pqxdh.Bytes)
    (state : PqxdhDeploymentNative.State KemSK) :
    sourceStep setup codec reader erased checks serverSeed (.inr (.beaconRaw index raw)) state =
      liftStep (PqxdhDeploymentNative.handler setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) serverSeed) (.inr (.beaconRaw index raw)) state := by
  simp only [sourceStep, liftStep]
  rw [PqxdhBoundaryRecordExecution.handler_beaconRaw setup codec reader erased checks serverSeed index raw state]
  exact PqxdhBoundaryProgram.outcome_ok state _

/-- Model oracles (classification E): adversary coins, the public HMAC (with CE's Extract-ROM point) and the BLAKE2b oracle are the CE handler's own branches, unchanged; no production code is claimed for them. -/
theorem step_oracles (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize)
    (checks : Checks) (serverSeed : IdentitySeed) (state : PqxdhDeploymentNative.State KemSK) :
    (∀ coin, sourceStep setup codec reader erased checks serverSeed (.inl coin) state =
      liftStep (PqxdhDeploymentNative.handler setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) serverSeed) (.inl coin) state) ∧
    (∀ key message, sourceStep setup codec reader erased checks serverSeed (.inr (.hmac key message)) state =
      liftStep (PqxdhDeploymentNative.handler setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) serverSeed) (.inr (.hmac key message)) state) ∧
    (∀ bytes, sourceStep setup codec reader erased checks serverSeed (.inr (.hash bytes)) state =
      liftStep (PqxdhDeploymentNative.handler setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) serverSeed) (.inr (.hash bytes)) state) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- PB-D per-command join: for every command of the native interface and every complete deployment state, the source step equals the lifted CE native handler at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, for every `checks` (PB-14). This is the operational premise of `PqxdhBoundaryProgram.source_exact`. -/
theorem step_exact (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize)
    (checks : Checks) (serverSeed : IdentitySeed) :
    ∀ query state, sourceStep setup codec reader erased checks serverSeed query state =
      liftStep (PqxdhDeploymentNative.handler setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) serverSeed) query state := by
  intro query state
  rcases query with coin | command
  · exact (step_oracles setup codec reader erased checks serverSeed state).1 coin
  · cases command with
    | create pin keyId => exact step_create setup codec reader erased checks serverSeed pin keyId state
    | bundle index => exact step_bundle setup codec reader erased checks serverSeed index state
    | accept raw => exact step_accept setup codec reader erased checks serverSeed raw state
    | build session payload => exact step_build setup codec reader erased checks serverSeed session payload state
    | finish index raw => exact step_finish setup codec reader erased checks serverSeed index raw state
    | hmac key message => exact (step_oracles setup codec reader erased checks serverSeed state).2.1 key message
    | hash bytes => exact (step_oracles setup codec reader erased checks serverSeed state).2.2 bytes
    | serverSend keyId plaintext => exact step_serverSend setup codec reader erased checks serverSeed keyId plaintext state
    | serverRaw raw => exact step_serverRaw setup codec reader erased checks serverSeed raw state
    | beaconSend index plaintext => exact step_beaconSend setup codec reader erased checks serverSeed index plaintext state
    | beaconRaw index raw => exact step_beaconRaw setup codec reader erased checks serverSeed index raw state

/-- Every supported outcome of every source step is `ok` with a supported reply and complete poststate of the CE native command; in particular the entry-state placeholder of `outcome` for `fail`/`div` is never observed. -/
theorem step_normal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize)
    (checks : Checks) (serverSeed : IdentitySeed) (query : Spec.Domain) (state : PqxdhDeploymentNative.State KemSK)
    (result : RustM (Spec.Range query) × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support (sourceStep setup codec reader erased checks serverSeed query state)) :
    ∃ reply ∈ support ((PqxdhDeploymentNative.handler setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) serverSeed query).run state), result = (.ok reply.1, reply.2) := by
  rw [step_exact setup codec reader erased checks serverSeed query state, liftStep, support_map] at supported
  obtain ⟨reply, member, rfl⟩ := supported
  exact ⟨reply, member, rfl⟩

/-- Production-instance premise (D-2): header routing by `RawCtxFrameDecoding.sender reader.model` agrees with the production frame reader on every successful decode, by the existing `RawCtxFrameDecoding.decoderAgreement`; failure domains may differ. -/
theorem route_agreement (codec : Codec Reader Response) (reader : RawCtxNativeFramePrelude.Reader Message Root) :
    RawCtxServerRouting.DecoderAgreement (RawCtxFrameDecoding.sender reader.model)
      (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead :=
  RawCtxFrameDecoding.decoderAgreement reader.model

/-- Production-instance premise (D-2): the Phase 1 read-back law reads only the Phase 1 writer, reader and getters, which `withReader` keeps, so it holds at the production codec exactly when it holds at `codec`. -/
theorem phase1_withReader (codec : Codec Reader Response) (reader : RawCtxNativeFramePrelude.Reader Message Root) :
    PqxdhServerAuthNegativeControl.Phase1ReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader) ↔
      PqxdhServerAuthNegativeControl.Phase1ReadBack codec :=
  Iff.rfl

/-- Production-instance premise (D-2): the Phase 2 read-back law reads only the Phase 2 writer, reader and getters, which `withReader` keeps, so it holds at the production codec exactly when it holds at `codec`. -/
theorem phase2_withReader (codec : Codec Reader Response) (reader : RawCtxNativeFramePrelude.Reader Message Root) :
    PqxdhServerAuthNegativeControl.Phase2ReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader) ↔
      PqxdhServerAuthNegativeControl.Phase2ReadBack codec :=
  Iff.rfl

end BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.step_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.step_create

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.step_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.step_bundle

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.step_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.step_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.step_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.step_build

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.step_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.step_finish

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.step_serverSend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.step_serverSend

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.step_beaconSend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.step_beaconSend

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.step_serverRaw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.step_serverRaw

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.step_beaconRaw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.step_beaconRaw

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.step_oracles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.step_oracles

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.step_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.step_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.step_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.step_normal

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.route_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.route_agreement

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.phase1_withReader' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.phase1_withReader

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.phase2_withReader' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep.phase2_withReader
