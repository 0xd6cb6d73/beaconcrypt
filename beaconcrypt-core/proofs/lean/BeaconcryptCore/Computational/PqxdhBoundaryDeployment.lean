-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep
import BeaconcryptCore.Computational.PqxdhDeploymentSecrecy

/-! PB-D classical source join (item 7, increment I3; survey rows PB-12 and PB-14). `sourceGame` is the adaptive source execution of the whole common deployment experiment: the source-ordered Server birth of `PqxdhBoundaryBirth.serverBirth` (initialization, then one generated seed; a failed initialization keeps its runtime and draws nothing), then `PqxdhBoundaryProgram.execute` of the per-command source step `PqxdhBoundaryDeploymentStep.sourceStep` (whose commands are CE's approved interface under its deviations D1-D5, classification E; see that module) on the adversary wrapped by CE's own secrecy layer (`PqxdhDeploymentSecrecy.wrap`, which keeps the transcript, the test session and the fresh messages and issues only coins and sends for the secrecy commands), from the initial deployment state of the created Server. `classical` equates it with the CE game `PqxdhDeploymentSecrecy.game` at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model` on the full returned value: created Server, adversary output, final ledger, complete final deployment state (owners, Server, pending tokens, both caches, raw-attempt counters, produced frames) and runtime, with no projection, conditioning or event premise. The only change of shape is `okMap`, which wraps the adversary output and ledger in Rust `ok` exactly where `wrap` returns them; `unwrap` reads a source value back, so every observation and every event transfers (`classical_observe`; `classical_evalDist` in the evaluation-measure form `𝒟[·]` of the CE-12 headlines; `classical_probEvent` in the event form `Pr{let x ← ·}[·]`). The identity index is arbitrary (`classical_zero` is the index-0 instance of the PB-D pin #415) and `checks` is a free parameter (PB-14); the seven-site `Checks` mapping stays reviewed transcription (RT). No assumption or contract is added: the per-command join cites only published boundary equalities, all quantified over every deployment state. The secrecy layer, the model oracles and the post-run ledger are CE's own (classification E). Persistence, snapshots and Cap'n Proto are out of scope. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBoundaryDeployment
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhDeploymentInterface (Spec FreshBounds Mode ModeSpec asModeO)
open PqxdhBoundaryDeploymentStep (sourceStep)
variable {ι KemSK Reader Response Message Root A X Y : Type} {baseSpec : OracleSpec ι}

/-- The returned value of the source game: on a successful Server birth, the encoded created Server, the literal Rust result of the adaptive execution (on success the adversary output with its final ledger, where `PqxdhDeploymentSecrecy.wrap` returns them) and the complete final deployment state; `none` when initialization fails. -/
abbrev Outcome (KemSK X : Type) :=
  Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × RustM (X × PqxdhDeploymentSecrecy.Ledger) ×
    PqxdhDeploymentNative.State KemSK)

/-- The returned value of the CE game `PqxdhDeploymentSecrecy.game`. -/
abbrev GameOutcome (KemSK X : Type) :=
  Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK)

/-- Whole-program source join: for every native-interface program and every complete deployment state, adaptive source execution is the CE native simulation at the production instance with each reply and the complete poststate, by `PqxdhBoundaryProgram.source_exact` and `PqxdhBoundaryDeploymentStep.step_exact`. -/
theorem execute_exact {Z : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize)
    (checks : Checks) (serverSeed : IdentitySeed) (work : OracleComp Spec Z) (state : PqxdhDeploymentNative.State KemSK) :
    PqxdhBoundaryProgram.execute (sourceStep setup codec reader erased checks serverSeed) work state =
      (fun result => (RustM.ok result.1, result.2)) <$>
        (simulateQ (PqxdhDeploymentNative.handler setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) serverSeed) work).run state :=
  PqxdhBoundaryProgram.source_exact _ _
    (PqxdhBoundaryDeploymentStep.step_exact setup codec reader erased checks serverSeed) work state

/-- The adaptive classical source game: source-ordered Server birth, then adaptive source execution of the per-command source step on the adversary wrapped by CE's secrecy layer at the production codec, from the initial deployment state of the created Server. A failed initialization ends the run with no outcome and its returned runtime. -/
noncomputable def sourceGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) : StateT A ProbComp (Outcome KemSK X) := fun runtime => do
  let born ← (PqxdhBoundaryBirth.serverBirth setup.joint ensureInit identityIndex setup.serverKeyId).run runtime
  match born.1 with
  | none => pure (none, born.2)
  | some created =>
    (fun result => (some (PqxdhRegistrationJointServerBirth.encode created, result), born.2)) <$>
      PqxdhBoundaryProgram.execute (sourceStep setup codec reader erased checks created.seed)
        (PqxdhDeploymentSecrecy.wrap setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
          setup.serverKeyId bounds (asModeO mode adversary))
        (PqxdhDeploymentNative.initial created)

/-- A CE game value as a source value: the adversary output and the final ledger are wrapped in Rust `ok` (the inverse of the ledger move of `PqxdhDeploymentSecrecy.run_wrap`); the created Server, the complete deployment state and the runtime are unchanged. -/
def okMap (outcome : GameOutcome KemSK X × A) : Outcome KemSK X × A :=
  (outcome.1.map fun result => (result.1, RustM.ok (result.2.1, result.2.2.1), result.2.2.2), outcome.2)

/-- A source value read back as a CE game value: an `ok` result moves the ledger back into the state; a `fail` or `div` result, which `classical` shows is never produced, reads as no outcome. -/
def unwrap (outcome : Outcome KemSK X × A) : GameOutcome KemSK X × A :=
  (outcome.1.bind fun result => match result.2.1 with
    | .ok value => some (result.1, value.1, (value.2, result.2.2))
    | _ => none, outcome.2)

/-- `unwrap` is a left inverse of `okMap`: no part of a game value is lost. -/
theorem unwrap_okMap (outcome : GameOutcome KemSK X × A) : unwrap (okMap outcome) = outcome := by
  rcases outcome with ⟨_ | ⟨created, value, ledger, state⟩, runtime⟩ <;> rfl

/-- PB-12/PB-14 classical join: for every setup, codec, frame reader, buffer, `checks`, initialization, identity index, bounds, mode, adversary and runtime, the source game equals the CE game `PqxdhDeploymentSecrecy.game` at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model` on the full returned value (created Server, adversary output, ledger, complete deployment state with counters and produced frames, runtime), up to the `ok` wrapper `okMap`. -/
theorem classical (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    (sourceGame setup codec reader erased checks ensureInit identityIndex bounds mode adversary).run runtime =
      okMap <$> (PqxdhDeploymentSecrecy.game setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit identityIndex bounds mode adversary).run runtime := by
  rw [PqxdhDeploymentSecrecy.game_wrap, Functor.map_map]
  simp only [sourceGame, PqxdhDeploymentNative.game, StateT.run, PqxdhBoundaryBirth.server_source, map_bind]
  apply bind_congr
  rintro ⟨_ | created, after⟩
  · simp only [map_pure]
    rfl
  · have joined := execute_exact setup codec reader erased checks created.seed
      (PqxdhDeploymentSecrecy.wrap setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
        setup.serverKeyId bounds (asModeO mode adversary)) (PqxdhDeploymentNative.initial created)
    simp only [StateT.run] at joined
    simp only [joined, Functor.map_map]
    rfl

/-- The index-0 instance of `classical`, the identity index of the CE-12 headline games (PB-D pin #415). -/
theorem classical_zero (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    (sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run runtime =
      okMap <$> (PqxdhDeploymentSecrecy.game setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit 0 bounds mode adversary).run runtime :=
  classical setup codec reader erased checks ensureInit 0 bounds mode adversary runtime

/-- Every supported outcome of the source game is the `okMap` image of a supported outcome of the CE game at the production instance; in particular the source game never returns a `fail` or `div` result. -/
theorem classical_normal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A) (outcome : Outcome KemSK X × A)
    (supported : outcome ∈ support
      ((sourceGame setup codec reader erased checks ensureInit identityIndex bounds mode adversary).run runtime)) :
    ∃ value ∈ support ((PqxdhDeploymentSecrecy.game setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit identityIndex bounds mode adversary).run runtime),
      outcome = okMap value := by
  rw [classical, support_map] at supported
  obtain ⟨value, member, rfl⟩ := supported
  exact ⟨value, member, rfl⟩

/-- Any continuation of the source game sees exactly the CE game's returned value through `okMap`; no projection, success conditioning or event premise is introduced. -/
theorem classical_continuation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A) (next : Outcome KemSK X × A → ProbComp Y) :
    ((sourceGame setup codec reader erased checks ensureInit identityIndex bounds mode adversary).run runtime >>= next) =
      ((PqxdhDeploymentSecrecy.game setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit identityIndex bounds mode adversary).run runtime >>=
          fun outcome => next (okMap outcome)) := by
  rw [classical, bind_map_left]

/-- Generic observation transfer for item 8, in the form of the CE-12 headlines (`𝒟[decision <$> game] {true}`): for every observation `observe` of the CE game's returned value, observing the source game through `unwrap` is the same computation as observing the CE game at the production instance. -/
theorem classical_observe {Z : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A) (observe : GameOutcome KemSK X × A → Z) :
    (fun outcome => observe (unwrap outcome)) <$>
        (sourceGame setup codec reader erased checks ensureInit identityIndex bounds mode adversary).run runtime =
      observe <$> (PqxdhDeploymentSecrecy.game setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit identityIndex bounds mode adversary).run runtime := by
  rw [classical, Functor.map_map]
  simp only [unwrap_okMap]

/-- Generic distribution transfer for item 8 without the deprecated probability API: for every observation `observe` of the CE game's returned value into a measurable space, the evaluation measure `𝒟[·]` of observing the source game through `unwrap` equals that of observing the CE game at the production instance. With `Z = Bool` and the set `{true}` this is the event form `𝒟[decision <$> game] {true}` of the CE-12 headlines; `classical_probEvent` states the same transfer for every event in the forward form `Pr{let x ← ·}[·]`. -/
theorem classical_evalDist {Z : Type} [MeasurableSpace Z] (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A) (observe : GameOutcome KemSK X × A → Z) :
    𝒟[(fun outcome => observe (unwrap outcome)) <$>
        (sourceGame setup codec reader erased checks ensureInit identityIndex bounds mode adversary).run runtime] =
      𝒟[observe <$> (PqxdhDeploymentSecrecy.game setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit identityIndex bounds mode adversary).run runtime] := by
  rw [classical_observe]

/-- Generic event transfer for item 8: for every event `event` of the CE game's returned value, its probability in the CE game at the production instance equals the probability of `event ∘ unwrap` in the source game. -/
theorem classical_probEvent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A) (event : GameOutcome KemSK X × A → Prop) :
    Pr{let x ← ((sourceGame setup codec reader erased checks ensureInit identityIndex bounds mode adversary).run
        runtime)}[(event ∘ unwrap) x] =
      Pr{let x ← ((PqxdhDeploymentSecrecy.game setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit identityIndex bounds mode adversary).run runtime)}[event x] := by
  rw [classical, prEvent_map]
  simp only [Function.comp_apply, unwrap_okMap]

end BeaconcryptCore.Computational.PqxdhBoundaryDeployment

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeployment.execute_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeployment.execute_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeployment.unwrap_okMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeployment.unwrap_okMap

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeployment.classical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeployment.classical

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeployment.classical_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeployment.classical_zero

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeployment.classical_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeployment.classical_normal

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeployment.classical_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeployment.classical_continuation

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeployment.classical_observe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeployment.classical_observe

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeployment.classical_evalDist' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeployment.classical_evalDist

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryDeployment.classical_probEvent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryDeployment.classical_probEvent
