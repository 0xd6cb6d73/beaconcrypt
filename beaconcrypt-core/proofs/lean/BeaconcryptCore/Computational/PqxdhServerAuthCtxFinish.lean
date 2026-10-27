import BeaconcryptCore.Computational.PqxdhServerAuthCtxState
import BeaconcryptCore.Computational.PqxdhServerAuthFinishMaterial

/-! The actual finish handler uses the original probabilistic prefix and omitted table, then either the ordinary native receive or the concrete selected raw callback. Its only shared cache lives in the component interpreter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxFinish
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhSecretInputKdf PqxdhJointKdfGame
open CtxRomAuth
variable {KemSK Result Aux : Type}

/-- Run the actual callback with its own local state while retaining the complete protocol state outside it. -/
noncomputable def callback (work : PqxdhServerAuthCtxNative.Local Aux Result) (initial : Aux) :
    Program KemSK (Result × Aux) := StateT.lift (work.run initial)

/-- The callback's complete component poststate and its local result are retained when embedded in the protocol interpreter. -/
theorem callback_evaluate (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (work : PqxdhServerAuthCtxNative.Local Aux Result)
    (initial : Aux) (state : State KemSK) :
    (evaluate source key read (callback work initial)).run state =
      (fun result => ((result.1, result.2.1), (state.1, result.2.2))) <$>
        (PqxdhServerAuthCtxNative.evaluate source key read work).run (initial, state.2) := by
  rw [evaluate, callback, PqxdhServerAuthCtxNative.lift_evaluate]
  simp only [RawCtxSelectedReceiveCompiler.evaluated, PqxdhServerAuthCtxNative.evaluate,
    PqxdhSelectedStateInterpreter.evaluate, StateT.run, Functor.map_map, PqxdhSelectedStateInterpreter.pair]

/-- Complete the actual native registration checks and retain every unrelated protocol annotation. -/
noncomputable def complete (control : pqxdh.BeaconInitSent) (state : Local KemSK)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) : Option Pqxdh.Bytes × Local KemSK :=
  let outcome := finishOutcome control state.1.1 staged
  (outcome.1, ((outcome.2, state.1.2), state.2))

/-- The final native registration gate does not inspect or alter the commitment cache. -/
theorem complete_restore (control : pqxdh.BeaconInitSent) (state : Local KemSK)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) (cache : CtxRO.QueryCache) :
    Prod.map id (fun after => restore after cache) (complete control state staged) =
      complete control (restore state cache) staged := by
  rfl

/-- Execute the full raw callback before the original registration gate; the callback's actual optional plaintext-derived result determines publication. -/
noncomputable def after (control : pqxdh.BeaconInitSent)
    (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Option PqxdhBeaconPhase2Publication.Staged)) :
    Program KemSK (Option Pqxdh.Bytes) :=
  fun state => complete control state <$> work

/-- Final registration observation keeps the component's full poststate, including opening failures and shared-cache effects. -/
theorem after_evaluate (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (control : pqxdh.BeaconInitSent)
    (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Option PqxdhBeaconPhase2Publication.Staged))
    (state : State KemSK) :
    Prod.map id PqxdhServerAuthCtxState.project <$> (evaluate source key read (after control work)).run state =
      (fun result => complete control (restore state.1 result.2.cache) result.1) <$>
        (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read)
          source.crypto key) work).run state.2 := by
  change Prod.map id PqxdhServerAuthCtxState.project <$> PqxdhSelectedStateInterpreter.pair <$>
    (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read)
      source.crypto key) (complete control state.1 <$> work)).run state.2 = _
  rw [simulateQ_map, StateT.run_map]
  simp only [Functor.map_map, PqxdhSelectedStateInterpreter.pair, Prod.map_def, id_eq,
    PqxdhServerAuthCtxState.project, complete, restore, restoreFlat, finishOutcome]

/-- The complete original probabilistic prefix or table computation forwards unchanged while preserving every private component field. -/
theorem coins_simulate (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (work : ProbComp Result) (state : Component) :
    (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read)
      source.crypto key) (simulateQ PqxdhServerAuthCtxAmbient.coin work)).run state =
      (fun result => (result, state)) <$> work := by
  have same := congrArg (Functor.map (fun result => (result.1, result.2.2)))
    (PqxdhServerAuthCtxAmbient.coin_program source key read work ((), state))
  simpa only [RawCtxSelectedReceiveCompiler.evaluated, StateT.run, Functor.map_map,
    Prod.mk.eta, id_map'] using same

variable {ι : Type} {baseSpec : OracleSpec ι} {Reader WireResponse : Type}

/-- The selected finish uses the original application getter and actual raw callback, followed by the unchanged native final checks. -/
noncomputable def selected (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (rest : PqxdhServerAuthCtxCalls.Residual) (control : pqxdh.BeaconInitSent)
    (pending : PqxdhPhase2DhMetadata.Prepared WireResponse) : Program KemSK (Option Pqxdh.Bytes) :=
  after control (PqxdhServerAuthFinishMaterial.program source codec rest pending)

/-- The complete selected post-root finish preserves the literal factor callback, its returned plaintext-derived staged result, and every protocol/cache field. -/
theorem selected_source (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (control : pqxdh.BeaconInitSent) (pending : PqxdhPhase2DhMetadata.Prepared WireResponse)
    (state : State KemSK) :
    Prod.map id PqxdhServerAuthCtxState.project <$>
      (evaluate setup.source key codec.frameRead (selected setup.source codec rest control pending)).run state =
      (fun result => complete control (restore state.1 result.2.2) result.1) <$>
        ((factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest)).hiddenAfter pending).run
          ((), state.2.cache) := by
  rw [selected, after_evaluate]
  have same := congrArg (Functor.map (fun result => complete control (restore state.1 result.2.2) result.1))
    (PqxdhServerAuthFinishMaterial.program_source setup codec key rest pending ((), state.2))
  simpa only [factorServices, RawCtxSelectedReceiveCompiler.project, RawCtxSelectedReceiveCompiler.evaluated,
    StateT.run, Functor.map_map, Prod.map_def, id_eq] using same.symm

/-- Ordinary roots use the actual source initial KDF and native receive; known-key byte aliases remain permitted. -/
noncomputable def known (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (control : pqxdh.BeaconInitSent) (pending : PqxdhPhase2DhMetadata.Prepared WireResponse)
    (root : RootOutput) : Program KemSK (Option Pqxdh.Bytes) :=
  after control (Prod.fst <$> (simulateQ (PqxdhServerAuthCtxNative.beacon source codec)
    (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead pending (PqxdhRootTableInitialization.rootArray root))).run ())

/-- The complete ordinary post-root finish retains the original real KDF, optional getter/opening replies and every source/cache field. -/
theorem known_source (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (key : RootOutput) (control : pqxdh.BeaconInitSent)
    (pending : PqxdhPhase2DhMetadata.Prepared WireResponse) (root : RootOutput) (state : State KemSK) :
    Prod.map id PqxdhServerAuthCtxState.project <$>
      (evaluate setup.source key codec.frameRead (known setup.source codec control pending root)).run state =
      (fun result => complete control (restore state.1 result.2.2) result.1) <$>
        (simulateQ (beaconNative setup codec)
          (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead pending
            (PqxdhRootTableInitialization.rootArray root))).run ((), state.2.cache) := by
  rw [known, after_evaluate]
  have same := congrArg (Functor.map (fun result => complete control (restore state.1 result.2.2) result.1))
    (PqxdhServerAuthCtxNative.beacon_after_source setup codec key codec.frameRead pending
      (PqxdhRootTableInitialization.rootArray root) ((), state.2))
  rw [simulateQ_map, StateT.run_map]
  simpa only [RawCtxSelectedReceiveCompiler.project, PqxdhServerAuthCtxNative.evaluate,
    PqxdhSelectedStateInterpreter.evaluate, PqxdhSelectedStateInterpreter.pair,
    StateT.run, Functor.map_map, Prod.map_def, id_eq] using same.symm

/-- The actual source Beacon touch and returned table state are retained before either post-root continuation. -/
def touched (state : Local KemSK) (message : PqxdhJointDhExtractFamily.Message) (table : HiddenTable) : Local KemSK :=
  (({ state.1.1 with ghost := { state.1.1.ghost with touches := state.1.1.ghost.touches ++ [Touch.beacon message] } },
    state.1.2.1, table), state.2)

/-- The full key-free finish compiler retains the real prefix, exact selected-table dispatch and both complete source tail programs. -/
noncomputable def finish (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) (select : Bool)
    (raw : Pqxdh.Bytes) : Program KemSK (Option Pqxdh.Bytes) :=
  fun state =>
    match state.1.1.beacon.beacon.phase with
    | .initSent control _ oneTime kem => do
        let prepared ← simulateQ PqxdhServerAuthCtxAmbient.coin
          ((beaconPrefix setup codec context.beaconSeed control state.1.1.beacon.beacon.identity oneTime kem raw).run' ())
        match prepared with
        | none => pure (complete control state none)
        | some pending => do
            let message := PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected
            let derived ← simulateQ PqxdhServerAuthCtxAmbient.coin
              (((PqxdhServerAuthCtxState.tableServices (WireResponse := WireResponse) setup context select).derive message).run state.1.2.2)
            let next := touched state message derived.2
            match derived.1 with
            | .rejected => pure (complete control next none)
            | .root root => (known setup.source codec control pending root).run next
            | .hidden => (selected setup.source codec rest control pending).run next
    | _ => pure (none, state)

/-- Installing the component-owned cache commutes with the actual Beacon touch and table-result update. -/
theorem touched_restore (state : Local KemSK) (message : PqxdhJointDhExtractFamily.Message)
    (table : HiddenTable) (cache : CtxRO.QueryCache) :
    touched (restore state cache) message table = restore (touched state message table) cache := by
  rfl

/-- The actual complete Beacon finish has the same reply and full source poststate under the dynamic component interpreter, for arbitrary raw input and either designation route. -/
theorem finish_source (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (select : Bool) (raw : Pqxdh.Bytes) (key : RootOutput) (state : State KemSK) :
    Prod.map id PqxdhServerAuthCtxState.project <$>
      (evaluate setup.source key codec.frameRead (finish setup codec context rest select raw)).run state =
      (fun reply => (reply.1, (reply.2, state.1.2))) <$>
        (finishStep setup codec (context.publicValue setup) context.beaconSeed
          (if select then selectingServices setup context
            (factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest))
            else factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest)) raw).run
              (PqxdhServerAuthCtxState.project state).1 := by
  cases phase : state.1.1.1.beacon.beacon.phase <;>
    simp only [evaluate, PqxdhServerAuthCtxNative.evaluate, PqxdhSelectedStateInterpreter.evaluate,
      finish, finishStep, PqxdhServerAuthCtxState.project, restore, restoreFlat, StateT.run, phase]
  all_goals try simp only [simulateQ_pure, map_pure]
  all_goals try rfl
  have runBind {σ α β : Type} (work : StateT σ ProbComp α)
      (next : α → StateT σ ProbComp β) (initial : σ) :
      (work >>= next) initial = work initial >>= fun result => next result.1 result.2 := rfl
  have runCoins {α : Type} (work : ProbComp α) (initial : Component) :=
    coins_simulate setup.source key codec.frameRead work initial
  simp only [StateT.run] at runCoins
  simp only [simulateQ_bind, runBind, runCoins, bind_map_left, map_bind]
  refine bind_congr fun prepared => ?_
  cases prepared <;> simp only [simulateQ_pure, map_pure, simulateQ_bind, runBind, runCoins, bind_map_left, map_bind]
  all_goals try rfl
  have deriveSame :
      (if select then selectingServices setup context
        (factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest))
        else factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest)).derive =
      (tableServices (WireResponse := WireResponse) setup context select).derive := by
    cases select <;> rfl
  rw [deriveSame]
  refine bind_congr fun derived => ?_
  cases derived.1 <;> simp only [simulateQ_pure, map_pure, bind_pure_comp, Functor.map_map]
  all_goals try rfl
  case root root =>
    rename_i control prekey oneTime kem pending
    simpa only [evaluate, PqxdhServerAuthCtxNative.evaluate, PqxdhSelectedStateInterpreter.evaluate,
      StateT.run, Functor.map_map, complete, restore, restoreFlat, touched] using
      (known_source setup codec key control pending root
        (touched state.1 (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected) derived.2, state.2))
  case hidden =>
    rename_i control prekey oneTime kem pending
    cases select <;> simpa only [Bool.false_eq_true, ite_false, ite_true, selectingServices,
      evaluate, PqxdhServerAuthCtxNative.evaluate, PqxdhSelectedStateInterpreter.evaluate,
      StateT.run, Functor.map_map, complete, restore, restoreFlat, touched] using
      (selected_source setup codec checks context key rest control pending
        (touched state.1 (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected) derived.2, state.2))

end BeaconcryptCore.Computational.PqxdhServerAuthCtxFinish

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxFinish.callback_evaluate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxFinish.callback_evaluate

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxFinish.complete_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxFinish.complete_restore

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxFinish.after_evaluate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxFinish.after_evaluate

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxFinish.coins_simulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxFinish.coins_simulate

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxFinish.selected_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxFinish.selected_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxFinish.known_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxFinish.known_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxFinish.touched_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxFinish.touched_restore

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxFinish.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxFinish.finish_source
