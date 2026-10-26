import BeaconcryptCore.Computational.PqxdhServerAuthCtxFinish
import BeaconcryptCore.Computational.PqxdhServerAuthBuildSource

/-! The concrete complete build handler retains the original one-use token, full response outcome and session-indexed source seal trailer. Actual selected and ordinary tails use the same component-owned cache. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxBuild
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhSecretInputKdf PqxdhJointKdfGame
open CtxRomAuth
variable {KemSK : Type}
abbrev Response := PqxdhServerRegistrationPublication.Response
abbrev Outcome := RustM (Option Response × ServerState)
abbrev Log := List RawCtxSourceSend.SealContext
abbrev Compiler (KemSK : Type) := OptionT (Program KemSK)

/-- Settle the actual native build outcome, consume its pending token and append the reached successful-frame contexts under their original source session. -/
def complete (session : Nat) (state : Local KemSK) (outcome : Outcome) (log : Log) :
    Option Response × Local KemSK :=
  let result := afterBuild session state.1.1 (outcome, (log, state.1.1.ctx))
  (result.1, ((result.2, state.1.2), state.2))

/-- Actual settlement and session-labelled logging commute with restoration of the component-owned shared cache. -/
theorem complete_restore (session : Nat) (state : Local KemSK) (outcome : Outcome) (log : Log)
    (cache : CtxRO.QueryCache) :
    Prod.map id (fun after => restore after cache) (complete session state outcome log) =
      complete session (restore state cache) outcome log := by
  rfl

/-- Component refusal is distinct from the native response result. Every normal native outcome retains the entire reached seal trailer, including later outer-writer failure. -/
def post (session : Nat) (state : Local KemSK) (result : Option Outcome × Log) :
    Option (Option Response) × Local KemSK :=
  match result.1 with
  | none => (none, state)
  | some outcome => let settled := complete session state outcome result.2
                    (some settled.1, settled.2)

/-- Run the full optional component callback and then perform the original source settlement. -/
noncomputable def after (session : Nat)
    (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Option Outcome × Log)) : Compiler KemSK (Option Response) :=
  OptionT.mk fun state => post session state <$> work

/-- The callback's complete component poststate is retained through normal settlement and outer refusal. -/
theorem after_evaluate (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (session : Nat)
    (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Option Outcome × Log)) (state : State KemSK) :
    Prod.map id PqxdhServerAuthCtxState.project <$> (evaluate source key read (after session work).run).run state =
      (fun result => post session (restore state.1 result.2.cache) result.1) <$>
        (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read)
          source.crypto key) work).run state.2 := by
  change Prod.map id PqxdhServerAuthCtxState.project <$> PqxdhSelectedStateInterpreter.pair <$>
    (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read)
      source.crypto key) (post session state.1 <$> work)).run state.2 = _
  rw [simulateQ_map, StateT.run_map]
  simp only [Functor.map_map]
  congr 1
  funext result
  rcases result with ⟨⟨_ | outcome, log⟩, component⟩ <;> rfl

variable {ι : Type} {baseSpec : OracleSpec ι} {Reader WireResponse : Type}

/-- The actual selected builder starts a fresh local source seal trailer and retains its full optional result before session settlement. -/
noncomputable def selected (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : PqxdhServerAuthCtxCalls.Residual) (session : Nat)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (server : ServerState) : Compiler KemSK (Option Response) :=
  after session ((PqxdhServerAuthBuildProgram.compiled source codec checks rest token.pending payload () server).run.run [])

/-- The full selected builder, source log and final session settlement agree from an initially unused component endpoint. Failed inner and outer native writers remain in the same source execution. -/
theorem selected_source (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (session : Nat) (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (key : RootOutput) (state : State KemSK) (empty : state.2.selected.1.usedNonces = []) :
    Prod.map id PqxdhServerAuthCtxState.project <$>
      (evaluate setup.source key codec.frameRead
        (selected setup.source codec checks rest session token payload state.1.1.1.server).run).run state =
      (fun result => post session (restore state.1 result.2.2) (some result.1, result.2.1)) <$>
        ((factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest)).hiddenBuild
          token payload state.1.1.1.server).run ([], state.2.cache) := by
  rw [selected, after_evaluate]
  have same := congrArg (Functor.map (fun result => post session (restore state.1 result.2.2) (result.1, result.2.1)))
    (PqxdhServerAuthBuildSource.compiled_source setup codec checks key codec.frameRead rest
      token.pending payload () state.1.1.1.server ([], state.2) empty)
  simpa only [factorServices, RawCtxSelectedReceiveCompiler.project, PqxdhServerAuthCtxNative.evaluate,
    PqxdhSelectedStateInterpreter.evaluate, StateT.run, Functor.map_map, Prod.map_def,
    PqxdhSelectedStateInterpreter.pair, id_eq] using same.symm

/-- Ordinary roots run the real native builder and actual optional writers on the same shared component cache. -/
noncomputable def known (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (session : Nat) (token : PqxdhServerRelatedRootConsumer.Returned)
    (payload : Option Pqxdh.Bytes) (server : ServerState) : Compiler KemSK (Option Response) :=
  after session ((fun result => (some result.1, result.2)) <$>
    (simulateQ (PqxdhServerAuthCtxNative.tail source codec checks)
      (PqxdhServerRegistrationPublication.build source token.pending token.root payload () server)).run [])

/-- The full ordinary builder preserves every source outcome, successful-frame context and shared-cache effect before exact token and session settlement. -/
theorem known_source (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (session : Nat) (token : PqxdhServerRelatedRootConsumer.Returned)
    (payload : Option Pqxdh.Bytes) (key : RootOutput) (state : State KemSK) :
    Prod.map id PqxdhServerAuthCtxState.project <$>
      (evaluate setup.source key codec.frameRead
        (known setup.source codec checks session token payload state.1.1.1.server).run).run state =
      (fun result => post session (restore state.1 result.2.2) (some result.1, result.2.1)) <$>
        (simulateQ (tailImpl setup codec checks)
          (PqxdhServerRegistrationPublication.build setup.source token.pending token.root payload ()
            state.1.1.1.server)).run ([], state.2.cache) := by
  rw [known, after_evaluate, simulateQ_map, StateT.run_map]
  have same := congrArg (Functor.map (fun result => post session (restore state.1 result.2.2) (some result.1, result.2.1)))
    (PqxdhServerAuthCtxNative.build_source setup codec checks key codec.frameRead
      token.pending token.root payload state.1.1.1.server ([], state.2))
  simpa only [RawCtxSelectedReceiveCompiler.project, PqxdhServerAuthCtxNative.evaluate,
    PqxdhSelectedStateInterpreter.evaluate, StateT.run, Functor.map_map, Prod.map_def,
    PqxdhSelectedStateInterpreter.pair, id_eq] using same.symm

/-- Actual pending-token lookup dispatches the complete ordinary or selected builder, then consumes that token under the unchanged source settlement. -/
noncomputable def build (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : PqxdhServerAuthCtxCalls.Residual) (session : Nat)
    (payload : Option Pqxdh.Bytes) : Compiler KemSK (Option Response) :=
  OptionT.mk fun state =>
    match state.1.1.pending session with
    | none => pure (some none, state)
    | some token =>
        if state.1.2.1 session then
          (selected source codec checks rest session token payload state.1.1.server).run state
        else (known source codec checks session token payload state.1.1.server).run state

set_option backward.isDefEq.respectTransparency false in
/-- The complete actual build reply and source poststate are preserved. Only a reached selected builder requires the initially unused endpoint; an absent token or ordinary root adds no such condition. -/
theorem build_source (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (session : Nat) (payload : Option Pqxdh.Bytes) (key : RootOutput) (state : State KemSK)
    (empty : state.1.1.2.1 session = true → (state.1.1.1.pending session).isSome →
      state.2.selected.1.usedNonces = []) :
    Prod.map id PqxdhServerAuthCtxState.project <$>
      (evaluate setup.source key codec.frameRead (build setup.source codec checks rest session payload).run).run state =
      (fun reply => (some reply.1, (reply.2, state.1.2))) <$>
        (buildStep setup codec checks (factorServices setup codec checks context
          (PqxdhServerAuthCtxMaterial.output key rest)) session payload).run
            (PqxdhServerAuthCtxState.project state).1 := by
  cases found : state.1.1.1.pending session with
  | none =>
      simp only [build, OptionT.run_mk, evaluate, PqxdhServerAuthCtxNative.evaluate,
        PqxdhSelectedStateInterpreter.evaluate, StateT.run, buildStep, PqxdhServerAuthCtxState.project,
        restore, restoreFlat, found, simulateQ_pure, map_pure]
      rfl
  | some token =>
      by_cases marked : state.1.1.2.1 session = true
      · have same := selected_source setup codec checks context rest session token payload key state
          (empty marked (by rw [found]; rfl))
        simpa only [build, OptionT.run_mk, evaluate, PqxdhServerAuthCtxNative.evaluate,
          PqxdhSelectedStateInterpreter.evaluate, StateT.run, buildStep, PqxdhServerAuthCtxState.project,
          restore, restoreFlat, found, marked, ite_true, bind_pure_comp, Functor.map_map,
          post, complete, afterBuild] using same
      · have same := known_source setup codec checks session token payload key state
        simpa only [build, OptionT.run_mk, evaluate, PqxdhServerAuthCtxNative.evaluate,
          PqxdhSelectedStateInterpreter.evaluate, StateT.run, buildStep, PqxdhServerAuthCtxState.project,
          restore, restoreFlat, found, marked, Bool.false_eq_true, ite_false, bind_pure_comp, Functor.map_map,
          post, complete, afterBuild] using same

end BeaconcryptCore.Computational.PqxdhServerAuthCtxBuild

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuild.complete_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuild.complete_restore

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuild.after_evaluate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuild.after_evaluate

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuild.selected_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuild.selected_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuild.known_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuild.known_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuild.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuild.build_source
