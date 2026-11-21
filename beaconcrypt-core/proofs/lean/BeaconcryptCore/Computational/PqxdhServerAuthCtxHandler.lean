import BeaconcryptCore.Computational.PqxdhServerAuthCtxBuild
import BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling

/-! A concrete optional compiler for the entire original Server-authentication API. It retains all source fields, actual probabilistic work, designation and sticky refusal, and routes every cryptographic callback through the existing dynamic component interface. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxHandler
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhServerAuthCtxBuild (Compiler)
variable {KemSK Result : Type}

/-- Mathematical evaluation commutes with observing the actual reply while retaining every local and component field. -/
theorem map_evaluate {Value : Type} (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (work : Program KemSK Result) (f : Result → Value) :
    evaluate source key read (f <$> work) = f <$> evaluate source key read work := by
  simp only [map_eq_bind_pure_comp, Function.comp_def, evaluate, PqxdhServerAuthCtxNative.evaluate,
    PqxdhSelectedStateInterpreter.bind_evaluate, PqxdhSelectedStateInterpreter.pure_evaluate]

/-- Optional lifting wraps the actual source reply without changing either complete state or the component program. -/
theorem lifted_source (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (work : Program KemSK Result) (state : State KemSK) :
    Prod.map id PqxdhServerAuthCtxState.project <$>
      (evaluate source key read (OptionT.lift work).run).run state =
      (fun result => (some result.1, result.2)) <$>
        Prod.map id PqxdhServerAuthCtxState.project <$> (evaluate source key read work).run state := by
  simp only [OptionT.run_lift, bind_pure_comp, map_evaluate, StateT.run_map, Functor.map_map]
  rfl

variable {ι : Type} {baseSpec : OracleSpec ι} {Reader WireResponse : Type}

/-- The complete original API dispatch. Ordinary/public cryptographic work remains real; the selected operations expose no explicit selected-key argument. -/
noncomputable def route (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (select : Bool) : QueryImpl ServerAuthSpec (Compiler KemSK)
  | .inl coin => OptionT.lift (coins (unifSpec.query coin))
  | .inr (.accept raw) => OptionT.lift (accept setup codec checks context select raw)
  | .inr (.build session payload) => PqxdhServerAuthCtxBuild.build setup.source codec checks rest session payload
  | .inr (.finish raw) => OptionT.lift (PqxdhServerAuthCtxFinish.finish setup codec context rest select raw)
  | .inr (.hmac key message) => OptionT.lift (hmac setup context key message)
  | .inr (.hash bytes) => OptionT.lift (hash bytes)
  | .inr (.reveal keyId) => OptionT.lift (reveal keyId)

/-- Only a reached marked pending token requires an unused selected seal endpoint. Other source operations add no such condition. -/
def Ready (query : ServerAuthSpec.Domain) (state : State KemSK) : Prop :=
  match query with
  | .inr (.build session _) => state.1.1.2.1 session = true →
      (state.1.1.1.pending session).isSome → state.2.selected.1.usedNonces = []
  | _ => True

/-- Every concrete API route returns the actual source answer and full source poststate under the component interpreter. The sole unused-endpoint condition is supplied only to an actual selected builder. -/
theorem route_source (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (select : Bool) (query : ServerAuthSpec.Domain) (key : RootOutput) (state : State KemSK)
    (ready : Ready query state) :
    Prod.map id PqxdhServerAuthCtxState.project <$>
      (evaluate setup.source key codec.frameRead (route setup codec checks context rest select query).run).run state =
      (fun reply => (some reply.1, (reply.2, state.1.2))) <$>
        (skeleton setup codec checks (context.publicValue setup) context.beaconSeed
          (if select then selectingServices setup context
            (factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest))
            else factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest)) query).run
              (PqxdhServerAuthCtxState.project state).1 := by
  cases query with
  | inl coin =>
      rw [route, lifted_source, coins_source]
      simp only [skeleton, StateT.run, Functor.map_map]
      rfl
  | inr query =>
      cases query with
      | build session payload =>
          have same := PqxdhServerAuthCtxBuild.build_source setup codec checks context rest session payload key state ready
          cases select <;> exact same
      | accept raw =>
          rw [route, lifted_source, accept_source setup codec checks context select raw
            (PqxdhServerAuthCtxMaterial.output key rest) key state]
          simp only [skeleton, Functor.map_map]
          rfl
      | finish raw =>
          rw [route, lifted_source, PqxdhServerAuthCtxFinish.finish_source setup codec checks context rest select raw key state]
          simp only [skeleton, Functor.map_map]
          rfl
      | hmac hmacKey message =>
          rw [route, lifted_source, hmac_source setup codec checks context
            (PqxdhServerAuthCtxMaterial.output key rest) hmacKey message key state]
          cases select <;> simp only [Functor.map_map] <;> rfl
      | hash bytes =>
          rw [route, lifted_source, hash_source]
          simp only [Functor.map_map]
          rfl
      | reveal keyId =>
          rw [route, lifted_source, reveal_source]
          simp only [skeleton, StateT.run, map_pure]
          rfl


/-- A deterministic local settlement retains the actual component poststate and adds no request. -/
theorem post_evaluate {Value : Type} (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (work : Program KemSK Result)
    (post : Result × Local KemSK → Value × Local KemSK) (state : State KemSK) :
    (evaluate source key read (fun localState => post <$> work localState)).run state =
      (fun result => ((post (result.1, result.2.1)).1, (post (result.1, result.2.1)).2, result.2.2)) <$>
        (evaluate source key read work).run state := by
  change PqxdhSelectedStateInterpreter.pair <$> (simulateQ
    (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
      (post <$> work.run state.1)).run state.2 = _
  rw [simulateQ_map, StateT.run_map]
  simp only [evaluate, PqxdhServerAuthCtxNative.evaluate, StateT.run,
    PqxdhSelectedStateInterpreter.evaluate, Functor.map_map, PqxdhSelectedStateInterpreter.pair]


/-- Install the actual one-shot designation and sticky hidden-table refusal after the complete callback. -/
def settle (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (before : Local KemSK) (result : Result × Local KemSK) : Result × Local KemSK :=
  keepHiddenBad before (result.1, (result.2.1, before.2 || hiddenDesignated Q j query before.1))

/-- Settlement observes no component cache. Its full state projection is exactly the original source settlement. -/
theorem settle_restore (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (before : Local KemSK) (result : Result × Local KemSK) (oldCache newCache : CtxRomAuth.CtxRO.QueryCache) :
    Prod.map id (fun after => restore after newCache) (settle Q j query before result) =
      settle Q j query (restore before oldCache)
        (Prod.map id (fun after => restore after newCache) result) := by
  rw [settle, bad_restore before _ oldCache newCache]
  simp only [settle, restore, designated_restore, Prod.map, id_eq]

/-- The complete executable original API, including its exact one-shot selection and persistent refusal annotation. -/
noncomputable def handler (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) : QueryImpl ServerAuthSpec (Compiler KemSK) :=
  fun query => OptionT.mk fun before =>
    settle Q j query before <$>
      (route setup codec checks context rest
        (!before.2 && hiddenDesignated Q j query before.1) query).run before


/-- Projection commutes with the actual completed optional handler, including designation and refusal. -/
theorem handler_project (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain) (key : RootOutput) (state : State KemSK) :
    Prod.map id PqxdhServerAuthCtxState.project <$>
      (evaluate setup.source key codec.frameRead (handler setup codec checks context rest Q j query).run).run state =
      settle Q j query (PqxdhServerAuthCtxState.project state) <$>
        Prod.map id PqxdhServerAuthCtxState.project <$>
          (evaluate setup.source key codec.frameRead
            (route setup codec checks context rest (!state.1.2 && hiddenDesignated Q j query state.1.1) query).run).run state := by
  change Prod.map id PqxdhServerAuthCtxState.project <$>
    (evaluate setup.source key codec.frameRead (fun before =>
      settle Q j query state.1 <$> (route setup codec checks context rest
        (!state.1.2 && hiddenDesignated Q j query state.1.1) query).run before)).run state = _
  rw [post_evaluate]
  simp only [Functor.map_map]
  congr 1
  funext result
  exact settle_restore Q j query state.1 (result.1, result.2.1) state.2.cache result.2.2.cache


/-- The complete handler is the literal original omitted-entry source transition, with only a separate optional component layer. The reached selected builder's unused-endpoint obligation remains explicit. -/
theorem handler_source (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain) (key : RootOutput) (state : State KemSK)
    (ready : Ready query state) :
    Prod.map id PqxdhServerAuthCtxState.project <$>
      (evaluate setup.source key codec.frameRead (handler setup codec checks context rest Q j query).run).run state =
      (fun result => (some result.1, result.2)) <$>
        (hiddenHandler setup codec checks context Q j
          (factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest)) query).run
            (PqxdhServerAuthCtxState.project state) := by
  rw [handler_project, route_source setup codec checks context rest _ query key state ready]
  simp only [Functor.map_map, hiddenHandler, StateT.run, once, latch,
    PqxdhServerAuthCtxState.project, restore, designated_restore]
  simp only [settle, designated_restore]
  cases state.1.2 <;> cases hiddenDesignated Q j query state.1.1 <;>
    cases bad : state.1.1.2.2.bad <;> simp [keepHiddenBad, restoreFlat, bad]


/-- Evaluation retains the complete optional adaptive continuation and both private states. Refusal terminates the same continuation; it is not disclosed as an ordinary source reply. -/
theorem program_evaluate (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (compiler : QueryImpl ServerAuthSpec (Compiler KemSK))
    (client : OracleComp ServerAuthSpec Result) :
    evaluate source key read (simulateQ compiler client).run =
      simulateQ ((fun query => evaluate source key read (compiler query).run) :
        QueryImpl (RawCtxSelectedFamilyNonceCoupling.Optional ServerAuthSpec) (StateT (State KemSK) ProbComp))
        (RawCtxSelectedFamilyNonceCoupling.optionalClient client) := by
  rw [← RawCtxSelectedFamilyNonceCoupling.optional_client compiler client]
  exact PqxdhSelectedStateInterpreter.program _ _ _

end BeaconcryptCore.Computational.PqxdhServerAuthCtxHandler

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxHandler.map_evaluate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxHandler.map_evaluate
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxHandler.lifted_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxHandler.lifted_source
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxHandler.route_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxHandler.route_source
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxHandler.post_evaluate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxHandler.post_evaluate
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxHandler.settle_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxHandler.settle_restore
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxHandler.handler_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxHandler.handler_project
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxHandler.handler_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxHandler.handler_source
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxHandler.program_evaluate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxHandler.program_evaluate
