import BeaconcryptCore.Computational.PqxdhServerAuthEntryServices
import BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds
import BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds

/-! The concrete dynamic CTX compiler retains the original protocol state with an unused cache placeholder. The actual commitment cache belongs only to the component interpreter and is reinstalled by the mathematical source projection. The executable takes no component-cache or selected-key argument; arbitrary correlations in supplied local values remain possible. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxState
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor
open PqxdhSecretInputKdf PqxdhJointKdfGame
open CtxRomAuth

variable {KemSK Result : Type}

abbrev Component := AdaptiveCtxDynamicKnownKeys.SourceState
abbrev Local (KemSK : Type) := HiddenState KemSK
abbrev State (KemSK : Type) := Local KemSK × Component
abbrev Program (KemSK : Type) := StateT (Local KemSK) (OracleComp AdaptiveCtxDynamicKnownKeys.Spec)

/-- The source skeleton's commitment cache is supplied only by the mathematical projection. -/
def restoreFlat (state : FlatState KemSK HiddenTable) (cache : CtxRO.QueryCache) :
    FlatState KemSK HiddenTable := ({ state.1 with ctx := cache }, state.2)

/-- Restore only the original commitment cache; every protocol field and private source annotation is retained. -/
def restore (localState : Local KemSK) (cache : CtxRO.QueryCache) : HiddenState KemSK :=
  (restoreFlat localState.1 cache, localState.2)

def project (state : State KemSK) : HiddenState KemSK := restore state.1 state.2.cache

/-- A second mathematical cache installation replaces only the first one. -/
theorem restore_restore (localState : Local KemSK) (first second : CtxRO.QueryCache) :
    restore (restore localState first) second = restore localState second := by
  rfl

noncomputable def coins (work : ProbComp Result) : Program KemSK Result :=
  StateT.lift (simulateQ PqxdhServerAuthCtxAmbient.coin work)

noncomputable def evaluate (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (work : Program KemSK Result) :
    StateT (State KemSK) ProbComp Result := PqxdhServerAuthCtxNative.evaluate source key read work

/-- Every actual source coin program keeps the complete local and component states while forwarding its unchanged adaptive uniform draws. -/
theorem coins_evaluate (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (work : ProbComp Result) (state : State KemSK) :
    (evaluate source key read (coins work)).run state =
      (fun reply => (reply, state)) <$> work := by
  rw [evaluate, coins, PqxdhServerAuthCtxNative.lift_evaluate]
  exact PqxdhServerAuthCtxAmbient.coin_program source key read work state

/-- The same full source coin sampler preserves the restored original protocol state, including the actual private cache. -/
theorem coins_source (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (work : ProbComp Result) (state : State KemSK) :
    Prod.map id project <$> (evaluate source key read (coins work)).run state =
      (fun reply => (reply, project state)) <$> work := by
  simp only [coins_evaluate, Functor.map_map, Prod.map, id_eq]

/-- Forward the actual probabilistic local-state program. Only its local protocol state is available to the executable. -/
noncomputable def localCoins (work : StateT (Local KemSK) ProbComp Result) : Program KemSK Result :=
  fun state => simulateQ PqxdhServerAuthCtxAmbient.coin (work.run state)

/-- The forwarded complete probabilistic program retains every component field, not only the cache. -/
theorem localCoins_evaluate (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (work : StateT (Local KemSK) ProbComp Result)
    (state : State KemSK) :
    (evaluate source key read (localCoins work)).run state =
      (fun reply => (reply.1, (reply.2, state.2))) <$> work.run state.1 := by
  have same := congrArg (Functor.map (fun result => (result.1.1, (result.1.2, result.2.2))))
    (PqxdhServerAuthCtxAmbient.coin_program source key read (work.run state.1) state)
  change (fun a => (a.1.1, (a.1.2, a.2))) <$>
    (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
      (simulateQ PqxdhServerAuthCtxAmbient.coin (work.run state.1))).run state.2 = _
  simpa only [RawCtxSelectedReceiveCompiler.evaluated, StateT.run, Functor.map_map] using same

/-- A probabilistic flat step retains the existing one-shot flag. -/
noncomputable def flatCoins (work : StateT (FlatState KemSK HiddenTable) ProbComp Result) : Program KemSK Result :=
  localCoins fun state => (fun reply => (reply.1, (reply.2, state.2))) <$> work.run state.1

/-- Cache naturality is a structural equation, instantiated below for the actual source acceptance and public-HMAC programs. -/
theorem flatCoins_source (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (work : StateT (FlatState KemSK HiddenTable) ProbComp Result)
    (natural : ∀ before cache, work.run (restoreFlat before cache) =
      Prod.map id (fun after => restoreFlat after cache) <$> work.run before)
    (state : State KemSK) :
    Prod.map id project <$> (evaluate source key read (flatCoins work)).run state =
      (fun reply => (reply.1, (reply.2, state.1.2))) <$> work.run (project state).1 := by
  rw [flatCoins, localCoins_evaluate]
  change _ = (fun reply => (reply.1, (reply.2, state.1.2))) <$>
    work.run (restoreFlat state.1.1 state.2.cache)
  rw [natural]
  simp only [StateT.run, Functor.map_map, Prod.map, id_eq, project, restore]

variable {ι : Type} {baseSpec : OracleSpec ι} {Reader WireResponse : Type}

/-- The actual acceptance sampler uses only the omitted Extract table. Its unused response callbacks capture no selected material. -/
noncomputable def tableServices (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (select : Bool) : Services WireResponse HiddenTable where
  derive := if select then selectHidden setup.joint setup.dh context.seed context.scalar
    else hiddenDerive setup.hmac setup.joint setup.dh context.seed context.scalar
  table := hiddenPublic
  hiddenBuild _ _ server := pure (.ok (none, server))
  hiddenAfter _ := pure none

/-- An actual acceptance never calls either response continuation, so the selected factor and both source tail services disappear from this entire step. -/
theorem accept_services (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output)
    (raw : Pqxdh.Bytes) :
    acceptStep setup codec checks (context.publicValue setup)
        (factorServices setup codec checks context value) raw =
      acceptStep setup codec checks (context.publicValue setup) (tableServices setup context false) raw := by
  rfl

/-- Acceptance retains the complete source state and is independent of the private commitment-cache field. Every source sampler and the table reply remain in their original order. -/
theorem accept_restore (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (publicValue : PqxdhJointGapDh.PublicChallenge) (svc : Services WireResponse HiddenTable)
    (raw : Pqxdh.Bytes) (state : FlatState KemSK HiddenTable) (cache : CtxRO.QueryCache) :
    (acceptStep setup codec checks publicValue svc raw).run (restoreFlat state cache) =
      Prod.map id (fun after => restoreFlat after cache) <$>
        (acceptStep setup codec checks publicValue svc raw).run state := by
  simp only [acceptStep, StateT.run, restoreFlat, map_bind]
  refine bind_congr fun ⟨collected, consumed⟩ => ?_
  cases collected <;> simp only [map_pure, Prod.map, id_eq]
  split <;> simp only [map_pure, map_bind, Prod.map, id_eq]
  refine bind_congr fun ⟨derived, table⟩ => ?_
  cases derived <;> rfl

noncomputable def accept (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (select : Bool) (raw : Pqxdh.Bytes) :
    Program KemSK (Option Nat) :=
  flatCoins (acceptStep setup codec checks (context.publicValue setup) (tableServices setup context select) raw)

/-- The literal acceptance compiler preserves the complete original acceptance state and ordered source work. It makes no honest-candidate or successful-acceptance restriction. -/
theorem accept_table_source (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (select : Bool) (raw : Pqxdh.Bytes)
    (key : RootOutput) (state : State KemSK) :
    Prod.map id project <$> (evaluate setup.source key codec.frameRead
      (accept setup codec checks context select raw)).run state =
      (fun reply => (reply.1, (reply.2, state.1.2))) <$>
        (acceptStep setup codec checks (context.publicValue setup)
          (tableServices setup context select) raw).run (project state).1 := by
  exact flatCoins_source setup.source key codec.frameRead _
    (accept_restore setup codec checks (context.publicValue setup) (tableServices setup context select) raw) state

/-- The actual factor handler and its designated-selection variant both execute the same concrete acceptance compiler, with all candidate branches retained. -/
theorem accept_source (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (select : Bool) (raw : Pqxdh.Bytes)
    (value : PqxdhServerAuthKeySchedule.Output) (key : RootOutput) (state : State KemSK) :
    Prod.map id project <$> (evaluate setup.source key codec.frameRead
      (accept setup codec checks context select raw)).run state =
      (fun reply => (reply.1, (reply.2, state.1.2))) <$>
        (acceptStep setup codec checks (context.publicValue setup)
          (if select then selectingServices setup context (factorServices setup codec checks context value)
            else factorServices setup codec checks context value) raw).run (project state).1 := by
  cases select <;> exact accept_table_source setup codec checks context _ raw key state

/-- The public-HMAC step never accesses the CTX cache; it retains the exact real off-domain evaluation and the original omitted-entry table effects on-domain. -/
theorem hmac_restore (setup : Setup baseSpec KemSK) (svc : Services WireResponse HiddenTable)
    (hmacKey : HmacBlock) (message : Pqxdh.Bytes) (state : FlatState KemSK HiddenTable) (cache : CtxRO.QueryCache) :
    (hmacStep setup svc hmacKey message).run (restoreFlat state cache) =
      Prod.map id (fun after => restoreFlat after cache) <$> (hmacStep setup svc hmacKey message).run state := by
  simp only [hmacStep, StateT.run, restoreFlat]
  split <;> simp only [map_bind, map_pure, Prod.map, id_eq]

noncomputable def hmac (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (hmacKey : HmacBlock) (message : Pqxdh.Bytes) : Program KemSK HmacBlock :=
  flatCoins (hmacStep setup (tableServices (WireResponse := Unit) setup context false) hmacKey message)

/-- The concrete public-HMAC compiler preserves the actual factor-side table, touch log, replies and state. The selected output is absent from this executable interface. -/
theorem hmac_source (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output)
    (hmacKey : HmacBlock) (message : Pqxdh.Bytes) (key : RootOutput) (state : State KemSK) :
    Prod.map id project <$> (evaluate setup.source key codec.frameRead (hmac setup context hmacKey message)).run state =
      (fun reply => (reply.1, (reply.2, state.1.2))) <$>
        (hmacStep setup (factorServices setup codec checks context value) hmacKey message).run (project state).1 := by
  exact flatCoins_source setup.source key codec.frameRead _
    (hmac_restore setup (tableServices (WireResponse := Unit) setup context false) hmacKey message) state

noncomputable def hash (bytes : Pqxdh.Bytes) : Program KemSK CtxDigest :=
  StateT.lift (PqxdhServerAuthCtxAmbient.hash bytes)

/-- Public hashing uses the component-owned cache shared with every known and selected record operation; all protocol state remains intact. -/
theorem hash_source (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes) (state : State KemSK) :
    Prod.map id project <$> (evaluate source key read (hash bytes)).run state =
      (fun reply => (reply.1, (reply.2, state.1.2))) <$> (hashStep bytes).run (project state).1 := by
  have same := congrArg (Functor.map (fun result => (result.1, restore result.2.1 result.2.2)))
    (PqxdhServerAuthCtxAmbient.hash_source source key read bytes state)
  rw [evaluate, hash, PqxdhServerAuthCtxNative.lift_evaluate]
  simpa only [hashStep, StateT.run, project, restore, restoreFlat, bind_pure_comp,
    Functor.map_map, Prod.map_def, id_eq, RawCtxSelectedReceiveCompiler.project] using same

/-- The actual Server-kernel reveal takes no component-cache or selected-key argument. The reachable source state determines which kernel is installed. -/
def reveal (keyId : Std.U64) : Program KemSK (Option ratchet.concrete.ConcreteRatchetKernel) :=
  fun state => pure (revealKernel keyId state.1.1, state)

/-- The reveal returns exactly the installed kernel, preserving every private source and component field. Its reachable advanced-chain shape is supplied by the existing source invariant. -/
theorem reveal_source (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (keyId : Std.U64) (state : State KemSK) :
    (evaluate source key read (reveal keyId)).run state =
      pure (revealKernel keyId (project state).1.1, state) := by
  simp only [evaluate, reveal, PqxdhServerAuthCtxNative.evaluate, PqxdhSelectedStateInterpreter.evaluate,
    StateT.run, simulateQ_pure,
    revealKernel, project, restore, restoreFlat]
  rfl

/-- The one-shot designation inspects the actual session counter and Beacon phase, not the private CTX cache. -/
theorem designated_restore (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (state : FlatState KemSK HiddenTable) (cache : CtxRO.QueryCache) :
    hiddenDesignated Q j query (restoreFlat state cache) = hiddenDesignated Q j query state := by
  cases query with
  | inl _ => rfl
  | inr query => cases query <;> rfl

/-- Sticky omitted-entry refusal commutes with restoring the real cache, even when the cache changed during the query. All original result and protocol fields survive. -/
theorem bad_restore (before : Local KemSK) (result : Result × Local KemSK)
    (oldCache newCache : CtxRO.QueryCache) :
    Prod.map id (fun after => restore after newCache) (keepHiddenBad before result) =
      keepHiddenBad (restore before oldCache)
        (Prod.map id (fun after => restore after newCache) result) := by
  simp only [keepHiddenBad, restore, restoreFlat, Prod.map, id_eq]
  split <;> simp_all only [Bool.false_eq_true, ite_true, ite_false]

/-- The full forwarded local sampler pays every one of its actual uniform requests. -/
theorem localCoins_bound (work : StateT (Local KemSK) ProbComp Result) (state : Local KemSK) (bound : Nat)
    (bounded : (work.run state).IsTotalQueryBound bound) :
    ((localCoins work).run state).IsTotalQueryBound bound := by
  exact PqxdhServerAuthCtxAmbient.coin_bound (work.run state) bound bounded

/-- Acceptance and table sampling issue no record or commitment requests through their coin routing. Their uniform work is counted separately, not discarded. -/
theorem localCoins_other (work : StateT (Local KemSK) ProbComp Result) (state : Local KemSK) :
    ((localCoins work).run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute 0 ∧
      ((localCoins work).run state).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 ∧
      ((localCoins work).run state).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 := by
  exact PqxdhServerAuthCtxAmbient.coin_other (work.run state)

/-- Public hashing forwards exactly one dynamic request; local fields and deterministic source work add no hidden oracle request. -/
theorem hash_bound (bytes : Pqxdh.Bytes) (state : Local KemSK) :
    ((hash bytes).run state).IsTotalQueryBound 1 := by
  simp [hash, PqxdhServerAuthCtxAmbient.hash, StateT.run_lift, bind_pure_comp,
    isQueryBound_map_iff, IsTotalQueryBound]

end BeaconcryptCore.Computational.PqxdhServerAuthCtxState

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxState.restore_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxState.restore_restore

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxState.coins_evaluate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxState.coins_evaluate

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxState.coins_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxState.coins_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxState.localCoins_evaluate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxState.localCoins_evaluate

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxState.flatCoins_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxState.flatCoins_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxState.accept_services' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxState.accept_services

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxState.accept_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxState.accept_restore

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxState.accept_table_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxState.accept_table_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxState.accept_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxState.accept_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxState.hmac_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxState.hmac_restore

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxState.hmac_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxState.hmac_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxState.hash_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxState.hash_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxState.reveal_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxState.reveal_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxState.designated_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxState.designated_restore

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxState.bad_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxState.bad_restore

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxState.localCoins_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxState.localCoins_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxState.localCoins_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxState.localCoins_other

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxState.hash_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxState.hash_bound
