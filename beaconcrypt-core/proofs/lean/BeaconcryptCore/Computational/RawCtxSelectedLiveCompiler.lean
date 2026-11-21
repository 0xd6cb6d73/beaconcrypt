import BeaconcryptCore.Computational.RawCtxSelectedLiveSource
import BeaconcryptCore.Computational.RawCtxSelectedAliasCompiler

/-!
The original selected owner's adaptive record/public/read program compiles to the existing common receive/send/public primitive capability plus private read requests. A read request carries only the selected kernel representation, never the unavailable chain bytes. The compiler retains the original owner, read history, exposure flag and actual operation replies; the backend retains the one shared primitive state and the complete candidate list, including any prior entries. Both available and masked readers use the same program.

The complete equality only reassociates retained state. It preserves actual rejected operations, optional reads, failed callbacks, timestamps and all repeated inputs. The private kernel argument and analysis history are not exposed as public capabilities. This operational factorization does not prove a reached uniform cut, small exposure probability, initial-first32 secrecy, additional-owner freshness or the final source hybrid. The imported fixed-source/library contracts and live-only scope remain unchanged; snapshots, persistence and restoration are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedLiveCompiler
open RawCtxSelectedChain RawCtxSelectedLiveRead RawCtxSelectedLiveTrace
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

abbrev ReadInput := Read × Option Kernel
def ReadQueries : OracleSpec ReadInput := fun query => ReadSpec.Range query.1
abbrev Spec := RawCtxSelectedAliasPrimitives.Spec + ReadQueries

def primitiveForward : QueryImpl RawCtxSelectedAliasPrimitives.Spec (OracleComp Spec) :=
  fun query => Spec.query (.inl query)

noncomputable def handler {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (reader : Reader) :
    QueryImpl Spec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl query => RawCtxSelectedAliasPrimitives.handler source writer output query
  | .inr query => pure (reader query.1 query.2)

noncomputable def inputs : Spec.Domain → List RootOutput
  | .inl query => RawCtxSelectedAliasPrimitives.inputs query
  | .inr query => candidates query.1 query.2

noncomputable def recorded {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (reader : Reader) :=
  RawCtxSelectedQueryTrace.recorded (handler (Auxiliary := Auxiliary) source writer output reader) inputs

abbrev OuterState (Metadata : Type) (serverCount beaconCount : Nat) :=
  (RawCtxChainOwner.State Kernel Metadata × RawCtxProtocolReveals.History serverCount beaconCount) × Bool

noncomputable def compiler {Metadata : Type} {serverCount beaconCount : Nat}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) :
    QueryImpl SourceSpec (StateT (OuterState Metadata serverCount beaconCount) (OracleComp Spec)) :=
  fun query state => match query with
  | .inl request => do
      let result ← simulateQ primitiveForward ((RawCtxSelectedAliasCompiler.compiler sender decode request).run state.1.1)
      pure (result.1, ((result.2, RawCtxProtocolReveals.tick state.1.2), state.2))
  | .inr read => do
      let entry := some state.1.1.kernel
      let reply ← Spec.query (.inr (read, entry))
      pure (reply, ((state.1.1, RawCtxProtocolReveals.note (observation owner read reply) state.1.2),
        state.2 || exposed read entry))

/-- Forwarded original primitives retain their exact recorded source handler and all candidate entries. -/
theorem primitive_recorded {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (reader : Reader) :
    recorded (Auxiliary := Auxiliary) source writer output reader ∘ₛ primitiveForward =
      RawCtxSelectedAliasCompiler.recorded source writer output := by
  funext query state
  exact congrArg (fun work => work state)
    (_root_.simulateQ_spec_query (recorded source writer output reader) (.inl query))

noncomputable def nested {Metadata Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (reader : Reader) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) :
    QueryImpl SourceSpec (StateT (OuterState Metadata serverCount beaconCount)
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary × List RootOutput) ProbComp)) :=
  fun query state => match query with
  | .inl request =>
      (fun result => (result.1, ((result.2, RawCtxProtocolReveals.tick state.1.2), state.2))) <$>
        (RawCtxSelectedAliasCompiler.nested source writer output sender decode request).run state.1.1
  | .inr read => do
      let entry := some state.1.1.kernel
      let reply ← recorded source writer output reader (.inr (read, entry))
      pure (reply, ((state.1.1, RawCtxProtocolReveals.note (observation owner read reply) state.1.2),
        state.2 || exposed read entry))

/-- The compiled public/record/read step executes the same complete recorded callbacks and updates original chronology. -/
theorem step_recorded {Metadata Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (reader : Reader) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (query : SourceSpec.Domain) (state : OuterState Metadata serverCount beaconCount) :
    simulateQ (recorded (Auxiliary := Auxiliary) source writer output reader)
      ((compiler sender decode owner query).run state) =
      (nested source writer output reader sender decode owner query).run state := by
  cases query with
  | inl request =>
    simp only [compiler, nested, StateT.run, bind_pure_comp, simulateQ_map]
    rw [← QueryImpl.simulateQ_compose, primitive_recorded]
    exact congrArg (fun work => (fun result => (result.1,
      ((result.2, RawCtxProtocolReveals.tick state.1.2), state.2))) <$> work)
      (RawCtxSelectedAliasCompiler.step_recorded source writer output sender decode request state.1.1)
  | inr read =>
    simp only [compiler, nested, StateT.run, bind_pure_comp, simulateQ_map, simulateQ_spec_query]

def splitState {Metadata Auxiliary : Type} {serverCount beaconCount : Nat}
    (state : RawCtxSelectedLiveTrace.State Metadata Auxiliary serverCount beaconCount) :
    OuterState Metadata serverCount beaconCount × (RawCtxSharedPrimitive.SharedState Auxiliary × List RootOutput) :=
  (((state.1.1.1, state.1.2), state.2), state.1.1.2)

def joinState {Metadata Auxiliary : Type} {serverCount beaconCount : Nat}
    (state : OuterState Metadata serverCount beaconCount ×
      (RawCtxSharedPrimitive.SharedState Auxiliary × List RootOutput)) :
    RawCtxSelectedLiveTrace.State Metadata Auxiliary serverCount beaconCount :=
  (((state.1.1.1, state.2), state.1.1.2), state.1.2)

private theorem state_map {S A B : Type} (f : A → B) (work : StateT S ProbComp A) (state : S) :
    (f <$> work) state = (fun result => (f result.1, result.2)) <$> work state := by
  exact StateT.run_map f work state

private theorem state_pure {S A : Type} (value : A) (state : S) :
    (pure value : StateT S ProbComp A) state = pure (value, state) := rfl

/-- Flattening changes only the association of owner, original history, exposure bit and shared primitive/candidate state. -/
theorem nested_step {Metadata Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (reader : Reader) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (query : SourceSpec.Domain) (state : RawCtxSelectedLiveTrace.State Metadata Auxiliary serverCount beaconCount) :
    Prod.map id joinState <$>
      ((nested source writer output reader sender decode owner).flattenStateT query).run (splitState state) =
      (observedImpl source writer (RawCtxKdfRequestTable.fullResponse output) sender decode owner reader query).run state := by
  cases query with
  | inl request =>
    have old := congrFun (congrFun (RawCtxSelectedAliasCompiler.nested_flatten
      (Metadata := Metadata) (Auxiliary := Auxiliary) source writer output sender decode) request) state.1.1
    have lifted := congrArg (fun work => (fun result => (result.1,
      ((result.2, RawCtxProtocolReveals.tick state.1.2), state.2))) <$> work) old
    simpa only [nested, observedImpl, QueryImpl.flattenStateT, splitState, joinState,
      StateT.run, StateT.mk, state_map, Functor.map_map, Prod.map_def, id_eq, Function.comp_def,
      SourceSpec, RawCtxSelectedPublicTrace.SourceSpec, OracleSpec.Range, OracleSpec.add_def, Sum.elim] using lifted
  | inr read =>
    simp [nested, observedImpl, QueryImpl.flattenStateT, splitState,
      recorded, RawCtxSelectedQueryTrace.recorded, handler, inputs,
      StateT.run, StateT.mk, state_map, bind_pure_comp]
    rfl

def regroup {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat} :
    ((Result × OuterState Metadata serverCount beaconCount) ×
      (RawCtxSharedPrimitive.SharedState Auxiliary × List RootOutput)) →
    Result × RawCtxSelectedLiveTrace.State Metadata Auxiliary serverCount beaconCount :=
  fun result => (result.1.1, joinState (result.1.2, result.2))

/-- The same complete adaptive live trace is the compiled primitive program, with all prior history and candidates retained. -/
theorem source_project {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (reader : Reader) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (client : OracleComp SourceSpec Result) (state : RawCtxSelectedLiveTrace.State Metadata Auxiliary serverCount beaconCount) :
    regroup <$> (simulateQ (recorded source writer output reader)
      ((simulateQ (compiler sender decode owner) client).run (splitState state).1)).run (splitState state).2 =
      (simulateQ (observedImpl source writer (RawCtxKdfRequestTable.fullResponse output)
        sender decode owner reader) client).run state := by
  have equation : (recorded (Auxiliary := Auxiliary) source writer output reader).mapStateTBase
      (compiler (Metadata := Metadata) sender decode owner) =
        nested source writer output reader sender decode owner := by
    funext query outer
    exact step_recorded source writer output reader sender decode owner query outer
  have finished := simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (recorded (Auxiliary := Auxiliary) source writer output reader) (compiler sender decode owner)
    client (splitState state).1 (splitState state).2
  have steps : ∀ (query : SourceSpec.Domain)
      (outer : OuterState Metadata serverCount beaconCount × (RawCtxSharedPrimitive.SharedState Auxiliary × List RootOutput)),
      Prod.map id joinState <$>
        ((nested source writer output reader sender decode owner).flattenStateT query).run outer =
      (observedImpl source writer (RawCtxKdfRequestTable.fullResponse output)
        sender decode owner reader query).run (joinState outer) := by
    intro query outer
    exact nested_step source writer output reader sender decode owner query (joinState outer)
  rw [finished, equation, Functor.map_map]
  exact map_run_simulateQ_eq_of_query_map_eq _ _ joinState steps client (splitState state)

end BeaconcryptCore.Computational.RawCtxSelectedLiveCompiler

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveCompiler.primitive_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveCompiler.primitive_recorded

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveCompiler.step_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveCompiler.step_recorded

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveCompiler.nested_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveCompiler.nested_step

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveCompiler.source_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveCompiler.source_project
