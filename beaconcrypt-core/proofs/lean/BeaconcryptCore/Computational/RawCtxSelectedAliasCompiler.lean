import BeaconcryptCore.Computational.RawCtxSelectedAliasPrimitives

/-!
The actual owner/public interpreter compiles to one common source primitive capability without exposing selected chain bytes. Its original empty/decode/pin/shape checks, receive rollback, active failed-send advancement, optional replies, complete owner state and shared primitive state are unchanged. The compiled source run is exactly the existing chronological candidate trace, including every repeated known or public input.

The concrete alias coupling therefore applies to this same program: imposing the selected full76 response at byte-equal send/receive inputs and matching public addresses costs only the corresponding event in its original log. This is a fixed-target full-state theorem. Reached native stopped-input distribution, averaging through the explicit cut, live reveal/ancestor exposure and the complete global hybrid remain separate. Snapshots, persistence and restoration are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedAliasCompiler
open RawCtxSelectedAliasPrimitives RawCtxSelectedChain PqxdhJointKdfGame PqxdhFullSecretInputKdf

def receiveForward : QueryImpl ReceiveSpec (OracleComp Spec) :=
  fun query => Spec.query (.inl query)
def sendForward : QueryImpl SendSpec (OracleComp Spec) :=
  fun query => Spec.query (.inr (.inl query))
def publicForward : QueryImpl RawCtxServerServices.PublicSpec (OracleComp Spec) :=
  fun query => Spec.query (.inr (.inr query))

noncomputable def calls : RawCtxChainOwner.Calls Kernel (OracleComp Spec) :=
  { receive := fun entry requested context => simulateQ receiveForward (RawCtxChainReceive.execute entry requested context)
    send := fun entry context => simulateQ sendForward (RawCtxChainSend.execute entry context) }

/-- Original outer source admission and publication execute before/after the same primitive requests; only actual public replies reach the adaptive client. -/
noncomputable def compiler {Metadata : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl RawCtxSelectedPublicTrace.SourceSpec (StateT (RawCtxChainOwner.State Kernel Metadata) (OracleComp Spec))
  | .inl request => RawCtxChainOwner.ownerImpl calls sender decode request
  | .inr request => fun state => do
      let reply ← publicForward request
      pure (reply, state)

noncomputable def recorded {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (output : FullOutput) :=
  RawCtxSelectedQueryTrace.recorded (handler (Auxiliary := Auxiliary) source writer output) inputs

/-- Compiled receive requests are the original recorded native receive callbacks. -/
theorem receive_recorded {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (output : FullOutput) :
    recorded (Auxiliary := Auxiliary) source writer output ∘ₛ receiveForward =
      RawCtxSelectedQueryTrace.receiveCalls source writer (RawCtxKdfRequestTable.fullResponse output) := by
  funext query state
  exact congrArg (fun work => work state)
    (_root_.simulateQ_spec_query (recorded source writer output) (.inl query))

/-- Compiled sends retain the same source-selected arguments, optional replies and recorded input bytes. -/
theorem send_recorded {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (output : FullOutput) :
    recorded (Auxiliary := Auxiliary) source writer output ∘ₛ sendForward =
      RawCtxSelectedQueryTrace.sendCalls source writer (RawCtxKdfRequestTable.fullResponse output) := by
  funext query state
  exact congrArg (fun work => work state)
    (_root_.simulateQ_spec_query (recorded source writer output) (.inr (.inl query)))

/-- Compiled public operations are exactly the actual fixed-source public trace with its common cache. -/
theorem public_recorded {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (output : FullOutput) :
    recorded (Auxiliary := Auxiliary) source writer output ∘ₛ publicForward =
      RawCtxSelectedPublicTrace.publicImpl source writer := by
  funext query state
  exact congrArg (fun work => work state)
    (_root_.simulateQ_spec_query (recorded source writer output) (.inr (.inr query)))

noncomputable def nested {Metadata Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (output : FullOutput)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl RawCtxSelectedPublicTrace.SourceSpec
      (StateT (RawCtxChainOwner.State Kernel Metadata)
        (StateT (RawCtxSharedPrimitive.SharedState Auxiliary × List PqxdhSecretInputKdf.RootOutput) ProbComp))
  | .inl request => RawCtxChainOwner.ownerImpl
      (RawCtxSelectedTraceOwner.calls source writer (RawCtxKdfRequestTable.fullResponse output)) sender decode request
  | .inr request => fun state => do
      let reply ← RawCtxSelectedPublicTrace.publicImpl source writer request
      pure (reply, state)

/-- Each source step compiles to the same original full stateful callback execution. -/
theorem step_recorded {Metadata Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (output : FullOutput)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxSelectedPublicTrace.SourceSpec.Domain)
    (state : RawCtxChainOwner.State Kernel Metadata) :
    simulateQ (recorded (Auxiliary := Auxiliary) source writer output) ((compiler sender decode query).run state) =
      (nested source writer output sender decode query).run state := by
  rcases query with (send | raw) | request
  · simp only [compiler, nested, RawCtxChainOwner.ownerImpl, RawCtxChainOwner.sendOwner, StateT.run]
    by_cases empty : send.isEmpty = true
    · simp only [empty, ite_true]
      exact simulateQ_pure _ _
    · simp only [empty, Bool.false_eq_true, ite_false, calls, RawCtxSelectedTraceOwner.calls, bind_pure_comp]
      refine (simulateQ_map _ _ _).trans ?_
      rw [← QueryImpl.simulateQ_compose, send_recorded]
  · simp only [compiler, nested, RawCtxChainOwner.ownerImpl, RawCtxChainOwner.rawReceive, StateT.run]
    by_cases empty : raw.isEmpty = true
    · simp only [empty, ite_true]
      exact simulateQ_pure _ _
    · simp only [empty, Bool.false_eq_true, ite_false]
      cases decoded : decode raw with
      | none => exact simulateQ_pure _ _
      | some frame =>
        by_cases valid : RawCtxReceive.ValidFrame state.expectedSender state.associatedData frame
        · simp only [valid, ite_true]
          simp only [calls, RawCtxSelectedTraceOwner.calls, bind_pure_comp]
          refine (simulateQ_map _ _ _).trans ?_
          rw [← QueryImpl.simulateQ_compose, receive_recorded]
        · simp only [valid, ite_false]
          exact simulateQ_pure _ _
  · simp only [compiler, nested, StateT.run, bind_pure_comp]
    refine (simulateQ_map _ _ _).trans ?_
    exact congrArg (fun work => (fun reply => (reply, state)) <$> work)
      (congrFun (public_recorded source writer output) request)

/-- Flattening preserves exactly the original source/public owner, primitive state and chronological candidate log. -/
theorem nested_flatten {Metadata Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (output : FullOutput)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) :
    (nested (Metadata := Metadata) (Auxiliary := Auxiliary) source writer output sender decode).flattenStateT =
      RawCtxSelectedPublicTrace.sourceImpl source writer (RawCtxKdfRequestTable.fullResponse output) sender decode := by
  funext query state
  cases query with
  | inl request => rfl
  | inr request =>
    simp [nested, QueryImpl.flattenStateT, RawCtxSelectedPublicTrace.sourceImpl,
      StateT.run, StateT.mk]
    change (fun x => (x.1.1, (x.1.2, x.2))) <$>
      ((fun a => (a, state.1)) <$> RawCtxSelectedPublicTrace.publicImpl source writer request).run state.2 =
      (fun a => (a.1, (state.1, a.2))) <$> (RawCtxSelectedPublicTrace.publicImpl source writer request).run state.2
    rw [StateT.run_map, Functor.map_map]

/-- The actual full adaptive owner/public trace is the same compiled primitive program, up to reassociating retained state fields. -/
theorem source_schedule {Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (output : FullOutput)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxSelectedPublicTrace.SourceSpec Result)
    (state : RawCtxSelectedTraceOwner.State Metadata Auxiliary) :
    (simulateQ (recorded source writer output) ((simulateQ (compiler sender decode) client).run state.1)).run state.2 =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (RawCtxSelectedPublicTrace.sourceImpl source writer
          (RawCtxKdfRequestTable.fullResponse output) sender decode) client).run state := by
  have equation : (recorded (Auxiliary := Auxiliary) source writer output).mapStateTBase
      (compiler (Metadata := Metadata) sender decode) = nested source writer output sender decode := by
    funext query owner
    exact step_recorded source writer output sender decode query owner
  have finished := simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (recorded (Auxiliary := Auxiliary) source writer output) (compiler sender decode) client state.1 state.2
  simpa only [equation, nested_flatten] using finished

/-- Only reassociation changes: the complete API result, owner, primitive state and log are retained. -/
def regroup {Metadata Auxiliary Result : Type} :
    ((Result × RawCtxChainOwner.State Kernel Metadata) ×
      (RawCtxSharedPrimitive.SharedState Auxiliary × List PqxdhSecretInputKdf.RootOutput)) →
    Result × RawCtxSelectedTraceOwner.State Metadata Auxiliary :=
  fun result => (result.1.1, (result.1.2, result.2))

/-- The source execution is the exact projection of the same compiled program used by the alias coupling. -/
theorem source_project {Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (output : FullOutput)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxSelectedPublicTrace.SourceSpec Result)
    (state : RawCtxSelectedTraceOwner.State Metadata Auxiliary) :
    regroup <$> (simulateQ (recorded source writer output)
      ((simulateQ (compiler sender decode) client).run state.1)).run state.2 =
    (simulateQ (RawCtxSelectedPublicTrace.sourceImpl source writer
      (RawCtxKdfRequestTable.fullResponse output) sender decode) client).run state := by
  rw [source_schedule, Functor.map_map]
  exact id_map _

noncomputable def consistentGame {Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (output : FullOutput)
    (target : PqxdhSecretInputKdf.RootOutput) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxSelectedPublicTrace.SourceSpec Result)
    (state : RawCtxSelectedChainGame.Context Metadata Auxiliary) :
    ProbComp (Result × RawCtxSelectedTraceOwner.State Metadata Auxiliary) :=
  regroup <$> (simulateQ (RawCtxSelectedQueryTrace.recorded (consistent source writer output target) inputs)
    ((simulateQ (compiler sender decode) client).run state.1)).run (state.2, [])

/-- For the actual same owner/public continuation, enforcing the selected input's aliases costs only its original recorded input event. -/
theorem source_distance {Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (output : FullOutput)
    (target : PqxdhSecretInputKdf.RootOutput) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxSelectedPublicTrace.SourceSpec Result)
    (state : RawCtxSelectedChainGame.Context Metadata Auxiliary) :
    tvDist ((simulateQ (RawCtxSelectedPublicTrace.sourceImpl source writer
        (RawCtxKdfRequestTable.fullResponse output) sender decode) client).run (state.1, (state.2, [])))
      (consistentGame source writer output target sender decode client state) ≤
    Pr{let result ← ((simulateQ (RawCtxSelectedPublicTrace.sourceImpl source writer
        (RawCtxKdfRequestTable.fullResponse output) sender decode) client).run (state.1, (state.2, [])))}[target ∈ result.2.2.2].toReal := by
  have projected := (tvDist_map_le regroup
    ((simulateQ (recorded source writer output) ((simulateQ (compiler sender decode) client).run state.1)).run (state.2, []))
    ((simulateQ (RawCtxSelectedQueryTrace.recorded (consistent source writer output target) inputs)
      ((simulateQ (compiler sender decode) client).run state.1)).run (state.2, []))).trans
    (RawCtxSelectedAliasPrimitives.recorded_distance source writer output target
      ((simulateQ (compiler sender decode) client).run state.1) state.2)
  change tvDist _ _ ≤ Pr{let result ← ((simulateQ (recorded source writer output)
      ((simulateQ (compiler sender decode) client).run state.1)).run (state.2, []))}[target ∈ result.2.2].toReal at projected
  simp only [source_schedule source writer output sender decode client (state.1, (state.2, [])),
    prEvent_map] at projected
  simpa [regroup, Functor.map_map, consistentGame, -evalDist_apply_singleton, -evalDist_apply_setOf,
    -evalDist_apply_univ] using projected

end BeaconcryptCore.Computational.RawCtxSelectedAliasCompiler

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasCompiler.receive_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasCompiler.receive_recorded

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasCompiler.send_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasCompiler.send_recorded

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasCompiler.public_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasCompiler.public_recorded

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasCompiler.step_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasCompiler.step_recorded

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasCompiler.nested_flatten' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasCompiler.nested_flatten

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasCompiler.source_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasCompiler.source_schedule

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasCompiler.source_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasCompiler.source_project

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasCompiler.source_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasCompiler.source_distance
