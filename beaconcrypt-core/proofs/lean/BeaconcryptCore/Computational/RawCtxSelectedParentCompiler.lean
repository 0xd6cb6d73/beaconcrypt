import BeaconcryptCore.Computational.RawCtxSelectedParentLiveSource
import BeaconcryptCore.Computational.RawCtxGenericOwnerInterpretation
import BeaconcryptCore.Computational.RawCtxPendingLiveTails

/-!
The actual private pending owner/live compiler executes the same retained-parent source calls and real public backend. Its full source query, original optional response and owner/history state are retained through interpretation. The compiler has no target-byte argument; target bytes occur only in the mathematical native reader and representation used for the source equation. No arbitrary continuation compatibility premise is introduced.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedParentCompiler
open RawCtxSelectedParentCalls RawCtxSelectedParentOwner RawCtxSelectedParentEntry RawCtxSelectedParentTable RawCtxSelectedChain
open PqxdhJointKdfGame PqxdhSecretInputKdf

noncomputable def original {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (response : RatchetKdfResponse) :
    QueryImpl (RawCtxPendingOwnerQueries.OriginalSpec Slot)
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl query => RawCtxSelectedParentSource.labelReceive source writer prior entry response query
  | .inr (.inl query) => RawCtxSelectedParentSource.labelSend source writer prior entry response query
  | .inr (.inr query) => publicImpl source writer query

noncomputable def pending {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (response : RatchetKdfResponse) :=
  original (Auxiliary := Auxiliary) source writer prior entry response ∘ₛ RawCtxPendingOwnerQueries.erase

/-- The exact original receive and send source programs interpret to the retained-parent calls, before owner publication. -/
theorem calls_interpreted {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (response : RatchetKdfResponse) :
    RawCtxGenericOwnerInterpretation.interpretedCalls (original (Auxiliary := Auxiliary) source writer prior entry response)
      RawCtxPendingOwnerQueries.originalCalls = labelCalls source writer prior entry response := by
  have receive : original (Auxiliary := Auxiliary) source writer prior entry response ∘ₛ
      RawCtxPendingOwnerQueries.originalReceive = RawCtxSelectedParentSource.labelReceive source writer prior entry response := by
    funext query
    exact simulateQ_spec_query _ _
  have send : original (Auxiliary := Auxiliary) source writer prior entry response ∘ₛ
      RawCtxPendingOwnerQueries.originalSend = RawCtxSelectedParentSource.labelSend source writer prior entry response := by
    funext query
    exact simulateQ_spec_query _ _
  simp only [RawCtxGenericOwnerInterpretation.interpretedCalls, RawCtxPendingOwnerQueries.originalCalls,
    ← QueryImpl.simulateQ_compose, receive, send, labelCalls]

/-- The same actual original public/record compiler runs the retained source calls with every owner field and public effect intact. -/
theorem original_step {Metadata Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (response : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxSelectedPublicTrace.SourceSpec.Domain) (state : Owner Slot Metadata) :
    simulateQ (original (Auxiliary := Auxiliary) source writer prior entry response)
      ((RawCtxPendingOwnerQueries.originalCompiler sender decode query).run state) =
      (labelOwner source writer prior entry response sender decode query).run state := by
  have publicEquation : (fun request => simulateQ (original (Auxiliary := Auxiliary) source writer prior entry response)
      (RawCtxPendingOwnerQueries.originalPublic request)) = publicImpl source writer := by
    funext query
    exact simulateQ_spec_query _ _
  have equation := RawCtxGenericOwnerInterpretation.public_interpretation
    (original (Auxiliary := Auxiliary) source writer prior entry response) RawCtxPendingOwnerQueries.originalCalls
    RawCtxPendingOwnerQueries.originalPublic sender decode query state
  rw [calls_interpreted, publicEquation] at equation
  cases query <;> exact equation

/-- The full private pending payload is instrumentation; its actual source compiler interprets to the same retained owner/public step. -/
theorem pending_step {Metadata Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (response : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxSelectedPublicTrace.SourceSpec.Domain) (state : Owner Slot Metadata) :
    simulateQ (pending (Auxiliary := Auxiliary) source writer prior entry response)
      ((RawCtxPendingOwnerQueries.compiler sender decode query).run state) =
      (labelOwner source writer prior entry response sender decode query).run state := by
  rw [pending, QueryImpl.simulateQ_compose, RawCtxPendingOwnerQueries.step_erase, original_step]

/-- Every original adaptive owner/public client is interpreted with the same full owner and primitive state. -/
theorem owner_program {Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (response : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxSelectedPublicTrace.SourceSpec Result) (state : Owner Slot Metadata) :
    simulateQ (pending (Auxiliary := Auxiliary) source writer prior entry response)
      ((simulateQ (RawCtxPendingOwnerQueries.compiler sender decode) client).run state) =
      (simulateQ (labelOwner source writer prior entry response sender decode) client).run state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [pending_step]
    exact bind_congr fun result => ih result.1 result.2

noncomputable def live {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (response : RatchetKdfResponse) (reader : RawCtxGenericLiveRead.Reader Slot) :=
  RawCtxGenericLiveRead.handler (pending (Auxiliary := Auxiliary) source writer prior entry response) reader

/-- The actual full live frontend runs the same pending owner source computation or original live lookup before its precise history update. -/
theorem live_step {Metadata Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (response : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) (reader : RawCtxGenericLiveRead.Reader Slot)
    (query : RawCtxSelectedLiveTrace.SourceSpec.Domain)
    (state : RawCtxSelectedParentLiveSource.LabelState Metadata serverCount beaconCount) :
    simulateQ (live (Auxiliary := Auxiliary) source writer prior entry response reader)
      ((RawCtxGenericLiveRead.compiler RawCtxSelectedLiveRead.exposed sender decode owner query).run state) =
      (RawCtxSelectedParentLiveSource.labelImpl source writer prior entry response sender decode owner reader query).run state := by
  cases query with
  | inl request =>
    rw [live, RawCtxGenericLiveRead.original_step, pending_step]
    rfl
  | inr read =>
    rw [live, RawCtxGenericLiveRead.read_step]
    rfl

/-- The same complete original live client has no separately supplied continuation law: the actual compiled program realizes the retained interpreter directly. -/
theorem live_program {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (response : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) (reader : RawCtxGenericLiveRead.Reader Slot)
    (client : OracleComp RawCtxSelectedLiveTrace.SourceSpec Result)
    (state : RawCtxSelectedParentLiveSource.LabelState Metadata serverCount beaconCount) :
    simulateQ (live (Auxiliary := Auxiliary) source writer prior entry response reader)
      (RawCtxPendingLiveTails.program RawCtxSelectedLiveRead.exposed sender decode owner client state) =
      (simulateQ (RawCtxSelectedParentLiveSource.labelImpl source writer prior entry response sender decode owner reader) client).run state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => simp only [RawCtxPendingLiveTails.program, simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
    simp only [RawCtxPendingLiveTails.program, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [live_step]
    exact bind_congr fun result => ih result.1 result.2

/-- The native retained-table continuation equals interpretation of the original complete live compiler, retaining all source state except its added exposure ghost. -/
theorem native_program {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (client : OracleComp RawCtxSelectedLiveTrace.SourceSpec Result)
    (state : RawCtxSelectedParentLiveSource.LabelState Metadata serverCount beaconCount) :
    (simulateQ (RawCtxSelectedParentLiveSource.nativeImpl (Auxiliary := Auxiliary) source writer prior entry target sender decode owner) client).run
      (RawCtxSelectedParentLiveSource.project target state) =
      Prod.map id (RawCtxSelectedParentLiveSource.project target) <$>
        simulateQ (live source writer prior entry (childResponse prior entry target)
          (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)))
          (RawCtxPendingLiveTails.program RawCtxSelectedLiveRead.exposed sender decode owner client state) := by
  rw [live_program, RawCtxSelectedParentLiveSource.schedule_map]

end BeaconcryptCore.Computational.RawCtxSelectedParentCompiler

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentCompiler.calls_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentCompiler.calls_interpreted

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentCompiler.original_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentCompiler.original_step

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentCompiler.pending_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentCompiler.pending_step

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentCompiler.owner_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentCompiler.owner_program

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentCompiler.live_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentCompiler.live_step

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentCompiler.live_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentCompiler.live_program

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentCompiler.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentCompiler.native_program
