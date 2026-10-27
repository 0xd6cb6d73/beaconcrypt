import BeaconcryptCore.Computational.RawCtxSelectedParentOwner
import BeaconcryptCore.Computational.RawCtxReachedParentSource
import BeaconcryptCore.Computational.RawCtxPendingOwnerQueries
import BeaconcryptCore.Computational.RawCtxGenericOwnerInterpretation

/-!
The original native-chain pending compiler is interpreted by the same retained private KDF lookup, source opening/sealing callbacks and real public services as the native owner experiment. Erasing the added private pending payload keeps each actual request, response and complete callback state. These laws close the compiler-to-native-call interface; the retained table is an explicit intermediate game, with no freshness, uniformity or security premise.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedParentNativeCompiler
open RawCtxChainInterpretation RawCtxSelectedParentEntry RawCtxSelectedParentTable
open PqxdhJointKdfGame PqxdhSecretInputKdf

noncomputable def original {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) :
    QueryImpl (RawCtxPendingOwnerQueries.OriginalSpec RatchetChain)
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl query => RawCtxReachedParentSource.chainView (lookup prior entry target)
      (RawCtxReachedParentSource.sourceOpening source writer) query
  | .inr (.inl (.inl chain)) => pure (RawCtxInterpretedReceive.decodeResponse
      (RawCtxSelectedParentSource.response prior entry target (RawCtxChainSend.nativeRequest chain)))
  | .inr (.inl (.inr pending)) => RawCtxSelectedParentSource.nativeSend source writer prior entry target
      (.inr (RawCtxChainSend.nativeSeal id id pending))
  | .inr (.inr query) => RawCtxSelectedParentOwner.publicImpl source writer query

noncomputable def pending {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) :=
  original (Auxiliary := Auxiliary) source writer prior entry target ∘ₛ RawCtxPendingOwnerQueries.erase

private theorem kernel_id (kernel : RawCtxPendingOwnerQueries.Kernel RatchetChain) :
    mapChains id id kernel = kernel := by
  cases kernel
  rfl

/-- The actual native pending receive call is exactly the retained-table native driver, including all remaining skip/open work. -/
theorem receive_call {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput)
    (kernel : RawCtxPendingOwnerQueries.Kernel RatchetChain) (sequence : Std.U64)
    (context : RawCtxWholeOwner.OpenContext) :
    simulateQ (pending (Auxiliary := Auxiliary) source writer prior entry target)
      (RawCtxPendingOwnerQueries.calls.receive kernel sequence context) =
      (RawCtxSelectedParentCalls.nativeCalls source writer prior entry target).receive kernel sequence context := by
  rw [pending, QueryImpl.simulateQ_compose, RawCtxPendingOwnerQueries.receive_call]
  simp only [RawCtxPendingOwnerQueries.originalCalls, ← QueryImpl.simulateQ_compose,
    RawCtxSelectedParentCalls.nativeCalls, RawCtxChainReceive.execute]
  have receiveHandler : original (Auxiliary := Auxiliary) source writer prior entry target ∘ₛ
      RawCtxPendingOwnerQueries.originalReceive =
      RawCtxReachedParentSource.chainView (lookup prior entry target)
        (RawCtxReachedParentSource.sourceOpening source writer) := by
    funext query
    simp [QueryImpl.compose, original, RawCtxPendingOwnerQueries.originalReceive, OracleSpec.query]
  rw [receiveHandler]
  change simulateQ (RawCtxReachedParentSource.chainView (lookup prior entry target)
    (RawCtxReachedParentSource.sourceOpening source writer))
    (RawCtxChainReceive.program (RawCtxChainReceive.normalBegin kernel sequence context)) = _
  rw [← RawCtxReachedParentSource.view_program, RawCtxReachedParentSource.view_native]
  rw [← RawCtxChainReceive.normalBegin_native, kernel_id]

/-- The original pending send call retains its actual exhaustion, full KDF input, advanced sealing state and optional result. -/
theorem send_call {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput)
    (kernel : RawCtxPendingOwnerQueries.Kernel RatchetChain) (context : RawCtxSourceSend.SealContext) :
    simulateQ (pending (Auxiliary := Auxiliary) source writer prior entry target)
      (RawCtxPendingOwnerQueries.calls.send kernel context) =
      (RawCtxSelectedParentCalls.nativeCalls source writer prior entry target).send kernel context := by
  rw [pending, QueryImpl.simulateQ_compose, RawCtxPendingOwnerQueries.send_call]
  simp only [RawCtxPendingOwnerQueries.originalCalls, ← QueryImpl.simulateQ_compose,
    RawCtxSelectedParentCalls.nativeCalls, RawCtxChainSend.execute]
  have actual := RawCtxChainSend.program_native id id
    (original (Auxiliary := Auxiliary) source writer prior entry target ∘ₛ RawCtxPendingOwnerQueries.originalSend)
    (RawCtxSelectedParentSource.nativeSend source writer prior entry target)
    (fun request => by
      simp [QueryImpl.compose, original, RawCtxPendingOwnerQueries.originalSend, OracleSpec.query,
        RawCtxSelectedParentSource.nativeSend])
    (fun sealing => by
      simp [QueryImpl.compose, original, RawCtxPendingOwnerQueries.originalSend, OracleSpec.query])
    (RawCtxChainSend.normalBegin kernel context)
  have mapped : (fun result : RawCtxPendingOwnerQueries.Kernel RatchetChain × Option RawCtxSourceSend.Encrypted =>
      (mapChains id id result.1, result.2)) = id := by
    funext result
    rw [kernel_id]
    rfl
  rw [mapped] at actual
  simpa only [← RawCtxChainSend.normalBegin_native, kernel_id, Functor.map_id, id_eq] using actual.symm

/-- Interpreting both exact native pending calls gives the concrete source call record, with no compatibility premise. -/
theorem calls_interpretation {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) :
    RawCtxGenericOwnerInterpretation.interpretedCalls (pending (Auxiliary := Auxiliary) source writer prior entry target)
      RawCtxPendingOwnerQueries.calls = RawCtxSelectedParentCalls.nativeCalls source writer prior entry target := by
  exact congrArg₂ RawCtxChainOwner.Calls.mk
    (funext fun kernel => funext fun sequence => funext fun context => receive_call source writer prior entry target kernel sequence context)
    (funext fun kernel => funext fun context => send_call source writer prior entry target kernel context)

/-- Every public callback is the same real source service, preserving its complete shared primitive state. -/
theorem public_interpretation {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) :
    (fun request => simulateQ (pending (Auxiliary := Auxiliary) source writer prior entry target)
      (RawCtxPendingOwnerQueries.publicForward request)) = RawCtxSelectedParentOwner.publicImpl source writer := by
  funext request
  simp [pending, QueryImpl.compose, RawCtxPendingOwnerQueries.publicForward,
    RawCtxPendingOwnerQueries.erase, original, OracleSpec.query]

/-- The exact original native-chain pending frontend interprets to the full native owner/source step. -/
theorem compiler_step {Metadata Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxSelectedPublicTrace.SourceSpec.Domain)
    (state : RawCtxSelectedParentOwner.Owner RatchetChain Metadata) :
    simulateQ (pending (Auxiliary := Auxiliary) source writer prior entry target)
      ((RawCtxPendingOwnerQueries.compiler sender decode query).run state) =
      (RawCtxSelectedParentOwner.nativeOwner source writer prior entry target sender decode query).run state := by
  have actual := RawCtxGenericOwnerInterpretation.public_interpretation
    (pending (Auxiliary := Auxiliary) source writer prior entry target) RawCtxPendingOwnerQueries.calls
    RawCtxPendingOwnerQueries.publicForward sender decode query state
  rw [calls_interpretation, public_interpretation] at actual
  cases query <;> exact actual

/-- The complete original adaptive native pending program equals the same native owner/public execution before projecting any state. -/
theorem compiler_schedule {Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxSelectedPublicTrace.SourceSpec Result)
    (state : RawCtxSelectedParentOwner.Owner RatchetChain Metadata) :
    simulateQ (pending (Auxiliary := Auxiliary) source writer prior entry target)
      ((simulateQ (RawCtxPendingOwnerQueries.compiler sender decode) client).run state) =
      (simulateQ (RawCtxSelectedParentOwner.nativeOwner source writer prior entry target sender decode) client).run state := by
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  exact congrArg (fun handler : QueryImpl RawCtxSelectedPublicTrace.SourceSpec
    (StateT (RawCtxSelectedParentOwner.Owner RatchetChain Metadata)
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)) => (simulateQ handler client).run state)
    (funext fun query => funext fun owner => compiler_step source writer prior entry target sender decode query owner)

/-- Literal full-program equality preserves every selective primitive-query cap with all native and shared state retained. -/
theorem query_bounds {Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxSelectedPublicTrace.SourceSpec Result)
    (state : RawCtxSelectedParentOwner.Owner RatchetChain Metadata)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary)
    (predicate : unifSpec.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    ((simulateQ (pending source writer prior entry target)
      ((simulateQ (RawCtxPendingOwnerQueries.compiler sender decode) client).run state)).run primitive).IsQueryBoundP predicate budget ↔
    (((simulateQ (RawCtxSelectedParentOwner.nativeOwner source writer prior entry target sender decode) client).run state).run primitive).IsQueryBoundP predicate budget := by
  rw [compiler_schedule]

end BeaconcryptCore.Computational.RawCtxSelectedParentNativeCompiler

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentNativeCompiler.receive_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentNativeCompiler.receive_call

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentNativeCompiler.send_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentNativeCompiler.send_call

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentNativeCompiler.calls_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentNativeCompiler.calls_interpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentNativeCompiler.public_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentNativeCompiler.public_interpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentNativeCompiler.compiler_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentNativeCompiler.compiler_step

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentNativeCompiler.compiler_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentNativeCompiler.compiler_schedule

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentNativeCompiler.query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentNativeCompiler.query_bounds
