import BeaconcryptCore.Computational.RawCtxSelectedQueryTrace
import BeaconcryptCore.Computational.RawCtxSelectedChainGame

/-!
The actual complete mixed send/receive source carries a private log of available KDF inputs. Only the log is erased: every optional API reply, complete owner, counters, material slots and shared primitive state survive. Exact source control gives at most S+51R log entries under all adaptive continuations and replies, including repeated and rejected attempts.

The selected random observer retains its entire sampled response and full continued result. In the explicit uniform prior-full76 cut, its actual source trace supplies the candidate allowance internally, without success conditioning or an independently supplied list bound. This remains the specified cut, not a reached-native input-distribution theorem. Public evaluations, live disclosures and consistent alias reconciliation remain dependent work. Snapshots, persistence and restoration are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.RawCtxSelectedTraceOwner
open PqxdhSecretInputKdf RawCtxSelectedChain

noncomputable def calls {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) :
    RawCtxChainOwner.Calls Kernel
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary × List RootOutput) ProbComp) :=
  { receive := fun entry requested context =>
      simulateQ (RawCtxSelectedQueryTrace.receiveCalls source writer challenge)
        (RawCtxChainReceive.execute entry requested context)
    send := fun entry context =>
      simulateQ (RawCtxSelectedQueryTrace.sendCalls source writer challenge)
        (RawCtxChainSend.execute entry context) }

abbrev State (Metadata Auxiliary : Type) :=
  RawCtxChainOwner.State Kernel Metadata ×
    (RawCtxSharedPrimitive.SharedState Auxiliary × List RootOutput)

def erase {Metadata Auxiliary : Type} (state : State Metadata Auxiliary) :=
  (state.1, state.2.1)

private theorem pure_step {Metadata Auxiliary Result : Type}
    (value : Result × RawCtxChainOwner.State Kernel Metadata) (state : State Metadata Auxiliary) :
    Prod.map id erase <$>
      (fun x => (x.1.1, (x.1.2, x.2))) <$>
        (pure value : StateT (RawCtxSharedPrimitive.SharedState Auxiliary × List RootOutput) ProbComp _).run state.2 =
      (fun x => (x.1.1, (x.1.2, x.2))) <$>
        (pure value : StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp _).run state.2.1 := by
  simp only [StateT.run_pure, map_pure, Prod.map_def, id_eq, erase]

private theorem map_step {Metadata Auxiliary Result Value : Type}
    (left : StateT (RawCtxSharedPrimitive.SharedState Auxiliary × List RootOutput) ProbComp Value)
    (right : StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp Value)
    (finish : Value → Result × RawCtxChainOwner.State Kernel Metadata) (state : State Metadata Auxiliary)
    (realized : (Prod.map id Prod.fst) <$> left.run state.2 = right.run state.2.1) :
    Prod.map id erase <$>
      (fun x => (x.1.1, (x.1.2, x.2))) <$> (finish <$> left).run state.2 =
      (fun x => (x.1.1, (x.1.2, x.2))) <$> (finish <$> right).run state.2.1 := by
  have projected := congrArg
    (fun work => (fun x => ((finish x.1).1, ((finish x.1).2, x.2))) <$> work) realized
  simpa only [StateT.run_map, Functor.map_map, Prod.map_def, id_eq, erase, Function.comp_def] using projected

set_option backward.isDefEq.respectTransparency false in
/-- Recording every private source KDF input changes only the added log across each original API step. -/
theorem source_step {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : State Metadata Auxiliary) :
    Prod.map id erase <$>
      (RawCtxChainOwner.sourceImpl (calls source writer challenge) sender decode query).run state =
      (RawCtxChainOwner.sourceImpl (RawCtxSelectedChain.calls source writer challenge) sender decode query).run
        (erase state) := by
  cases query with
  | inl plaintext =>
    simp only [RawCtxChainOwner.sourceImpl, QueryImpl.flattenStateT,
      RawCtxChainOwner.ownerImpl, RawCtxChainOwner.sendOwner, StateT.run, StateT.mk, erase]
    split
    · exact pure_step _ state
    · exact map_step
        ((calls source writer challenge).send state.1.kernel
          ⟨plaintext, state.1.expectedSender, sender, state.1.associatedData⟩)
        ((RawCtxSelectedChain.calls source writer challenge).send state.1.kernel
          ⟨plaintext, state.1.expectedSender, sender, state.1.associatedData⟩)
        (fun result => (result.2, {state.1 with kernel := result.1})) state
        (RawCtxSelectedQueryTrace.send_erase source writer challenge _ _ state.2)
  | inr raw =>
    simp only [RawCtxChainOwner.sourceImpl, QueryImpl.flattenStateT,
      RawCtxChainOwner.ownerImpl, RawCtxChainOwner.rawReceive, StateT.run, StateT.mk, erase]
    split
    · exact pure_step _ state
    · cases decoded : decode raw with
      | none => exact pure_step _ state
      | some frame =>
        dsimp only
        split
        · have lifted := map_step
            ((calls source writer challenge).receive state.1.kernel frame.sequence
              ⟨raw, frame, state.1.associatedData⟩)
            ((RawCtxSelectedChain.calls source writer challenge).receive state.1.kernel frame.sequence
              ⟨raw, frame, state.1.associatedData⟩)
            (RawCtxChainOwner.publish state.1) state
            (RawCtxSelectedQueryTrace.receive_erase source writer challenge _ _ _ state.2)
          exact lifted
        · exact pure_step _ state

/-- The complete adaptive owner erases only its added candidate log; the original optional replies and both full states are retained. -/
theorem source_schedule {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result) (state : State Metadata Auxiliary) :
    Prod.map id erase <$>
      (simulateQ (RawCtxChainOwner.sourceImpl (calls source writer challenge) sender decode) client).run state =
      (simulateQ (RawCtxChainOwner.sourceImpl (RawCtxSelectedChain.calls source writer challenge) sender decode) client).run
        (erase state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ erase (source_step source writer challenge sender decode) client state

/-- In the real selected world the trace projects to the unchanged actual source owner game, including every retry and failed-send advancement. -/
theorem native_schedule {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (target : RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result) (state : State Metadata Auxiliary) :
    (simulateQ (RawCtxMixedOwner.sourceImpl (RawCtxSourceMaterialLabels.nativeImpl source writer) sender decode) client).run
      (RawCtxChainOwner.nativeState (nativeKernel target) state.1, state.2.1) =
      (fun result => (result.1, (RawCtxChainOwner.nativeState (nativeKernel target) result.2.1, result.2.2.1))) <$>
        (simulateQ (RawCtxChainOwner.sourceImpl
          (calls source writer (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest target)))
          sender decode) client).run state := by
  refine (RawCtxSelectedChain.source_schedule source writer target sender decode client (erase state)).trans ?_
  rw [← source_schedule source writer _ sender decode client state, Functor.map_map]
  rfl

private theorem map_length {Metadata Auxiliary Result Value : Type}
    (work : StateT (RawCtxSharedPrimitive.SharedState Auxiliary × List RootOutput) ProbComp Value)
    (finish : Value → Result × RawCtxChainOwner.State Kernel Metadata) (state : State Metadata Auxiliary)
    (budget : Nat)
    (bounded : ∀ reply ∈ support (work.run state.2), reply.2.2.length ≤ state.2.2.length + budget)
    (result : Result × State Metadata Auxiliary)
    (supported : result ∈ support
      ((fun x => (x.1.1, (x.1.2, x.2))) <$> (finish <$> work).run state.2)) :
    result.2.2.2.length ≤ state.2.2.length + budget := by
  simp only [StateT.run_map, Functor.map_map, support_map, Set.mem_image] at supported
  rcases supported with ⟨reply, hreply, rfl⟩
  exact bounded reply hreply

private theorem pure_length {Metadata Auxiliary Result : Type}
    (value : Result × RawCtxChainOwner.State Kernel Metadata) (state : State Metadata Auxiliary)
    (budget : Nat) (result : Result × State Metadata Auxiliary)
    (supported : result ∈ support ((fun x => (x.1.1, (x.1.2, x.2))) <$>
      (pure value : StateT (RawCtxSharedPrimitive.SharedState Auxiliary × List RootOutput) ProbComp _).run state.2)) :
    result.2.2.2.length ≤ state.2.2.length + budget := by
  simp only [StateT.run_pure, map_pure, support_pure, Set.mem_singleton_iff] at supported
  subst result
  exact Nat.le_add_right _ _

/-- Every original source call adds at most one send input or 51 receive inputs, including rejected attempts. -/
theorem source_step_length {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : State Metadata Auxiliary)
    (result : RawCtxMixedOwner.SourceSpec.Range query × State Metadata Auxiliary)
    (supported : result ∈ support
      ((RawCtxChainOwner.sourceImpl (calls source writer challenge) sender decode query).run state)) :
    result.2.2.2.length ≤ state.2.2.length + if query.isLeft = true then 1 else 51 := by
  cases query with
  | inl plaintext =>
    simp only [RawCtxChainOwner.sourceImpl, QueryImpl.flattenStateT,
      RawCtxChainOwner.ownerImpl, RawCtxChainOwner.sendOwner, StateT.run, StateT.mk] at supported
    split at supported
    · exact pure_length _ state 1 result supported
    · exact map_length
        ((calls source writer challenge).send state.1.kernel
          ⟨plaintext, state.1.expectedSender, sender, state.1.associatedData⟩)
        (fun reply => (reply.2, {state.1 with kernel := reply.1})) state 1
        (RawCtxSelectedQueryTrace.send_length source writer challenge _ _ state.2)
        result supported
  | inr raw =>
    simp only [RawCtxChainOwner.sourceImpl, QueryImpl.flattenStateT,
      RawCtxChainOwner.ownerImpl, RawCtxChainOwner.rawReceive, StateT.run, StateT.mk] at supported
    split at supported
    · exact pure_length _ state 51 result supported
    · cases decoded : decode raw with
      | none => exact pure_length _ state 51 result (decoded ▸ supported)
      | some frame =>
        rw [decoded] at supported
        dsimp only at supported
        split at supported
        · exact map_length
            ((calls source writer challenge).receive state.1.kernel frame.sequence
              ⟨raw, frame, state.1.associatedData⟩)
            (RawCtxChainOwner.publish state.1) state 51
            (RawCtxSelectedQueryTrace.receive_length source writer challenge _ _ _ state.2)
            result supported
        · exact pure_length _ state 51 result supported

/-- The same adaptive source execution accumulates at most S+51*R known-input candidates, without a stopping or retry multiplier. -/
theorem source_length {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result) (qSend qRaw : Nat)
    (sendBound : client.IsQueryBoundP (fun query => query.isLeft = true) qSend)
    (rawBound : client.IsQueryBoundP (fun query => query.isRight = true) qRaw)
    (state : State Metadata Auxiliary) (result : Result × State Metadata Auxiliary)
    (supported : result ∈ support
      ((simulateQ (RawCtxChainOwner.sourceImpl (calls source writer challenge) sender decode) client).run state)) :
    result.2.2.2.length ≤ state.2.2.length + qSend + 51*qRaw := by
  induction client using OracleComp.inductionOn generalizing qSend qRaw state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact Nat.le_add_right _ _ |>.trans (Nat.le_add_right _ _)
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at sendBound rawBound
    simp only [simulateQ_bind, simulateQ_spec_query] at supported
    change result ∈ support
      (((RawCtxChainOwner.sourceImpl (calls source writer challenge) sender decode query).run state) >>= fun reply =>
        (simulateQ (RawCtxChainOwner.sourceImpl (calls source writer challenge) sender decode) (next reply.1)).run reply.2) at supported
    rw [mem_support_bind_iff] at supported
    obtain ⟨reply, headSupport, tailSupport⟩ := supported
    have head := source_step_length source writer challenge sender decode query state reply headSupport
    have tail := ih reply.1 _ _ (sendBound.2 reply.1) (rawBound.2 reply.1) reply.2 result tailSupport
    cases query <;> simp only [Sum.isLeft, Sum.isRight, if_true, Bool.false_eq_true, if_false, not_true_eq_false, false_or] at head tail sendBound rawBound <;> omega

open PqxdhFullSecretInputKdf ENNReal

abbrev TraceResult (Result Metadata Auxiliary : Type) := FullOutput × (Result × State Metadata Auxiliary)

def candidates {Result Metadata Auxiliary : Type} (result : TraceResult Result Metadata Auxiliary) : List RootOutput :=
  result.2.2.2.2

/-- The selected random source continuation retains its full sampled response, original result and complete owner/primitive/log state. -/
noncomputable def randomObserver {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (context : RawCtxSelectedChainGame.Context Metadata Auxiliary) : ProbComp (TraceResult Result Metadata Auxiliary) := do
  let output ← $ᵗ FullOutput
  let result ← (simulateQ (RawCtxChainOwner.sourceImpl
    (calls source writer (RawCtxKdfRequestTable.fullResponse output)) sender decode) client).run
      (context.1, (context.2, []))
  pure (output, result)

/-- The actual original send/raw schedule discharges the candidate-list allowance internally. -/
theorem randomObserver_length {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result) (qSend qRaw : Nat)
    (sendBound : client.IsQueryBoundP (fun query => query.isLeft = true) qSend)
    (rawBound : client.IsQueryBoundP (fun query => query.isRight = true) qRaw)
    (context : RawCtxSelectedChainGame.Context Metadata Auxiliary)
    (result : TraceResult Result Metadata Auxiliary)
    (supported : result ∈ support (randomObserver source writer sender decode client context)) :
    (candidates result).length ≤ qSend + 51*qRaw := by
  simp only [randomObserver, mem_support_bind_iff, mem_support_pure_iff] at supported
  rcases supported with ⟨output, _, reply, hreply, rfl⟩
  simpa only [candidates, List.length_nil, Nat.zero_add] using
    source_length source writer (RawCtxKdfRequestTable.fullResponse output) sender decode client
      qSend qRaw sendBound rawBound (context.1, (context.2, [])) reply hreply

/-- In the same explicit full76 cut, the concrete adaptive source trace supplies its own candidate allowance. No success conditioning or independent candidate-list premise is used. -/
theorem stopped_candidates_bound {Prior Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result) (qSend qRaw : Nat)
    (sendBound : client.IsQueryBoundP (fun query => query.isLeft = true) qSend)
    (rawBound : client.IsQueryBoundP (fun query => query.isRight = true) qRaw)
    (sample : ProbComp Prior)
    (stop : Prior → RatchetMaterial → RawCtxSelectedChainGame.Context Metadata Auxiliary) :
    Pr[fun result => result.1 ∈ candidates result.2 |
      RawCtxFreshChainCut.observedCut sample stop (randomObserver source writer sender decode client)] ≤
      ((qSend + 51*qRaw : Nat) : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) :=
  RawCtxSelectedInputCandidates.observed_candidates sample stop
    (randomObserver source writer sender decode client) candidates (qSend + 51*qRaw)
    (randomObserver_length source writer sender decode client qSend qRaw sendBound rawBound)

end BeaconcryptCore.Computational.RawCtxSelectedTraceOwner

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedTraceOwner.source_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedTraceOwner.source_step

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedTraceOwner.source_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedTraceOwner.source_schedule

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedTraceOwner.native_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedTraceOwner.native_schedule

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedTraceOwner.source_step_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedTraceOwner.source_step_length

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedTraceOwner.source_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedTraceOwner.source_length

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedTraceOwner.randomObserver_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedTraceOwner.randomObserver_length

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedTraceOwner.stopped_candidates_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedTraceOwner.stopped_candidates_bound
