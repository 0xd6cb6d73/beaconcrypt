import BeaconcryptCore.Computational.RawCtxSelectedTraceOwner

/-!
Actual public coins, shared-cache commitment queries and every typed fixed-source KDF projection interleave with the selected owner in one complete state. The private candidate log records every known source input and every 32-byte public input, including repetitions, failed source attempts and all projections at the initial/ongoing address. Erasing only that log gives the original selected-source/public interpreter.

The original all-continuation caps give S+51R+K candidates and the explicit uniform full76 cut gives the corresponding unconditioned finite-byte guess bound. Public evaluations stay real. This does not establish a native reached cut, consistent random-table alias routing, or live exposure freshness. All owner/log/context fields remain private protocol or analysis state. Snapshots, persistence and restoration are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedPublicTrace
open PqxdhSecretInputKdf PqxdhJointKdfGame

/-- Every available 32-byte input is retained; other widths cannot equal a selected chain. -/
def bytesCandidate (bytes : Pqxdh.Bytes) : List RootOutput :=
  if length : bytes.length = 32 then [⟨bytes, length⟩] else []

/-- The candidate view keeps all original input bytes, independent of the public projection requested. -/
theorem bytesCandidate_contains (target : RootOutput) : target ∈ bytesCandidate target.toList := by
  simp [bytesCandidate]

set_option backward.isDefEq.respectTransparency false in
/-- Each public call contributes at most one full input, including repeated projection requests. -/
theorem bytesCandidate_length (bytes : Pqxdh.Bytes) : (bytesCandidate bytes).length ≤ 1 := by
  unfold bytesCandidate
  split <;> simp

def inputs : RawCtxServerServices.PublicSpec.Domain → List RootOutput
  | .inr (.inr view) => bytesCandidate view.input
  | _ => []

def isKdf : RawCtxServerServices.PublicSpec.Domain → Prop
  | .inr (.inr _) => True
  | _ => False

instance : DecidablePred isKdf := fun query => by
  rcases query with coin | (hash | view) <;> simp only [isKdf] <;> infer_instance

/-- All same-width public inputs are charged even when a different label makes aliasing impossible. -/
theorem inputs_bound (query : RawCtxServerServices.PublicSpec.Domain) :
    (inputs query).length ≤ if isKdf query then 1 else 0 := by
  rcases query with coin | (hash | view)
  · simp [inputs, isKdf]
  · simp [inputs, isKdf]
  · exact bytesCandidate_length view.input

/-- Every public projection at the selected actual ratchet address records that exact input, including initial-prefix aliases. -/
theorem public_alias (target : RootOutput) (view : JointKdfViewQuery)
    (same : view.address = FixedHkdfDomain.ratchet.address target.toList) :
    target ∈ inputs (.inr (.inr view)) := by
  have input := congrArg PqxdhJointKdf.JointKdfAddress.input same
  change view.input = target.toList at input
  simpa only [inputs, input] using bytesCandidate_contains target

noncomputable def publicImpl {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :=
  RawCtxSelectedQueryTrace.recorded
    (RawCtxProtocolBackend.backend (Auxiliary := Auxiliary) source writer ∘ₛ RawCtxServerServices.publicLift) inputs

/-- The real public function, original typed projection, public coins and same CTX cache are retained after erasing only the input log. -/
theorem public_erase {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (query : RawCtxServerServices.PublicSpec.Domain)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary × List RootOutput) :
    Prod.map id Prod.fst <$> (publicImpl source writer query).run state =
      ((RawCtxProtocolBackend.backend source writer ∘ₛ RawCtxServerServices.publicLift) query).run state.1 :=
  RawCtxSelectedQueryTrace.query_erase _ _ _ _

/-- Public hash/coin effects preserve the input count, while every public KDF call is charged once. -/
theorem public_length {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (query : RawCtxServerServices.PublicSpec.Domain)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary × List RootOutput)
    (result : RawCtxServerServices.PublicSpec.Range query × (RawCtxSharedPrimitive.SharedState Auxiliary × List RootOutput))
    (supported : result ∈ support ((publicImpl source writer query).run state)) :
    result.2.2.length ≤ state.2.length + if isKdf query then 1 else 0 := by
  exact RawCtxSelectedQueryTrace.length_bound _ inputs isKdf inputs_bound
    (RawCtxServerServices.PublicSpec.query query) _ (by by_cases h : isKdf query <;> simp [h]) state result
      (by simpa only [simulateQ_spec_query, publicImpl] using supported)

abbrev SourceSpec := RawCtxMixedOwner.SourceSpec + RawCtxServerServices.PublicSpec

noncomputable def sourceImpl {Metadata Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl SourceSpec (StateT (RawCtxSelectedTraceOwner.State Metadata Auxiliary) ProbComp) :=
  fun query state => match query with
  | .inl request =>
      (RawCtxChainOwner.sourceImpl (RawCtxSelectedTraceOwner.calls source writer challenge) sender decode request).run state
  | .inr request => do
      let result ← (publicImpl source writer request).run state.2
      pure (result.1, (state.1, result.2))

/-- Original private selected-source callbacks and actual public evaluation share one full primitive state. -/
noncomputable def erasedImpl {Metadata Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl SourceSpec (StateT (RawCtxSelectedChainGame.Context Metadata Auxiliary) ProbComp) :=
  fun query state => match query with
  | .inl request =>
      (RawCtxChainOwner.sourceImpl (RawCtxSelectedChain.calls source writer challenge) sender decode request).run state
  | .inr request => do
      let result ← ((RawCtxProtocolBackend.backend source writer ∘ₛ RawCtxServerServices.publicLift) request).run state.2
      pure (result.1, (state.1, result.2))

/-- The full source/public step preserves all original replies and states while adding only its actual input trace. -/
theorem source_step {Metadata Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : SourceSpec.Domain) (state : RawCtxSelectedTraceOwner.State Metadata Auxiliary) :
    Prod.map id RawCtxSelectedTraceOwner.erase <$> (sourceImpl source writer challenge sender decode query).run state =
      (erasedImpl source writer challenge sender decode query).run (RawCtxSelectedTraceOwner.erase state) := by
  cases query with
  | inl request => exact RawCtxSelectedTraceOwner.source_step source writer challenge sender decode request state
  | inr request =>
    have projected := congrArg (fun work => (fun result => (result.1, (state.1, result.2))) <$> work)
      (public_erase source writer request state.2)
    have normalized :
        (fun result => (result.1, (state.1, result.2))) <$>
          ((RawCtxProtocolBackend.backend source writer ∘ₛ RawCtxServerServices.publicLift) request).run state.2.1 =
        (do
          let result ← ((RawCtxProtocolBackend.backend source writer ∘ₛ
            RawCtxServerServices.publicLift) request).run state.2.1
          pure (result.1, (state.1, result.2))) := by
      rw [map_eq_bind_pure_comp]
      simp only [Function.comp_def]
    simpa only [sourceImpl, erasedImpl, StateT.run, bind_pure_comp, Functor.map_map,
      RawCtxSelectedTraceOwner.erase, Prod.map_def, id_eq, Function.comp_def,
      SourceSpec, OracleSpec.Range, OracleSpec.add_def, Sum.elim] using projected.trans normalized

/-- Arbitrary mixed public/record continuations retain their original complete source state after erasing only the candidate log. -/
theorem source_schedule {Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (state : RawCtxSelectedTraceOwner.State Metadata Auxiliary) :
    Prod.map id RawCtxSelectedTraceOwner.erase <$>
      (simulateQ (sourceImpl source writer challenge sender decode) client).run state =
      (simulateQ (erasedImpl source writer challenge sender decode) client).run (RawCtxSelectedTraceOwner.erase state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ RawCtxSelectedTraceOwner.erase
    (source_step source writer challenge sender decode) client state

def cost : SourceSpec.Domain → Nat
  | .inl (.inl _) => 1
  | .inl (.inr _) => 51
  | .inr request => if isKdf request then 1 else 0

/-- The actual source/public step adds only the private derivation allowance or its one public input. -/
theorem source_step_length {Metadata Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : SourceSpec.Domain) (state : RawCtxSelectedTraceOwner.State Metadata Auxiliary)
    (result : SourceSpec.Range query × RawCtxSelectedTraceOwner.State Metadata Auxiliary)
    (supported : result ∈ support ((sourceImpl source writer challenge sender decode query).run state)) :
    result.2.2.2.length ≤ state.2.2.length + cost query := by
  cases query with
  | inl request =>
    have bounded := RawCtxSelectedTraceOwner.source_step_length source writer challenge sender decode request state result supported
    cases request <;> exact bounded
  | inr request =>
    simp only [sourceImpl, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at supported
    rcases supported with ⟨reply, hreply, rfl⟩
    exact public_length source writer request state.2 reply hreply

def IsSend : SourceSpec.Domain → Prop
  | .inl request => request.isLeft = true
  | _ => False

def IsRaw : SourceSpec.Domain → Prop
  | .inl request => request.isRight = true
  | _ => False

def IsPublicKdf : SourceSpec.Domain → Prop
  | .inr request => isKdf request
  | _ => False

instance : DecidablePred IsSend := fun query => by
  rcases query with request | request <;> simp only [IsSend] <;> infer_instance
instance : DecidablePred IsRaw := fun query => by
  rcases query with request | request <;> simp only [IsRaw] <;> infer_instance
instance : DecidablePred IsPublicKdf := fun query => by
  rcases query with request | request <;> simp only [IsPublicKdf] <;> infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Original adaptive send, raw and public-KDF caps derive the complete actual candidate bound S+51R+K. -/
theorem source_length {Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (qSend qRaw qKdf : Nat)
    (sendBound : client.IsQueryBoundP IsSend qSend)
    (rawBound : client.IsQueryBoundP IsRaw qRaw)
    (kdfBound : client.IsQueryBoundP IsPublicKdf qKdf)
    (state : RawCtxSelectedTraceOwner.State Metadata Auxiliary)
    (result : Result × RawCtxSelectedTraceOwner.State Metadata Auxiliary)
    (supported : result ∈ support ((simulateQ (sourceImpl source writer challenge sender decode) client).run state)) :
    result.2.2.2.length ≤ state.2.2.length + qSend + 51*qRaw + qKdf := by
  induction client using OracleComp.inductionOn generalizing qSend qRaw qKdf state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact Nat.le_add_right _ _ |>.trans (Nat.le_add_right _ _) |>.trans (Nat.le_add_right _ _)
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at sendBound rawBound kdfBound
    simp only [simulateQ_bind, simulateQ_spec_query] at supported
    change result ∈ support
      (((sourceImpl source writer challenge sender decode query).run state) >>= fun reply =>
        (simulateQ (sourceImpl source writer challenge sender decode) (next reply.1)).run reply.2) at supported
    rw [mem_support_bind_iff] at supported
    obtain ⟨reply, headSupport, tailSupport⟩ := supported
    have head := source_step_length source writer challenge sender decode query state reply headSupport
    have tail := ih reply.1 _ _ _ (sendBound.2 reply.1) (rawBound.2 reply.1)
      (kdfBound.2 reply.1) reply.2 result tailSupport
    rcases query with (send | raw) | (coin | (hash | view))
    all_goals simp only [IsSend, IsRaw, IsPublicKdf, isKdf, cost, Sum.isLeft, Sum.isRight,
      ite_true, ite_false, Bool.false_eq_true, not_true_eq_false, false_or] at head tail sendBound rawBound kdfBound
    all_goals omega

open PqxdhFullSecretInputKdf ENNReal
set_option maxRecDepth 2048

/-- Public views remain actual fixed-source evaluations in the same complete random-challenge continuation. -/
noncomputable def randomObserver {Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result)
    (context : RawCtxSelectedChainGame.Context Metadata Auxiliary) :
    ProbComp (RawCtxSelectedTraceOwner.TraceResult Result Metadata Auxiliary) := do
  let output ← $ᵗ FullOutput
  let result ← (simulateQ (sourceImpl source writer
    (RawCtxKdfRequestTable.fullResponse output) sender decode) client).run
      (context.1, (context.2, []))
  pure (output, result)

/-- The mixed record/public execution supplies its own candidate allowance with every original attempt retained. -/
theorem randomObserver_length {Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (qSend qRaw qKdf : Nat)
    (sendBound : client.IsQueryBoundP IsSend qSend)
    (rawBound : client.IsQueryBoundP IsRaw qRaw)
    (kdfBound : client.IsQueryBoundP IsPublicKdf qKdf)
    (context : RawCtxSelectedChainGame.Context Metadata Auxiliary)
    (result : RawCtxSelectedTraceOwner.TraceResult Result Metadata Auxiliary)
    (supported : result ∈ support (randomObserver source writer sender decode client context)) :
    (RawCtxSelectedTraceOwner.candidates result).length ≤ qSend + 51*qRaw + qKdf := by
  simp only [randomObserver, mem_support_bind_iff, mem_support_pure_iff] at supported
  rcases supported with ⟨output, _, reply, hreply, rfl⟩
  simpa only [RawCtxSelectedTraceOwner.candidates, List.length_nil, Nat.zero_add] using
    source_length source writer (RawCtxKdfRequestTable.fullResponse output) sender decode client
      qSend qRaw qKdf sendBound rawBound kdfBound (context.1, (context.2, [])) reply hreply

/-- In the explicit full76 cut, all native known-chain and actual public inputs have their unconditioned finite-byte guess bound. -/
theorem stopped_candidates_bound {Prior Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (qSend qRaw qKdf : Nat)
    (sendBound : client.IsQueryBoundP IsSend qSend)
    (rawBound : client.IsQueryBoundP IsRaw qRaw)
    (kdfBound : client.IsQueryBoundP IsPublicKdf qKdf)
    (sample : ProbComp Prior)
    (stop : Prior → RatchetMaterial → RawCtxSelectedChainGame.Context Metadata Auxiliary) :
    Pr{let result ← RawCtxFreshChainCut.observedCut sample stop (randomObserver source writer sender decode client)}[result.1 ∈ RawCtxSelectedTraceOwner.candidates result.2] ≤
      ((qSend + 51*qRaw + qKdf : Nat) : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) :=
  RawCtxSelectedInputCandidates.observed_candidates sample stop
    (randomObserver source writer sender decode client) RawCtxSelectedTraceOwner.candidates
    (qSend + 51*qRaw + qKdf)
    (randomObserver_length source writer sender decode client qSend qRaw qKdf sendBound rawBound kdfBound)

end BeaconcryptCore.Computational.RawCtxSelectedPublicTrace

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPublicTrace.bytesCandidate_contains' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPublicTrace.bytesCandidate_contains

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPublicTrace.bytesCandidate_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPublicTrace.bytesCandidate_length

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPublicTrace.inputs_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPublicTrace.inputs_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPublicTrace.public_alias' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPublicTrace.public_alias

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPublicTrace.public_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPublicTrace.public_erase

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPublicTrace.public_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPublicTrace.public_length

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPublicTrace.source_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPublicTrace.source_step

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPublicTrace.source_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPublicTrace.source_schedule

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPublicTrace.source_step_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPublicTrace.source_step_length

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPublicTrace.source_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPublicTrace.source_length

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPublicTrace.randomObserver_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPublicTrace.randomObserver_length

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPublicTrace.stopped_candidates_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPublicTrace.stopped_candidates_bound
