import BeaconcryptCore.Computational.RawCtxSelectiveChainGame
import BeaconcryptCore.Computational.RawCtxQueryOccurrence

/-!
Two neighboring actual selective native games have the same complete prefix up to the first matched cache miss at the selected logical depth. The scanner saves the original dependent query continuation and the complete reached interpreter state before its callback. The exact adjacent decompositions retain every original source result and state field, including early completion and the entire private table.

At a supported private cut, the earlier stage uses the actual full output and the next stage samples one full output; both then execute the same complete real future backend. Cursor depth never decreases, so later descendants and permitted current-chain reveals are not replaced by additional uniform tables. The actual finite native family instantiates this same common-prefix equality. This is a checked operational splice; the reached source sampler and concrete family native-to-Slot continuation must still establish a target-free Extract/PRF observer. The saved private state and arbitrary saved function are not claimed available to such an observer. No fresh miss, uniform input, source target lineage or small primitive advantage is assumed. Snapshots, persistence and restoration are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix
open PqxdhJointKdf PqxdhJointKdfGame RawCtxSelectiveChainGame RawCtxPendingMixedPrefix

/-- The cut is the actual matched miss at this stage's selected logical depth. -/
def isCut {ι State : Type} {spec : OracleSpec ι} (stage : Nat)
    (query : (spec + JointKdfRO).Domain) (state : State × Store) : Bool :=
  match query with
  | .inl _ => false
  | .inr request => decide (state.2.1 request = none) && matched state.2.2 request && decide (state.2.2.depth = stage)

/-- Both neighboring executions stop at the same state-dependent condition before its private callback. -/
noncomputable def scan {ι State Result : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (cutStage runStage : Nat)
    (other : QueryImpl spec (StateT State ProbComp)) (client : OracleComp (spec + JointKdfRO) Result) :
    State × Store → ProbComp (Prefix (spec + JointKdfRO) Result (State × Store)) :=
  OracleComp.recOn client
    (fun result state => pure (.complete result, state))
    (fun query next recurse state => if isCut cutStage query state then pure (.pending query next, state)
      else do
        let (reply, updated) ← (handler source runStage other query).run state
        recurse reply updated)

/-- The complete client result and reached state survive early completion. -/
theorem scan_pure {ι State Result : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (cutStage runStage : Nat)
    (other : QueryImpl spec (StateT State ProbComp)) (result : Result) (state : State × Store) :
    scan source cutStage runStage other (pure result) state = pure (.complete result, state) := rfl

/-- The first eligible original callback is saved with its complete original continuation. -/
theorem scan_cut {ι State Result : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (cutStage runStage : Nat)
    (other : QueryImpl spec (StateT State ProbComp)) (query : (spec + JointKdfRO).Domain)
    (next : (spec + JointKdfRO).Range query → OracleComp (spec + JointKdfRO) Result) (state : State × Store)
    (chosen : isCut cutStage query state = true) :
    scan source cutStage runStage other ((spec + JointKdfRO).query query >>= next) state =
      pure (.pending query next, state) := by
  change (if isCut cutStage query state then _ else _ : ProbComp _) = _
  rw [chosen]
  rfl

/-- Every preceding query executes with its original optional reply and complete state effect. -/
theorem scan_other {ι State Result : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (cutStage runStage : Nat)
    (other : QueryImpl spec (StateT State ProbComp)) (query : (spec + JointKdfRO).Domain)
    (next : (spec + JointKdfRO).Range query → OracleComp (spec + JointKdfRO) Result) (state : State × Store)
    (chosen : isCut cutStage query state = false) :
    scan source cutStage runStage other ((spec + JointKdfRO).query query >>= next) state =
      (do let (reply, updated) ← (handler source runStage other query).run state
          scan source cutStage runStage other (next reply) updated) := by
  change (if isCut cutStage query state then _ else _ : ProbComp _) = _
  rw [chosen]
  rfl

/-- Before the cut, the two complete stateful interpreters are literally the same operation. -/
theorem handler_same {ι State : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (other : QueryImpl spec (StateT State ProbComp)) (query : (spec + JointKdfRO).Domain)
    (state : State × Store) (unchosen : isCut stage query state = false) :
    (handler source stage other query).run state = (handler source (stage + 1) other query).run state := by
  cases query with
  | inl query => rfl
  | inr request =>
    have absent : ¬ Eligible stage request state.2 := by
      intro eligible
      have chosen : isCut (spec := spec) stage (Sum.inr request : (spec + JointKdfRO).Domain) state = true := by
        simp [isCut, eligible.1, eligible.2.1, eligible.2.2]
      rw [unchosen] at chosen
      cases chosen
    simp only [handler, StateT.run, adjacent_same source stage request state.2 absent]

/-- Completing the actual cut resumes exactly the original complete stateful client. -/
theorem scan_finish {ι State Result : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (cutStage runStage : Nat)
    (other : QueryImpl spec (StateT State ProbComp)) (client : OracleComp (spec + JointKdfRO) Result)
    (state : State × Store) :
    (scan source cutStage runStage other client state >>= finish (handler source runStage other)) =
      (simulateQ (handler source runStage other) client).run state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure result => rfl
  | query_bind query next ih =>
    cases chosen : isCut cutStage query state with
    | true => rw [scan_cut source cutStage runStage other query next state chosen]; rfl
    | false =>
      simp only [scan_other source cutStage runStage other query next state chosen, bind_assoc, ih,
        simulateQ_query_bind, StateT.run_bind]
      rfl

/-- The entire prefix before the selected miss is identical in both neighboring native stages. -/
theorem scan_same {ι State Result : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (other : QueryImpl spec (StateT State ProbComp)) (client : OracleComp (spec + JointKdfRO) Result)
    (state : State × Store) :
    scan source stage stage other client state = scan source stage (stage + 1) other client state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure result => rfl
  | query_bind query next ih =>
    cases chosen : isCut stage query state with
    | true => rw [scan_cut source stage stage other query next state chosen,
        scan_cut source stage (stage + 1) other query next state chosen]
    | false =>
      rw [scan_other source stage stage other query next state chosen,
        scan_other source stage (stage + 1) other query next state chosen,
        handler_same source stage other query state chosen]
      apply bind_congr
      intro reply
      exact ih reply.1 reply.2

/-- Both complete neighboring stages use the same actual reached prefix, followed by their complete original resumed programs. -/
theorem adjacent_complete {ι State Result : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (other : QueryImpl spec (StateT State ProbComp)) (client : OracleComp (spec + JointKdfRO) Result)
    (state : State × Store) :
    (scan source stage stage other client state >>= finish (handler source stage other)) =
      (simulateQ (handler source stage other) client).run state ∧
    (scan source stage stage other client state >>= finish (handler source (stage + 1) other)) =
      (simulateQ (handler source (stage + 1) other) client).run state := by
  refine ⟨scan_finish source stage stage other client state, ?_⟩
  rw [scan_same, scan_finish]

/-- A supported cut is an eligible callback of the actual original program, with its same dependent continuation and reached state. -/
theorem pending_origin {ι State Result : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (cutStage runStage : Nat)
    (other : QueryImpl spec (StateT State ProbComp)) (client : OracleComp (spec + JointKdfRO) Result)
    (state reached : State × Store) (target : (spec + JointKdfRO).Domain)
    (continuation : (spec + JointKdfRO).Range target → OracleComp (spec + JointKdfRO) Result)
    (supported : (Stopped.pending target continuation, reached) ∈ support (scan source cutStage runStage other client state)) :
    isCut cutStage target reached = true ∧ RawCtxQueryOccurrence.Occurs target continuation client := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value =>
    simp only [scan_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
    cases supported.1
  | query_bind query next ih =>
    cases chosen : isCut cutStage query state with
    | true =>
      simp only [scan_cut source cutStage runStage other query next state chosen,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
      cases supported.1
      rw [supported.2]
      exact ⟨chosen, RawCtxQueryOccurrence.here _ _⟩
    | false =>
      simp only [scan_other source cutStage runStage other query next state chosen,
        support_bind, Set.mem_iUnion] at supported
      rcases supported with ⟨reply, _, supported⟩
      have tail := ih reply.1 reply.2 supported
      exact ⟨tail.1, RawCtxQueryOccurrence.later target query continuation next reply.1 tail.2⟩

/-- Every actual backend step preserves or increases the cursor depth, including failed operations and cache hits. -/
theorem handler_monotone {ι State : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (other : QueryImpl spec (StateT State ProbComp)) (query : (spec + JointKdfRO).Domain)
    (state : State × Store) (result : (spec + JointKdfRO).Range query × (State × Store))
    (supported : result ∈ support ((handler source stage other query).run state)) :
    state.2.2.depth ≤ result.2.2.2.depth := by
  cases query with
  | inl query =>
    simp only [handler, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at supported
    rcases supported with ⟨reply, _, rfl⟩
    exact Nat.le_refl _
  | inr request =>
    simp only [handler, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at supported
    rcases supported with ⟨reply, selected, rfl⟩
    have actual := private_state source stage request state.2 reply selected
    change state.2.2.depth ≤ reply.2.2.depth
    rw [actual, advance_depth]
    exact Nat.le_add_right _ _

/-- Once its selected prefix is past, the stage uses the real memoized backend for every future callback. -/
theorem saturated_step {ι State : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (other : QueryImpl spec (StateT State ProbComp)) (query : (spec + JointKdfRO).Domain)
    (state : State × Store) (past : stage ≤ state.2.2.depth) :
    (handler source stage other query).run state = (handler source 0 other query).run state := by
  cases query with
  | inl query => rfl
  | inr request =>
    have same : privateStep source stage request state.2 = privateStep source 0 request state.2 := by
      cases found : state.2.1 request with
      | some output => rw [private_hit source stage request state.2 output found,
          private_hit source 0 request state.2 output found]
      | none => rw [private_real source stage request state.2 found (Or.inr past),
          private_real source 0 request state.2 found (Or.inr (Nat.zero_le _))]
    simp only [handler, StateT.run, same]

/-- Every complete continuation after the selected prefix keeps all future derivations real, including later current-chain reveals and descendants. -/
theorem saturated_run {ι State Result : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (other : QueryImpl spec (StateT State ProbComp)) (client : OracleComp (spec + JointKdfRO) Result)
    (state : State × Store) (past : stage ≤ state.2.2.depth) :
    (simulateQ (handler source stage other) client).run state =
      (simulateQ (handler source 0 other) client).run state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure result => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [saturated_step source stage other query state past]
    apply bind_congr_of_forall_mem_support
    intro reply supported
    exact ih reply.1 reply.2 (past.trans (handler_monotone source 0 other query state reply supported))

/-- The Boolean private cut test is exactly the stated source cache/match/depth event. -/
theorem private_isCut {ι State : Type} (spec : OracleSpec ι) (stage : Nat)
    (request : JointKdfAddress) (state : State × Store) :
    isCut (spec := spec) stage (.inr request) state = true ↔ Eligible stage request state.2 := by
  simp [isCut, Eligible, and_assoc]

noncomputable def resume {ι State Result : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (other : QueryImpl spec (StateT State ProbComp))
    (request : JointKdfAddress)
    (next : PqxdhFullSecretInputKdf.FullOutput → OracleComp (spec + JointKdfRO) Result)
    (state : State × Store) (output : PqxdhFullSecretInputKdf.FullOutput) :=
  (simulateQ (handler source 0 other) (next output)).run
    (state.1, (state.2.1.cacheQuery request output, advance state.2.2 request output))

/-- At the actual selected cut, the real stage resumes the original full future program through the unchanged real backend. -/
theorem finish_real {ι State Result : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (other : QueryImpl spec (StateT State ProbComp)) (request : JointKdfAddress)
    (next : PqxdhFullSecretInputKdf.FullOutput → OracleComp (spec + JointKdfRO) Result)
    (state : State × Store) (eligible : Eligible stage request state.2) :
    finish (handler source stage other) (Stopped.pending (.inr request) next, state) =
      resume source other request next state (productionStream source.crypto request) := by
  have depth := eligible.2.2
  simp only [finish, handler, StateT.run,
    private_real source stage request state.2 eligible.1 (Or.inr (by omega)), pure_bind]
  exact saturated_run source stage other _ _ (by simp [advance, eligible.2.1, depth])

/-- The neighboring stage draws one full child and runs the same complete real future continuation, retaining its next-chain descendants. -/
theorem finish_random {ι State Result : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (other : QueryImpl spec (StateT State ProbComp)) (request : JointKdfAddress)
    (next : PqxdhFullSecretInputKdf.FullOutput → OracleComp (spec + JointKdfRO) Result)
    (state : State × Store) (eligible : Eligible stage request state.2) :
    finish (handler source (stage + 1) other) (Stopped.pending (.inr request) next, state) =
      ($ᵗ PqxdhFullSecretInputKdf.FullOutput) >>= resume source other request next state := by
  have depth := eligible.2.2
  simp only [finish, handler, StateT.run,
    private_selected source (stage + 1) request state.2 eligible.1 eligible.2.1 (by omega),
    bind_map_left, bind_assoc, pure_bind]
  apply bind_congr
  intro output
  exact saturated_run source (stage + 1) other _ _ (by simp [advance, eligible.2.1, depth])

/-- The actual finite native family has one common reached prefix for each adjacent stage, retaining its original complete role/reveal continuation. -/
theorem family_adjacent {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) (store : Store) :
    let common := scan source stage stage (RawCtxProtocolBackend.backend source writer)
      (RawCtxSelectiveKdfFamily.program serverCount beaconCount senderId route decode client state) (primitive, store)
    family source writer stage serverCount beaconCount senderId route decode client state primitive store =
      (common >>= finish (handler source stage (RawCtxProtocolBackend.backend source writer))) ∧
    family source writer (stage + 1) serverCount beaconCount senderId route decode client state primitive store =
      (common >>= finish (handler source (stage + 1) (RawCtxProtocolBackend.backend source writer))) := by
  have complete := adjacent_complete source stage (RawCtxProtocolBackend.backend source writer)
    (RawCtxSelectiveKdfFamily.program serverCount beaconCount senderId route decode client state) (primitive, store)
  exact ⟨complete.1.symm, complete.2.symm⟩

end BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.scan_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.scan_pure

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.scan_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.scan_cut

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.scan_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.scan_other

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.handler_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.handler_same

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.scan_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.scan_finish

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.scan_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.scan_same

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.adjacent_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.adjacent_complete

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.pending_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.pending_origin

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.handler_monotone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.handler_monotone

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.saturated_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.saturated_step

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.saturated_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.saturated_run

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.private_isCut' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.private_isCut

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.finish_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.finish_real

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.finish_random' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.finish_random

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.family_adjacent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix.family_adjacent
