import BeaconcryptCore.Computational.RawCtxSelectiveChainBudgets

/-!
The actual private-only finite-family compiler supplies S+51R possible private KDF calls, including cache hits, failed operations and all adaptive continuations. Every callback preserves or advances the selected cursor, with at most one advance per private call and none for public evaluations or other backend operations. Complete executions therefore stay below their original depth plus S+51R. A supported selected stop is strictly before that bound because its unexecuted private query remains charged.

Starting the cursor at zero gives a proved finite bound for selected hybrid stages. This is cursor-stage coverage; it does not by itself equate an arbitrary native entry counter with zero or identify an accepted record with that cursor. Actual initialization, direction/record provenance and final target selection consume those separate source correspondences. No fresh-miss, honesty, success, uniformity or cryptographic premise is added, and no probability or cost is transported across distribution equality.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectiveChainDepth
open PqxdhJointKdf PqxdhJointKdfGame RawCtxSelectiveChainGame RawCtxServerServiceBounds

/-- Each supported original callback advances the cursor at most once; public and other native callbacks cannot advance it. -/
theorem step {ι State : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (other : QueryImpl spec (StateT State ProbComp)) (query : (spec + JointKdfRO).Domain)
    (state : State × Store) (result : (spec + JointKdfRO).Range query × (State × Store))
    (supported : result ∈ support ((handler source stage other query).run state)) :
    state.2.2.depth ≤ result.2.2.2.depth ∧
      result.2.2.2.depth ≤ state.2.2.depth + (if query.isRight then 1 else 0) := by
  cases query with
  | inl query =>
      simp only [handler, StateT.run, bind_pure_comp, support_map, Set.mem_image] at supported
      rcases supported with ⟨reply, _, rfl⟩
      simp
  | inr request =>
      simp only [handler, StateT.run, bind_pure_comp, support_map, Set.mem_image] at supported
      rcases supported with ⟨reply, replySupport, rfl⟩
      rw [private_state source stage request state.2 reply replySupport]
      simp only [advance_depth, Sum.isRight_inr, if_true]
      split_ifs <;> omega

/-- Every complete adaptive schedule preserves prior depth and spends at most its all-reply private-query cap, including cache hits. -/
theorem complete {ι State Result : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (other : QueryImpl spec (StateT State ProbComp))
    (client : OracleComp (spec + JointKdfRO) Result) (budget : Nat)
    (bounded : client.IsQueryBoundP (fun query => query.isRight = true) budget)
    (state : State × Store) (result : Result × (State × Store))
    (supported : result ∈ support ((simulateQ (handler source stage other) client).run state)) :
    state.2.2.depth ≤ result.2.2.2.depth ∧ result.2.2.2.depth ≤ state.2.2.depth + budget := by
  induction client using OracleComp.inductionOn generalizing budget state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨Nat.le_refl _, Nat.le_add_right _ _⟩
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query] at supported
      change result ∈ support (((handler source stage other query).run state) >>= fun reply =>
        (simulateQ (handler source stage other) (next reply.1)).run reply.2) at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨reply, replySupport, tailSupport⟩ := supported
      have head := step source stage other query state reply replySupport
      have tail := ih reply.1 _ (bounded.2 reply.1) reply.2 result tailSupport
      have available := bounded.1
      by_cases chosen : query.isRight = true
      all_goals simp [chosen] at head tail available
      all_goals omega

/-- Private-only compilation preserves the original native KDF cap; public HKDF evaluations do not enter it. -/
theorem compiled_private {Result : Type}
    (client : OracleComp RawCtxServerServices.BackendSpec Result) (budget : Nat)
    (bounded : client.IsQueryBoundP (nativePredicate .kdf) budget) :
    (simulateQ RawCtxSelectiveKdfFamily.compiler client).IsQueryBoundP (fun query => query.isRight = true) budget := by
  refine RawCtxSourceOpen.simulate_bound RawCtxSelectiveKdfFamily.compiler
    (nativePredicate .kdf) (fun query => query.isRight = true) client budget bounded ?_
  intro query
  rcases query with coin | ((request | request) | view)
  all_goals simp only [RawCtxSelectiveKdfFamily.compiler, isQueryBoundP_map_iff]
  all_goals apply (isQueryBoundP_query_iff _ _ _).mpr
  all_goals simp [nativePredicate, RawCtxMixedOwner.callKind]

/-- The actual finite-family source supplies S+51R private calls under every possible callback continuation. -/
theorem source_private {Metadata PeerMetadata Identity DhPair KemPair Result : Type}
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    (RawCtxSelectiveKdfFamily.program serverCount beaconCount senderId route decode client state).IsQueryBoundP
      (fun query => query.isRight = true) (budget.1 .send + 51 * budget.1 .raw) := by
  apply compiled_private
  simpa [RawCtxMixedOwner.sendCost, RawCtxMixedOwner.receiveCost] using
    RawCtxRevealBudgets.backend_bound serverCount beaconCount senderId route decode client budget bounded state .kdf

/-- A supported selected stop occurs strictly before the original private-call cap, with its unexecuted callback still charged. -/
theorem pending {ι State Result : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (cutStage runStage : Nat)
    (other : QueryImpl spec (StateT State ProbComp))
    (client : OracleComp (spec + JointKdfRO) Result) (budget : Nat)
    (bounded : client.IsQueryBoundP (fun query => query.isRight = true) budget)
    (state reached : State × Store) (query : (spec + JointKdfRO).Domain)
    (next : (spec + JointKdfRO).Range query → OracleComp (spec + JointKdfRO) Result)
    (supported : (RawCtxPendingMixedPrefix.Stopped.pending query next, reached) ∈ support
      (RawCtxSelectiveChainPrefix.scan source cutStage runStage other client state)) :
    state.2.2.depth ≤ reached.2.2.depth ∧ reached.2.2.depth < state.2.2.depth + budget := by
  induction client using OracleComp.inductionOn generalizing budget state reached query next with
  | pure value =>
      simp only [RawCtxSelectiveChainPrefix.scan_pure, mem_support_pure_iff] at supported
      cases supported
  | query_bind request outside ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      cases chosen : RawCtxSelectiveChainPrefix.isCut cutStage request state with
      | true =>
          rw [RawCtxSelectiveChainPrefix.scan_cut source cutStage runStage other request outside state chosen,
            mem_support_pure_iff] at supported
          have sameState := congrArg Prod.snd supported
          change reached = state at sameState
          subst reached
          have isPrivate : request.isRight = true := by
            cases request with
            | inl original => cases chosen
            | inr original => rfl
          have available := bounded.1
          simp [isPrivate] at available
          exact ⟨Nat.le_refl _, by omega⟩
      | false =>
          rw [RawCtxSelectiveChainPrefix.scan_other source cutStage runStage other request outside state chosen,
            mem_support_bind_iff] at supported
          obtain ⟨reply, replySupport, tailSupport⟩ := supported
          have head := step source runStage other request state reply replySupport
          have tail := ih reply.1 _ (bounded.2 reply.1) reply.2 reached query next tailSupport
          have available := bounded.1
          by_cases isPrivate : request.isRight = true
          all_goals simp [isPrivate] at head tail available
          all_goals omega

/-- Every supported actual family execution stays within the source-derived private-call depth cap. -/
theorem family_depth {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) (store : Store)
    (result : (Result × RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) ×
      (RawCtxSharedPrimitive.SharedState Auxiliary × Store))
    (supported : result ∈ support (family source writer stage serverCount beaconCount senderId route decode client state primitive store)) :
    store.2.depth ≤ result.2.2.2.depth ∧
      result.2.2.2.depth ≤ store.2.depth + (budget.1 .send + 51 * budget.1 .raw) :=
  complete source stage (RawCtxProtocolBackend.backend source writer) _ _
    (source_private serverCount beaconCount senderId route decode client budget bounded state)
    (primitive, store) result supported

/-- Starting at logical depth zero, every supported selected cut has a stage index in the finite source private-call catalogue. -/
theorem stage_lt {ι State Result : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (cutStage runStage : Nat)
    (other : QueryImpl spec (StateT State ProbComp))
    (client : OracleComp (spec + JointKdfRO) Result) (budget : Nat)
    (bounded : client.IsQueryBoundP (fun query => query.isRight = true) budget)
    (state reached : State × Store) (zero : state.2.2.depth = 0)
    (query : (spec + JointKdfRO).Domain)
    (next : (spec + JointKdfRO).Range query → OracleComp (spec + JointKdfRO) Result)
    (supported : (RawCtxPendingMixedPrefix.Stopped.pending query next, reached) ∈ support
      (RawCtxSelectiveChainPrefix.scan source cutStage runStage other client state)) :
    cutStage < budget := by
  have cap := (pending source cutStage runStage other client budget bounded state reached query next supported).2
  have chosen := (RawCtxSelectiveChainPrefix.pending_origin source cutStage runStage other client state reached query next supported).1
  have depth : reached.2.2.depth = cutStage := by
    cases query with
    | inl original => cases chosen
    | inr request => exact ((RawCtxSelectiveChainPrefix.private_isCut spec cutStage request reached).mp chosen).2.2
  omega

/-- The original finite-family source instantiates the strict stage cap S+51R without an opaque protocol budget or fresh-miss premise. -/
theorem family_stage_lt {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (cutStage runStage : Nat)
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) (store : Store) (zero : store.2.depth = 0)
    (reached : RawCtxSharedPrimitive.SharedState Auxiliary × Store)
    (query : RawCtxSelectiveKdfFamily.FamilySpec.Domain)
    (next : RawCtxSelectiveKdfFamily.FamilySpec.Range query → OracleComp RawCtxSelectiveKdfFamily.FamilySpec
      (Result × RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount))
    (supported : (RawCtxPendingMixedPrefix.Stopped.pending query next, reached) ∈ support
      (RawCtxSelectiveChainPrefix.scan source cutStage runStage (RawCtxProtocolBackend.backend source writer)
        (RawCtxSelectiveKdfFamily.program serverCount beaconCount senderId route decode client state) (primitive, store))) :
    cutStage < budget.1 .send + 51 * budget.1 .raw :=
  stage_lt source cutStage runStage (RawCtxProtocolBackend.backend source writer) _ _
    (source_private serverCount beaconCount senderId route decode client budget bounded state)
    (primitive, store) reached zero query next supported

end BeaconcryptCore.Computational.RawCtxSelectiveChainDepth

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainDepth.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainDepth.step

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainDepth.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainDepth.complete

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainDepth.compiled_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainDepth.compiled_private

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainDepth.source_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainDepth.source_private

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainDepth.pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainDepth.pending

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainDepth.family_depth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainDepth.family_depth

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainDepth.stage_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainDepth.stage_lt

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainDepth.family_stage_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainDepth.family_stage_lt
