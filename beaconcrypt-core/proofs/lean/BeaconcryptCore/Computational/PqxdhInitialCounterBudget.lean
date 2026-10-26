import BeaconcryptCore.Computational.PqxdhInitialSourcePublication
import BeaconcryptCore.Computational.RawCtxReceiveSendFields

/-!
The selected initialized sender counter is bounded by the actual chronological private-call count. Repeated cache hits and failed sealing attempts remain counted, while receives preserve the sender fields. This is an operational bound on the source controller, not an inference from the length of a possibly cyclic cached walk.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialCounterBudget
open PqxdhJointKdfGame PqxdhInitialNativeLog
variable {ι M P I D K X Response Shared A N C Result : Type} {extra : OracleSpec ι} {S B : Nat}

private theorem inputs_length (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain)
    (past : List PqxdhJointKdf.JointKdfAddress) :
    past.length ≤ (inputs query past).length ∧ (inputs query past).length ≤ past.length + 1 := by
  cases query with
  | inr query => exact ⟨le_refl _, Nat.le_add_right _ _⟩
  | inl query =>
    unfold inputs RawCtxSelectiveFamilyLog.inputs
    cases found : RawCtxSelectedFamilyContext.queryAddress query <;> simp [found]

/-- Every actual callback preserves its chronological prefix and adds at most one private-input entry. -/
theorem step_length (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (PqxdhInitialBeaconAmbient.Ambient A N C))
    (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain)
    (state : State A N C) (result : (Spec extra RatchetChain I D K X Response Shared S B).Range query × State A N C)
    (supported : result ∈ support ((handler source writer stage external query).run state)) :
    state.1.2.length ≤ result.2.1.2.length ∧ result.2.1.2.length ≤ state.1.2.length + 1 := by
  simp only [handler, StateT.run, bind_pure_comp, support_map, Set.mem_image] at supported
  obtain ⟨reply, reached, rfl⟩ := supported
  exact inputs_length query state.1.2

/-- The complete actual primitive schedule retains all earlier chronological entries. -/
theorem program_mono (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (PqxdhInitialBeaconAmbient.Ambient A N C))
    (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B) Result)
    (state : State A N C) (result : Result × State A N C)
    (supported : result ∈ support ((simulateQ (handler source writer stage external) client).run state)) :
    state.1.2.length ≤ result.2.1.2.length := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact le_refl _
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨reply, head, tail⟩ := supported
    exact (step_length source writer stage external query state reply head).1.trans (ih reply.1 reply.2 result tail)

/-- The literal source all-reply callback allowance bounds its actual chronological private-call growth, including repeated cache hits. -/
theorem program_length (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (PqxdhInitialBeaconAmbient.Ambient A N C))
    (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B) Result)
    (budget : Nat) (bounded : client.IsTotalQueryBound budget)
    (state : State A N C) (result : Result × State A N C)
    (supported : result ∈ support ((simulateQ (handler source writer stage external) client).run state)) :
    result.2.1.2.length ≤ state.1.2.length + budget := by
  induction client using OracleComp.inductionOn generalizing budget state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact Nat.le_add_right _ _
  | query_bind query next ih =>
    rw [isTotalQueryBound_query_bind_iff] at bounded
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨reply, head, tail⟩ := supported
    have first := (step_length source writer stage external query state reply head).2
    have rest := ih reply.1 (budget - 1) (bounded.2 reply.1) reply.2 result tail
    omega

private theorem begin_counter {Chain Material Context : Type}
    (entry : RefinedRatchet Chain Chain Material) (context : Context) :
    match RawCtxChainSend.normalBegin entry context with
    | .exhausted kernel _ => kernel = entry
    | .requested pending => pending.entry = entry ∧
        pending.committed_control.send_sequence.val = entry.control.send_sequence.val + 1 := by
  by_cases full : entry.control.send_sequence = core.num.U64.MAX
  · have begin : RawCtxChainSend.normalBegin entry context = .exhausted entry context := by
      apply RustM.ok.inj
      rw [← RawCtxChainSend.normalBegin_exact]
      simp only [RawCtxChainSend.beginSend, ratchet.control.advance_send_max entry.control full, bind_tc_ok]
    simp only [begin]
  · obtain ⟨advanced, advancedEq, sendEq, receiveEq, cacheEq, sequenceEq, keyEq⟩ :=
      ratchet.control.advance_send_ok entry.control full
    have begin : RawCtxChainSend.normalBegin entry context = .requested {
        entry := entry, context, committed_control := advanced.state, logical := advanced.key,
        sequence := advanced.state.send_sequence, request := entry.send_chain } := by
      apply RustM.ok.inj
      rw [← RawCtxChainSend.normalBegin_exact]
      simp [RawCtxChainSend.beginSend, advancedEq, sequenceEq, keyEq,
        ratchet.control.SendKey.impl.sequence, core.option.Option.Insts.CoreCmpPartialEqOption.eq,
        core.U64.Insts.CoreCmpPartialEqU64, ratchet.control.RatchetState.impl.send_sequence]
    simp only [begin]
    exact ⟨trivial, sendEq⟩

/-- Each executed pending send advances its counter only after the same actual private request has been appended to the source log. -/
theorem send_counter (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (PqxdhInitialBeaconAmbient.Ambient A N C))
    (entry : RawCtxPendingOwnerQueries.Kernel RatchetChain) (context : RawCtxSourceSend.SealContext)
    (state : State A N C) (valid : entry.control.send_sequence.val ≤ state.1.2.length)
    (result : (RawCtxPendingOwnerQueries.Kernel RatchetChain × Option RawCtxSourceSend.Encrypted) × State A N C)
    (supported : result ∈ support ((simulateQ (handler (S := S) (B := B) source writer stage external)
      (PqxdhInitialPendingPost.calls.send entry context)).run state)) :
    result.1.1.control.send_sequence.val ≤ result.2.1.2.length := by
  have begin := begin_counter entry context
  change result ∈ support ((simulateQ (handler source writer stage external)
    (simulateQ PqxdhInitialPendingPost.primitiveForward
      (simulateQ RawCtxPendingOwnerQueries.sendForward
        (RawCtxPendingOwnerQueries.sendProgram (RawCtxChainSend.normalBegin entry context))))).run state) at supported
  cases start : RawCtxChainSend.normalBegin entry context with
  | exhausted kernel saved =>
    simp only [start] at begin
    subst kernel
    simp only [start, RawCtxPendingOwnerQueries.sendProgram, simulateQ_pure,
      StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact valid
  | requested pending =>
    simp only [start] at begin
    simp only [start, RawCtxPendingOwnerQueries.sendProgram, simulateQ_bind, simulateQ_spec_query,
      RawCtxPendingOwnerQueries.sendForward, PqxdhInitialPendingPost.primitiveForward,
      simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at supported
    obtain ⟨reply, first, sealed, second, final⟩ := supported
    subst result
    have logged : reply.2.1.2.length = state.1.2.length + 1 := by
      simp only [handler, StateT.run, bind_pure_comp, support_map, Set.mem_image] at first
      obtain ⟨actual, reached, rfl⟩ := first
      simp [inputs, RawCtxSelectiveFamilyLog.inputs, RawCtxSelectedFamilyContext.queryAddress, RawCtxSelectedFamilyContext.primitiveAddress]
    have monotone := (step_length (S := S) (B := B) source writer stage external
      (.inl (.inl (.inr (.inl (.inr (RawCtxChainSend.ready pending reply.1)))))) reply.2 sealed second).1
    change pending.committed_control.send_sequence.val ≤ sealed.2.1.2.length
    omega

/-- Actual pending receives preserve the sender counter under every supported opening result. -/
theorem receive_counter (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (PqxdhInitialBeaconAmbient.Ambient A N C))
    (entry : RawCtxPendingOwnerQueries.Kernel RatchetChain) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (state : State A N C)
    (result : (RawCtxPendingOwnerQueries.Kernel RatchetChain × core.option.Option RawCtxWholeOwner.Decrypted) × State A N C)
    (supported : result ∈ support ((simulateQ (handler (S := S) (B := B) source writer stage external)
      (PqxdhInitialPendingPost.calls.receive entry target context)).run state)) :
    result.1.1.control.send_sequence = entry.control.send_sequence := by
  have projected : (result.1, result.2.1.1) ∈ support
      ((simulateQ (RawCtxPendingNativeCalls.pending (RawCtxSourceSendPath.native source writer stage)
        (RawCtxPendingSelectiveFamily.backend source writer stage ∘ₛ RawCtxServerServices.publicLift))
          (RawCtxPendingOwnerQueries.calls.receive entry target context)).run state.1.1) := by
    rw [← PqxdhInitialNativePath.primitive_projection source writer stage external _ state, support_map]
    exact ⟨result, supported, rfl⟩
  change (result.1, result.2.1.1) ∈ support
    (((RawCtxGenericOwnerInterpretation.interpretedCalls
      (RawCtxPendingNativeCalls.pending (RawCtxSourceSendPath.native source writer stage)
        (RawCtxPendingSelectiveFamily.backend source writer stage ∘ₛ RawCtxServerServices.publicLift)) RawCtxPendingOwnerQueries.calls).receive entry target context).run state.1.1) at projected
  rw [RawCtxPendingNativeCalls.calls_interpretation] at projected
  have original : ((ConcreteRatchetKernel.mk result.1.1, result.1.2), result.2.1.1) ∈ support
      ((simulateQ (RawCtxSourcePathCalls.receiveImpl source writer stage)
        (RawCtxOwnerOracle.receive ⟨entry⟩ target context)).run state.1.1) := by
    rw [RawCtxSourcePathCalls.receiveImpl, RawCtxGenericNativeCalls.receive_realized, StateT.run_map, support_map]
    exact ⟨(result.1, result.2.1.1), projected, rfl⟩
  exact (RawCtxReceiveSendFields.receive_fields (RawCtxSourcePathCalls.receiveImpl source writer stage)
    state.1.1 ⟨entry⟩ target context _ original).2

noncomputable def calls (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (PqxdhInitialBeaconAmbient.Ambient A N C)) :=
  RawCtxGenericOwnerInterpretation.interpretedCalls (handler (S := S) (B := B) source writer stage external)
    PqxdhInitialPendingPost.calls

/-- The complete actual callbacks discharge sender-counter preservation from chronological source calls, with no supplied callback invariant. -/
theorem rules (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (PqxdhInitialBeaconAmbient.Ambient A N C)) :
    RawCtxFamilyStateInvariant.Rules (calls (S := S) (B := B) source writer stage external)
      (fun before after => before.1.2.length ≤ after.1.2.length)
      (fun kernel state => kernel.control.send_sequence.val ≤ state.1.2.length) where
  refl := fun _ => le_refl _
  trans := fun _ _ _ => Nat.le_trans
  mono := fun _ _ _ grow valid => valid.trans grow
  receive := fun entry target context state result supported => by
    have monotone := program_mono source writer stage external _ state result supported
    refine ⟨monotone, fun valid => ?_⟩
    rw [receive_counter source writer stage external entry target context state result supported]
    exact valid.trans monotone
  send := fun entry context state result supported =>
    ⟨program_mono source writer stage external _ state result supported,
     fun valid => send_counter source writer stage external entry context state valid result supported⟩

/-- The original raw parser, opening and publication preserve the bounded sender counter through every failure branch. -/
theorem raw_counter (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (PqxdhInitialBeaconAmbient.Ambient A N C))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (entry : RawCtxChainOwner.State (RawCtxPendingOwnerQueries.Kernel RatchetChain) M)
    (state : State A N C) (valid : entry.kernel.control.send_sequence.val ≤ state.1.2.length)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxChainOwner.State (RawCtxPendingOwnerQueries.Kernel RatchetChain) M) × State A N C)
    (supported : result ∈ support ((simulateQ (handler (S := S) (B := B) source writer stage external)
      ((RawCtxChainOwner.rawReceive PqxdhInitialPendingPost.calls decode raw).run entry)).run state)) :
    result.1.2.kernel.control.send_sequence.val ≤ result.2.1.2.length := by
  rw [RawCtxGenericOwnerInterpretation.raw_interpretation] at supported
  exact (RawCtxFamilyStateInvariant.raw _ _ _ (rules source writer stage external)
    decode raw entry state result supported).2 valid

end BeaconcryptCore.Computational.PqxdhInitialCounterBudget

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCounterBudget.step_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCounterBudget.step_length

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCounterBudget.program_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCounterBudget.program_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCounterBudget.program_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCounterBudget.program_length

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCounterBudget.send_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCounterBudget.send_counter

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCounterBudget.receive_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCounterBudget.receive_counter

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCounterBudget.rules' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCounterBudget.rules

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCounterBudget.raw_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCounterBudget.raw_counter
