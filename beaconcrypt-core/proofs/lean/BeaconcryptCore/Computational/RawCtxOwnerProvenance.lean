import BeaconcryptCore.Computational.RawCtxWholeOwner

/-!
This source correspondence closes the prepared-sequence seam of the one-owner raw interface. Actual extracted admission and every resumed typed KDF response preserve the decoded target and immutable context, without a valid-entry premise or fixed callback-value law. Supported probabilistic success identifies the actual opening callback, source-selected material and optional plaintext, with the same complete final primitive state. Returned API metadata therefore agrees with the original decoded frame and selected sender pin.

These are operational statements, not authentication conclusions. The decoder remains an explicit deterministic function, primitive callbacks remain arbitrary stateful computations, and native peer-map routing/owner-slot behavior require their own refinement. No primitive security, key uniqueness, random-oracle consistency, freshness or plaintext secrecy is assumed here. Existing rank and callback bounds remain unchanged; support does not assert losslessness of independently aborting callbacks.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxOwnerProvenance

/-- Future validation tests the requested sequence before any successful publication. -/
theorem validated_target {SendChain ReceiveChain Material : Type}
    (state : refined.RefinedRatchet SendChain ReceiveChain Material)
    (pending : refined.PendingReceive ReceiveChain Material) (target : Std.U64)
    (hvalid : refined.pending_receive_is_valid state pending target = ok true) :
    pending.target_sequence = target := by
  by_contra hne
  simp [refined.pending_receive_is_valid, control.RatchetState.impl.receive_sequence, hne] at hvalid

/-- Every live capability retains its original target and immutable open context. -/
def Scope {Context : Type} (target : Std.U64) (context : Context) : ReceiveEffect Context → Prop
  | .ReceiveRejected _ actual => actual = context
  | .ReceiveKdfRequested pending => pending.target = target ∧ pending.context = context
  | .ReceiveOpenRequested pending => pending.sequence = ok target ∧ pending.context = context

/-- Any typed KDF response preserves target and context through the actual source continuation. -/
theorem resume_scope {Context : Type} (pending : ReceiveKdf Context)
    (response : RatchetKdfResponse) :
    ∃ result, pending.resume response = ok result ∧ Scope pending.target pending.context result := by
  obtain ⟨result, hresume, _⟩ := pending.resume_progress response
  refine ⟨result, hresume, ?_⟩
  simp only [ReceiveKdf.resume, Bind.bind, Aeneas.Std.bind] at hresume
  repeat' split at hresume
  all_goals simp_all only [Scope, ReceiveOpen.sequence, receive_rejected, RustM.ok.injEq,
    reduceCtorEq]
  all_goals subst result
  all_goals first | rfl | exact ⟨rfl, rfl⟩

/-- A successful receive plan never substitutes another sequence for the decoded target. -/
theorem plan_target (state : control.RatchetState) (target : Std.U64)
    (plan : control.ReceivePlan) (sequence : Std.U64)
    (hplan : control.plan_receive_until state target = ok plan)
    (hsequence : plan.sequence = core.option.Option.Some sequence) :
    sequence = target := by
  simp only [control.plan_receive_until, Bind.bind, Aeneas.Std.bind] at hplan
  repeat' split at hplan
  all_goals simp_all only [RustM.ok.injEq, reduceCtorEq]
  all_goals subst plan
  all_goals simpa only [core.option.Option.Some, core.option.Option.None, Option.some.injEq, reduceCtorEq] using hsequence.symm

/-- Source admission retains the decoded target and immutable context on every path. -/
theorem begin_scope {Context : Type} (entry : ConcreteRatchetKernel)
    (target : Std.U64) (context : Context) :
    ∃ result, begin_receive entry target context = ok result ∧ Scope target context result := by
  obtain ⟨result, hbegin, _⟩ := begin_receive_entry_exact entry target context
  refine ⟨result, hbegin, ?_⟩
  simp only [begin_receive, Bind.bind, Aeneas.Std.bind] at hbegin
  repeat' split at hbegin
  all_goals simp_all only [receive_rejected, RustM.ok.injEq, reduceCtorEq]
  all_goals subst result
  all_goals simp only [Scope, ReceiveOpen.sequence, RustM.ok.injEq, and_true]
  · exact (refined.prepare_cached_receive_success_inv _ _ _ (by assumption)).sequence_eq.trans
      (plan_target _ _ _ _ (by assumption) (by assumption))
  · exact plan_target _ _ _ _ (by assumption) (by assumption)

/-- The total source normalizer preserves exactly the same target and context. -/
theorem oracle_resume_scope {Context : Type} (pending : ReceiveKdf Context)
    (response : RatchetKdfResponse) :
    Scope pending.target pending.context (RawCtxOwnerOracle.resume pending response) := by
  obtain ⟨result, hresult, hscope⟩ := resume_scope pending response
  have heq := RustM.ok.inj ((RawCtxOwnerOracle.resume_exact pending response).symm.trans hresult)
  exact heq.symm ▸ hscope

/-- The normalized admission retains the decoded target and context without validity assumptions. -/
theorem oracle_begin_scope {Context : Type} (entry : ConcreteRatchetKernel)
    (target : Std.U64) (context : Context) :
    Scope target context (RawCtxOwnerOracle.begin entry target context) := by
  obtain ⟨result, hresult, hscope⟩ := begin_scope entry target context
  have heq := RustM.ok.inj ((RawCtxOwnerOracle.begin_exact entry target context).symm.trans hresult)
  exact heq.symm ▸ hscope

/-- Every successful supported source result comes from an actual scoped opening callback and its full final state. -/
theorem supported_success {PrimitiveState Context Plaintext : Type} {ι : Type}
    {base : OracleSpec ι}
    {impl : QueryImpl (RawCtxOwnerOracle.ReceiveSpec Context Plaintext)
      (StateT PrimitiveState (OracleComp base))}
    {entry : PrimitiveState × ReceiveEffect Context}
    {result : (ConcreteRatchetKernel × core.option.Option Plaintext) × PrimitiveState}
    {qKdf qOpen : Nat}
    (run : RawCtxOwnerOracle.SupportedExecution impl entry result qKdf qOpen)
    (target : Std.U64) (context : Context) (hscope : Scope target context entry.2)
    (plaintext : Plaintext) (hsuccess : result.1.2 = .Some plaintext) :
    ∃ pending before, pending.sequence = ok target ∧ pending.context = context ∧
      (.Some plaintext, result.2) ∈ support ((impl (.inr pending)).run before) := by
  induction run with
  | rejected => cases hsuccess
  | opened state pending reply nextState hsupport =>
      exact ⟨pending, state, hscope.1, hscope.2, hsuccess ▸ hsupport⟩
  | resume state pending response nextState result qKdf qOpen hsupport tail ih =>
      exact ih (by simpa only [hscope.1, hscope.2] using oracle_resume_scope pending response) hsuccess

/-- Actual probabilistic receive success identifies the opening callback for the original decoded request. -/
theorem receive_success {PrimitiveState Context Plaintext : Type} {ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl (RawCtxOwnerOracle.ReceiveSpec Context Plaintext)
      (StateT PrimitiveState (OracleComp base)))
    (state : PrimitiveState) (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (result : (ConcreteRatchetKernel × core.option.Option Plaintext) × PrimitiveState)
    (hsupport : result ∈ support ((simulateQ impl
      (RawCtxOwnerOracle.receive entry target context)).run state))
    (plaintext : Plaintext) (hsuccess : result.1.2 = .Some plaintext) :
    ∃ pending before, pending.sequence = ok target ∧ pending.context = context ∧
      (.Some plaintext, result.2) ∈ support ((impl (.inr pending)).run before) := by
  obtain ⟨qKdf, qOpen, run⟩ := RawCtxOwnerOracle.supported_execution impl state _ result hsupport
  exact supported_success run target context (oracle_begin_scope entry target context) plaintext hsuccess

open RawCtxWholeOwner in
/-- Adapter success contains exactly a returned optional plaintext and the selected source opening arguments. -/
theorem adapter_success {PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (pending : ReceiveOpen OpenContext) (state nextState : PrimitiveState) (message : Decrypted)
    (hsupport : (.Some message, nextState) ∈ support
      (((impl ∘ₛ adapter) (.inr pending)).run state)) :
    ∃ input plaintext, arguments pending = some input ∧ message = decrypted input plaintext ∧
      (.Some plaintext, nextState) ∈ support ((impl (.inr input)).run state) := by
  simp only [QueryImpl.compose, adapter] at hsupport
  split at hsupport
  all_goals simp only [simulateQ_bind, simulateQ_pure, simulateQ_spec_query, StateT.run_bind,
    StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq, reduceCtorEq] at hsupport
  · exact hsupport.1.elim
  · obtain ⟨⟨reply, finalState⟩, hreply, hmessage, rfl⟩ := hsupport
    cases reply <;> simp only [RawCtxOwnerResult.mapReply, reduceCtorEq] at hmessage
    exact ⟨_, _, by assumption, Option.some.inj hmessage, hreply⟩

open RawCtxWholeOwner in
/-- A successful source receive passes the original target/context and selected material to the actual optional opening. -/
theorem receive_adapter_success {PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (state : PrimitiveState) (entry : ConcreteRatchetKernel) (target : Std.U64) (context : OpenContext)
    (result : (ConcreteRatchetKernel × core.option.Option Decrypted) × PrimitiveState)
    (hsupport : result ∈ support ((simulateQ (impl ∘ₛ adapter)
      (RawCtxOwnerOracle.receive entry target context)).run state))
    (message : Decrypted) (hsuccess : result.1.2 = .Some message) :
    ∃ (pending : ReceiveOpen OpenContext) (input : OpenInput) (plaintext : Pqxdh.Bytes) (before : PrimitiveState), arguments pending = some input ∧
      pending.material = ok (.Some input.material) ∧
      input.sequence = target ∧ input.context = context ∧ message = decrypted input plaintext ∧
      (.Some plaintext, result.2) ∈ support ((impl (.inr input)).run before) := by
  obtain ⟨pending, before, hsequence, hcontext, hopen⟩ :=
    receive_success (impl ∘ₛ adapter) state entry target context result hsupport message hsuccess
  obtain ⟨input, plaintext, hargs, hmessage, hreply⟩ := adapter_success impl pending before result.2 message hopen
  obtain ⟨hmaterial, hinputSequence, hinputContext⟩ := arguments_some pending input hargs
  exact ⟨pending, input, plaintext, before, hargs, hmaterial,
    RustM.ok.inj (hinputSequence.symm.trans hsequence), hinputContext.trans hcontext, hmessage, hreply⟩

open RawCtxWholeOwner in
/-- Every raw success uses the decoded frame, selected material, exact context and actual opening reply. -/
theorem raw_success {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : OwnerState Metadata) (primitive : PrimitiveState)
    (result : (core.option.Option Decrypted × OwnerState Metadata) × PrimitiveState)
    (hsupport : result ∈ support (rawGame impl decode raw state primitive))
    (message : Decrypted) (hsuccess : result.1.1 = .Some message) :
    ∃ (frame : RawCtxReceive.DecodedFrame) (pending : ReceiveOpen OpenContext)
      (input : OpenInput) (plaintext : Pqxdh.Bytes) (before : PrimitiveState),
      decode raw = some frame ∧ RawCtxReceive.ValidFrame state.owner.expectedSender state.owner.associatedData frame ∧
      arguments pending = some input ∧ pending.material = ok (.Some input.material) ∧
      input.sequence = frame.sequence ∧ input.context = ⟨raw, frame, state.owner.associatedData⟩ ∧
      message = decrypted input plaintext ∧
      (.Some plaintext, result.2) ∈ support ((impl (.inr input)).run before) := by
  unfold rawGame rawReceive StateT.run at hsupport
  split at hsupport
  all_goals repeat' split at hsupport
  all_goals try unfold StateT.run at hsupport
  all_goals try split at hsupport
  all_goals change result ∈ support ((simulateQ impl _).run primitive) at hsupport
  all_goals simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hsupport
  all_goals try { subst result; cases hsuccess }
  obtain ⟨opened, hopen, rfl⟩ := hsupport
  rw [← QueryImpl.simulateQ_compose] at hopen
  obtain ⟨pending, input, plaintext, before, facts⟩ :=
    receive_adapter_success impl primitive state.owner.kernel _ _ opened hopen message hsuccess
  exact ⟨_, pending, input, plaintext, before, by assumption, by assumption, facts⟩

open RawCtxWholeOwner in
/-- Returned message metadata is exactly the decoded sender/sequence checked for this owner. -/
theorem raw_success_metadata {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : OwnerState Metadata) (primitive : PrimitiveState)
    (result : (core.option.Option Decrypted × OwnerState Metadata) × PrimitiveState)
    (hsupport : result ∈ support (rawGame impl decode raw state primitive))
    (message : Decrypted) (hsuccess : result.1.1 = .Some message) :
    ∃ frame, decode raw = some frame ∧ message.keyId = frame.sender ∧
      message.keyId = state.owner.expectedSender ∧ message.sequence = frame.sequence := by
  obtain ⟨frame, pending, input, plaintext, before, hdecode, hvalid, hargs, hmaterial,
    hsequence, hcontext, hmessage, hreply⟩ := raw_success impl decode raw state primitive result hsupport message hsuccess
  exact ⟨frame, hdecode, by simp only [hmessage, decrypted, hcontext],
    by simpa only [hmessage, decrypted, hcontext] using hvalid.1,
    by simpa only [hmessage, decrypted] using hsequence⟩

end BeaconcryptCore.Computational.RawCtxOwnerProvenance

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerProvenance.validated_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerProvenance.validated_target

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerProvenance.resume_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerProvenance.resume_scope

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerProvenance.plan_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerProvenance.plan_target

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerProvenance.begin_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerProvenance.begin_scope

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerProvenance.oracle_resume_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerProvenance.oracle_resume_scope

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerProvenance.oracle_begin_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerProvenance.oracle_begin_scope

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerProvenance.supported_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerProvenance.supported_success

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerProvenance.receive_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerProvenance.receive_success

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerProvenance.adapter_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerProvenance.adapter_success

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerProvenance.receive_adapter_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerProvenance.receive_adapter_success

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerProvenance.raw_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerProvenance.raw_success

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerProvenance.raw_success_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerProvenance.raw_success_metadata
