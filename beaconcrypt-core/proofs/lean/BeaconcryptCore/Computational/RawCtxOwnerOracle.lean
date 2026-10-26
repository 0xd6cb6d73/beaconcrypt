import BeaconcryptCore.Computational.RawCtxOwnerEffects
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
This is a private oracle interpretation of the actual extracted receive driver. The normalizers select only results whose source RustM computations are already proved total and unique; their exact equalities are checked below. They do not provide executable replacements for the native adapter.

The source program is finite for every typed KDF response and has no fuel fallback. Deterministic interpretation preserves the complete source result and primitive state. Probabilistic interpretation admits arbitrary state-dependent callbacks, retains each returned state, and proves source rollback and callback query bounds without fixed-reply laws. Support facts do not assert probability-one termination of a callback that itself aborts. The counted private source callbacks are not new primitive security assumptions, and the inner KDF, random, AEAD and CTX-cache costs remain separate component ledgers.

The raw decoder, routing, whole-owner loop, actual optional-result construction and component key selection are separate interfaces. This module does not assert a global authentication, secrecy or native codec theorem.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxOwnerOracle

/-- The exact source response resumes one capability; totality is already proved for every typed reply. -/
noncomputable def resume {Context : Type} (pending : ReceiveKdf Context)
    (response : RatchetKdfResponse) : ReceiveEffect Context :=
  (pending.resume_progress response).choose

theorem resume_exact {Context : Type} (pending : ReceiveKdf Context)
    (response : RatchetKdfResponse) : pending.resume response = ok (resume pending response) :=
  (pending.resume_progress response).choose_spec.1

/-- No callback response can prevent the source continuation rank from decreasing. -/
theorem resume_rank {Context : Type} (pending : ReceiveKdf Context)
    (response : RatchetKdfResponse) :
    effectDepth (resume pending response) < effectDepth (.ReceiveKdfRequested pending) := by
  have progress := (pending.resume_progress response).choose_spec.2
  change ResumeProgress pending (resume pending response) at progress
  cases hnext : resume pending response with
  | ReceiveRejected => simp [effectDepth]
  | ReceiveOpenRequested => simp [effectDepth]
  | ReceiveKdfRequested later =>
      have remaining := progress.2
      simp only [hnext] at remaining
      simpa only [effectDepth, Nat.add_lt_add_iff_right] using remaining

/-- Extract the unique total source publication kernel; retain the callback's actual option. -/
noncomputable def finish {Context Plaintext : Type} (pending : ReceiveOpen Context)
    (reply : core.option.Option Plaintext) : ConcreteRatchetKernel × core.option.Option Plaintext :=
  ((pending.finish_result_exact reply).choose, reply)

theorem finish_exact {Context Plaintext : Type} (pending : ReceiveOpen Context)
    (reply : core.option.Option Plaintext) : pending.finish reply = ok (finish pending reply) :=
  (pending.finish_result_exact reply).choose_spec

/-- These are private source callbacks, not additional adversary or primitive security interfaces. -/
abbrev ReceiveSpec (Context Plaintext : Type) :=
  (SymmetricRatchetKdfRequest →ₒ RatchetKdfResponse) +
    (ReceiveOpen Context →ₒ core.option.Option Plaintext)

/-- Interpret actual source capabilities, retaining the typed KDF reply and actual optional plaintext. -/
noncomputable def program {Context Plaintext : Type} (effect : ReceiveEffect Context) :
    OracleComp (ReceiveSpec Context Plaintext)
      (ConcreteRatchetKernel × core.option.Option Plaintext) :=
  match effect with
  | .ReceiveRejected entry _ => pure (entry, .None)
  | .ReceiveOpenRequested pending => do
      let reply ← (ReceiveSpec Context Plaintext).query (.inr pending)
      pure (finish pending reply)
  | .ReceiveKdfRequested pending => do
      let response ← (ReceiveSpec Context Plaintext).query (.inl pending.request)
      program (resume pending response)
termination_by effectDepth effect
decreasing_by exact resume_rank _ _

/-- Interpret private callbacks with their complete deterministic state effects. -/
def deterministicImpl {PrimitiveState Context Plaintext : Type}
    (execute : RawCtxOwnerEffects.KdfEffect PrimitiveState)
    (openReply : RawCtxOwnerEffects.OpenEffect PrimitiveState Context Plaintext) :
    QueryImpl (ReceiveSpec Context Plaintext) (StateM PrimitiveState)
  | .inl request => fun state => execute state request
  | .inr pending => fun state => openReply state pending

/-- Every complete stateful source execution has exactly the same VCVio program result and state. -/
theorem deterministic_execution {PrimitiveState Context Plaintext : Type}
    {execute : RawCtxOwnerEffects.KdfEffect PrimitiveState}
    {openReply : RawCtxOwnerEffects.OpenEffect PrimitiveState Context Plaintext}
    {entry : PrimitiveState × ReceiveEffect Context}
    {result : (ConcreteRatchetKernel × core.option.Option Plaintext) × PrimitiveState}
    {qKdf qOpen : Nat}
    (run : RawCtxOwnerEffects.Execution execute openReply entry result qKdf qOpen) :
    (simulateQ (deterministicImpl execute openReply) (program entry.2)).run entry.1 = result := by
  induction run with
  | rejected state entry context => simp only [program, simulateQ_pure, StateT.run_pure]; rfl
  | opened state pending result hfinish =>
      rw [program, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      simp only [simulateQ_pure, StateT.run_pure]
      change (finish pending (openReply state pending).1, (openReply state pending).2) = _
      exact congrArg (fun result => (result, (openReply state pending).2))
        (RustM.ok.inj ((finish_exact pending (openReply state pending).1).symm.trans hfinish))
  | resume state pending next result qKdf qOpen hresume tail ih =>
      have hnext := RustM.ok.inj ((resume_exact pending (execute state pending.request).1).symm.trans hresume)
      rw [program, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      change (simulateQ (deterministicImpl execute openReply)
        (program (resume pending (execute state pending.request).1))).run
          (execute state pending.request).2 = result
      simpa only [hnext] using ih

/-- A supported probabilistic execution retains every callback's full returned state and counts source calls. -/
inductive SupportedExecution {PrimitiveState Context Plaintext : Type} {ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl (ReceiveSpec Context Plaintext)
      (StateT PrimitiveState (OracleComp base))) :
    (PrimitiveState × ReceiveEffect Context) →
      ((ConcreteRatchetKernel × core.option.Option Plaintext) × PrimitiveState) → Nat → Nat → Prop where
  | rejected (state : PrimitiveState) (entry : ConcreteRatchetKernel) (context : Context) :
      SupportedExecution impl (state, .ReceiveRejected entry context) ((entry, .None), state) 0 0
  | opened (state : PrimitiveState) (pending : ReceiveOpen Context)
      (reply : core.option.Option Plaintext) (nextState : PrimitiveState)
      (hsupport : (reply, nextState) ∈ support ((impl (.inr pending)).run state)) :
      SupportedExecution impl (state, .ReceiveOpenRequested pending)
        (finish pending reply, nextState) 0 1
  | resume (state : PrimitiveState) (pending : ReceiveKdf Context)
      (response : RatchetKdfResponse) (nextState : PrimitiveState)
      (result : (ConcreteRatchetKernel × core.option.Option Plaintext) × PrimitiveState)
      (qKdf qOpen : Nat)
      (hsupport : (response, nextState) ∈ support ((impl (.inl pending.request)).run state))
      (tail : SupportedExecution impl (nextState, resume pending response) result qKdf qOpen) :
      SupportedExecution impl (state, .ReceiveKdfRequested pending) result (qKdf + 1) qOpen

/-- Arbitrary probabilistic, state-dependent primitive replies follow only exact source executions. -/
theorem supported_execution {PrimitiveState Context Plaintext : Type} {ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl (ReceiveSpec Context Plaintext)
      (StateT PrimitiveState (OracleComp base)))
    (state : PrimitiveState) (effect : ReceiveEffect Context)
    (result : (ConcreteRatchetKernel × core.option.Option Plaintext) × PrimitiveState)
    (hsupport : result ∈ support ((simulateQ impl (program effect)).run state)) :
    ∃ qKdf qOpen, SupportedExecution impl (state, effect) result qKdf qOpen := by
  generalize hdepth : effectDepth effect = depth
  induction depth using Nat.strong_induction_on generalizing effect state with
  | h depth ih =>
      cases effect with
      | ReceiveRejected entry context =>
          simp only [program, simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at hsupport
          exact ⟨0, 0, hsupport ▸ .rejected state entry context⟩
      | ReceiveOpenRequested pending =>
          simp only [program, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
            simulateQ_pure, StateT.run_pure, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at hsupport
          obtain ⟨reply, hreply, rfl⟩ := hsupport
          exact ⟨0, 1, .opened state pending reply.1 reply.2 hreply⟩
      | ReceiveKdfRequested pending =>
          rw [program, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hsupport
          obtain ⟨response, hresponse, htail⟩ := hsupport
          obtain ⟨qKdf, qOpen, tail⟩ := ih _
            (hdepth ▸ resume_rank pending response.1) response.2 _ htail rfl
          exact ⟨qKdf + 1, qOpen, .resume state pending response.1 response.2 result
            qKdf qOpen hresponse tail⟩

/-- A source KDF reply cannot change the saved rollback entry. -/
theorem resume_entry {Context : Type} (pending : ReceiveKdf Context)
    (response : RatchetKdfResponse) : effectEntry (resume pending response) = pending.entry :=
  (pending.resume_progress response).choose_spec.2.1

/-- Actual optional rejection restores only the saved source kernel. -/
theorem finish_none {Context Plaintext : Type} (pending : ReceiveOpen Context) :
    finish pending (.None : core.option.Option Plaintext) = (pending.entry, .None) := by
  exact RustM.ok.inj ((finish_exact pending .None).symm.trans rfl)

/-- The actual VCVio source program issues at most the source continuation rank in KDF calls. -/
theorem program_kdf_bound {Context Plaintext : Type} (effect : ReceiveEffect Context) :
    (program (Plaintext := Plaintext) effect).IsQueryBoundP
      (fun request => request.isLeft = true) (effectDepth effect) := by
  generalize hdepth : effectDepth effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
      cases effect with
      | ReceiveRejected entry context => simp [program]
      | ReceiveOpenRequested pending =>
          rw [program, isQueryBoundP_query_bind_iff]
          simp
      | ReceiveKdfRequested pending =>
          rw [program, isQueryBoundP_query_bind_iff]
          simp only [Sum.isLeft, not_true_eq_false, false_or, ite_true]
          refine ⟨by simp only [effectDepth] at hdepth; omega, fun response => ?_⟩
          exact (ih _ (hdepth ▸ resume_rank pending response) _ rfl).mono
            (Nat.le_pred_of_lt (hdepth ▸ resume_rank pending response))

/-- Every actual receive program issues at most one opening callback, including rejection. -/
theorem program_open_bound {Context Plaintext : Type} (effect : ReceiveEffect Context) :
    (program (Plaintext := Plaintext) effect).IsQueryBoundP
      (fun request => request.isRight = true) 1 := by
  generalize hdepth : effectDepth effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
      cases effect with
      | ReceiveRejected entry context => simp [program]
      | ReceiveOpenRequested pending =>
          rw [program, isQueryBoundP_query_bind_iff]
          simp
      | ReceiveKdfRequested pending =>
          rw [program, isQueryBoundP_query_bind_iff]
          simp only [Sum.isRight, Bool.false_eq_true, not_false_eq_true, true_or,
            ite_false, true_and]
          exact fun response => ih _ (hdepth ▸ resume_rank pending response) _ rfl

/-- Failed probabilistic callbacks roll back the source kernel without constraining their final state. -/
theorem SupportedExecution.failure_entry {PrimitiveState Context Plaintext : Type} {ι : Type}
    {base : OracleSpec ι}
    {impl : QueryImpl (ReceiveSpec Context Plaintext)
      (StateT PrimitiveState (OracleComp base))}
    {entry : PrimitiveState × ReceiveEffect Context}
    {result : (ConcreteRatchetKernel × core.option.Option Plaintext) × PrimitiveState}
    {qKdf qOpen : Nat} (run : SupportedExecution impl entry result qKdf qOpen)
    (hfailure : result.1.2 = .None) : result.1.1 = effectEntry entry.2 := by
  induction run with
  | rejected => rfl
  | opened state pending reply nextState hsupport =>
      change reply = .None at hfailure
      simp only [hfailure, finish_none, effectEntry]
  | resume state pending response nextState result qKdf qOpen hsupport tail ih =>
      exact (ih hfailure).trans (resume_entry pending response)

/-- Every supported opening result keeps full primitive state while failed acceptance restores the entry kernel. -/
theorem program_failure_entry {PrimitiveState Context Plaintext : Type} {ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl (ReceiveSpec Context Plaintext)
      (StateT PrimitiveState (OracleComp base)))
    (state : PrimitiveState) (effect : ReceiveEffect Context)
    (result : (ConcreteRatchetKernel × core.option.Option Plaintext) × PrimitiveState)
    (hsupport : result ∈ support ((simulateQ impl (program effect)).run state))
    (hfailure : result.1.2 = .None) : result.1.1 = effectEntry effect := by
  obtain ⟨qKdf, qOpen, run⟩ := supported_execution impl state effect result hsupport
  exact run.failure_entry hfailure

/-- Extract only the total source admission effect, without changing any checks. -/
noncomputable def begin {Context : Type} (entry : ConcreteRatchetKernel)
    (target : Std.U64) (context : Context) : ReceiveEffect Context :=
  (begin_receive_entry_exact entry target context).choose

theorem begin_exact {Context : Type} (entry : ConcreteRatchetKernel)
    (target : Std.U64) (context : Context) :
    begin_receive entry target context = ok (begin entry target context) :=
  (begin_receive_entry_exact entry target context).choose_spec.1

theorem begin_entry {Context : Type} (entry : ConcreteRatchetKernel)
    (target : Std.U64) (context : Context) : effectEntry (begin entry target context) = entry :=
  (begin_receive_entry_exact entry target context).choose_spec.2

/-- One actual source receive, suitable for stateful probabilistic callback interpretation. -/
noncomputable def receive {Context Plaintext : Type} (entry : ConcreteRatchetKernel)
    (target : Std.U64) (context : Context) :
    OracleComp (ReceiveSpec Context Plaintext)
      (ConcreteRatchetKernel × core.option.Option Plaintext) :=
  program (begin entry target context)

/-- The deterministic instantiation exactly evaluates the existing whole-state source driver. -/
theorem receive_deterministic {PrimitiveState Context Plaintext : Type}
    (execute : RawCtxOwnerEffects.KdfEffect PrimitiveState)
    (openReply : RawCtxOwnerEffects.OpenEffect PrimitiveState Context Plaintext)
    (state : PrimitiveState) (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context) :
    RawCtxOwnerEffects.receiveEffectsNext execute openReply state entry target context =
      ok ((simulateQ (deterministicImpl execute openReply) (receive entry target context)).run state) := by
  obtain ⟨result, qKdf, qOpen, run⟩ :=
    RawCtxOwnerEffects.execution_exists execute openReply state (begin entry target context)
  rw [RawCtxOwnerEffects.receiveEffectsNext, begin_exact, bind_tc_ok, receive, deterministic_execution run]
  exact run.driver_eq

/-- Probabilistic receive rejection restores the whole ratchet; primitive state is retained by the interpreter. -/
theorem receive_failure_entry {PrimitiveState Context Plaintext : Type} {ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl (ReceiveSpec Context Plaintext)
      (StateT PrimitiveState (OracleComp base)))
    (state : PrimitiveState) (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (result : (ConcreteRatchetKernel × core.option.Option Plaintext) × PrimitiveState)
    (hsupport : result ∈ support ((simulateQ impl (receive entry target context)).run state))
    (hfailure : result.1.2 = .None) : result.1.1 = entry :=
  (program_failure_entry impl state _ result hsupport hfailure).trans (begin_entry entry target context)

end BeaconcryptCore.Computational.RawCtxOwnerOracle

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerOracle.resume_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerOracle.resume_exact

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerOracle.resume_rank' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerOracle.resume_rank

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerOracle.finish_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerOracle.finish_exact

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerOracle.deterministic_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerOracle.deterministic_execution

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerOracle.supported_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerOracle.supported_execution

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerOracle.resume_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerOracle.resume_entry

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerOracle.finish_none' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerOracle.finish_none

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerOracle.program_kdf_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerOracle.program_kdf_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerOracle.program_open_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerOracle.program_open_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerOracle.SupportedExecution.failure_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerOracle.SupportedExecution.failure_entry

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerOracle.program_failure_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerOracle.program_failure_entry

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerOracle.begin_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerOracle.begin_exact

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerOracle.begin_entry' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerOracle.begin_entry

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerOracle.receive_deterministic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerOracle.receive_deterministic

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerOracle.receive_failure_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerOracle.receive_failure_entry
