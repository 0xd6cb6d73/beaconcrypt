import BeaconcryptCore.Computational.RawCtxReceive

/-!
This source-interpreter boundary keeps a complete primitive state separate from the kernel that extracted publication may roll back. It is deterministic operational refinement, not a cryptographic reduction or multi-key game.

The counted operations are source KDF and opening callbacks. Their internal uniform, base-AEAD, CTX-cache and other costs are not asserted to be zero; those remain the exact component query-accounting obligations. A callback can also reject missing material before making an inner CTX call. The callback-value laws used to recover the existing pure source interpretation say only which exact reply is returned, not that it is secure or authentic. The effectful transition and execution relation themselves impose no fixed-reply law.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxOwnerEffects

/-- The primitive state is separate from the owned protocol kernel. -/
abbrev KdfEffect (PrimitiveState : Type) :=
  PrimitiveState → SymmetricRatchetKdfRequest → RatchetKdfResponse × PrimitiveState

/-- The callback returns its true optional result together with every primitive effect. -/
abbrev OpenEffect (PrimitiveState Context Plaintext : Type) :=
  PrimitiveState → ReceiveOpen Context → core.option.Option Plaintext × PrimitiveState

/-- A source driver step retains primitive effects through the actual extracted publication. -/
def receiveEffectStep {PrimitiveState Context Plaintext : Type}
    (execute : KdfEffect PrimitiveState) (openReply : OpenEffect PrimitiveState Context Plaintext)
    (state : PrimitiveState × ReceiveEffect Context) :
    RustM (ControlFlow (PrimitiveState × ReceiveEffect Context)
      ((ConcreteRatchetKernel × core.option.Option Plaintext) × PrimitiveState)) := do
  match state.2 with
  | .ReceiveRejected entry _ => ok (.done ((entry, .None), state.1))
  | .ReceiveKdfRequested pending =>
      let response := execute state.1 pending.request
      let next ← pending.resume response.1
      ok (.cont (response.2, next))
  | .ReceiveOpenRequested pending =>
      let reply := openReply state.1 pending
      let result ← pending.finish reply.1
      ok (.done (result, reply.2))

/-- Preparation rejection returns the whole kernel and unchanged primitive state. -/
theorem rejected_step {PrimitiveState Context Plaintext : Type}
    (execute : KdfEffect PrimitiveState) (openReply : OpenEffect PrimitiveState Context Plaintext)
    (state : PrimitiveState) (entry : ConcreteRatchetKernel) (context : Context) :
    receiveEffectStep execute openReply (state, .ReceiveRejected entry context) =
      ok (.done ((entry, .None), state)) := by
  rfl

/-- Failed opening restores the ratchet entry while retaining the callback's final primitive state. -/
theorem failed_open_retains_effects {PrimitiveState Context Plaintext : Type}
    (execute : KdfEffect PrimitiveState) (openReply : OpenEffect PrimitiveState Context Plaintext)
    (state nextState : PrimitiveState) (pending : ReceiveOpen Context)
    (hreply : openReply state pending = (.None, nextState)) :
    receiveEffectStep execute openReply (state, .ReceiveOpenRequested pending) =
      ok (.done ((pending.entry, .None), nextState)) := by
  simp [receiveEffectStep, hreply, ReceiveOpen.finish]

/-- Finite source executions count KDF callbacks and opening callbacks separately. -/
inductive Execution {PrimitiveState Context Plaintext : Type}
    (execute : KdfEffect PrimitiveState) (openReply : OpenEffect PrimitiveState Context Plaintext) :
    (PrimitiveState × ReceiveEffect Context) →
      ((ConcreteRatchetKernel × core.option.Option Plaintext) × PrimitiveState) → Nat → Nat → Prop where
  | rejected (state : PrimitiveState) (entry : ConcreteRatchetKernel) (context : Context) :
      Execution execute openReply (state, .ReceiveRejected entry context)
        ((entry, .None), state) 0 0
  | opened (state : PrimitiveState) (pending : ReceiveOpen Context)
      (result : ConcreteRatchetKernel × core.option.Option Plaintext)
      (hfinish : pending.finish (openReply state pending).1 = ok result) :
      Execution execute openReply (state, .ReceiveOpenRequested pending)
        (result, (openReply state pending).2) 0 1
  | resume (state : PrimitiveState) (pending : ReceiveKdf Context) (next : ReceiveEffect Context)
      (result : (ConcreteRatchetKernel × core.option.Option Plaintext) × PrimitiveState)
      (qKdf qOpen : Nat)
      (hresume : pending.resume (execute state pending.request).1 = ok next)
      (tail : Execution execute openReply ((execute state pending.request).2, next)
        result qKdf qOpen) :
      Execution execute openReply (state, .ReceiveKdfRequested pending)
        result (qKdf + 1) qOpen

/-- The effectful interpreter follows the same source loop, keeping the primitive state outside publication. -/
def receiveEffects {PrimitiveState Context Plaintext : Type}
    (execute : KdfEffect PrimitiveState) (openReply : OpenEffect PrimitiveState Context Plaintext)
    (entry : PrimitiveState × ReceiveEffect Context) :
    RustM ((ConcreteRatchetKernel × core.option.Option Plaintext) × PrimitiveState) :=
  loop (receiveEffectStep execute openReply) entry

/-- Every exact finite effect execution evaluates the driver with its complete final primitive state. -/
theorem Execution.driver_eq {PrimitiveState Context Plaintext : Type}
    {execute : KdfEffect PrimitiveState} {openReply : OpenEffect PrimitiveState Context Plaintext}
    {entry : PrimitiveState × ReceiveEffect Context}
    {result : (ConcreteRatchetKernel × core.option.Option Plaintext) × PrimitiveState}
    {qKdf qOpen : Nat} (run : Execution execute openReply entry result qKdf qOpen) :
    receiveEffects execute openReply entry = ok result := by
  induction run with
  | rejected state entry context =>
      rw [receiveEffects, loop.eq_def]
      simp [receiveEffectStep]
  | opened state pending result hfinish =>
      rw [receiveEffects, loop.eq_def]
      simp [receiveEffectStep, hfinish]
  | resume state pending next result qKdf qOpen hresume tail ih =>
      rw [receiveEffects, loop.eq_def]
      simpa only [receiveEffects, receiveEffectStep, hresume, bind_tc_ok] using ih

/-- One public receive invokes at most one opening callback, including callbacks returning rejection. -/
theorem Execution.open_bound {PrimitiveState Context Plaintext : Type}
    {execute : KdfEffect PrimitiveState} {openReply : OpenEffect PrimitiveState Context Plaintext}
    {entry : PrimitiveState × ReceiveEffect Context}
    {result : (ConcreteRatchetKernel × core.option.Option Plaintext) × PrimitiveState}
    {qKdf qOpen : Nat} (run : Execution execute openReply entry result qKdf qOpen) :
    qOpen ≤ 1 := by
  induction run with
  | rejected => decide
  | opened => decide
  | resume _ _ _ _ _ _ _ _ ih => exact ih

/-- The existing source rank decreases for every callback response, independently of primitive state. -/
theorem execution_exists {PrimitiveState Context Plaintext : Type}
    (execute : KdfEffect PrimitiveState) (openReply : OpenEffect PrimitiveState Context Plaintext)
    (state : PrimitiveState) (effect : ReceiveEffect Context) :
    ∃ result qKdf qOpen, Execution execute openReply (state, effect) result qKdf qOpen := by
  generalize hdepth : effectDepth effect = depth
  induction depth using Nat.strong_induction_on generalizing effect state with
  | h depth ih =>
      cases effect with
      | ReceiveRejected entry context =>
          exact ⟨((entry, .None), state), 0, 0, .rejected state entry context⟩
      | ReceiveOpenRequested pending =>
          obtain ⟨kernel, hfinish⟩ := pending.finish_result_exact (openReply state pending).1
          exact ⟨((kernel, (openReply state pending).1), (openReply state pending).2),
            0, 1, .opened state pending _ hfinish⟩
      | ReceiveKdfRequested pending =>
          obtain ⟨next, hresume, hprogress⟩ := pending.resume_progress (execute state pending.request).1
          have hlt : effectDepth next < depth := by
            cases next with
            | ReceiveRejected => simp only [effectDepth] at hdepth ⊢; omega
            | ReceiveOpenRequested => simp only [effectDepth] at hdepth ⊢; omega
            | ReceiveKdfRequested later =>
                have hremaining := hprogress.2
                simp only [effectDepth] at hdepth ⊢
                change later.remaining.val < pending.remaining.val at hremaining
                omega
          obtain ⟨result, qKdf, qOpen, tail⟩ :=
            ih (effectDepth next) hlt (execute state pending.request).2 next rfl
          exact ⟨result, qKdf + 1, qOpen, .resume state pending next result qKdf qOpen hresume tail⟩

/-- Failed stateful executions restore the source entry without any fixed-reply or cryptographic premise. -/
theorem Execution.failure_entry {PrimitiveState Context Plaintext : Type}
    {execute : KdfEffect PrimitiveState} {openReply : OpenEffect PrimitiveState Context Plaintext}
    {entry : PrimitiveState × ReceiveEffect Context}
    {result : (ConcreteRatchetKernel × core.option.Option Plaintext) × PrimitiveState}
    {qKdf qOpen : Nat} (run : Execution execute openReply entry result qKdf qOpen)
    (hfailure : result.1.2 = .None) : result.1.1 = effectEntry entry.2 := by
  induction run with
  | rejected => rfl
  | opened state pending result hfinish =>
      obtain ⟨kernel, hresult⟩ := pending.finish_result_exact (openReply state pending).1
      have hpair := RustM.ok.inj (hresult.symm.trans hfinish)
      have hnone : (openReply state pending).1 = .None :=
        (congrArg Prod.snd hpair).trans hfailure
      rw [hnone, ReceiveOpen.finish] at hfinish
      exact (congrArg Prod.fst (RustM.ok.inj hfinish)).symm
  | resume state pending next result qKdf qOpen hresume tail ih =>
      obtain ⟨next', hnext, hprogress⟩ := pending.resume_progress (execute state pending.request).1
      have heq : next' = next := RustM.ok.inj (hnext.symm.trans hresume)
      exact (ih hfailure).trans (heq ▸ hprogress.1)

/-- KDF callback count is bounded by the actual source continuation rank, even for state-dependent replies. -/
theorem Execution.kdf_bound {PrimitiveState Context Plaintext : Type}
    {execute : KdfEffect PrimitiveState} {openReply : OpenEffect PrimitiveState Context Plaintext}
    {entry : PrimitiveState × ReceiveEffect Context}
    {result : (ConcreteRatchetKernel × core.option.Option Plaintext) × PrimitiveState}
    {qKdf qOpen : Nat} (run : Execution execute openReply entry result qKdf qOpen) :
    qKdf ≤ effectDepth entry.2 := by
  induction run with
  | rejected => exact Nat.zero_le _
  | opened => exact Nat.zero_le _
  | resume state pending next result qKdf qOpen hresume tail ih =>
      obtain ⟨next', hnext, hprogress⟩ := pending.resume_progress (execute state pending.request).1
      have heq : next' = next := RustM.ok.inj (hnext.symm.trans hresume)
      subst next'
      have hlt : effectDepth next < effectDepth (.ReceiveKdfRequested pending) := by
        cases next with
        | ReceiveRejected => simp [effectDepth]
        | ReceiveOpenRequested => simp [effectDepth]
        | ReceiveKdfRequested later =>
            have hremaining := hprogress.2
            change later.remaining.val < pending.remaining.val at hremaining
            simp only [effectDepth]
            omega
      exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih hlt)

/-- Exact callback-value laws recover the existing source execution; primitive effects stay in the original run. -/
theorem Execution.project {PrimitiveState Context Plaintext : Type}
    {execute : KdfEffect PrimitiveState} {openReply : OpenEffect PrimitiveState Context Plaintext}
    (fixedKdf : KdfInterpreter)
    (fixedOpen : ReceiveOpen Context → core.option.Option Plaintext)
    (hkdf : ∀ state request, (execute state request).1 = fixedKdf request)
    (hopen : ∀ state pending, (openReply state pending).1 = fixedOpen pending)
    {entry : PrimitiveState × ReceiveEffect Context}
    {result : (ConcreteRatchetKernel × core.option.Option Plaintext) × PrimitiveState}
    {qKdf qOpen : Nat} (run : Execution execute openReply entry result qKdf qOpen) :
    ReceiveExecution fixedKdf fixedOpen entry.2 result.1.1 result.1.2 := by
  induction run with
  | rejected state entry context => exact .rejected entry context
  | opened state pending result hfinish =>
      apply ReceiveExecution.opened
      simpa only [hopen] using hfinish
  | resume state pending next result qKdf qOpen hresume tail ih =>
      apply ReceiveExecution.resume pending next result.1.1 result.1.2
      · simpa only [hkdf] using hresume
      · exact ih

/-- Every existing finite source execution lifts with all callback state changes retained. -/
theorem execution_lift {PrimitiveState Context Plaintext : Type}
    (execute : KdfEffect PrimitiveState) (openReply : OpenEffect PrimitiveState Context Plaintext)
    (fixedKdf : KdfInterpreter)
    (fixedOpen : ReceiveOpen Context → core.option.Option Plaintext)
    (hkdf : ∀ state request, (execute state request).1 = fixedKdf request)
    (hopen : ∀ state pending, (openReply state pending).1 = fixedOpen pending)
    (state : PrimitiveState) (effect : ReceiveEffect Context)
    (kernel : ConcreteRatchetKernel) (reply : core.option.Option Plaintext)
    (run : ReceiveExecution fixedKdf fixedOpen effect kernel reply) :
    ∃ nextState qKdf qOpen,
      Execution execute openReply (state, effect) ((kernel, reply), nextState) qKdf qOpen := by
  induction run generalizing state with
  | rejected entry context => exact ⟨state, 0, 0, .rejected state entry context⟩
  | opened pending result opened hfinish =>
      refine ⟨(openReply state pending).2, 0, 1, .opened state pending (result, opened) ?_⟩
      simpa only [hopen] using hfinish
  | resume pending next result opened hresume tail ih =>
      obtain ⟨nextState, qKdf, qOpen, lifted⟩ := ih (execute state pending.request).2
      refine ⟨nextState, qKdf + 1, qOpen, .resume state pending next
        ((result, opened), nextState) qKdf qOpen ?_ lifted⟩
      simpa only [hkdf] using hresume

/-- A complete receive takes the actual source admission path before interpreting primitive effects. -/
def receiveEffectsNext {PrimitiveState Context Plaintext : Type}
    (execute : KdfEffect PrimitiveState) (openReply : OpenEffect PrimitiveState Context Plaintext)
    (state : PrimitiveState) (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context) :
    RustM ((ConcreteRatchetKernel × core.option.Option Plaintext) × PrimitiveState) := do
  let effect ← begin_receive entry target context
  receiveEffects execute openReply (state, effect)

/-- Arbitrary state-dependent callbacks terminate with exact primitive state, source rollback and counted bounds. -/
theorem receiveEffectsNext_total {PrimitiveState Context Plaintext : Type}
    (execute : KdfEffect PrimitiveState) (openReply : OpenEffect PrimitiveState Context Plaintext)
    (state : PrimitiveState) (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context) :
    ∃ effect result qKdf qOpen,
      begin_receive entry target context = ok effect ∧
      Execution execute openReply (state, effect) result qKdf qOpen ∧
      receiveEffectsNext execute openReply state entry target context = ok result ∧
      (result.1.2 = .None → result.1.1 = entry) ∧
      qKdf ≤ effectDepth effect ∧ qOpen ≤ 1 := by
  obtain ⟨effect, hbegin, hentry⟩ := begin_receive_entry_exact entry target context
  obtain ⟨result, qKdf, qOpen, run⟩ := execution_exists execute openReply state effect
  refine ⟨effect, result, qKdf, qOpen, hbegin, run, ?_, ?_, run.kdf_bound, run.open_bound⟩
  · simp only [receiveEffectsNext, hbegin, bind_tc_ok, run.driver_eq]
  · intro hfailure
    exact (run.failure_entry hfailure).trans hentry

/-- Exact callback interpretation preserves source results and rejection rollback without resetting primitive state. -/
theorem receiveEffectsNext_refines {PrimitiveState Context Plaintext : Type}
    (execute : KdfEffect PrimitiveState) (openReply : OpenEffect PrimitiveState Context Plaintext)
    (fixedKdf : KdfInterpreter)
    (fixedOpen : ReceiveOpen Context → core.option.Option Plaintext)
    (hkdf : ∀ state request, (execute state request).1 = fixedKdf request)
    (hopen : ∀ state pending, (openReply state pending).1 = fixedOpen pending)
    (state : PrimitiveState) (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context) :
    ∃ kernel reply nextState qKdf qOpen effect,
      begin_receive entry target context = ok effect ∧
      Execution execute openReply (state, effect) ((kernel, reply), nextState) qKdf qOpen ∧
      receiveEffectsNext execute openReply state entry target context = ok ((kernel, reply), nextState) ∧
      receiveNext fixedKdf entry target context fixedOpen = ok (kernel, reply) ∧
      (reply = .None → kernel = entry) ∧ qOpen ≤ 1 := by
  obtain ⟨kernel, reply, run⟩ := receiveRun_exists fixedKdf entry target context fixedOpen
  obtain ⟨effect, hbegin, execution⟩ := run
  obtain ⟨nextState, qKdf, qOpen, lifted⟩ :=
    execution_lift execute openReply fixedKdf fixedOpen hkdf hopen state effect kernel reply execution
  have hdriver : receiveNext fixedKdf entry target context fixedOpen = ok (kernel, reply) :=
    ReceiveRun.driver_eq ⟨effect, hbegin, execution⟩
  refine ⟨kernel, reply, nextState, qKdf, qOpen, effect, hbegin, lifted, ?_, hdriver, ?_, lifted.open_bound⟩
  · simp only [receiveEffectsNext, hbegin, bind_tc_ok, lifted.driver_eq]
  · intro hnone
    subst reply
    exact receiveNext_failure_entry fixedKdf entry kernel target context fixedOpen hdriver

end BeaconcryptCore.Computational.RawCtxOwnerEffects

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerEffects.rejected_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerEffects.rejected_step
/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerEffects.failed_open_retains_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerEffects.failed_open_retains_effects
/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerEffects.Execution.driver_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerEffects.Execution.driver_eq
/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerEffects.Execution.open_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerEffects.Execution.open_bound
/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerEffects.Execution.project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerEffects.Execution.project
/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerEffects.execution_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerEffects.execution_lift
/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerEffects.receiveEffectsNext_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerEffects.receiveEffectsNext_refines

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerEffects.execution_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerEffects.execution_exists
/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerEffects.Execution.failure_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerEffects.Execution.failure_entry
/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerEffects.Execution.kdf_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerEffects.Execution.kdf_bound
/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerEffects.receiveEffectsNext_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerEffects.receiveEffectsNext_total
