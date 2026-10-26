import BeaconcryptCore.Refinement.RatchetExecution

/-! A complete receive driver sequences the extracted phases; exact finite executions prove its termination. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option autoImplicit false

namespace beaconcrypt_core.ratchet.concrete

/-- One interpreter-driven transition of the extracted receive state machine. -/
def receiveDriverStep {Context Plaintext : Type} (execute : KdfInterpreter)
    (openReply : ReceiveOpen Context → core.option.Option Plaintext) (effect : ReceiveEffect Context) :
    RustM (ControlFlow (ReceiveEffect Context) (ConcreteRatchetKernel × core.option.Option Plaintext)) := do
  match effect with
  | .ReceiveRejected entry _ => ok (.done (entry, .None))
  | .ReceiveKdfRequested pending =>
      let next ← pending.resume (execute pending.request)
      ok (.cont next)
  | .ReceiveOpenRequested pending =>
      let result ← pending.finish (openReply pending)
      ok (.done result)

/-- Run extracted receive phases until rejection or authentication finishes. -/
def receiveDriver {Context Plaintext : Type} (execute : KdfInterpreter)
    (openReply : ReceiveOpen Context → core.option.Option Plaintext) (effect : ReceiveEffect Context) :
    RustM (ConcreteRatchetKernel × core.option.Option Plaintext) :=
  loop (receiveDriverStep execute openReply) effect

/-- The synchronous receive composition starts with actual production admission. -/
def receiveNext {Context Plaintext : Type} (execute : KdfInterpreter)
    (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (openReply : ReceiveOpen Context → core.option.Option Plaintext) :
    RustM (ConcreteRatchetKernel × core.option.Option Plaintext) := do
  let started ← begin_receive entry target context
  receiveDriver execute openReply started

/-- Every exact finite phase execution evaluates the complete driver to its recorded result. -/
theorem ReceiveExecution.driver_eq {Context Plaintext : Type} {execute : KdfInterpreter}
    {openReply : ReceiveOpen Context → core.option.Option Plaintext}
    {effect : ReceiveEffect Context} {result : ConcreteRatchetKernel} {opened : core.option.Option Plaintext}
    (run : ReceiveExecution execute openReply effect result opened) :
    receiveDriver execute openReply effect = ok (result, opened) := by
  induction run with
  | rejected entry context =>
      rw [receiveDriver, loop.eq_def]
      simp only [receiveDriverStep]
  | opened pending result opened hfinish =>
      rw [receiveDriver, loop.eq_def]
      simp only [receiveDriverStep, hfinish, bind_tc_ok]
  | resume pending next result opened hresume tail ih =>
      rw [receiveDriver, loop.eq_def]
      simpa only [receiveDriver, receiveDriverStep, hresume, bind_tc_ok] using ih

/-- A complete receive run establishes the actual driver's result, including termination. -/
theorem ReceiveRun.driver_eq {Context Plaintext : Type} {execute : KdfInterpreter}
    {openReply : ReceiveOpen Context → core.option.Option Plaintext}
    {entry result : ConcreteRatchetKernel} {target : Std.U64} {context : Context}
    {opened : core.option.Option Plaintext}
    (run : ReceiveRun execute openReply entry target context result opened) :
    receiveNext execute entry target context openReply = ok (result, opened) := by
  obtain ⟨effect, hbegin, execution⟩ := run
  simp only [receiveNext, hbegin, bind_tc_ok, execution.driver_eq]

end beaconcrypt_core.ratchet.concrete
