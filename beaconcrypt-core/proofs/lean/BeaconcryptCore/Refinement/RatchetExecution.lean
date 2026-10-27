import BeaconcryptCore.Refinement.RatchetInterpreter

/-! Finite executions of the extracted receive phases under fixed pure interpreters. Every transition is an equation about the extracted operation; existence of a complete execution is proved separately from this relation. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option autoImplicit false

namespace beaconcrypt_core.ratchet.concrete

/-- An exact counted sequence of extracted KDF resumptions. -/
inductive ReceiveKdfTrace {Context : Type} (execute : KdfInterpreter) :
    ReceiveEffect Context → ReceiveEffect Context → Nat → Prop where
  | refl (effect : ReceiveEffect Context) : ReceiveKdfTrace execute effect effect 0
  | step (pending : ReceiveKdf Context) (next final : ReceiveEffect Context) (count : Nat)
      (hresume : pending.resume (execute pending.request) = ok next)
      (tail : ReceiveKdfTrace execute next final count) :
      ReceiveKdfTrace execute (ReceiveEffect.ReceiveKdfRequested pending) final (count + 1)

/-- A complete receive execution ending in rejection or the actual extracted finish result. -/
inductive ReceiveExecution {Context Plaintext : Type} (execute : KdfInterpreter)
    (openReply : ReceiveOpen Context → core.option.Option Plaintext) :
    ReceiveEffect Context → ConcreteRatchetKernel → core.option.Option Plaintext → Prop where
  | rejected (entry : ConcreteRatchetKernel) (context : Context) :
      ReceiveExecution execute openReply (ReceiveEffect.ReceiveRejected entry context)
        entry core.option.Option.None
  | resume (pending : ReceiveKdf Context) (next : ReceiveEffect Context)
      (result : ConcreteRatchetKernel) (opened : core.option.Option Plaintext)
      (hresume : pending.resume (execute pending.request) = ok next)
      (tail : ReceiveExecution execute openReply next result opened) :
      ReceiveExecution execute openReply (ReceiveEffect.ReceiveKdfRequested pending) result opened
  | opened (pending : ReceiveOpen Context) (result : ConcreteRatchetKernel)
      (opened : core.option.Option Plaintext)
      (hfinish : pending.finish (openReply pending) = ok (result, opened)) :
      ReceiveExecution execute openReply (ReceiveEffect.ReceiveOpenRequested pending) result opened

/-- One complete operation begins with the extracted admission function. -/
def ReceiveRun {Context Plaintext : Type} (execute : KdfInterpreter)
    (openReply : ReceiveOpen Context → core.option.Option Plaintext)
    (entry : ConcreteRatchetKernel) (sequence : Std.U64) (context : Context)
    (result : ConcreteRatchetKernel) (opened : core.option.Option Plaintext) : Prop :=
  ∃ effect, begin_receive entry sequence context = ok effect ∧
    ReceiveExecution execute openReply effect result opened

/-- A checked KDF prefix followed by a terminal execution is a complete execution. -/
theorem ReceiveKdfTrace.complete {Context Plaintext : Type} {execute : KdfInterpreter}
    {openReply : ReceiveOpen Context → core.option.Option Plaintext}
    {effect terminal : ReceiveEffect Context} {count : Nat}
    {result : ConcreteRatchetKernel} {opened : core.option.Option Plaintext}
    (trace : ReceiveKdfTrace execute effect terminal count)
    (tail : ReceiveExecution execute openReply terminal result opened) :
    ReceiveExecution execute openReply effect result opened := by
  induction trace with
  | refl => exact tail
  | step pending next final count hresume tracePrefix ih =>
      exact .resume pending next result opened hresume (ih tail)

/-- Fixed interpreters and extracted transitions determine the complete result uniquely. -/
theorem ReceiveExecution.deterministic {Context Plaintext : Type} {execute : KdfInterpreter}
    {openReply : ReceiveOpen Context → core.option.Option Plaintext}
    {effect : ReceiveEffect Context}
    {result otherResult : ConcreteRatchetKernel}
    {opened otherOpened : core.option.Option Plaintext}
    (run : ReceiveExecution execute openReply effect result opened)
    (other : ReceiveExecution execute openReply effect otherResult otherOpened) :
    result = otherResult ∧ opened = otherOpened := by
  induction run generalizing otherResult otherOpened
  case resume pending next result opened hresume tail ih =>
    cases other with
    | resume _ next' _ _ hresume' tail' =>
        exact ih ((RustM.ok.inj (hresume'.symm.trans hresume)) ▸ tail')
  case rejected => cases other; exact ⟨rfl, rfl⟩
  case opened pending result opened hfinish =>
    cases other with
    | opened _ _ _ hfinish' =>
        exact Prod.mk.inj (RustM.ok.inj (hfinish.symm.trans hfinish'))

/-- Repeating one whole operation from the same entry has the same result. -/
theorem ReceiveRun.deterministic {Context Plaintext : Type} {execute : KdfInterpreter}
    {openReply : ReceiveOpen Context → core.option.Option Plaintext}
    {entry result otherResult : ConcreteRatchetKernel} {sequence : Std.U64} {context : Context}
    {opened otherOpened : core.option.Option Plaintext}
    (run : ReceiveRun execute openReply entry sequence context result opened)
    (other : ReceiveRun execute openReply entry sequence context otherResult otherOpened) :
    result = otherResult ∧ opened = otherOpened := by
  obtain ⟨effect, hbegin, execution⟩ := run
  obtain ⟨otherEffect, hotherBegin, otherExecution⟩ := other
  exact execution.deterministic ((RustM.ok.inj (hotherBegin.symm.trans hbegin)) ▸ otherExecution)

end beaconcrypt_core.ratchet.concrete
