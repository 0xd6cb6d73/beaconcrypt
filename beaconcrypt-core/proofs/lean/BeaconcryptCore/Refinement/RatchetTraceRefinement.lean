import BeaconcryptCore.Refinement.RatchetLifetime
import BeaconcryptCore.Refinement.RatchetReceiveIdeal

/-! Observable behavioral refinement of complete synchronous core operations. The ideal API boundary invokes the unchanged ratchet operations, recording failed sealing as a consumed ideal send and treating bounded-counter exhaustion and invalid wire sequence zero as explicit stutters. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace beaconcrypt_core.ratchet.concrete

/-- Inputs to complete core operations. The Boolean records the external seal outcome; successful replies contain precisely the ideal encryption. -/
inductive APIAction (AD PT CT : Type) where
  | send (ad : AD) (plaintext : PT) (sealed : Bool)
  | receive (target : Std.U64) (ad : AD) (ciphertext : CT)

/-- Observable API results, with failure causes and consumed send indices reconstructed from the entry counter. Receive rejection retains the API's absent-plaintext granularity. -/
inductive APIObservation (PT CT : Type) where
  | sent (message : Ratchet.Msg CT)
  | sealFailed (index : Nat)
  | exhausted
  | received (plaintext : core.option.Option PT)
  | invalidSequence

/-- Both ideal chains, counters, and the complete skipped-key store. -/
structure IdealRoleState where
  send : Ratchet.SendState RatchetChain
  receive : Ratchet.RecvState RatchetChain RatchetMaterial

/-- A successful seal callback returns the ideal ciphertext; failure is represented by the actual optional return value. -/
def apiSealReply {AD PT CT : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (ad : AD) (plaintext : PT) (sealed : Bool)
    (material : RatchetMaterial) (_sequence : Std.U64) (_context : Unit) :
    core.option.Option CT :=
  if sealed then .Some (cr.enc material ad plaintext) else .None

/-- Instrumentation of a send's actual result, retaining the successful wire message and distinguishing whether an absent output consumed an index. -/
def observeSend {PT CT : Type} (sequence : Std.U64) (output : core.option.Option CT) :
    APIObservation PT CT :=
  match output with
  | .Some ciphertext => .sent ⟨sequence.val, ciphertext⟩
  | .None => if sequence = core.num.U64.MAX then .exhausted else .sealFailed sequence.val

/-- Run only the established compositions of extracted admission, request, resume, and finish definitions, then annotate their actual outputs. -/
noncomputable def executeAction {AD PT CT : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (entry : ConcreteRatchetKernel) (action : APIAction AD PT CT) :
    RustM (ConcreteRatchetKernel × APIObservation PT CT) := do
  match action with
  | .send ad plaintext sealed =>
      let (next, output) ← sealNext execute entry ()
        (apiSealReply (withInterpreter cr execute) ad plaintext sealed)
      ok (next, observeSend entry.refined.control.send_sequence output)
  | .receive target ad ciphertext =>
      let (next, output) ← receiveNext execute entry target ()
        (receiveIdealOpenReply (withInterpreter cr execute) ad ciphertext)
      ok (next, if target = 0#u64 then .invalidSequence else .received output)

/-- Execute a finite sequence of complete core operations, recording every result. -/
noncomputable def executeTrace {AD PT CT : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (entry : ConcreteRatchetKernel) : List (APIAction AD PT CT) →
    RustM (ConcreteRatchetKernel × List (APIObservation PT CT))
  | [] => ok (entry, [])
  | action :: actions => do
      let (next, output) ← executeAction cr execute entry action
      let (finalState, outputs) ← executeTrace cr execute next actions
      ok (finalState, output :: outputs)

/-- The API wrapper executes an actual ideal send even if sealing fails: its ciphertext is withheld, but its consumed index and successor state remain observable. Exhaustion and invalid zero sequence are named stutters. -/
def idealAction {AD PT CT : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (entry : IdealRoleState) (action : APIAction AD PT CT) :
    IdealRoleState × APIObservation PT CT :=
  match action with
  | .send ad plaintext sealed =>
      if entry.send.n = 2 ^ 64 - 1 then (entry, .exhausted)
      else
        let (message, next) := Ratchet.sendStep cr entry.send ad plaintext
        ({ entry with send := next }, if sealed then .sent message else .sealFailed message.idx)
  | .receive target ad ciphertext =>
      if target = 0#u64 then (entry, .invalidSequence)
      else
        let (output, next) := Ratchet.recvStep cr entry.receive ad ⟨target.val - 1, ciphertext⟩
        ({ entry with receive := next }, .received (receiveIdealPlaintext output))

/-- The complete ideal run retains one observation for each API invocation. -/
def idealTrace {AD PT CT : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (entry : IdealRoleState) : List (APIAction AD PT CT) →
    IdealRoleState × List (APIObservation PT CT)
  | [] => (entry, [])
  | action :: actions =>
      let (next, output) := idealAction cr entry action
      let (finalState, outputs) := idealTrace cr next actions
      (finalState, output :: outputs)

/-- Every complete API operation terminates with the ideal observation and full represented ideal successor state. -/
theorem KernelRefines.executeAction_refines {AD PT CT : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (origin : RatchetChain) (ideal : IdealRoleState) (entry : ConcreteRatchetKernel)
    (h : KernelRefines (withInterpreter cr execute) origin ideal.send ideal.receive entry)
    (action : APIAction AD PT CT) :
    ∃ result, executeAction cr execute entry action =
        ok (result, (idealAction (withInterpreter cr execute) ideal action).2) ∧
      KernelRefines (withInterpreter cr execute) origin
        (idealAction (withInterpreter cr execute) ideal action).1.send
        (idealAction (withInterpreter cr execute) ideal action).1.receive result := by
  cases action with
  | send ad plaintext sealed =>
      by_cases hmax : entry.refined.control.send_sequence = core.num.U64.MAX
      · have hidealMax : ideal.send.n = 18446744073709551615 :=
          h.sendSequence.symm.trans (congrArg UScalar.val hmax)
        exact ⟨entry, by simp [executeAction, sealNext,
          begin_send_exhausted_restores_entry entry () hmax, observeSend, hmax,
          idealAction, hidealMax], by simpa [idealAction, hidealMax] using h⟩
      · obtain ⟨pending, hbegin, hpending⟩ := begin_send_refines (withInterpreter cr execute)
          origin ideal.send ideal.receive entry () h hmax
        obtain ⟨ready, hresume, hready⟩ := SendKdf.resume_refines (withInterpreter cr execute)
          origin ideal.send ideal.receive entry () pending hpending (execute pending.request)
          (interpreter_request_refines cr execute ideal.send.ck pending.request
            hpending.requestInput hpending.requestInfo)
        have hidealMax : ideal.send.n ≠ 18446744073709551615 := by
          exact fun heq => hmax (UScalar.eq_of_val_eq (h.sendSequence.trans heq))
        refine ⟨ready.advanced, ?_, ?_⟩
        · cases sealed <;> simp [executeAction, sealNext, hbegin, hresume,
            SendSeal.finish_returns_interpreter_result, apiSealReply, observeSend,
            idealAction, hidealMax, hmax, hready.material, h.sendSequence, Ratchet.sendStep]
        · simpa [idealAction, hidealMax, Ratchet.sendStep] using hready.advanced
  | receive target ad ciphertext =>
      by_cases hzero : target = 0#u64
      · have hrun : ReceiveRun execute
            (receiveIdealOpenReply (withInterpreter cr execute) ad ciphertext)
            entry 0#u64 () entry core.option.Option.None :=
          ⟨_, h.begin_receive_zero (withInterpreter cr execute) origin ideal.send ideal.receive
            entry (), ReceiveExecution.rejected entry ()⟩
        exact ⟨entry, by simp [executeAction, hzero, hrun.driver_eq, idealAction],
          by simpa [idealAction, hzero] using h⟩
      · have hpositive : 0 < target.val :=
          Nat.pos_of_ne_zero (fun heq => hzero (UScalar.eq_of_val_eq heq))
        obtain ⟨result, hrun, hresult, _⟩ := h.receive_ideal cr execute origin ideal.send
          ideal.receive entry () target hpositive ad ciphertext
        exact ⟨result, by simp! only [executeAction, hrun, bind_tc_ok, hzero, ↓reduceIte,
          idealAction], by simpa only [idealAction, hzero, ↓reduceIte] using hresult⟩

/-- Every finite mixed history terminates and matches every ideal API observation, retaining both chains, counters, and all skipped materials through the full state relation. -/
theorem KernelRefines.executeTrace_refines {AD PT CT : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (origin : RatchetChain) (ideal : IdealRoleState) (entry : ConcreteRatchetKernel)
    (h : KernelRefines (withInterpreter cr execute) origin ideal.send ideal.receive entry)
    (actions : List (APIAction AD PT CT)) :
    ∃ result, executeTrace cr execute entry actions =
        ok (result, (idealTrace (withInterpreter cr execute) ideal actions).2) ∧
      KernelRefines (withInterpreter cr execute) origin
        (idealTrace (withInterpreter cr execute) ideal actions).1.send
        (idealTrace (withInterpreter cr execute) ideal actions).1.receive result := by
  induction actions generalizing ideal entry with
  | nil => exact ⟨entry, rfl, h⟩
  | cons action actions ih =>
      obtain ⟨next, hstep, hnext⟩ := h.executeAction_refines cr execute origin ideal entry action
      obtain ⟨result, htail, hresult⟩ := ih (idealAction (withInterpreter cr execute) ideal action).1 next hnext
      exact ⟨result, by simp! only [executeTrace, hstep, bind_tc_ok, htail, idealTrace], hresult⟩

/-- Correspondence holds for any actual successful driver evaluation, not just the witness chosen by the existence proof. -/
theorem KernelRefines.executeTrace_observed {AD PT CT : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (origin : RatchetChain) (ideal : IdealRoleState) (entry result : ConcreteRatchetKernel)
    (h : KernelRefines (withInterpreter cr execute) origin ideal.send ideal.receive entry)
    (actions : List (APIAction AD PT CT)) (observations : List (APIObservation PT CT))
    (hactual : executeTrace cr execute entry actions = ok (result, observations)) :
    observations = (idealTrace (withInterpreter cr execute) ideal actions).2 ∧
      KernelRefines (withInterpreter cr execute) origin
        (idealTrace (withInterpreter cr execute) ideal actions).1.send
        (idealTrace (withInterpreter cr execute) ideal actions).1.receive result := by
  obtain ⟨canonical, hcanonical, hresult⟩ := h.executeTrace_refines cr execute origin ideal entry actions
  have heq := Prod.mk.inj (RustM.ok.inj (hactual.symm.trans hcanonical))
  exact ⟨heq.2, heq.1.symm ▸ hresult⟩

/-- Any universal finite input/output trace property of the ideal API semantics transfers to actual evaluations under the explicit observation abstraction. -/
theorem KernelRefines.transfer_trace_property {AD PT CT : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (origin : RatchetChain) (ideal : IdealRoleState) (entry : ConcreteRatchetKernel)
    (h : KernelRefines (withInterpreter cr execute) origin ideal.send ideal.receive entry)
    (property : List (APIAction AD PT CT) → List (APIObservation PT CT) → Prop)
    (hmodel : ∀ actions, property actions (idealTrace (withInterpreter cr execute) ideal actions).2)
    (actions : List (APIAction AD PT CT)) (result : ConcreteRatchetKernel)
    (observations : List (APIObservation PT CT))
    (hactual : executeTrace cr execute entry actions = ok (result, observations)) :
    property actions observations :=
  (h.executeTrace_observed cr execute origin ideal entry result actions observations hactual).1.symm ▸ hmodel actions

/-- The successful-send ciphertext can be recovered exactly from the observation; failure annotations preserve the absent output. -/
def sentCiphertext {PT CT : Type} : APIObservation PT CT → core.option.Option CT
  | .sent message => .Some message.ct
  | _ => .None

/-- Send instrumentation does not discard or invent the actual optional ciphertext. -/
theorem observeSend_ciphertext {PT CT : Type} (sequence : Std.U64)
    (output : core.option.Option CT) : sentCiphertext (observeSend (PT := PT) sequence output) = output := by
  by_cases hmax : sequence = core.num.U64.MAX <;> cases output <;> simp [observeSend, sentCiphertext, hmax]

/-- The send observation is computed from the actual phase driver's optional ciphertext and entry counter. -/
theorem executeAction_send_eq {AD PT CT : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (entry result : ConcreteRatchetKernel) (ad : AD) (plaintext : PT) (sealed : Bool)
    (output : core.option.Option CT)
    (hrun : sealNext execute entry () (apiSealReply (withInterpreter cr execute) ad plaintext sealed) =
      ok (result, output)) :
    executeAction cr execute entry (.send ad plaintext sealed) =
      ok (result, observeSend entry.refined.control.send_sequence output) := by
  simp [executeAction, hrun]

/-- Every positive-sequence receive observation retains the actual phase driver's complete optional plaintext. -/
theorem executeAction_receive_eq {AD PT CT : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (entry result : ConcreteRatchetKernel) (target : Std.U64) (ad : AD) (ciphertext : CT)
    (output : core.option.Option PT) (hpositive : target ≠ 0#u64)
    (hrun : receiveNext execute entry target ()
      (receiveIdealOpenReply (withInterpreter cr execute) ad ciphertext) = ok (result, output)) :
    executeAction cr execute entry (.receive target ad ciphertext) = ok (result, .received output) := by
  simp [executeAction, hrun, hpositive]

/-- Every actual seal callback satisfying only the successful-encryption primitive contract is represented by a Boolean outcome for this invocation. No state or trace correspondence is assumed. -/
theorem KernelRefines.sealNext_callback_covered {AD PT CT : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (origin : RatchetChain) (ideal : IdealRoleState) (entry : ConcreteRatchetKernel)
    (h : KernelRefines (withInterpreter cr execute) origin ideal.send ideal.receive entry)
    (ad : AD) (plaintext : PT)
    (sealReply : RatchetMaterial → Std.U64 → Unit → core.option.Option CT)
    (hcorrect : ∀ material sequence context ciphertext,
      sealReply material sequence context = .Some ciphertext →
      ciphertext = (withInterpreter cr execute).enc material ad plaintext) :
    ∃ sealed, sealNext execute entry () sealReply =
      sealNext execute entry () (apiSealReply (withInterpreter cr execute) ad plaintext sealed) := by
  by_cases hmax : entry.refined.control.send_sequence = core.num.U64.MAX
  · exact ⟨false, by simp [sealNext, begin_send_exhausted_restores_entry entry () hmax]⟩
  · obtain ⟨pending, hbegin, hpending⟩ := begin_send_refines (withInterpreter cr execute)
      origin ideal.send ideal.receive entry () h hmax
    obtain ⟨ready, hresume, _⟩ := SendKdf.resume_refines (withInterpreter cr execute)
      origin ideal.send ideal.receive entry () pending hpending (execute pending.request)
      (interpreter_request_refines cr execute ideal.send.ck pending.request
        hpending.requestInput hpending.requestInfo)
    cases hreply : sealReply ready.material ready.sequence ready.context with
    | none =>
        exact ⟨false, by simp [sealNext, hbegin, hresume, SendSeal.finish_returns_interpreter_result,
          hreply, apiSealReply]⟩
    | some ciphertext =>
        exact ⟨true, by simp [sealNext, hbegin, hresume, SendSeal.finish_returns_interpreter_result,
          hreply, apiSealReply, hcorrect ready.material ready.sequence ready.context ciphertext hreply]⟩

end beaconcrypt_core.ratchet.concrete
