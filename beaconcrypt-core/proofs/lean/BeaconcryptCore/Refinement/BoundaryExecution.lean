import BeaconcryptCore.Refinement.ByteTraceRefinement

/-! Finite executions with actual optional crypto callbacks. Each send may fail independently and as a function of its material; the proof selects only that outcome annotation while preserving every supplied plaintext, ciphertext, associated-data value, and sequence. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet.concrete
open BeaconcryptCore.Refinement.RepresentationBridge
open BeaconcryptCore.Refinement.ByteTraceRefinement

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BeaconcryptCore.Refinement.BoundaryExecution

/-- Public invocation inputs, excluding the externally chosen result of sealing. -/
inductive Invocation where
  | send (ad : Pqxdh.RecordAD) (plaintext : Pqxdh.Bytes)
  | receive (target : Std.U64) (ad : Pqxdh.RecordAD) (ciphertext : Pqxdh.Bytes)

/-- The same invocation fields are retained when a byte action additionally records its seal outcome. -/
def byteInvocation : ByteAction → Invocation
  | .send ad plaintext _ => .send ad plaintext
  | .receive target ad ciphertext => .receive target ad ciphertext

/-- Actual external callbacks supplied to complete extracted operations. -/
inductive Action where
  | send (ad : Pqxdh.RecordAD) (plaintext : Pqxdh.Bytes)
      (reply : ratchet.RatchetMaterial → Std.U64 → Unit → core.option.Option Pqxdh.Bytes)
  | receive (target : Std.U64) (ad : Pqxdh.RecordAD) (ciphertext : Pqxdh.Bytes)
      (reply : ReceiveOpen Unit → core.option.Option Pqxdh.Bytes)

/-- Every non-callback action input is retained verbatim. -/
def invocation : Action → Invocation
  | .send ad plaintext _ => .send ad plaintext
  | .receive target ad ciphertext _ => .receive target ad ciphertext

/-- Primitive-only callback contracts. Sealing may fail without restriction; successful results must be the complete expected record. Opening must return exactly the byte model's authenticated plaintext for the material supplied by the extracted accessor, including rejection. -/
def Correct (c : Pqxdh.Crypto) (execute : KdfInterpreter) : Action → Prop
  | .send ad plaintext reply => ∀ material sequence context ciphertext,
      reply material sequence context = .Some ciphertext →
        ciphertext = (concreteCrypto c execute).enc material ad plaintext
  | .receive _ ad ciphertext reply => ∀ pending,
      reply pending = receiveIdealOpenReply (concreteCrypto c execute) ad ciphertext pending

/-- Execute the supplied callbacks on the actual extracted phase composition and retain its exact API observation. -/
noncomputable def runAction (execute : KdfInterpreter) (entry : ConcreteRatchetKernel) :
    Action → RustM (ConcreteRatchetKernel × ByteObservation)
  | .send _ _ reply => do
      let (next, output) ← sealNext execute entry () reply
      ok (next, observeSend entry.refined.control.send_sequence output)
  | .receive target _ _ reply => do
      let (next, output) ← receiveNext execute entry target () reply
      ok (next, if target = 0#u64 then .invalidSequence else .received output)

/-- Execute a finite mixed history with independently supplied callbacks at every invocation. -/
noncomputable def runTrace (execute : KdfInterpreter) (entry : ConcreteRatchetKernel) :
    List Action → RustM (ConcreteRatchetKernel × List ByteObservation)
  | [] => ok (entry, [])
  | action :: actions => do
      let (next, output) ← runAction execute entry action
      let (finalState, outputs) ← runTrace execute next actions
      ok (finalState, output :: outputs)

/-- Every legitimate actual callback invocation is covered by a byte action with identical inputs. Only the actual seal outcome is selected. -/
theorem action_covered (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (origin : Pqxdh.Bytes) (ideal : ByteRoleState) (entry : ConcreteRatchetKernel)
    (h : ByteKernelRefines c execute origin ideal.send ideal.receive entry)
    (action : Action) (hcorrect : Correct c execute action) :
    ∃ byteAction, byteInvocation byteAction = invocation action ∧
      runAction execute entry action = executeAction (recordCrypto c) execute entry byteAction := by
  cases action with
  | send ad plaintext reply =>
    obtain ⟨concreteOrigin, send, receive, _, _, _, hkernel⟩ := h
    obtain ⟨sealed, hcovered⟩ := hkernel.sealNext_callback_covered (recordCrypto c) execute
      concreteOrigin ⟨send, receive⟩ entry ad plaintext reply hcorrect
    exact ⟨.send ad plaintext sealed, rfl, by simp only [runAction, executeAction, hcovered]⟩
  | receive target ad ciphertext reply =>
    exact ⟨.receive target ad ciphertext, rfl, by
      simp only [runAction, executeAction, funext hcorrect, concreteCrypto]⟩

private theorem byteAction_refines (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (hlaw : KdfLaw c execute) (origin : Pqxdh.Bytes) (ideal : ByteRoleState)
    (entry : ConcreteRatchetKernel)
    (h : ByteKernelRefines c execute origin ideal.send ideal.receive entry)
    (action : ByteAction) :
    ∃ result, executeAction (recordCrypto c) execute entry action =
        ok (result, (byteAction c ideal action).2) ∧
      ByteKernelRefines c execute origin (byteAction c ideal action).1.send
        (byteAction c ideal action).1.receive result := by
  rcases h with ⟨concreteOrigin, send, receive, horigin, hsend, hreceive, h⟩
  have hrole : mapRoleState ⟨send, receive⟩ = ideal := by
    cases ideal
    simp_all only [mapRoleState]
  obtain ⟨result, hrun, hresult⟩ := h.executeAction_refines (recordCrypto c) execute
    concreteOrigin ⟨send, receive⟩ entry action
  rw [← hrole, ← action_commutes c execute hlaw]
  exact ⟨result, hrun, _, _, _, horigin, rfl, rfl, hresult⟩

/-- Every finite history of legitimate actual callbacks terminates and has a byte-model history. All invocation inputs and every observation are preserved, and the final kernel remains related to the full byte state. Send failure choices may vary arbitrarily by invocation and reached material. -/
theorem runTrace_refines (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (hlaw : KdfLaw c execute) (origin : Pqxdh.Bytes) (ideal : ByteRoleState)
    (entry : ConcreteRatchetKernel)
    (h : ByteKernelRefines c execute origin ideal.send ideal.receive entry)
    (actions : List Action) (hcorrect : ∀ action ∈ actions, Correct c execute action) :
    ∃ byteActions result,
      byteActions.map byteInvocation = actions.map invocation ∧
      runTrace execute entry actions = ok (result, (byteTrace c ideal byteActions).2) ∧
      ByteKernelRefines c execute origin (byteTrace c ideal byteActions).1.send
        (byteTrace c ideal byteActions).1.receive result := by
  induction actions generalizing ideal entry with
  | nil => exact ⟨[], entry, rfl, rfl, h⟩
  | cons action actions ih =>
    obtain ⟨selected, hinput, hcovered⟩ := action_covered c execute origin ideal entry h action
      (hcorrect action (by simp))
    obtain ⟨next, hnext, hnextRefines⟩ := byteAction_refines c execute hlaw origin ideal entry h selected
    obtain ⟨selectedTail, result, hinputs, htail, hfinal⟩ :=
      ih (byteAction c ideal selected).1 next hnextRefines (fun a ha => hcorrect a (by simp [ha]))
    exact ⟨selected :: selectedTail, result, by simp only [List.map_cons, hinput, hinputs],
      by simp! only [runTrace, hcovered, hnext, bind_tc_ok, htail, byteTrace], hfinal⟩

/-- Any actual completed callback history has a matching byte execution with identical inputs and observations and a fully related final state. -/
theorem runTrace_observed (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (hlaw : KdfLaw c execute) (origin : Pqxdh.Bytes) (ideal : ByteRoleState)
    (entry result : ConcreteRatchetKernel)
    (h : ByteKernelRefines c execute origin ideal.send ideal.receive entry)
    (actions : List Action) (hcorrect : ∀ action ∈ actions, Correct c execute action)
    (observations : List ByteObservation)
    (hactual : runTrace execute entry actions = ok (result, observations)) :
    ∃ byteActions,
      byteActions.map byteInvocation = actions.map invocation ∧
      observations = (byteTrace c ideal byteActions).2 ∧
      ByteKernelRefines c execute origin (byteTrace c ideal byteActions).1.send
        (byteTrace c ideal byteActions).1.receive result := by
  obtain ⟨selected, canonical, hinputs, hcanonical, hresult⟩ :=
    runTrace_refines c execute hlaw origin ideal entry h actions hcorrect
  have heq := Prod.mk.inj (RustM.ok.inj (hactual.symm.trans hcanonical))
  exact ⟨selected, hinputs, heq.2, heq.1.symm ▸ hresult⟩

/-- Universal finite properties of invocation inputs, exact observations, and final byte states transfer to histories with arbitrary legitimate actual callbacks. A model property must hold for every possible seal-outcome schedule. -/
theorem transfer_finite_property (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (hlaw : KdfLaw c execute) (origin : Pqxdh.Bytes) (ideal : ByteRoleState)
    (entry : ConcreteRatchetKernel)
    (h : ByteKernelRefines c execute origin ideal.send ideal.receive entry)
    (property : List Invocation → List ByteObservation → ByteRoleState → Prop)
    (hmodel : ∀ byteActions, property (byteActions.map byteInvocation)
      (byteTrace c ideal byteActions).2 (byteTrace c ideal byteActions).1)
    (actions : List Action) (hcorrect : ∀ action ∈ actions, Correct c execute action)
    (result : ConcreteRatchetKernel) (observations : List ByteObservation)
    (hactual : runTrace execute entry actions = ok (result, observations)) :
    ∃ finalIdeal : ByteRoleState,
      ByteKernelRefines c execute origin finalIdeal.send finalIdeal.receive result ∧
      property (actions.map invocation) observations finalIdeal := by
  obtain ⟨selected, hinputs, hobservations, hresult⟩ :=
    runTrace_observed c execute hlaw origin ideal entry result h actions hcorrect observations hactual
  exact ⟨(byteTrace c ideal selected).1, hresult, by simpa only [hinputs, ← hobservations] using hmodel selected⟩

/--
info: 'BeaconcryptCore.Refinement.BoundaryExecution.runTrace_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms runTrace_refines

/--
info: 'BeaconcryptCore.Refinement.BoundaryExecution.transfer_finite_property' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms transfer_finite_property

end BeaconcryptCore.Refinement.BoundaryExecution
