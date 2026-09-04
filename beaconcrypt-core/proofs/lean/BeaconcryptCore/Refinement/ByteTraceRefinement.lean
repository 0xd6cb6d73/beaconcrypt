import BeaconcryptCore.Refinement.RepresentationBridge
import BeaconcryptCore.Refinement.RatchetTraceRefinement

/-! Finite behavioral refinement from the extracted synchronous core driver to the unchanged PQXDH byte ratchet. API failures are explicit observations; successful records and plaintexts retain every byte. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet.concrete
open BeaconcryptCore.Refinement.RepresentationBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BeaconcryptCore.Refinement.ByteTraceRefinement

/-- Both byte-model role states, including every skipped key and nonce. -/
structure ByteRoleState where
  send : Ratchet.SendState Pqxdh.Bytes
  receive : Ratchet.RecvState Pqxdh.Bytes (Pqxdh.Bytes × Pqxdh.Bytes)

/-- Preserve all modeled state information at the byte boundary. -/
def mapRoleState (state : IdealRoleState) : ByteRoleState :=
  ⟨mapSend state.send, mapRecv state.receive⟩

abbrev ByteAction := APIAction Pqxdh.RecordAD Pqxdh.Bytes Pqxdh.Bytes
abbrev ByteObservation := APIObservation Pqxdh.Bytes Pqxdh.Bytes

/-- The unchanged PQXDH ratchet operations with explicit core API outcomes. Failed sealing performs an ideal send whose ciphertext is withheld, retaining its consumed index; exhaustion and invalid sequence zero leave the state unchanged. -/
def byteAction (c : Pqxdh.Crypto) (entry : ByteRoleState) (action : ByteAction) :
    ByteRoleState × ByteObservation :=
  match action with
  | .send ad plaintext sealed =>
      if entry.send.n = 2 ^ 64 - 1 then (entry, .exhausted)
      else
        let (message, next) := Ratchet.sendStep (Pqxdh.ratchetCrypto c) entry.send ad plaintext
        ({ entry with send := next }, if sealed then .sent message else .sealFailed message.idx)
  | .receive target ad ciphertext =>
      if target = 0#u64 then (entry, .invalidSequence)
      else
        let (output, next) := Ratchet.recvStep (Pqxdh.ratchetCrypto c) entry.receive ad ⟨target.val - 1, ciphertext⟩
        ({ entry with receive := next }, .received (receiveIdealPlaintext output))

/-- A byte-model execution retains one complete observation per API invocation. -/
def byteTrace (c : Pqxdh.Crypto) (entry : ByteRoleState) :
    List ByteAction → ByteRoleState × List ByteObservation
  | [] => (entry, [])
  | action :: actions =>
      let (next, output) := byteAction c entry action
      let (finalState, outputs) := byteTrace c next actions
      (finalState, output :: outputs)

/-- Every API outcome commutes with the byte representation, including consumed failed sends and explicit stutters. -/
theorem action_commutes (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (hlaw : KdfLaw c execute) (entry : IdealRoleState) (action : ByteAction) :
    (mapRoleState (idealAction (concreteCrypto c execute) entry action).1,
      (idealAction (concreteCrypto c execute) entry action).2) =
      byteAction c (mapRoleState entry) action := by
  cases action with
  | send ad plaintext sealed =>
    simp only [idealAction, byteAction, mapRoleState, mapSend]
    by_cases hmax : entry.send.n = 2 ^ 64 - 1 <;>
      simp only [hmax, if_true, if_false, Ratchet.sendStep, enc_commutes,
        kdfMsg_commutes c execute hlaw, kdfChain_commutes c execute hlaw]
  | receive target ad ciphertext =>
    by_cases hzero : target = 0#u64 <;>
      simp only [idealAction, byteAction, hzero, if_true, if_false, mapRoleState]
    rw [← recvStep_commutes c execute hlaw entry.receive ad ⟨target.val - 1, ciphertext⟩]

/-- Every finite API history preserves the complete byte-model state and every observation. -/
theorem trace_commutes (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (hlaw : KdfLaw c execute) (entry : IdealRoleState) (actions : List ByteAction) :
    (mapRoleState (idealTrace (concreteCrypto c execute) entry actions).1,
      (idealTrace (concreteCrypto c execute) entry actions).2) =
      byteTrace c (mapRoleState entry) actions := by
  induction actions generalizing entry with
  | nil => rfl
  | cons action actions ih =>
    simp only [idealTrace, byteTrace, ← action_commutes c execute hlaw]
    rw [← ih]

/-- Every finite execution from a represented kernel terminates and has a corresponding byte-model execution with identical observations and related final states. -/
theorem executeTrace_refines (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (hlaw : KdfLaw c execute) (origin : Pqxdh.Bytes) (ideal : ByteRoleState)
    (entry : ConcreteRatchetKernel)
    (h : ByteKernelRefines c execute origin ideal.send ideal.receive entry)
    (actions : List ByteAction) :
    ∃ result, executeTrace (recordCrypto c) execute entry actions =
        ok (result, (byteTrace c ideal actions).2) ∧
      ByteKernelRefines c execute origin (byteTrace c ideal actions).1.send
        (byteTrace c ideal actions).1.receive result := by
  rcases h with ⟨concreteOrigin, send, receive, horigin, hsend, hreceive, h⟩
  have hrole : mapRoleState ⟨send, receive⟩ = ideal := by
    cases ideal
    simp_all only [mapRoleState]
  obtain ⟨result, hrun, hresult⟩ := h.executeTrace_refines (recordCrypto c) execute
    concreteOrigin ⟨send, receive⟩ entry actions
  rw [← hrole, ← trace_commutes c execute hlaw]
  exact ⟨result, hrun, _, _, _, horigin, rfl, rfl, hresult⟩

/-- Every actual completed driver evaluation has exactly the byte-model trace and a related final kernel. Existence and termination are supplied by `executeTrace_refines`. -/
theorem executeTrace_observed (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (hlaw : KdfLaw c execute) (origin : Pqxdh.Bytes) (ideal : ByteRoleState)
    (entry result : ConcreteRatchetKernel)
    (h : ByteKernelRefines c execute origin ideal.send ideal.receive entry)
    (actions : List ByteAction) (observations : List ByteObservation)
    (hactual : executeTrace (recordCrypto c) execute entry actions = ok (result, observations)) :
    observations = (byteTrace c ideal actions).2 ∧
      ByteKernelRefines c execute origin (byteTrace c ideal actions).1.send
        (byteTrace c ideal actions).1.receive result := by
  obtain ⟨canonical, hcanonical, hresult⟩ := executeTrace_refines c execute hlaw origin ideal entry h actions
  have heq := Prod.mk.inj (RustM.ok.inj (hactual.symm.trans hcanonical))
  exact ⟨heq.2, heq.1.symm ▸ hresult⟩

/-- Transfer of universal predicates on finite input/output traces and represented final byte states. This theorem supplies the related final state; no implementation property or refinement claim is assumed. -/
theorem transfer_finite_property (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (hlaw : KdfLaw c execute) (origin : Pqxdh.Bytes) (ideal : ByteRoleState)
    (entry : ConcreteRatchetKernel)
    (h : ByteKernelRefines c execute origin ideal.send ideal.receive entry)
    (property : List ByteAction → List ByteObservation → ByteRoleState → Prop)
    (hmodel : ∀ actions, property actions (byteTrace c ideal actions).2 (byteTrace c ideal actions).1)
    (actions : List ByteAction) (result : ConcreteRatchetKernel) (observations : List ByteObservation)
    (hactual : executeTrace (recordCrypto c) execute entry actions = ok (result, observations)) :
    ∃ finalIdeal : ByteRoleState, ByteKernelRefines c execute origin finalIdeal.send finalIdeal.receive result ∧
      property actions observations finalIdeal := by
  obtain ⟨hobservations, hresult⟩ := executeTrace_observed c execute hlaw origin ideal entry result h actions observations hactual
  exact ⟨(byteTrace c ideal actions).1, hresult, hobservations.symm ▸ hmodel actions⟩

/-- The existing ideal ratchet's well-formedness theorem is preserved by every API outcome. -/
theorem byteAction_recvWf (c : Pqxdh.Crypto) (entry : ByteRoleState)
    (h : Ratchet.RecvWf entry.receive) (action : ByteAction) :
    Ratchet.RecvWf (byteAction c entry action).1.receive := by
  cases action with
  | send ad plaintext sealed =>
    by_cases hmax : entry.send.n = 2 ^ 64 - 1 <;> simpa only [byteAction, hmax, if_true, if_false] using h
  | receive target ad ciphertext =>
    by_cases hzero : target = 0#u64
    · simpa only [byteAction, hzero, if_true] using h
    · simpa only [byteAction, hzero, if_false] using h.recvStep (c := Pqxdh.ratchetCrypto c) ad ⟨target.val - 1, ciphertext⟩

/-- The existing ideal receive invariant holds after every finite byte-model history. -/
theorem byteTrace_recvWf (c : Pqxdh.Crypto) (entry : ByteRoleState)
    (h : Ratchet.RecvWf entry.receive) (actions : List ByteAction) :
    Ratchet.RecvWf (byteTrace c entry actions).1.receive := by
  induction actions generalizing entry with
  | nil => exact h
  | cons action actions ih => exact ih (byteAction c entry action).1 (byteAction_recvWf c entry h action)

/-- The complete receive invariant of the unchanged byte model transfers to every actual extracted history, including the bounded skipped-key store, past-only indices, and no duplicate skipped indices. -/
theorem executeTrace_recvWf (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (hlaw : KdfLaw c execute) (origin : Pqxdh.Bytes) (ideal : ByteRoleState)
    (entry result : ConcreteRatchetKernel)
    (h : ByteKernelRefines c execute origin ideal.send ideal.receive entry)
    (hwf : Ratchet.RecvWf ideal.receive) (actions : List ByteAction) (observations : List ByteObservation)
    (hactual : executeTrace (recordCrypto c) execute entry actions = ok (result, observations)) :
    ∃ finalIdeal : ByteRoleState, ByteKernelRefines c execute origin finalIdeal.send finalIdeal.receive result ∧
      Ratchet.RecvWf finalIdeal.receive :=
  transfer_finite_property c execute hlaw origin ideal entry h
    (fun _ _ finalState => Ratchet.RecvWf finalState.receive)
    (fun actions => byteTrace_recvWf c ideal hwf actions) actions result observations hactual

/-- A real optional seal callback satisfying only successful-record correctness refines the byte API for some actual seal outcome. Failure is unrestricted and may consume the next key; the result kernel and optional ciphertext come from the actual extracted driver evaluation. -/
theorem sealNext_callback_refines (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (hlaw : KdfLaw c execute) (origin : Pqxdh.Bytes) (ideal : ByteRoleState)
    (entry result : ConcreteRatchetKernel)
    (h : ByteKernelRefines c execute origin ideal.send ideal.receive entry)
    (ad : Pqxdh.RecordAD) (plaintext : Pqxdh.Bytes)
    (sealReply : ratchet.RatchetMaterial → Std.U64 → Unit → core.option.Option Pqxdh.Bytes)
    (hcorrect : ∀ material sequence context ciphertext,
      sealReply material sequence context = .Some ciphertext →
      ciphertext = (concreteCrypto c execute).enc material ad plaintext)
    (output : core.option.Option Pqxdh.Bytes)
    (hactual : sealNext execute entry () sealReply = ok (result, output)) :
    ∃ sealed, observeSend entry.refined.control.send_sequence output =
        (byteAction c ideal (.send ad plaintext sealed)).2 ∧
      ByteKernelRefines c execute origin (byteAction c ideal (.send ad plaintext sealed)).1.send
        (byteAction c ideal (.send ad plaintext sealed)).1.receive result := by
  have hentry := h
  obtain ⟨concreteOrigin, send, receive, _, _, _, hkernel⟩ := h
  obtain ⟨sealed, hcovered⟩ := hkernel.sealNext_callback_covered (recordCrypto c) execute
    concreteOrigin ⟨send, receive⟩ entry ad plaintext sealReply hcorrect
  have htrace : executeTrace (recordCrypto c) execute entry [.send ad plaintext sealed] =
      ok (result, [observeSend entry.refined.control.send_sequence output]) := by
    simp! only [executeTrace, executeAction, ← hcovered, hactual, bind_tc_ok]
  refine ⟨sealed, ?_⟩
  simpa only [byteTrace, List.cons.injEq, and_true] using
    executeTrace_observed c execute hlaw origin ideal entry result hentry _ _ htrace

/--
info: 'BeaconcryptCore.Refinement.ByteTraceRefinement.executeTrace_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms executeTrace_refines

/--
info: 'BeaconcryptCore.Refinement.ByteTraceRefinement.transfer_finite_property' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms transfer_finite_property

/--
info: 'BeaconcryptCore.Refinement.ByteTraceRefinement.sealNext_callback_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms sealNext_callback_refines

end BeaconcryptCore.Refinement.ByteTraceRefinement
