import BeaconcryptCore.Refinement.PqxdhConcreteSession
import BeaconcryptCore.Refinement.PqxdhProtocol
import BeaconcryptCore.Refinement.RatchetRoleReachability

/-! Failed first-record sealing and the atomic ideal server boundary. An aborted candidate must retain the previous allocation state; it cannot refine a successful atomic serverEmit. The optional-publication closure is stated separately from the unchanged model. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
open BeaconcryptCore.Refinement.PqxdhConcreteSession

set_option autoImplicit false

namespace BeaconcryptCore.Refinement.ServerTransactionRefinement

/-- Result of the candidate transaction; only successful publication exposes a peer and its advanced kernel. -/
inductive CandidateResult (Ciphertext : Type) where
  | sealFailed (state : pqxdh.ServerState)
  | published (state : pqxdh.ServerState) (peer : pqxdh.EstablishedPeer)
      (kernel : ratchet.concrete.ConcreteRatchetKernel) (ciphertext : Ciphertext)

/-- Candidate-bound server initialization uses the actual extracted candidate request constructor. -/
def initializeCandidate (candidate : pqxdh.ServerRegistrationCandidate)
    (root : Std.Array Std.U8 32#usize) (initial : InitialKdfInterpreter) :
    RustM ratchet.concrete.ConcreteRatchetKernel := do
  let pending ← pqxdh.concrete.start_server_candidate_ratchet_kdf candidate root
  pqxdh.concrete.resume_initial_ratchet_kdf pending (initial pending.request)

theorem initializeCandidate_eq (candidate : pqxdh.ServerRegistrationCandidate)
    (root : Std.Array Std.U8 32#usize) (initial : InitialKdfInterpreter) :
    initializeCandidate candidate root initial = initializeServer root initial := rfl

/-- Compose extracted initialization, actual first-send phases, and extracted candidate commit or abort. -/
def finishCandidate {Ciphertext : Type} (candidate : pqxdh.ServerRegistrationCandidate)
    (root : Std.Array Std.U8 32#usize) (initial : InitialKdfInterpreter)
    (execute : ratchet.concrete.KdfInterpreter)
    (sealReply : ratchet.RatchetMaterial → Std.U64 → Unit → core.option.Option Ciphertext) :
    RustM (CandidateResult Ciphertext) := do
  let initialized ← initializeCandidate candidate root initial
  let (advanced, output) ← ratchet.concrete.sealNext execute initialized () sealReply
  match output with
  | .None =>
      let state ← pqxdh.server_abort_candidate candidate
      ok (.sealFailed state)
  | .Some ciphertext =>
      let (state, peer) ← pqxdh.server_commit candidate
      ok (.published state peer advanced ciphertext)

/-- Failure of the actual first seal discards the transient advanced ratchet and returns exactly the candidate's previous server state. -/
theorem finishCandidate_failed {AD PT CT Ciphertext : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (candidate : pqxdh.ServerRegistrationCandidate) (root : Std.Array Std.U8 32#usize)
    (initial : InitialKdfInterpreter) (execute : ratchet.concrete.KdfInterpreter) :
    finishCandidate candidate root initial execute (fun _ _ _ => (core.option.Option.None : core.option.Option Ciphertext)) =
      ok (.sealFailed candidate.previous_state) := by
  obtain ⟨beaconOrigin, serverOrigin, beacon, server, _, hinitial, _, _, _, hs⟩ :=
    initial_kernels_refine (ratchet.concrete.withInterpreter cr execute) root initial
  have hmax : server.refined.control.send_sequence ≠ core.num.U64.MAX := by
    intro hmax
    have hv := congrArg UScalar.val hmax
    have hz := hs.sendSequence
    simp only at hz
    rw [hz] at hv
    contradiction
  obtain ⟨pending, hbegin, hpending⟩ := ratchet.concrete.begin_send_refines
    (ratchet.concrete.withInterpreter cr execute) beaconOrigin ⟨serverOrigin, 0⟩
    ⟨beaconOrigin, 0, []⟩ server () hs hmax
  obtain ⟨ready, hresume, hready⟩ := ratchet.concrete.SendKdf.resume_refines
    (ratchet.concrete.withInterpreter cr execute) beaconOrigin ⟨serverOrigin, 0⟩
    ⟨beaconOrigin, 0, []⟩ server () pending hpending (execute pending.request)
    (ratchet.concrete.interpreter_request_refines cr execute serverOrigin pending.request
      hpending.requestInput hpending.requestInfo)
  simp only [finishCandidate, initializeCandidate_eq, hinitial, bind_tc_ok, ratchet.concrete.sealNext,
    hbegin, hresume, ratchet.concrete.SendSeal.finish_returns_interpreter_result,
    pqxdh.server_abort_candidate]
  rfl

/-- Exact obstruction to an atomic serverEmit refinement: on a free nonexhausted identifier, the ideal counter increments but a failed concrete candidate returns its old counter. -/
theorem failed_candidate_differs_from_atomic_emit (c : Pqxdh.Crypto)
    (entry : Pqxdh.ServerState) (candidate : pqxdh.ServerRegistrationCandidate)
    (ikB root kemCipher ephemeral application : Pqxdh.Bytes)
    (hcounter : candidate.previous_state.last_key_id.val = entry.n)
    (hmax : entry.n ≠ Pqxdh.maxKeyId)
    (hfree : ¬ (entry.peers.lookup (entry.n + 1)).isSome) :
    (Pqxdh.serverEmit c entry ikB root kemCipher ephemeral application).2.n ≠
      candidate.previous_state.last_key_id.val := by
  simp only [Pqxdh.serverEmit, if_neg hmax, if_neg hfree, hcounter]
  omega

/-- API publication observations preserve every emitted response and distinguish an externally failed seal from a core rejection. -/
inductive PublicationObservation where
  | rejected (error : Pqxdh.ServerError)
  | sealFailed
  | published (response : Pqxdh.KexResponse)

/-- Map an atomic ideal result without erasing any response or error. -/
def atomicObservation : Except Pqxdh.ServerError Pqxdh.KexResponse → PublicationObservation
  | .error error => .rejected error
  | .ok response => .published response

/-- Optional publication at the already consumed replay-token prefix. This is an explicit abort closure, not a new theorem equating aborted calls to atomic serverRespond. -/
def idealPublication (c : Pqxdh.Crypto) (entry : Pqxdh.ServerState)
    (ikB root kemCipher ephemeral application : Pqxdh.Bytes) (sealed : Bool) :
    PublicationObservation × Pqxdh.ServerState :=
  let (output, next) := Pqxdh.serverEmit c entry ikB root kemCipher ephemeral application
  match output with
  | .error error => (.rejected error, next)
  | .ok response => if sealed then (.published response, next) else (.sealFailed, entry)

/-- When publication succeeds, the closure is exactly the unchanged atomic ideal result and state. -/
theorem idealPublication_completed (c : Pqxdh.Crypto) (entry : Pqxdh.ServerState)
    (ikB root kemCipher ephemeral application : Pqxdh.Bytes) :
    idealPublication c entry ikB root kemCipher ephemeral application true =
      (atomicObservation (Pqxdh.serverEmit c entry ikB root kemCipher ephemeral application).1,
        (Pqxdh.serverEmit c entry ikB root kemCipher ephemeral application).2) := by
  unfold idealPublication
  cases h : Pqxdh.serverEmit c entry ikB root kemCipher ephemeral application with
  | mk output next => cases output <;> rfl

/-- On a permitted but externally failed publication, all server state remains at the explicit consumed-token prefix. -/
theorem idealPublication_failed (c : Pqxdh.Crypto) (entry : Pqxdh.ServerState)
    (ikB root kemCipher ephemeral application : Pqxdh.Bytes)
    (hmax : entry.n ≠ Pqxdh.maxKeyId)
    (hfree : ¬ (entry.peers.lookup (entry.n + 1)).isSome) :
    idealPublication c entry ikB root kemCipher ephemeral application false =
      (.sealFailed, entry) := by
  simp [idealPublication, Pqxdh.serverEmit, hmax, hfree]

/-- A state property preserved by the atomic emission also survives the explicit abort closure, provided it holds at the consumed-token entry. No assertion about a desired concrete refinement is assumed. -/
theorem idealPublication_preserves (c : Pqxdh.Crypto) (entry : Pqxdh.ServerState)
    (ikB root kemCipher ephemeral application : Pqxdh.Bytes) (sealed : Bool)
    (property : Pqxdh.ServerState → Prop) (hentry : property entry)
    (hatomic : property (Pqxdh.serverEmit c entry ikB root kemCipher ephemeral application).2) :
    property (idealPublication c entry ikB root kemCipher ephemeral application sealed).2 := by
  unfold idealPublication
  cases h : Pqxdh.serverEmit c entry ikB root kemCipher ephemeral application with
  | mk output next =>
      cases output <;> cases sealed <;> simp_all only [Bool.false_eq_true, if_false, if_true]

end BeaconcryptCore.Refinement.ServerTransactionRefinement
