import BeaconcryptCore.Refinement.ProtocolComposition
import BeaconcryptCore.Refinement.BoundaryExecution

/-! Complete beacon registration followed by an arbitrary finite history with actual primitive callbacks. Registration errors halt before the history; successful registration supplies the actual kernel used by every subsequent extracted operation. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet.concrete PqxdhRefinement
open BeaconcryptCore.Refinement.PqxdhConcreteSession
open BeaconcryptCore.Refinement.RepresentationBridge
open BeaconcryptCore.Refinement.ProtocolComposition
open BeaconcryptCore.Refinement.ByteTraceRefinement
open BeaconcryptCore.Refinement.BoundaryExecution

set_option autoImplicit false

namespace BeaconcryptCore.Refinement.ProtocolHistory

abbrev HistoryResult := Except Pqxdh.BeaconError
  (pqxdh.BeaconEstablished × ConcreteRatchetKernel × List ByteObservation)

/-- Sequence the checked registration driver and actual callback-driven finite ratchet driver without resetting or replacing the established kernel. -/
noncomputable def completeHistory (c : Pqxdh.Crypto)
    (derive : pqxdh.RootKeyInput → Std.Array Std.U8 32#usize)
    (initial : InitialKdfInterpreter) (execute : KdfInterpreter)
    (state : pqxdh.BeaconInitSent) (inputs : pqxdh.BeaconFinishInputs)
    (sender target : Std.U64) (ciphertext : Pqxdh.Bytes) (actions : List Action) :
    RustM HistoryResult := do
  let registered ← completeBeacon (concreteCrypto c execute) derive initial execute
    state inputs sender target ciphertext
  match registered with
  | .error error => ok (.error error)
  | .ok (established, kernel) =>
      let (finalState, observations) ← runTrace execute kernel actions
      ok (.ok (established, finalState, observations))

/-- Exact registration error or exact assigned identity followed by byte-model observations and a fully represented final state. -/
def HistoryResultRefines (c : Pqxdh.Crypto) (execute : KdfInterpreter) (ikSk : Pqxdh.Bytes)
    (actions : List Action) (result : HistoryResult)
    (idealRegistration : Except Pqxdh.BeaconError Nat × Pqxdh.BeaconState) : Prop :=
  match result with
  | .error error => idealRegistration = (.error error, .aborted)
  | .ok (established, finalState, observations) =>
      ∃ origin send receive byteActions,
        idealRegistration = (.ok established.assigned_key_id.val,
          .established (absBinding established.server_binding) ikSk established.assigned_key_id.val
            (Pqxdh.assocData (absBytes established.server_binding.identity_public_key) (c.edPub ikSk))
            send receive) ∧
        byteActions.map byteInvocation = actions.map invocation ∧
        observations = (byteTrace c ⟨send, receive⟩ byteActions).2 ∧
        ByteKernelRefines c execute origin (byteTrace c ⟨send, receive⟩ byteActions).1.send
          (byteTrace c ⟨send, receive⟩ byteActions).1.receive finalState

/-- Every typed registration outcome and arbitrary subsequent finite history terminates and has exact ideal registration and byte-ratchet observations. -/
theorem completeHistory_refines (c : Pqxdh.Crypto)
    (derive : pqxdh.RootKeyInput → Std.Array Std.U8 32#usize)
    (initial : InitialKdfInterpreter) (execute : KdfInterpreter)
    (hrootLaw : RootKdfLaw c derive) (hinitial : InitialKdfLaw c initial) (hstep : KdfLaw c execute)
    (state : pqxdh.BeaconInitSent) (inputs : pqxdh.BeaconFinishInputs)
    (sender target : Std.U64) (response : Pqxdh.KexResponse)
    (ikSk preSk otSk kemSk ikSX : Pqxdh.Bytes)
    (hboundary : BeaconBoundary c state inputs sender target response ikSk preSk otSk kemSk ikSX)
    (actions : List Action) (hcorrect : ∀ action ∈ actions, Correct c execute action) :
    ∃ result, completeHistory c derive initial execute state inputs sender target
        response.appFrame.cipherText actions = ok result ∧
      HistoryResultRefines c execute ikSk actions result
        (Pqxdh.beaconFinish c (.initSent (absBinding state.expected_server_binding) ikSk preSk otSk kemSk) response) := by
  obtain ⟨registered, hregister, hrelated⟩ := completeBeacon_refines c derive initial execute
    hrootLaw hinitial hstep state inputs sender target response ikSk preSk otSk kemSk ikSX hboundary
  cases registered with
  | ok registered =>
      obtain ⟨established, kernel⟩ := registered
      obtain ⟨origin, send, receive, hkernel, hmodel⟩ := hrelated
      have hbyte : ByteKernelRefines c execute (absChain origin) (mapSend send) (mapRecv receive) kernel :=
        ⟨origin, send, receive, rfl, rfl, rfl, hkernel⟩
      obtain ⟨byteActions, finalState, hinputs, htrace, hfinal⟩ := BoundaryExecution.runTrace_refines c execute hstep
        (absChain origin) ⟨mapSend send, mapRecv receive⟩ kernel hbyte actions hcorrect
      exact ⟨.ok (established, finalState, (byteTrace c ⟨mapSend send, mapRecv receive⟩ byteActions).2),
        by simp [completeHistory, hregister, htrace],
        absChain origin, mapSend send, mapRecv receive, byteActions, hmodel, hinputs, rfl, hfinal⟩
  | error error =>
      exact ⟨.error error, by simp [completeHistory, hregister], hrelated⟩

/-- The composed correspondence holds for every actual evaluation, not just the witness constructed by the termination theorem. -/
theorem completeHistory_observed (c : Pqxdh.Crypto)
    (derive : pqxdh.RootKeyInput → Std.Array Std.U8 32#usize)
    (initial : InitialKdfInterpreter) (execute : KdfInterpreter)
    (hrootLaw : RootKdfLaw c derive) (hinitial : InitialKdfLaw c initial) (hstep : KdfLaw c execute)
    (state : pqxdh.BeaconInitSent) (inputs : pqxdh.BeaconFinishInputs)
    (sender target : Std.U64) (response : Pqxdh.KexResponse)
    (ikSk preSk otSk kemSk ikSX : Pqxdh.Bytes)
    (hboundary : BeaconBoundary c state inputs sender target response ikSk preSk otSk kemSk ikSX)
    (actions : List Action) (hcorrect : ∀ action ∈ actions, Correct c execute action) (result : HistoryResult)
    (hactual : completeHistory c derive initial execute state inputs sender target
      response.appFrame.cipherText actions = ok result) :
    HistoryResultRefines c execute ikSk actions result
      (Pqxdh.beaconFinish c (.initSent (absBinding state.expected_server_binding) ikSk preSk otSk kemSk) response) := by
  obtain ⟨canonical, hcanonical, hrelated⟩ := completeHistory_refines c derive initial execute
    hrootLaw hinitial hstep state inputs sender target response ikSk preSk otSk kemSk ikSX hboundary actions hcorrect
  exact (RustM.ok.inj (hcanonical.symm.trans hactual)) ▸ hrelated

/--
info: 'BeaconcryptCore.Refinement.ProtocolHistory.completeHistory_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms completeHistory_observed

end BeaconcryptCore.Refinement.ProtocolHistory
