-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationSigningContinuations
import BeaconcryptCore.PanicFreedom.RegistrationPublication
import BeaconcryptCore.PanicFreedom.RegistrationSigningContinuations
import BeaconcryptCore.Computational.MldsaTranscriptAuth

/-!
A chronological interpreter of the extracted hash/sign/publication phases. Its hash and signing oracles are explicit parameters; encoding success is an explicit reply. The outer native scheduler and the connection of these oracles to cryptographic implementations remain outside this interpreter theorem.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
open BeaconcryptCore.Refinement.RegistrationInputs

set_option autoImplicit false

namespace BeaconcryptCore.Refinement.RegistrationSigningTrace

open BeaconcryptCore.Computational

abbrev HashOracle := Pqxdh.Bytes → Std.Array Std.U8 64#usize
abbrev SignOracle := registration.MldsaSigningRequest → core.option.Option (Slice Std.U8)

/-- Typed oracle outputs induce the byte-level hash used by the existing origin theorem. -/
def hashBytesOracle (hash : HashOracle) : MldsaTranscriptAuth.Hash512 := fun bytes => absBytes (hash bytes)

def replyBytes : core.option.Option (Slice Std.U8) → Option Pqxdh.Bytes
  | .None => none
  | .Some bytes => some (TranscriptAuthParts.absSlice bytes)

/-- An attempted signing query records its actual selected key and exact unsigned preimage. -/
structure Observation where
  publicKey : Std.Array Std.U8 1952#usize
  payload : MldsaTranscriptAuth.Payload
  reply : Option Pqxdh.Bytes

def Observation.call (observation : Observation) : MldsaTranscriptAuth.SigningCall :=
  ⟨observation.payload, observation.reply⟩

/-- One key's log includes both roles, preserving their order and every failed reply. -/
def historyFor (publicKey : Pqxdh.Bytes) (observations : List Observation) : List MldsaTranscriptAuth.SigningCall :=
  observations.filterMap fun observation =>
    if absBytes observation.publicKey = publicKey then some observation.call else none

inductive Publication (Encoded : Type) where
  | beaconStopped (effect : registration.BeaconInitEffect)
  | beaconPublished (result : core.result.Result (registration.PublishedBeaconInit Encoded) pqxdh.BeaconFresh)
  | serverStopped (state : pqxdh.ServerState)
  | serverPublished (result : core.result.Result (registration.PublishedServerResponse Encoded) pqxdh.ServerState)

structure DispatchResult (Encoded : Type) where
  event : Option Observation
  outcome : Publication Encoded

/-- Submit the actual Beacon ML request, recording the query before interpreting its reply and publication. -/
def submitBeacon {Encoded : Type} (pending : registration.BeaconMldsaSigning)
    (payload : MldsaTranscriptAuth.Payload) (sign : SignOracle) (encoded : core.option.Option Encoded) :
    RustM (DispatchResult Encoded) := do
  let request ← pending.request
  let reply := sign request
  let event := some (Observation.mk request.public_key payload (replyBytes reply))
  let result ← pending.resume reply
  match result with
  | .Ready ready =>
      let published ← ready.publish encoded
      ok ⟨event, .beaconPublished published⟩
  | other => ok ⟨event, .beaconStopped other⟩

/-- The server uses the same chronological logging rule, including publication failure. -/
def submitServer {Encoded : Type} (pending : registration.ServerResponseSigning)
    (payload : MldsaTranscriptAuth.Payload) (sign : SignOracle) (encoded : core.option.Option Encoded) :
    RustM (DispatchResult Encoded) := do
  let request ← pending.request
  let reply := sign request
  let event := some (Observation.mk request.public_key payload (replyBytes reply))
  let result ← pending.resume reply
  match result with
  | .Ok ready =>
      let published ← ready.publish encoded
      ok ⟨event, .serverPublished published⟩
  | .Err previous => ok ⟨event, .serverStopped previous⟩

inductive Command where
  | beacon (hashing : registration.BeaconInitHash)
  | server (hashing : registration.ServerResponseHash)

/-- A source phase is hashed and resumed before its actual selected ML request is submitted. -/
def dispatch {Encoded : Type} (hash : HashOracle) (sign : SignOracle)
    (command : Command) (encoded : core.option.Option Encoded) : RustM (DispatchResult Encoded) := do
  match command with
  | .beacon hashing =>
      let request ← hashing.request
      let transcript := RegistrationInputs.hashBytes request
      let next ← hashing.resume (.Some (hash transcript))
      match next with
      | .MldsaSigningRequested pending => submitBeacon pending ⟨.beacon, transcript⟩ sign encoded
      | other => ok ⟨none, .beaconStopped other⟩
  | .server hashing =>
      let request ← hashing.request
      let transcript := RegistrationInputs.hashBytes request
      let next ← hashing.resume (.Some (hash transcript))
      match next with
      | .Ok pending => submitServer pending ⟨.server, transcript⟩ sign encoded
      | .Err previous => ok ⟨none, .serverStopped previous⟩

def beaconRequest (pending : registration.BeaconMldsaSigning) : registration.MldsaSigningRequest :=
  ⟨pending.state.beacon_mldsa, .Beacon, pending.input, authentication.SIGNING_CONTEXT⟩

def serverRequest (pending : registration.ServerResponseSigning) : registration.MldsaSigningRequest :=
  ⟨pending.binding.server_pin.public_key, .Server, pending.input, authentication.SIGNING_CONTEXT⟩

/-- Query recording is unconditional on signing success and on the later encoding/publication reply. -/
theorem submit_beacon_logs {Encoded : Type} (pending : registration.BeaconMldsaSigning)
    (payload : MldsaTranscriptAuth.Payload) (sign : SignOracle) (encoded : core.option.Option Encoded) :
    ∃ result, submitBeacon pending payload sign encoded = ok result ∧
      result.event = some ⟨pending.state.beacon_mldsa, payload, replyBytes (sign (beaconRequest pending))⟩ := by
  obtain ⟨effect, effectRun⟩ :=
    BeaconcryptCore.PanicFreedom.RegistrationSigningContinuations.BeaconMldsaSigning_resume_total
      pending (sign (beaconRequest pending))
  simp only [beaconRequest] at effectRun
  cases effect <;> simp only [submitBeacon, registration.BeaconMldsaSigning.request, effectRun, bind_tc_ok]
  all_goals try exact ⟨_, rfl, rfl⟩
  rename_i ready
  obtain ⟨published, publishRun⟩ :=
    BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconInitReady_publish_total ready encoded
  simp only [publishRun, bind_tc_ok]
  exact ⟨_, rfl, rfl⟩

theorem submit_server_logs {Encoded : Type} (pending : registration.ServerResponseSigning)
    (payload : MldsaTranscriptAuth.Payload) (sign : SignOracle) (encoded : core.option.Option Encoded) :
    ∃ result, submitServer pending payload sign encoded = ok result ∧
      result.event = some ⟨pending.binding.server_pin.public_key, payload,
        replyBytes (sign (serverRequest pending))⟩ := by
  obtain ⟨effect, effectRun⟩ :=
    BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerResponseSigning_resume_total
      pending (sign (serverRequest pending))
  have requestRun : pending.request = ok (serverRequest pending) := rfl
  cases effect <;> simp only [submitServer, requestRun, bind_tc_ok, effectRun]
  all_goals try exact ⟨_, rfl, rfl⟩
  case Ok ready =>
    obtain ⟨published, publishRun⟩ :=
      BeaconcryptCore.PanicFreedom.RegistrationTrivial.ServerResponseReady_publish_total ready encoded
    simp only [publishRun, bind_tc_ok]
    exact ⟨_, rfl, rfl⟩

def Command.request : Command → RustM registration.HashRequest
  | .beacon hashing => hashing.request
  | .server hashing => hashing.request

def Command.payload : Command → MldsaTranscriptAuth.Payload
  | .beacon hashing => ⟨.beacon, absBytes hashing.input⟩
  | .server hashing => ⟨.server, absBytes hashing.prefix ++
      TranscriptAuthParts.absSlice hashing.ciphertext ++ absBytes hashing.assigned_id⟩

def Command.publicKey : Command → Std.Array Std.U8 1952#usize
  | .beacon hashing => hashing.state.beacon_mldsa
  | .server hashing => hashing.binding.server_pin.public_key

def Command.role : Command → authentication.AuthRole
  | .beacon _ => .Beacon
  | .server _ => .Server

/-- The preimage recorded in a command is exactly the ordered bytes sent to its actual hash request. -/
theorem command_request_exact (command : Command) :
    ∃ request, command.request = ok request ∧ hashBytes request = command.payload.transcript := by
  cases command with
  | beacon hashing => exact ⟨_, rfl, rfl⟩
  | server hashing =>
    refine ⟨_, rfl, ?_⟩
    simp [hashBytes, TranscriptAuthParts.absParts, TranscriptAuthParts.absSlice,
      Command.payload, absBytes, Array.to_slice, Array.make, List.map, List.flatten, List.append_assoc]

end BeaconcryptCore.Refinement.RegistrationSigningTrace

/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningTrace.submit_beacon_logs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningTrace.submit_beacon_logs
/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningTrace.submit_server_logs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningTrace.submit_server_logs
/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningTrace.command_request_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningTrace.command_request_exact
