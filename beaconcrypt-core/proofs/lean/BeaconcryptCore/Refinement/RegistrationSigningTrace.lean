-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationSigningContinuations
import BeaconcryptCore.PanicFreedom.RegistrationTrivial
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

/-- One key's log preserves all prior Server response signing attempts and every failed reply. -/
def historyFor (publicKey : Pqxdh.Bytes) (observations : List Observation) : List MldsaTranscriptAuth.SigningCall :=
  observations.filterMap fun observation =>
    if absBytes observation.publicKey = publicKey then some observation.call else none

inductive Publication (Encoded : Type) where
  | serverStopped (state : pqxdh.ServerState)
  | serverPublished (result : core.result.Result (registration.PublishedServerResponse Encoded) pqxdh.ServerState)

structure DispatchResult (Encoded : Type) where
  event : Option Observation
  outcome : Publication Encoded

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
  | server (hashing : registration.ServerResponseHash)

/-- A source phase is hashed and resumed before its actual selected ML request is submitted. -/
def dispatch {Encoded : Type} (hash : HashOracle) (sign : SignOracle)
    (command : Command) (encoded : core.option.Option Encoded) : RustM (DispatchResult Encoded) := do
  match command with
  | .server hashing =>
      let request ← hashing.request
      let transcript := RegistrationInputs.hashBytes request
      let next ← hashing.resume (.Some (hash transcript))
      match next with
      | .Ok pending => submitServer pending ⟨.server, transcript⟩ sign encoded
      | .Err previous => ok ⟨none, .serverStopped previous⟩

def serverRequest (pending : registration.ServerResponseSigning) : registration.MldsaSigningRequest :=
  ⟨pending.binding.server_pin.public_key, .Server, pending.input, authentication.SIGNING_CONTEXT⟩

/-- Query recording is unconditional on signing success and on the later encoding/publication reply. -/
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
  | .server hashing => hashing.request

def Command.payload : Command → MldsaTranscriptAuth.Payload
  | .server hashing => ⟨.server, absBytes hashing.prefix ++
      TranscriptAuthParts.absSlice hashing.ciphertext ++ absBytes hashing.assigned_id⟩

def Command.publicKey : Command → Std.Array Std.U8 1952#usize
  | .server hashing => hashing.binding.server_pin.public_key

def Command.role : Command → authentication.AuthRole
  | .server _ => .Server

/-- The preimage recorded in a command is exactly the ordered bytes sent to its actual hash request. -/
theorem command_request_exact (command : Command) :
    ∃ request, command.request = ok request ∧ hashBytes request = command.payload.transcript := by
  cases command with
  | server hashing =>
    refine ⟨_, rfl, ?_⟩
    simp [hashBytes, TranscriptAuthParts.absParts, TranscriptAuthParts.absSlice,
      Command.payload, absBytes, Array.to_slice, Array.make, List.map, List.flatten, List.append_assoc]

end BeaconcryptCore.Refinement.RegistrationSigningTrace

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
