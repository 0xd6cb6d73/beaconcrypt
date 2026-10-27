-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.KeyAgreement
import BeaconcryptCore.Refinement.RegistrationPublication
import BeaconcryptCore.Refinement.PeerCollections

/-!
Exact source ownership and collection effects of server registration. Primitive replies and native collection operations remain external. The collection results below use explicit faithful entry/set laws and retain the complete peer and allocation state; no correctness theorem for HashMap, allocation, or durable installation is assumed or claimed.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
open BeaconcryptCore.Refinement.PeerCollections

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BeaconcryptCore.Refinement.PeerOwnership

/-- The trusted restoration/wrapping boundary preserves the supplied complete binding and exact ratchet owner. -/
theorem peer_from_trusted_parts {Ratchet : Type} (binding : session.SessionBinding) (ratchet : Ratchet) :
    peer.Peer.from_trusted_parts binding ratchet = ok (⟨binding, ratchet⟩ : peer.Peer Ratchet) := by
  rfl

/-- Every observer reads the same immutable binding and the ratchet stored with it. -/
theorem peer_observers {Ratchet : Type} (owner : peer.Peer Ratchet) :
    owner.key_id = ok owner.binding.assigned_key_id ∧
      peer.Peer.impl.binding owner = ok owner.binding ∧
      peer.Peer.impl.ratchet owner = ok owner.ratchet ∧
      owner.into_parts = ok (owner.binding, owner.ratchet) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Returning a mutable ratchet borrow updates only that ratchet; every authenticated binding byte stays owned by the same peer. -/
theorem peer_ratchet_borrow {Ratchet : Type} (owner : peer.Peer Ratchet) :
    owner.ratchet_mut = ok (owner.ratchet, fun updated => { owner with ratchet := updated }) := by
  rfl

/-- Core retains the exact authenticated request and allocation entry before requesting replay membership. -/
theorem registration_lookup_begin (control : pqxdh.ServerState)
    (authenticated : registration.AuthenticatedInit) :
    peer.begin_registration_lookup control authenticated = ok ⟨control, authenticated⟩ := by
  rfl

/-- Replay membership is requested for the identifier computed from this retained authenticated input. -/
theorem registration_lookup_request (pending : peer.RegistrationLookup) :
    pending.request = pqxdh.registration_id pending.authenticated.registration := by
  rfl

/-- The actual membership request has the canonical authenticated identity/one-time-key replay bytes. -/
theorem registration_lookup_request_bytes (pending : peer.RegistrationLookup) :
    ∃ identifier, pending.request = ok identifier ∧
      absBytes identifier.bytes = (absVerified pending.authenticated.registration).rid := by
  exact registration_id_abs pending.authenticated.registration

/-- A consumed reply rejects before emitting any primitive request. -/
theorem registration_lookup_consumed (pending : peer.RegistrationLookup) :
    pending.resume true = ok (.Rejected .None) := by
  rfl

/-- A fresh reply starts the existing agreement machine with the same allocation entry and authenticated fields. -/
theorem registration_lookup_fresh (pending : peer.RegistrationLookup) :
    pending.resume false = agreement.begin_server_agreement pending.control .Fresh pending.authenticated := by
  rfl

/-- The insertion continuation is created from completed shared-secret preparation and retains that exact agreement. -/
theorem registration_insert_begin (accepted : agreement.ServerAgreement) :
    peer.begin_registration_insert accepted = ok ⟨accepted⟩ := by
  rfl

/-- Replay insertion selects the identifier belonging to the completed agreement. -/
theorem registration_insert_request (pending : peer.RegistrationInsert) :
    pending.request = ok pending.agreement.pending.registration_id := by
  rfl

/-- Only an actual successful set insertion yields the one-use response capability, with no independent agreement argument. -/
theorem registration_insert_resume (pending : peer.RegistrationInsert) (inserted : Bool) :
    pending.resume inserted = ok (if inserted then .Some ⟨pending.agreement⟩ else .None) := by
  cases inserted <;> rfl

/-- The completion lookup returns its retained source-selected peer identifier. -/
theorem completion_lookup_request (pending : peer.CompletionLookup) :
    pending.request = ok pending.key_id := by
  rfl

/-- The occupancy reply changes only availability; the exact consumed agreement, owner pin, application, and entry control select completion. -/
theorem completion_lookup_resume (pending : peer.CompletionLookup) (occupied : Bool) :
    pending.resume occupied = registration.begin_server_completion pending.control pending.pin
      (if occupied then .Occupied else .Available) pending.registration.agreement pending.application := by
  cases occupied <;> rfl

/-- The next-ID reply is retained together with the same consumed capability and all completion inputs. -/
theorem completion_lookup_begin_next (control : pqxdh.ServerState)
    (pin : session.ServerAuthenticationPin) (registration : peer.ConsumedRegistration)
    (application : Slice Std.U8) (next : Std.U64)
    (nextRun : pqxdh.server_next_key_id control = ok (.Ok next)) :
    peer.begin_completion_lookup control pin registration application =
      ok (.Ok ⟨control, pin, registration, application, next⟩) := by
  simp [peer.begin_completion_lookup, nextRun]

/-- Exhaustion returns the caller's entry control before any peer lookup is requested. -/
theorem completion_lookup_begin_exhausted (control : pqxdh.ServerState)
    (pin : session.ServerAuthenticationPin) (registration : peer.ConsumedRegistration)
    (application : Slice Std.U8) (exhausted : control.last_key_id = core.num.U64.MAX) :
    peer.begin_completion_lookup control pin registration application = ok (.Err control) := by
  simp [peer.begin_completion_lookup, pqxdh.server_next_key_id, exhausted]

/-- A nonexhausted entry requests the mathematical successor of its actual live counter and preserves every other completion input. -/
theorem completion_lookup_live_successor (control : pqxdh.ServerState)
    (pin : session.ServerAuthenticationPin) (registration : peer.ConsumedRegistration)
    (application : Slice Std.U8) (available : control.last_key_id ≠ core.num.U64.MAX) :
    ∃ pending, peer.begin_completion_lookup control pin registration application = ok (.Ok pending) ∧
      pending.control = control ∧ pending.pin = pin ∧ pending.registration = registration ∧
      pending.application = application ∧ pending.key_id.val = control.last_key_id.val + 1 := by
  exact (BeaconcryptCore.Refinement.PqxdhSurface.next_server_key_id_success control available).elim
    fun next facts => ⟨⟨control, pin, registration, application, next⟩,
      completion_lookup_begin_next control pin registration application next facts.1,
      rfl, rfl, rfl, rfl, facts.2⟩

/-- Every successful source insertion setup retains the published peer and bytes; a stale allocation reply cannot replace its live entry control. -/
def insertionRetains {Encoded : Type} (control : pqxdh.ServerState)
    (published : registration.PublishedServerResponse Encoded) :
    core.result.Result (peer.PeerInsert Encoded) pqxdh.ServerState → Prop
  | .Err previous => previous = control
  | .Ok pending => pending.previous = control ∧ pending.next = published.control ∧
      pending.peer.binding = published.binding ∧ pending.peer.ratchet = published.kernel ∧
      pending.encoded = published.encoded ∧
      pqxdh.server_next_key_id control = ok (.Ok pending.next.last_key_id)

/-- Insertion setup checks the live counter before transferring the actual published binding, kernel, and encoded output. -/
theorem peer_insert_begin_retains {Encoded : Type} (control : pqxdh.ServerState)
    (published : registration.PublishedServerResponse Encoded) :
    ∃ result, peer.begin_peer_insert control published = ok result ∧ insertionRetains control published result := by
  obtain ⟨next, nextRun⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok control
  cases next
  · simp only [peer.begin_peer_insert, nextRun, registration.PublishedServerResponse.into_parts,
      pqxdh.ServerState.impl.last_key_id, peer.Peer.from_trusted_parts, bind_tc_ok]
    dsimp! only
    split
    · exact ⟨.Err control, rfl, rfl⟩
    · refine ⟨.Ok ⟨control, published.control, ⟨published.binding, published.kernel⟩, published.encoded⟩,
        rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      simp_all
      scalar_tac
  · exact ⟨.Err control, by simp [peer.begin_peer_insert, nextRun], rfl⟩

/-- The actual insertion request selects the identifier of the peer retained by that capability. -/
theorem peer_insert_request {Encoded : Type} (pending : peer.PeerInsert Encoded) :
    pending.request = ok pending.peer.binding.assigned_key_id := by
  rfl

/-- Splitting an insertion transfers its exact complete peer and retains only the matching allocation and encoded-output publication rights. -/
theorem peer_insert_parts {Encoded : Type} (pending : peer.PeerInsert Encoded) :
    pending.into_parts = ok (pending.peer,
      (⟨pending.previous, pending.next, pending.peer.binding.assigned_key_id, pending.encoded⟩ :
        peer.PublicationFinish Encoded)) := by
  rfl

/-- Rejection returns the exact entry allocation state; successful insertion publishes its retained successor, peer identifier, and bytes. -/
theorem publication_finish {Encoded : Type} (pending : peer.PublicationFinish Encoded) (inserted : Bool) :
    pending.finish inserted = ok (if inserted then
      .Ok ⟨pending.next, pending.key_id, pending.encoded⟩ else .Err pending.previous) := by
  cases inserted <;> rfl

/-- The final published observation keeps the complete successor state and actual encoded output. -/
theorem published_peer_parts {Encoded : Type} (published : peer.PublishedPeer Encoded) :
    published.into_parts = ok (published.control, published.key_id, published.encoded) := by
  rfl

/-- Execute the actual core transfer and publication continuations around the native insertion reply. -/
def finishInsertion {Encoded : Type} (pending : peer.PeerInsert Encoded) (inserted : Bool) :
    RustM (core.result.Result (pqxdh.ServerState × Std.U64 × Encoded) pqxdh.ServerState) := do
  let (_, finish) ← pending.into_parts
  let result ← finish.finish inserted
  match result with
  | .Err previous => ok (.Err previous)
  | .Ok published =>
    let parts ← published.into_parts
    ok (.Ok parts)

/-- Exact source composition retains allocation, identifier and bytes on success and returns entry allocation on failure. -/
theorem finish_insertion_exact {Encoded : Type} (pending : peer.PeerInsert Encoded) (inserted : Bool) :
    finishInsertion pending inserted = ok (if inserted then
      .Ok (pending.next, pending.peer.binding.assigned_key_id, pending.encoded)
      else .Err pending.previous) := by
  cases inserted <;> rfl

/-- The functional collection observation of this exact core insertion outcome. -/
def collectionPublication {Encoded : Type} (pending : peer.PeerInsert Encoded)
    (before after : PeerMap (peer.Peer ratchet.concrete.ConcreteRatchetKernel)) :
    core.result.Result (pqxdh.ServerState × Std.U64 × Encoded) pqxdh.ServerState → Prop
  | .Err previous => previous = pending.previous ∧ after = before
  | .Ok (next, identifier, encoded) => next = pending.next ∧
      identifier = pending.peer.binding.assigned_key_id ∧ encoded = pending.encoded ∧
      before identifier.val = none ∧ after = publishAt before identifier.val pending.peer

/-- Under the explicit vacant-entry laws, the actual source result publishes exactly its owned peer or preserves the complete entry map and counter. -/
theorem collection_insertion_refines {Encoded : Type} (pending : peer.PeerInsert Encoded)
    (before after : PeerMap (peer.Peer ratchet.concrete.ConcreteRatchetKernel)) (inserted : Bool)
    (faithful : FaithfulFreshInsert before pending.peer.binding.assigned_key_id.val
      pending.peer inserted after) :
    ∃ result, finishInsertion pending inserted = ok result ∧ collectionPublication pending before after result := by
  cases inserted
  · exact ⟨.Err pending.previous, finish_insertion_exact pending false, rfl, faithful.failed rfl⟩
  · exact (faithful_success before _ pending.peer true after faithful rfl).elim
      fun free changed => ⟨.Ok (pending.next, pending.peer.binding.assigned_key_id, pending.encoded),
        finish_insertion_exact pending true, rfl, rfl, rfl, free, changed⟩

/-- The actual replay reply controls the response capability while the faithful native set operation consumes exactly the retained agreement's identifier. -/
theorem registration_insert_collection (pending : peer.RegistrationInsert)
    (before after : ReplaySet) (inserted : Bool)
    (faithful : FaithfulReplayInsert before (absBytes pending.agreement.pending.registration_id.bytes)
      inserted after) :
    pending.request = ok pending.agreement.pending.registration_id ∧
      pending.resume inserted = ok (if inserted then .Some ⟨pending.agreement⟩ else .None) ∧
      after = consumeAt before (absBytes pending.agreement.pending.registration_id.bytes) := by
  exact ⟨registration_insert_request pending, registration_insert_resume pending inserted,
    faithful_replay_effect before _ inserted after faithful⟩

/-- Interpret the actual retained lookup request against an extensional replay-set observation. -/
def replayLookupWith (pending : peer.RegistrationLookup) (consumed : ReplaySet) :
    RustM agreement.AgreementEffect := do
  let identifier ← pending.request
  pending.resume (consumed (absBytes identifier.bytes))

/-- Once the actual agreement identifier has been inserted, a lookup of that same authenticated identifier rejects before primitive work. This holds even if its later response capability was dropped or publication failed. -/
theorem replay_lookup_after_insert (pending : peer.RegistrationInsert) (lookup : peer.RegistrationLookup)
    (before after : ReplaySet) (inserted : Bool)
    (sameRequest : lookup.request = pending.request)
    (faithful : FaithfulReplayInsert before (absBytes pending.agreement.pending.registration_id.bytes)
      inserted after) :
    replayLookupWith lookup after = ok (.Rejected .None) := by
  simp [replayLookupWith, sameRequest, registration_insert_request, faithful.selected,
    registration_lookup_consumed]

/-- Completing the actual server root-KDF continuation retains the candidate's identifier and complete binding in the replay-insertion capability. The source clears the root preimage before this capability exists. -/
theorem root_completion_replay_origin (candidate : pqxdh.PendingServerRegistration)
    (binding : session.RegistrationBinding) (root : Array Std.U8 32#usize) :
    ∃ accepted : agreement.ServerAgreement,
      agreement.RootKdfPending.resume ⟨.Server candidate binding⟩ (.Some root) =
        ok (.ServerComplete accepted) ∧
      peer.begin_registration_insert accepted = ok ⟨accepted⟩ ∧
      peer.RegistrationInsert.request ⟨accepted⟩ = ok candidate.registration_id ∧
      accepted.binding = binding ∧
      accepted.pending.root_key_input.bytes = Array.repeat 192#usize 0#u8 := by
  exact ⟨⟨{ candidate with root_key_input := ⟨Array.repeat 192#usize 0#u8⟩ }, binding, ⟨root⟩⟩,
    BeaconcryptCore.Refinement.KeyAgreement.root_success_refines ⟨.Server candidate binding⟩ root,
    rfl, rfl, rfl, rfl⟩

/-- Every candidate obtained from actual preparation fixes its next counter and peer identifier to the same checked live successor. -/
theorem prepared_candidate_allocation (control : pqxdh.ServerState)
    (accepted : pqxdh.PendingServerRegistration) (binding : pqxdh.ServerBinding)
    (availability : pqxdh.KeyIdAvailability) (candidate : pqxdh.ServerRegistrationCandidate)
    (prepared : pqxdh.server_prepare_commit control accepted binding availability = ok (.Ok candidate)) :
    candidate.previous_state = control ∧ candidate.next_state.last_key_id = candidate.key_id ∧
      pqxdh.server_next_key_id control = ok (.Ok candidate.key_id) := by
  obtain ⟨next, nextRun⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok control
  obtain ⟨ad, adRun⟩ := BeaconcryptCore.PanicFreedom.build_associated_data_ok
    binding.identity_public_key accepted.beacon_identity_public_key
  simp only [pqxdh.server_prepare_commit, array_eq_abs, nextRun, adRun, bind_tc_ok] at prepared
  cases next <;> cases availability <;> split_ifs at prepared <;> simp_all [bind_tc_ok]
  all_goals simp [← prepared]

/-- Execute the actual encoding-publication gate before requesting insertion. -/
def prepareInsertion {Encoded : Type} (control : pqxdh.ServerState)
    (ready : registration.ServerResponseReady) (encoded : core.option.Option Encoded) :
    RustM (core.result.Result (peer.PeerInsert Encoded) pqxdh.ServerState) := do
  let result ← ready.publish encoded
  match result with
  | .Err previous => ok (.Err previous)
  | .Ok published => peer.begin_peer_insert control published

/-- Encoding failure does not yield an insertion request or a completed publication capability. -/
theorem prepare_insertion_encoding_failure {Encoded : Type} (control : pqxdh.ServerState)
    (ready : registration.ServerResponseReady) :
    prepareInsertion control ready (.None : core.option.Option Encoded) = ok (.Err ready.candidate.previous_state) := by
  rfl

/-- The peer transferred by actual response publication contains the exact retained full authenticated binding, AD, source-owned ratchet and encoded reply. Its identifier/counter agreement is derived from actual candidate preparation. -/
theorem prepared_response_insertion {Encoded : Type} (control : pqxdh.ServerState)
    (accepted : pqxdh.PendingServerRegistration) (binding : pqxdh.ServerBinding)
    (availability : pqxdh.KeyIdAvailability) (ready : registration.ServerResponseReady) (encoded : Encoded)
    (prepared : pqxdh.server_prepare_commit control accepted binding availability = ok (.Ok ready.candidate)) :
    ∃ pending, prepareInsertion control ready (.Some encoded) = ok (.Ok pending) ∧
      pending.previous = control ∧ pending.next = ready.candidate.next_state ∧
      pending.peer.binding = BeaconcryptCore.Refinement.RegistrationPublication.completedBinding
        ready.binding ready.candidate.key_id ∧ pending.peer.ratchet = ready.kernel ∧
      pending.peer.binding.assigned_key_id = pending.next.last_key_id ∧ pending.encoded = encoded := by
  obtain ⟨previous, sameId, nextRun⟩ := prepared_candidate_allocation control accepted binding availability
    ready.candidate prepared
  refine ⟨⟨control, ready.candidate.next_state,
    ⟨BeaconcryptCore.Refinement.RegistrationPublication.completedBinding ready.binding ready.candidate.key_id,
      ready.kernel⟩, encoded⟩, ?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
  · simp [prepareInsertion, BeaconcryptCore.Refinement.RegistrationPublication.server_publication_refines,
      peer.begin_peer_insert, nextRun, registration.PublishedServerResponse.into_parts,
      pqxdh.ServerState.impl.last_key_id, sameId, peer.Peer.from_trusted_parts]
  · exact sameId.symm

/-- Complete source-to-collection publication: the response's actual prepared candidate supplies the full peer, and faithful vacant insertion either preserves the entire entry context or publishes the same peer identifier and successor counter together. -/
theorem prepared_publication_collection {Encoded : Type} (control : pqxdh.ServerState)
    (accepted : pqxdh.PendingServerRegistration) (binding : pqxdh.ServerBinding)
    (availability : pqxdh.KeyIdAvailability) (ready : registration.ServerResponseReady) (encoded : Encoded)
    (prepared : pqxdh.server_prepare_commit control accepted binding availability = ok (.Ok ready.candidate)) :
    ∃ pending, prepareInsertion control ready (.Some encoded) = ok (.Ok pending) ∧
      pending.peer.binding = BeaconcryptCore.Refinement.RegistrationPublication.completedBinding
        ready.binding ready.candidate.key_id ∧ pending.peer.ratchet = ready.kernel ∧
      pending.encoded = encoded ∧ pending.peer.binding.assigned_key_id = pending.next.last_key_id ∧
      ∀ (before after : PeerMap (peer.Peer ratchet.concrete.ConcreteRatchetKernel)) (inserted : Bool),
        FaithfulFreshInsert before pending.peer.binding.assigned_key_id.val pending.peer inserted after →
        ∃ result, finishInsertion pending inserted = ok result ∧ collectionPublication pending before after result ∧
          match result with
          | .Err previous => previous = control
          | .Ok (next, identifier, _) => next = ready.candidate.next_state ∧ identifier = next.last_key_id := by
  obtain ⟨pending, prepareRun, previous, next, ownedBinding, kernel, sameId, actualEncoded⟩ :=
    prepared_response_insertion control accepted binding availability ready encoded prepared
  refine ⟨pending, prepareRun, ownedBinding, kernel, actualEncoded, sameId, ?_⟩
  intro before after inserted faithful
  obtain ⟨result, resultRun, collection⟩ := collection_insertion_refines pending before after inserted faithful
  refine ⟨result, resultRun, collection, ?_⟩
  cases result with
  | Err entry => exact collection.1.trans previous
  | Ok parts =>
    rcases parts with ⟨live, identifier, output⟩
    exact ⟨collection.1.trans next, collection.2.1.trans
      (sameId.trans (congrArg (fun state : pqxdh.ServerState => state.last_key_id) collection.1).symm)⟩

end BeaconcryptCore.Refinement.PeerOwnership

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.peer_from_trusted_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.peer_from_trusted_parts

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.peer_observers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.peer_observers

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.peer_ratchet_borrow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.peer_ratchet_borrow

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.registration_lookup_begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.registration_lookup_begin

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.registration_lookup_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.registration_lookup_request

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.registration_lookup_request_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.registration_lookup_request_bytes

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.registration_lookup_consumed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.registration_lookup_consumed

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.registration_lookup_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.registration_lookup_fresh

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.registration_insert_begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.registration_insert_begin

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.registration_insert_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.registration_insert_request

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.registration_insert_resume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.registration_insert_resume

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.completion_lookup_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.completion_lookup_request

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.completion_lookup_resume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.completion_lookup_resume

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.completion_lookup_begin_next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.completion_lookup_begin_next

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.completion_lookup_begin_exhausted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.completion_lookup_begin_exhausted

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.completion_lookup_live_successor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.completion_lookup_live_successor

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.peer_insert_begin_retains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.peer_insert_begin_retains

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.peer_insert_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.peer_insert_request

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.peer_insert_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.peer_insert_parts

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.publication_finish' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.publication_finish

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.published_peer_parts' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.published_peer_parts

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.finish_insertion_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.finish_insertion_exact

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.collection_insertion_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.collection_insertion_refines

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.registration_insert_collection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.registration_insert_collection

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.replay_lookup_after_insert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.replay_lookup_after_insert

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.root_completion_replay_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.root_completion_replay_origin

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.prepared_candidate_allocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.prepared_candidate_allocation

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.prepare_insertion_encoding_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.prepare_insertion_encoding_failure

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.prepared_response_insertion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.prepared_response_insertion

/-- info: 'BeaconcryptCore.Refinement.PeerOwnership.prepared_publication_collection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerOwnership.prepared_publication_collection
