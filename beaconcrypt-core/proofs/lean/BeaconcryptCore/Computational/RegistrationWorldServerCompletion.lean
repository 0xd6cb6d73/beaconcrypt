-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationWorldServerReplay
import BeaconcryptCore.Computational.RegistrationWorldServerPublication

/-! The concrete real Server completion follows native completion lookup, actual initial64/ongoing76 and raw record effects, response hash/ML signing/dynamic encoding, live-counter peer setup, actual World insertion, and native publication finish. The root-family state and replay set are outside this controller's writable state. This real source interpretation retains concrete kernels; the separate proved hidden-install compiler is used after the key-schedule hybrid and does not reclassify these known-reference operations as a protected-key theorem. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationWorldServerCompletion
open PqxdhRecordLiftInterface
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationWorldAgreement (State)
variable {n : Nat} {Auxiliary Encoded ι KemSK Reader Response : Type} {base : OracleSpec ι}

abbrev Result (Encoded : Type) := core.result.Result (peer.PublishedPeer Encoded) pqxdh.ServerState

private def continueWith {Input : Type} (action : RustM Input)
    (next : Input → StateT (State n Auxiliary) ProbComp (RustM (Result Encoded))) :
    StateT (State n Auxiliary) ProbComp (RustM (Result Encoded)) :=
  match action with
  | .ok value => next value
  | .fail error => pure (.fail error)
  | .div => pure .div

private def continueResult {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → StateT (State n Auxiliary) ProbComp (RustM (Result Encoded))) :
    StateT (State n Auxiliary) ProbComp (RustM (Result Encoded)) :=
  match action with
  | .ok (.Ok value) => next value
  | .ok (.Err previous) => pure (.ok (.Err previous))
  | .fail error => pure (.fail error)
  | .div => pure .div

/-- The real typed source requests the existing World capability, preserving the signing ledger and native backend auxiliary state. -/
noncomputable def capability (query : Capability n) : StateT (State n Auxiliary) ProbComp ((CapabilitySpec n).Range query) :=
  fun state => (fun result => (result.1, { state with world := (result.2, state.world.2) })) <$>
    (PqxdhRecordLiftWorld.effects (.inr query)).run state.world.1

/-- Actual source publication transfers the complete retained native peer into the live vacant entry. -/
noncomputable def install (control : pqxdh.ServerState) (published : registration.PublishedServerResponse Encoded) :
    StateT (State n Auxiliary) ProbComp (RustM (Result Encoded)) :=
  continueResult (peer.begin_peer_insert control published) fun pending =>
    continueWith pending.request fun keyId =>
      continueWith pending.into_parts fun parts => do
        let inserted ← capability (.installServer keyId (PeerBinding.ofSession parts.1.binding) (.known parts.1.ratchet))
        pure (parts.2.finish inserted)

noncomputable def signing
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) :
    StateT (State n Auxiliary) ProbComp (RustM (RegistrationWorldServerPublication.Result Encoded)) := fun state =>
  (fun result => (result.1, { state with world := result.2 })) <$>
    (simulateQ (RegistrationWorldSigning.outgoing sign)
      (RegistrationWorldServerPublication.program encode pending)).run state.world

noncomputable def publish
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded) (control : pqxdh.ServerState)
    (pending : registration.ServerResponseHash) : StateT (State n Auxiliary) ProbComp (RustM (Result Encoded)) := do
  let published ← signing sign encode pending
  continueResult published (install control)

noncomputable def fromInitial (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded) (control : pqxdh.ServerState)
    (pending : registration.ServerInitialKdf) : StateT (State n Auxiliary) ProbComp (RustM (Result Encoded)) := do
  let record ← simulateQ (RegistrationWorldRecords.handler setup codec)
    (RegistrationServerRecordExecutor.fromInitial pending)
  continueResult record (publish sign encode control)

/-- Source exhaustion precedes occupancy lookup; the actual full owner pin and native allocator are checked before either initial-record KDF. -/
noncomputable def server (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (consumed : peer.ConsumedRegistration) (application : Slice U8) :
    StateT (State n Auxiliary) ProbComp (RustM (Result Encoded)) :=
  continueResult (peer.begin_completion_lookup control current consumed application) fun lookup =>
    continueWith lookup.request fun keyId => do
      let occupied ← capability (.peerPresent keyId)
      continueResult (lookup.resume occupied) (fromInitial setup codec sign encode control)

/-- Retain the same related-root table/history while actual post-root primitives and peer publication update the World. -/
noncomputable def global (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (consumed : peer.ConsumedRegistration) (application : Slice U8) :
    StateT (RegistrationWorldServerReplay.Global n Auxiliary) ProbComp (RustM (Result Encoded)) := fun before =>
  (fun result => (result.1, (before.1, result.2))) <$>
    (server setup codec sign encode control current consumed application).run before.2

/-- Native insertion uses exactly its actual owned peer, binding, kernel and source-selected identifier. -/
theorem install_native (control : pqxdh.ServerState) (published : registration.PublishedServerResponse Encoded)
    (pending : peer.PeerInsert Encoded)
    (prepared : peer.begin_peer_insert control published = .ok (.Ok pending)) :
    install (n := n) (Auxiliary := Auxiliary) control published = (do
      let inserted ← capability (.installServer pending.peer.binding.assigned_key_id
        (PeerBinding.ofSession pending.peer.binding) (.known pending.peer.ratchet))
      pure ((⟨pending.previous, pending.next, pending.peer.binding.assigned_key_id, pending.encoded⟩ :
        peer.PublicationFinish Encoded).finish inserted)) := by
  simp only [install, prepared, continueResult,
    BeaconcryptCore.Refinement.PeerOwnership.peer_insert_request,
    BeaconcryptCore.Refinement.PeerOwnership.peer_insert_parts, continueWith]

/-- Actual ML signing and dynamic publication in the complete World project to the reached common-cache native signing interpreter. -/
theorem signing_project
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) (state : State n Auxiliary) :
    Prod.map id (fun current : State n Auxiliary => RegistrationWorldSigning.project current.world) <$>
        (signing sign encode pending).run state =
      (simulateQ (RegistrationSigningShared.implementation sign)
        (RegistrationWorldServerPublication.program encode pending)).run (RegistrationWorldSigning.project state.world) := by
  have same := RegistrationWorldServerPublication.world_project sign encode pending state.world
  change (fun result => (result.1, RegistrationWorldSigning.project result.2)) <$>
      (simulateQ (RegistrationWorldSigning.outgoing sign)
        (RegistrationWorldServerPublication.program encode pending)).run state.world = _ at same
  simpa only [signing, StateT.run, Functor.map_map, Prod.map, id_eq] using same

/-- No response completion, primitive failure, signature failure, failed encoding or refused peer insertion can change the root-family table or history. -/
theorem global_family (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (consumed : peer.ConsumedRegistration) (application : Slice U8)
    (before : RegistrationWorldServerReplay.Global n Auxiliary)
    (result : RustM (Result Encoded) × RegistrationWorldServerReplay.Global n Auxiliary)
    (supported : result ∈ support ((global setup codec sign encode control current consumed application).run before)) :
    result.2.1 = before.1 := by
  simp only [global, StateT.run, support_map] at supported
  obtain ⟨inner, _possible, rfl⟩ := supported
  rfl

end BeaconcryptCore.Computational.RegistrationWorldServerCompletion

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldServerCompletion.install_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldServerCompletion.install_native

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldServerCompletion.signing_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldServerCompletion.signing_project

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldServerCompletion.global_family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldServerCompletion.global_family
