-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityOriginProbability
import BeaconcryptCore.Computational.RegistrationNativeIdentityTargetTrace

/-! The original accepted session and its original verified tuple embed into the whole native changed-prekey event. Peer designation supplies its final owner's identity through actual publication. Owner designation has a weaker public identity condition; its identity-matched branch is handled explicitly rather than assuming that missing equality. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityOriginLedger
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Phase1Candidate Phase1KeyTuple Ed25519PublicKey)
open RegistrationNativeInterface (Entry)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem erased_accept (entry : Entry) (raw : Pqxdh.Bytes) (session : Nat)
    (same : entry.erase = (⟨.inl (.inr (.accept raw)), some session⟩ : PqxdhDeploymentInterface.Entry)) :
    entry = ⟨.inl (.inr (.accept raw)), some session⟩ := by
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases same
  · cases command <;> cases same
    rfl
  · cases same

theorem accepted_packet (wire : RegistrationNativeWire.Wire) (ledger : RegistrationNativeLedger.State)
    (consistent : ledger.ledger.transcript = ledger.transcript.map Entry.erase)
    (session : Nat) (raw : Pqxdh.Bytes) (candidate : Phase1Candidate)
    (accepted : PqxdhDeploymentTranscript.acceptOf ledger.ledger.transcript session = some raw)
    (candidateFound : PqxdhDeploymentTranscript.candidateOf (RegistrationNativeWire.ledgerCodec wire) raw = some candidate) :
    ∃ packet ∈ RegistrationNativeIdentityFinalReports.packets wire ledger.transcript, RegistrationRootInput.candidate packet = candidate := by
  obtain ⟨packet, decoded⟩ := RegistrationNativeParsedTarget.candidate_parsed wire raw candidate candidateFound
  have member := PqxdhDeploymentKemTransfer.acceptOf_mem ledger.ledger.transcript session raw accepted
  rw [consistent] at member
  obtain ⟨entry, present, erased⟩ := List.mem_map.mp member
  have same := erased_accept entry raw session erased
  subst entry
  refine ⟨packet, RegistrationNativeIdentityFinalReports.packet_member wire ledger.transcript raw session packet present decoded, ?_⟩
  rw [RegistrationNativeKemPublicTarget.candidate_read wire raw packet decoded] at candidateFound
  exact Option.some.inj candidateFound

theorem source_detached (setup : Setup base KemSK)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
    (candidate : Phase1Candidate) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple)
    (accepted : PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto candidate = some (identity, keys)) :
    PqxdhEd25519EufCma.acceptPhase1Candidate setup.joint.verify candidate = some (identity, keys) := by
  unfold PqxdhDeploymentTranscript.acceptedKeys at accepted
  rw [PqxdhJointPhase1Reports.sourceAccept_eq _ setup.joint
    (PqxdhJointPhase1Reports.source_attached_adapter setup.source.crypto setup.joint setup.secretOfSeed setup.wiring shortRejects)] at accepted
  exact accepted

/-- Original session bytes and the final actual generated owner give a source origin event whenever that unchanged verified tuple has the owner's identity and a changed prekey. -/
theorem same_session_changed (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
    (result : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source))
    (consistent : result.2.1.ledger.transcript = result.2.1.transcript.map Entry.erase)
    (session : Nat) (raw : Pqxdh.Bytes) (candidate : Phase1Candidate) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (member : owner ∈ result.2.2.beacons)
    (accepted : PqxdhDeploymentTranscript.acceptOf result.2.1.ledger.transcript session = some raw)
    (candidateFound : PqxdhDeploymentTranscript.candidateOf (RegistrationNativeWire.ledgerCodec wire) raw = some candidate)
    (keysFound : PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto candidate = some (identity, keys))
    (matched : identity = (setup.joint.publicKeys owner.identitySeed).ed25519)
    (different : keys.prekey ≠ PqxdhPhase2InputBytes.word owner.prekeyPublic) :
    RegistrationNativeIdentityOriginEvents.Changed setup.joint wire result.2.1.transcript result.2.2.beacons := by
  obtain ⟨packet, present, same⟩ := accepted_packet wire result.2.1 consistent session raw candidate accepted candidateFound
  refine ⟨packet, present, owner, member, keys, ?_, different⟩
  rw [same, ← matched]
  exact source_detached setup shortRejects candidate identity keys keysFound

/-- Peer designation's actual publication supplies the owner identity without narrowing the accepted packet or its ML fields to the original bundle. -/
theorem peer_changed (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (readback : RegistrationNativeWire.InitReadBack wire)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : RegistrationNativeExperiment.State n KemSK source)
    (result : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before))
    (keyId : U64) (session index : Nat)
    (designated : PqxdhDeploymentTranscript.designate setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      created.server.server.metadata.sender result.2.1.ledger.transcript (.peer keyId) = some (session, index))
    (raw : Pqxdh.Bytes) (candidate : Phase1Candidate) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple)
    (accepted : PqxdhDeploymentTranscript.acceptOf result.2.1.ledger.transcript session = some raw)
    (candidateFound : PqxdhDeploymentTranscript.candidateOf (RegistrationNativeWire.ledgerCodec wire) raw = some candidate)
    (keysFound : PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto candidate = some (identity, keys))
    (owner : RegistrationNativeBeaconFrontend.Owner source) (found : result.2.2.beacons[index]? = some owner)
    (different : keys.prekey ≠ PqxdhPhase2InputBytes.word owner.prekeyPublic) :
    RegistrationNativeIdentityOriginEvents.Changed setup.joint wire result.2.1.transcript result.2.2.beacons := by
  obtain ⟨response, actualRaw, actualCandidate, actualKeys, linked, rawFound, actualFound, actualVerified, _indexValid, published⟩ :=
    PqxdhDeploymentTranscript.designate_peer setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      created.server.server.metadata.sender keyId result.2.1.ledger.transcript session index designated
  have rawEq := Option.some.inj (rawFound.symm.trans accepted)
  subst actualRaw
  have candidateEq := Option.some.inj (actualFound.symm.trans candidateFound)
  subst actualCandidate
  have keysEq := Option.some.inj (actualVerified.symm.trans keysFound)
  subst actualKeys
  have tagged := RegistrationNativeIdentityTargetTrace.publishes_identity setup checks wire route representation created credential readback bounds mode work
    before result supported candidate keys.pqKey index owner found published
  have detached := source_detached setup shortRejects candidate identity keys keysFound
  have encoded := (PqxdhEd25519EufCma.acceptPhase1Candidate_some_witness setup.joint.verify candidate identity keys detached).1
  have parsed := congrArg PqxdhEd25519EufCma.parseIdentity (encoded.symm.trans tagged)
  simp only [PqxdhEd25519EufCma.parseIdentity_encodedIdentity, Option.some.injEq] at parsed
  have consistent := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire created.server.server.metadata.sender bounds
    (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) mode work before result supported
  exact same_session_changed setup wire shortRejects result consistent session raw candidate identity keys owner
    (List.mem_of_getElem? found) accepted candidateFound keysFound parsed different

end BeaconcryptCore.Computational.RegistrationNativeIdentityOriginLedger

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOriginLedger.accepted_packet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOriginLedger.accepted_packet
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOriginLedger.source_detached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOriginLedger.source_detached
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOriginLedger.same_session_changed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOriginLedger.same_session_changed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOriginLedger.peer_changed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOriginLedger.peer_changed
