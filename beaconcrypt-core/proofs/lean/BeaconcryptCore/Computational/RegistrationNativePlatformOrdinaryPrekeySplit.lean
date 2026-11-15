-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTargetFields
import BeaconcryptCore.Computational.RegistrationNativeIdentityOriginLedger
import BeaconcryptCore.Computational.RegistrationNativeLorCanonical
import BeaconcryptCore.Computational.RegistrationNativePlatformNativeBundleFields
import BeaconcryptCore.Computational.RegistrationNativeLedgerJournal
import BeaconcryptCore.Computational.RegistrationNativePrekeyPublicationTrace
import BeaconcryptCore.Computational.RegistrationNativeIdentityPublicationTrace
/-! The actual dynamic-writer source run splits a failed public prekey equality into a changed-prekey event for the same final owner. The packet and ordinary signature verification remain on the original real run. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPrekeySplit
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

variable {A : Type} [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "wire" => RegistrationNativePlatformConcreteSource.wire
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets
local notation "typed" => RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route representation created credential
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "native" => RegistrationNativeRawAdapter.handler canonical typed
open RegistrationNativeOwnerRoster (Prefix)
open RegistrationNativePrekeyPublicationTrace (publication)
open RegistrationNativeOwnerFields (metadata)

open PqxdhEd25519EufCma (Phase1Candidate Phase1KeyTuple Ed25519PublicKey)
open PqxdhDeploymentInterface (FreshBounds Mode Budget Handle)
open RegistrationNativePrekeyEvents (Pinned GoodApp)
variable (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
include shortRejects

/-- Actual peer designation names the same final concrete source owner identity in its accepted tuple. -/
theorem peer_changed (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : Native × Platform)
    (result : A × (RegistrationNativeLedger.State × (Native × Platform)))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto canonical created.server.server.metadata.sender bounds typed mode work before))
    (keyId : U64) (session index : Nat)
    (designated : PqxdhDeploymentTranscript.designate setup.source.crypto (RegistrationNativeWire.ledgerCodec canonical)
      created.server.server.metadata.sender result.2.1.ledger.transcript (.peer keyId) = some (session,index))
    (raw : Pqxdh.Bytes) (candidate : Phase1Candidate) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple)
    (accepted : PqxdhDeploymentTranscript.acceptOf result.2.1.ledger.transcript session = some raw)
    (candidateFound : PqxdhDeploymentTranscript.candidateOf (RegistrationNativeWire.ledgerCodec canonical) raw = some candidate)
    (keysFound : PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto candidate = some (identity,keys))
    (owner : RegistrationNativeBeaconFrontend.Owner source) (found : result.2.2.1.beacons[index]? = some owner)
    (different : keys.prekey ≠ PqxdhPhase2InputBytes.word owner.prekeyPublic) :
    RegistrationNativeIdentityOriginEvents.Changed setup.joint canonical result.2.1.transcript result.2.2.1.beacons := by
  obtain ⟨response,actualRaw,actualCandidate,actualKeys,linked,rawFound,actualFound,actualVerified,_indexValid,published⟩ :=
    PqxdhDeploymentTranscript.designate_peer setup.source.crypto (RegistrationNativeWire.ledgerCodec canonical)
      created.server.server.metadata.sender keyId result.2.1.ledger.transcript session index designated
  have rawEq := Option.some.inj (rawFound.symm.trans accepted)
  subst actualRaw
  have candidateEq := Option.some.inj (actualFound.symm.trans candidateFound)
  subst actualCandidate
  have keysEq := Option.some.inj (actualVerified.symm.trans keysFound)
  subst actualKeys
  have tagged := RegistrationNativePlatformOrdinaryTargetFields.publishes_identity setup checks route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reservePackets bounds mode work before result supported candidate keys.pqKey index owner found published
  have detached := RegistrationNativeIdentityOriginLedger.source_detached setup shortRejects candidate identity keys keysFound
  have encoded := (PqxdhEd25519EufCma.acceptPhase1Candidate_some_witness setup.joint.verify candidate identity keys detached).1
  have parsed := congrArg PqxdhEd25519EufCma.parseIdentity (encoded.symm.trans tagged)
  simp only [PqxdhEd25519EufCma.parseIdentity_encodedIdentity,Option.some.injEq] at parsed
  have consistent := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto canonical created.server.server.metadata.sender bounds typed mode work before result supported
  exact RegistrationNativeIdentityOriginLedger.same_session_changed setup canonical shortRejects (result.1,(result.2.1,result.2.2.1)) consistent session raw candidate identity keys owner
    (List.mem_of_getElem? found) accepted candidateFound keysFound parsed different

/-- Original real peer designation either keeps its public prekey equality or supplies a changed-prekey packet on that same run. -/
theorem pinned_or_changed (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : Native × Platform)
    (result : A × (RegistrationNativeLedger.State × (Native × Platform)))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto canonical created.server.server.metadata.sender bounds typed mode work before))
    (handle : Handle) :
    Pinned setup.source.crypto (RegistrationNativeWire.ledgerCodec canonical) created.server.server.metadata.sender result.2.1.ledger.transcript handle ∨
      RegistrationNativeIdentityOriginEvents.Changed setup.joint canonical result.2.1.transcript result.2.2.1.beacons := by
  classical
  cases handle with
  | owner index => exact Or.inl trivial
  | peer keyId =>
    by_cases pinned : Pinned setup.source.crypto (RegistrationNativeWire.ledgerCodec canonical) created.server.server.metadata.sender result.2.1.ledger.transcript (.peer keyId)
    · exact Or.inl pinned
    · unfold Pinned at pinned
      push Not at pinned
      obtain ⟨session,index,designated,different⟩ := pinned
      obtain ⟨_response,raw,candidate,keys,_linked,accepted,candidateFound,keysFound,_valid,published⟩ :=
        PqxdhDeploymentTranscript.designate_peer setup.source.crypto (RegistrationNativeWire.ledgerCodec canonical)
          created.server.server.metadata.sender keyId result.2.1.ledger.transcript session index designated
      obtain ⟨publishedPacket,publishedFound,_identity,_pq⟩ := published
      obtain ⟨publishedRaw,bundled,_parsed⟩ := Option.bind_eq_some_iff.mp publishedFound
      obtain ⟨owner,ownerAt,publicKey⟩ := RegistrationNativePlatformOrdinaryTargetFields.published_at setup checks route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper reservePackets bounds mode work before result supported index publishedRaw bundled
      have changed : keys.2.prekey ≠ PqxdhPhase2InputBytes.word owner.prekeyPublic := by
        intro equal
        apply different
        simp only [RegistrationNativePrekeyEvents.acceptedAt,accepted,Option.bind_some,candidateFound,keysFound,Option.map_some,publicKey,equal]
      exact Or.inr (peer_changed setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets shortRejects
        bounds mode work before result supported keyId session index designated raw candidate keys.1 keys.2 accepted candidateFound keysFound owner ownerAt changed)

/-- One changed-prekey event covers every failed pin equality among all admitted tests. -/
theorem real_pin_tests (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : Native × Platform)
    (result : A × (RegistrationNativeLedger.State × (Native × Platform)))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto canonical created.server.server.metadata.sender bounds typed mode work before)) :
    RegistrationNativeIdentityOriginEvents.Changed setup.joint canonical result.2.1.transcript result.2.2.1.beacons ∨
      RegistrationNativeLorCanonical.OnTests setup.source.crypto canonical created.server.server.metadata.sender result.2.1.ledger.transcript
        (Pinned setup.source.crypto (RegistrationNativeWire.ledgerCodec canonical) created.server.server.metadata.sender result.2.1.ledger.transcript) := by
  classical
  by_cases changed : RegistrationNativeIdentityOriginEvents.Changed setup.joint canonical result.2.1.transcript result.2.2.1.beacons
  · exact Or.inl changed
  · right
    intro pre entry post handle left right split query admitted
    exact (pinned_or_changed setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets shortRejects
      bounds mode work before result supported handle).resolve_right changed

/-- Broad actual LR eligibility splits into one original changed-prekey event or a canonical target with every public pin equality. -/
theorem real_eligible_split (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (filter : RegistrationNativeLorEvents.Filter A)
    (before : Native × Platform) (result : A × (RegistrationNativeLedger.State × (Native × Platform)))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto canonical created.server.server.metadata.sender bounds typed mode work before))
    (eligible : RegistrationNativeLorEvents.j setup.source.crypto canonical created.server.server.metadata.sender budget filter (result.1,result.2.1) = true) :
    RegistrationNativeIdentityOriginEvents.Changed setup.joint canonical result.2.1.transcript result.2.2.1.beacons ∨
      ∃ target : Fin budget.accept × Fin budget.capacity,
        RegistrationNativeLorCanonical.GoodAt setup.source.crypto canonical created.server.server.metadata.sender budget filter target (result.1,result.2.1) := by
  rcases real_pin_tests setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets shortRejects
    bounds mode work before result supported with changed | pinned
  · exact Or.inl changed
  · obtain ⟨target,chosen⟩ := RegistrationNativeLorCanonical.broad_selected setup.source.crypto canonical created.server.server.metadata.sender bounds typed mode work budget bounded before filter result supported eligible
    exact Or.inr ⟨target,chosen,pinned⟩

/-- Broad original APP success splits before any game change, retaining one changed-prekey event. -/
theorem ceapp_split (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : Native × Platform) (budget : Budget)
    (claim : A → Option (Nat × Pqxdh.Bytes))
    (result : A × (RegistrationNativeLedger.State × (Native × Platform)))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto canonical created.server.server.metadata.sender bounds typed mode work before))
    (winning : RegistrationNativeEvents.CEAppWin setup.source.crypto canonical created.server.server.metadata.sender budget claim (result.1,(result.2.1,result.2.2.1))) :
    RegistrationNativeIdentityOriginEvents.Changed setup.joint canonical result.2.1.transcript result.2.2.1.beacons ∨
      GoodApp setup.source.crypto canonical created.server.server.metadata.sender budget claim (result.1,(result.2.1,result.2.2.1)) := by
  obtain ⟨index,guess,entry,claimed,fresh,designated,guessed⟩ := winning
  rcases pinned_or_changed setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets shortRejects
    bounds mode work before result supported entry.handle with pinned | changed
  · exact Or.inr ⟨index,guess,entry,claimed,fresh,designated,guessed,pinned⟩
  · exact Or.inl changed

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPrekeySplit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPrekeySplit.peer_changed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPrekeySplit.peer_changed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPrekeySplit.pinned_or_changed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPrekeySplit.pinned_or_changed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPrekeySplit.real_pin_tests' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPrekeySplit.real_pin_tests

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPrekeySplit.real_eligible_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPrekeySplit.real_eligible_split

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPrekeySplit.ceapp_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPrekeySplit.ceapp_split
