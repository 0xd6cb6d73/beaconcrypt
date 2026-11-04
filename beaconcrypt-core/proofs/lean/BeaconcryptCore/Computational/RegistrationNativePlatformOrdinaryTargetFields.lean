-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPublicationTrace
import BeaconcryptCore.Computational.RegistrationNativeIdentityTargetTrace
import BeaconcryptCore.Computational.RegistrationNativePrekeyEvents
import BeaconcryptCore.Computational.RegistrationNativePlatformNativeBundleFields
import BeaconcryptCore.Computational.RegistrationNativeLedgerJournal
import BeaconcryptCore.Computational.RegistrationNativePrekeyPublicationTrace
import BeaconcryptCore.Computational.RegistrationNativeIdentityPublicationTrace
/-! The original public designation scanner names concrete source publications whose identity and prekey agree with the final actual runtime owner. Stateful failures and the native/platform pair remain in the same run. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTargetFields
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

variable {A : Type} [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
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

open RegistrationNativeInterface (Entry)
omit primitive in
private theorem bundle_mem (transcript : List PqxdhDeploymentInterface.Entry) (owner : Nat) (raw : Pqxdh.Bytes)
    (found : PqxdhDeploymentTranscript.bundleOf transcript owner = some raw) :
    (⟨.inl (.inr (.bundle owner)), some raw⟩ : PqxdhDeploymentInterface.Entry) ∈ transcript := by
  obtain ⟨entry, member, value⟩ := List.exists_of_findSome?_eq_some found
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases value
  · cases command with
    | bundle index =>
        cases reply with
        | none => cases value
        | some encoded =>
            simp only at value
            split at value
            · rename_i same
              simp only [Option.some.injEq] at value
              subst same value
              exact member
            · cases value
    | _ => cases value
  · cases value

omit primitive in
private theorem erased_bundle (entry : Entry) (owner : Nat) (raw : Pqxdh.Bytes)
    (same : entry.erase = (⟨.inl (.inr (.bundle owner)), some raw⟩ : PqxdhDeploymentInterface.Entry)) :
    RegistrationNativePrekeyPublicationTrace.publication entry = some (owner, raw) := by
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases same
  · cases command <;> cases same
    rfl
  · cases same


/-- A successful original bundle has the literal decoded fields of its final actual owner. -/
theorem original_bundle (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : Native × Platform)
    (result : A × (RegistrationNativeLedger.State × (Native × Platform)))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto canonical created.server.server.metadata.sender bounds typed mode work before))
    (index : Nat) (raw : Pqxdh.Bytes)
    (found : PqxdhDeploymentTranscript.bundleOf result.2.1.ledger.transcript index = some raw) :
    ∃ owner packet,result.2.2.1.beacons[index]? = some owner ∧ RegistrationNativeWire.readInit canonical raw = some packet ∧
      (PqxdhRefinement.absBytes packet.pre_key).drop 64 = PqxdhEd25519EufCma.prekeyMessage (PqxdhPhase2InputBytes.word owner.prekeyPublic) ∧
      PqxdhEd25519EufCma.parseIdentity (PqxdhRefinement.absBytes packet.identity_key) = some (setup.joint.publicKeys owner.identitySeed).ed25519 := by
  have observed := RegistrationNativePlatformOrdinaryPublicationTrace.run_holds setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets bounds mode work before result supported
  have projected := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto canonical created.server.server.metadata.sender bounds typed mode work before result supported
  have member := bundle_mem result.2.1.ledger.transcript index raw found
  rw [projected] at member
  obtain ⟨entry,nativeMember,erasedEntry⟩ := List.mem_map.mp member
  exact observed entry nativeMember index raw (erased_bundle entry index raw erasedEntry)

/-- The original publication prekey equals the retained owner's generated immutable prekey. -/
theorem published_at (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : Native × Platform)
    (result : A × (RegistrationNativeLedger.State × (Native × Platform)))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto canonical created.server.server.metadata.sender bounds typed mode work before))
    (index : Nat) (raw : Pqxdh.Bytes)
    (found : PqxdhDeploymentTranscript.bundleOf result.2.1.ledger.transcript index = some raw) :
    ∃ owner,result.2.2.1.beacons[index]? = some owner ∧
      RegistrationNativePrekeyEvents.publishedAt (RegistrationNativeWire.ledgerCodec canonical) result.2.1.ledger.transcript index =
        some (PqxdhPhase2InputBytes.word owner.prekeyPublic) := by
  obtain ⟨owner,packet,ownerAt,parsed,prekey,_identity⟩ := original_bundle setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets bounds mode work before result supported index raw found
  refine ⟨owner,ownerAt,?_⟩
  simp only [RegistrationNativePrekeyEvents.publishedAt,found,Option.bind_some,
    RegistrationNativeKemPublicTarget.candidate_read canonical raw packet parsed,
    RegistrationNativePrekeyEvents.publishedPrekey,RegistrationRootInput.candidate,prekey,
    PqxdhEd25519EufCma.parsePrekeyMessage_prekeyMessage]

/-- Broad public publication identifies the final generated identity without requiring accepted ML bytes to equal a bundle. -/
theorem publishes_identity (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : Native × Platform)
    (result : A × (RegistrationNativeLedger.State × (Native × Platform)))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto canonical created.server.server.metadata.sender bounds typed mode work before))
    (accepted : PqxdhEd25519EufCma.Phase1Candidate) (pqKey : PqxdhKemIndCca.MlKem768PublicKey) (index : Nat)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (found : result.2.2.1.beacons[index]? = some owner)
    (published : PqxdhDeploymentTranscript.Publishes (RegistrationNativeWire.ledgerCodec canonical) result.2.1.ledger.transcript accepted pqKey index) :
    accepted.identityKey = PqxdhEd25519EufCma.encodedIdentity (setup.joint.publicKeys owner.identitySeed).ed25519 := by
  obtain ⟨packet,publishedFound,identityMatches,_pqMatches⟩ := published
  obtain ⟨raw,bundled,packetRead⟩ := Option.bind_eq_some_iff.mp publishedFound
  obtain ⟨actualOwner,nativePacket,ownerAt,parsed,_prekey,identity⟩ :=
    original_bundle setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets bounds mode work before result supported index raw bundled
  have sameOwner : actualOwner = owner := Option.some.inj (ownerAt.symm.trans found)
  subst actualOwner
  rw [RegistrationNativeKemPublicTarget.candidate_read canonical raw nativePacket parsed] at packetRead
  have samePacket := Option.some.inj packetRead
  rw [←samePacket] at identityMatches
  have canonicalIdentity := (PqxdhEd25519EufCma.parseIdentity_eq_some_iff _ _).mp identity
  exact identityMatches.symm.trans canonicalIdentity

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTargetFields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTargetFields.original_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTargetFields.original_bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTargetFields.published_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTargetFields.published_at

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTargetFields.publishes_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTargetFields.publishes_identity
