-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPublicSnapshots
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperiment
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemClientJournal
import BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication
import BeaconcryptCore.Computational.RegistrationNativePlatformKemInitializedJournal

/-! Actual native bundle publication is tested at each successful raw acceptance using only earlier public bundle returns. The owner map belongs to that same captured prefix. Public ordinal snapshots give the explicit finite acceptance-position sum and keep every later callback, so future publication cannot redefine an earlier failure. The primitive advantage bound for the frozen final-runtime clients remains separate. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCausalPublication
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open RegistrationNativeInterface (FullSpec asModeO queryClass)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι}

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (source : RegistrationNativeMldsa.Source)
variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (bounds : FreshBounds) (mode : Mode)
variable (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
variable (previous : Platform)


variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Whole" => RegistrationNativeLedger.State × (Native × Platform)
omit primitives in
def ownerIdentities (setup : Setup base KemSK) (before : Native) : List PqxdhEd25519EufCma.Ed25519PublicKey :=
  before.beacons.map fun owner => (setup.joint.publicKeys owner.identitySeed).ed25519

omit primitives in
/-- The original decoded Ed25519 tuple origin failure at one successful native raw acceptance. Only actual bundle returns before this acceptance count as publications. This is not equality of all six Init bytes. -/
def AcceptanceFailure (setup : Setup base KemSK) (wire : Wire) (before : Whole) : Prop :=
  ∃ prior raw session candidate identity decoded owner,
    before.1.transcript = prior ++ [⟨.inl (.inr (.accept raw)), some session⟩] ∧
    PqxdhDeploymentTranscript.candidateOf (RegistrationNativeWire.ledgerCodec wire) raw = some candidate ∧
    PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto candidate = some (identity, decoded) ∧
    (ownerIdentities source setup before.2.1)[owner]? = some identity ∧
    PqxdhDeploymentPublishedTuple.publishedTuple (RegistrationNativeWire.ledgerCodec wire) (prior.map RegistrationNativeInterface.Entry.erase) owner ≠ some decoded

omit primitives in
/-- A successful acceptance itself never publishes a bundle in the actual native public transcript. -/
theorem publication_before_accept (wire : Wire) (prior : List RegistrationNativeInterface.Entry) (raw : Pqxdh.Bytes) (session owner : Nat) :
    PqxdhDeploymentPublishedTuple.publishedTuple (RegistrationNativeWire.ledgerCodec wire)
      ((prior ++ [(⟨.inl (.inr (.accept raw)), some session⟩ : RegistrationNativeInterface.Entry)]).map RegistrationNativeInterface.Entry.erase) owner =
    PqxdhDeploymentPublishedTuple.publishedTuple (RegistrationNativeWire.ledgerCodec wire) (prior.map RegistrationNativeInterface.Entry.erase) owner := by
  simpa only [List.map_append, List.map_cons, List.map_nil, RegistrationNativeInterface.Entry.erase, RegistrationNativeInterface.eraseCommand] using
    PqxdhDeploymentCausalPublication.publication_before_accept (RegistrationNativeWire.ledgerCodec wire)
      (prior.map RegistrationNativeInterface.Entry.erase) raw session owner

omit primitives in
/-- The saved-prefix native event is the old decoded-tuple predicate at that SAME actual prefix's owner map and public bytes. No legacy/native game equality is asserted. -/
theorem failure_published (setup : Setup base KemSK) (wire : Wire) (before : Whole) (failed : AcceptanceFailure source setup wire before) :
    PqxdhDeploymentPublishedTuple.PublishedForgery setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      (before.1.transcript.map RegistrationNativeInterface.Entry.erase) (ownerIdentities source setup before.2.1) := by
  obtain ⟨prior, raw, session, candidate, identity, decoded, owner, transcript, parsed, verified, owned, unpublished⟩ := failed
  refine ⟨raw, session, ?_, candidate, identity, decoded, owner, parsed, verified, owned, ?_⟩
  · rw [transcript, List.map_append, List.map_cons, List.map_nil]
    exact List.mem_append_right _ List.mem_cons_self
  · rw [transcript, publication_before_accept]
    exact unpublished

/-- The finite public acceptance-position sum bounds the actual private native prefix event by the published-tuple event in literal publicly frozen executions of the SAME runtime. A primitive advantage bound for those frozen executions is a separate obligation. -/
theorem prefix_bound (count : Nat) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : Native) :
    Pr{let result ← (RegistrationNativePlatformOrdinaryPublicSnapshots.run setup checks wire route representation source view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode previous created credential count work before)}[
      ∃ target snapshot, result.2.captured target = some snapshot ∧ AcceptanceFailure source setup wire snapshot.2] ≤
      ∑ target : Fin count, Pr{let result ← ((simulateQ
        (RegistrationNativePlatformOrdinaryPublicSnapshots.full setup checks wire route representation source view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds created credential)
        (PqxdhDeploymentServerAuthEmbed.freeze RegistrationNativePlatformOrdinaryPublicSnapshots.defaults
          (RegistrationNativePlatformOrdinaryPublicSnapshots.stopAt target.val) (asModeO mode work))).run (RegistrationNativeLedger.empty, (before, previous)))}[
            PqxdhDeploymentPublishedTuple.PublishedForgery setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
              (result.2.1.transcript.map RegistrationNativeInterface.Entry.erase) (ownerIdentities source setup result.2.2.1)] := by
  apply le_trans _ (RegistrationNativePlatformOrdinaryPublicSnapshots.captured_bound setup checks wire route representation source view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer bounds mode previous created credential count work before
      (fun state => PqxdhDeploymentPublishedTuple.PublishedForgery setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
        (state.1.transcript.map RegistrationNativeInterface.Entry.erase) (ownerIdentities source setup state.2.1)))
  apply prEvent_mono
  rintro result ⟨target, snapshot, captured, failed⟩
  exact ⟨target, snapshot, captured, failure_published source setup wire snapshot.2 failed⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCausalPublication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCausalPublication.publication_before_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCausalPublication.publication_before_accept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCausalPublication.failure_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCausalPublication.failure_published

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCausalPublication.prefix_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCausalPublication.prefix_bound
