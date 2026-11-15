-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPrekeySplit
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRunPacking
import BeaconcryptCore.Computational.RegistrationNativeIdentityOriginLedger
import BeaconcryptCore.Computational.RegistrationNativeLorCanonical
import BeaconcryptCore.Computational.RegistrationNativePlatformNativeBundleFields
import BeaconcryptCore.Computational.RegistrationNativeLedgerJournal
import BeaconcryptCore.Computational.RegistrationNativePrekeyPublicationTrace
import BeaconcryptCore.Computational.RegistrationNativeIdentityPublicationTrace
/-! Original broad LR and APP eligibility split on the literal dynamic-writer execution. Full native and platform outcomes are retained; concrete source publication fields discharge the prekey equality alternative. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCanonical
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


/-- The literal source native/P result retains the original public prekey split. -/
theorem pinned_or_changed (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : Native) (previous : Platform)
    (result : (((A × RegistrationNativeLedger.State) × Native) × Platform))
    (supported : result ∈ support ((RegistrationNativePlatformOrdinaryExperiment.run setup checks wire route representation created source credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work before).run previous)) (handle : Handle) :
    Pinned setup.source.crypto (RegistrationNativeWire.ledgerCodec canonical) created.server.server.metadata.sender result.1.1.2.ledger.transcript handle ∨
      RegistrationNativeIdentityOriginEvents.Changed setup.joint canonical result.1.1.2.transcript result.1.2.beacons := by
  exact RegistrationNativePlatformOrdinaryPrekeySplit.pinned_or_changed setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets shortRejects
    bounds mode work (before,previous) (result.1.1.1,(result.1.1.2,(result.1.2,result.2)))
    (RegistrationNativePlatformOrdinaryRunPacking.supported setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work before previous result supported) handle

/-- One original changed-prekey event covers all actual admitted tests at once. -/
theorem real_pin_tests (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : Native) (previous : Platform)
    (result : (((A × RegistrationNativeLedger.State) × Native) × Platform))
    (supported : result ∈ support ((RegistrationNativePlatformOrdinaryExperiment.run setup checks wire route representation created source credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work before).run previous)) :
    RegistrationNativeIdentityOriginEvents.Changed setup.joint canonical result.1.1.2.transcript result.1.2.beacons ∨
      RegistrationNativeLorCanonical.OnTests setup.source.crypto canonical created.server.server.metadata.sender result.1.1.2.ledger.transcript
        (Pinned setup.source.crypto (RegistrationNativeWire.ledgerCodec canonical) created.server.server.metadata.sender result.1.1.2.ledger.transcript) := by
  exact RegistrationNativePlatformOrdinaryPrekeySplit.real_pin_tests setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets shortRejects
    bounds mode work (before,previous) (result.1.1.1,(result.1.1.2,(result.1.2,result.2)))
    (RegistrationNativePlatformOrdinaryRunPacking.supported setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work before previous result supported)

/-- Original broad real LR eligibility uses the actual source run, without an additional hidden-test eligibility condition. -/
theorem real_eligible_split (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (filter : RegistrationNativeLorEvents.Filter A)
    (before : Native) (previous : Platform) (result : (((A × RegistrationNativeLedger.State) × Native) × Platform))
    (supported : result ∈ support ((RegistrationNativePlatformOrdinaryExperiment.run setup checks wire route representation created source credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work before).run previous))
    (eligible : RegistrationNativeLorEvents.j setup.source.crypto canonical created.server.server.metadata.sender budget filter result.1.1 = true) :
    RegistrationNativeIdentityOriginEvents.Changed setup.joint canonical result.1.1.2.transcript result.1.2.beacons ∨
      ∃ target : Fin budget.accept × Fin budget.capacity,
        RegistrationNativeLorCanonical.GoodAt setup.source.crypto canonical created.server.server.metadata.sender budget filter target result.1.1 := by
  exact RegistrationNativePlatformOrdinaryPrekeySplit.real_eligible_split setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets shortRejects
    bounds mode work budget bounded filter (before,previous) (result.1.1.1,(result.1.1.2,(result.1.2,result.2)))
    (RegistrationNativePlatformOrdinaryRunPacking.supported setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work before previous result supported) eligible

/-- Original broad APP success splits before any game change on the same complete source native/platform result. -/
theorem ceapp_split (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : Native) (previous : Platform) (budget : Budget)
    (claim : A → Option (Nat × Pqxdh.Bytes))
    (result : (((A × RegistrationNativeLedger.State) × Native) × Platform))
    (supported : result ∈ support ((RegistrationNativePlatformOrdinaryExperiment.run setup checks wire route representation created source credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work before).run previous))
    (winning : RegistrationNativeEvents.CEAppWin setup.source.crypto canonical created.server.server.metadata.sender budget claim (result.1.1.1,(result.1.1.2,result.1.2))) :
    RegistrationNativeIdentityOriginEvents.Changed setup.joint canonical result.1.1.2.transcript result.1.2.beacons ∨
      GoodApp setup.source.crypto canonical created.server.server.metadata.sender budget claim (result.1.1.1,(result.1.1.2,result.1.2)) := by
  exact RegistrationNativePlatformOrdinaryPrekeySplit.ceapp_split setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets shortRejects
    bounds mode work (before,previous) budget claim (result.1.1.1,(result.1.1.2,(result.1.2,result.2)))
    (RegistrationNativePlatformOrdinaryRunPacking.supported setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work before previous result supported) winning

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCanonical

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCanonical.pinned_or_changed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCanonical.pinned_or_changed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCanonical.real_pin_tests' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCanonical.real_pin_tests

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCanonical.real_eligible_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCanonical.real_eligible_split

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCanonical.ceapp_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCanonical.ceapp_split
