-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargets
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPrekeySplit
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionPinSplit
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

open PqxdhEd25519EufCma (Phase1Candidate Phase1KeyTuple Ed25519PublicKey)
open PqxdhDeploymentInterface (FreshBounds Mode Budget Handle)
open RegistrationNativePrekeyEvents (Pinned GoodApp)
variable (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
include shortRejects

/-- The literal original current source event is either the SAME changed-prekey event or one pin-filtered parsed target, before any target union or primitive comparison. -/
theorem real_split (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (before : Native × Platform)
    (result : A × (RegistrationNativeLedger.State × (Native × Platform)))
    (supported : result∈support (RegistrationNativeFullCompiler.run setup.source.crypto canonical created.server.server.metadata.sender bounds typed mode work before))
    (kind : RegistrationNativePlatformRecordSessionTargets.Kind)
    (produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame))
    (failed : RegistrationNativePlatformRecordSessionTargets.Failure setup.source.crypto (RegistrationNativeWire.ledgerCodec canonical)
      created.server.server.metadata.sender budget route kind (result.1,result.2.1) produced) :
    RegistrationNativeIdentityOriginEvents.Changed setup.joint canonical result.2.1.transcript result.2.2.1.beacons ∨
      ∃target:Fin budget.accept × Fin budget.capacity,
        RegistrationNativePlatformRecordSessionTargets.PinnedAt setup.source.crypto canonical created.server.server.metadata.sender budget route kind target (result.1,result.2.1) := by
  obtain ⟨target,selected⟩:=RegistrationNativePlatformRecordSessionTargets.selected setup.source.crypto canonical created.server.server.metadata.sender
    bounds typed mode work budget bounded before result supported route kind produced failed
  have split:=RegistrationNativePlatformRecordSessionTargets.pinned_or_changed setup.source.crypto canonical created.server.server.metadata.sender budget route kind
    target (result.1,result.2.1) selected
    (RegistrationNativeIdentityOriginEvents.Changed setup.joint canonical result.2.1.transcript result.2.2.1.beacons)
    (fun handle=>RegistrationNativePlatformOrdinaryPrekeySplit.pinned_or_changed setup checks route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reservePackets shortRejects bounds mode work before result supported handle)
  rcases split with pinned|changed
  · exact Or.inr ⟨target,pinned⟩
  · exact Or.inl changed

/-- The same original changed-prekey probability is charged once, followed by the original parsed-accept times owner sum. No failed history or broad designated record is excluded. -/
theorem real_probability (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (before : Native × Platform)
    (kind : RegistrationNativePlatformRecordSessionTargets.Kind) :
    Pr{let result←RegistrationNativeFullCompiler.run setup.source.crypto canonical created.server.server.metadata.sender bounds typed mode work before}[
      RegistrationNativePlatformRecordSessionTargets.Failure setup.source.crypto (RegistrationNativeWire.ledgerCodec canonical)
        created.server.server.metadata.sender budget route kind (result.1,result.2.1) []]≤
      Pr{let result←RegistrationNativeFullCompiler.run setup.source.crypto canonical created.server.server.metadata.sender bounds typed mode work before}[
        RegistrationNativeIdentityOriginEvents.Changed setup.joint canonical result.2.1.transcript result.2.2.1.beacons]+
      ∑target:Fin budget.accept × Fin budget.capacity,
        Pr{let result←RegistrationNativeFullCompiler.run setup.source.crypto canonical created.server.server.metadata.sender bounds typed mode work before}[
          RegistrationNativePlatformRecordSessionTargets.PinnedAt setup.source.crypto canonical created.server.server.metadata.sender budget route kind target (result.1,result.2.1)] := by
  classical
  calc
    _≤Pr{let result←RegistrationNativeFullCompiler.run setup.source.crypto canonical created.server.server.metadata.sender bounds typed mode work before}[
        RegistrationNativeIdentityOriginEvents.Changed setup.joint canonical result.2.1.transcript result.2.2.1.beacons ∨
          ∃target∈(Finset.univ:Finset (Fin budget.accept × Fin budget.capacity)),
            RegistrationNativePlatformRecordSessionTargets.PinnedAt setup.source.crypto canonical created.server.server.metadata.sender budget route kind target (result.1,result.2.1)] := by
      apply prEvent_mono_of_support
      intro result supported failed
      rcases real_split setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets shortRejects
        bounds mode work budget bounded before result supported kind [] failed with changed|⟨target,pinned⟩
      · exact Or.inl changed
      · exact Or.inr ⟨target,Finset.mem_univ _,pinned⟩
    _≤_:= (prEvent_or_le _ _ _).trans (add_le_add le_rfl (prEvent_exists_finset_le Finset.univ _ _))
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionPinSplit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionPinSplit.real_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionPinSplit.real_split

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionPinSplit.real_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionPinSplit.real_probability
