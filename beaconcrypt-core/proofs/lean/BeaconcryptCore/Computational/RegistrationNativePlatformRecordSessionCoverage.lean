-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionPinSplit
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryStartupTargets
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCanonical
import BeaconcryptCore.Computational.RegistrationNativeLorCoverage
import BeaconcryptCore.Computational.RegistrationNativeIdentityOriginLedger
import BeaconcryptCore.Computational.RegistrationNativeLorCanonical
import BeaconcryptCore.Computational.RegistrationNativePlatformNativeBundleFields
import BeaconcryptCore.Computational.RegistrationNativeLedgerJournal
import BeaconcryptCore.Computational.RegistrationNativePrekeyPublicationTrace
import BeaconcryptCore.Computational.RegistrationNativeIdentityPublicationTrace
/-! Original broad APP success retains its literal initialized dynamic-writer profile. Concrete source publication fields derive its canonical target split and charge one changed-prekey event. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionCoverage
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

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

open PqxdhDeploymentInterface (Budget FreshBounds)
open RegistrationNativeLorCoverage (broad select)
variable (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (previous : Platform)
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "whole" => RegistrationNativePlatformIdentityOriginObserved.native setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer source ensureInit identityIndex serverKeyId bounds mode adversary previous

noncomputable def event (budget : Budget) (kind : RegistrationNativePlatformRecordSessionTargets.Kind)
    (observed : RegistrationNativeEvents.Observed A Native) : Bool :=
  @decide (RegistrationNativePlatformRecordSessionTargets.Failure setup.source.crypto (RegistrationNativeWire.ledgerCodec canonical)
    serverKeyId budget route kind (observed.1,observed.2.1) []) (Classical.propDecidable _)
noncomputable def targetEvent (budget : Budget) (kind : RegistrationNativePlatformRecordSessionTargets.Kind)
    (target : Fin budget.accept ×Fin budget.capacity) (observed : RegistrationNativeEvents.Observed A Native) : Bool :=
  @decide (RegistrationNativePlatformRecordSessionTargets.PinnedAt setup.source.crypto canonical serverKeyId budget route kind target (observed.1,observed.2.1)) (Classical.propDecidable _)
private theorem full_receipt (observed : RegistrationNativeEvents.Observed A Native ×Platform) (supported : some observed∈support whole) :
    ∃initial,some initial∈support (RegistrationNativeExperiment.start (n:=n) setup source ensureInit identityIndex serverKeyId) ∧
      (observed.1.1,(observed.1.2.1,(observed.1.2.2,observed.2)))∈support
        (RegistrationNativeFullCompiler.run setup.source.crypto canonical initial.created.server.server.metadata.sender bounds
          (RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route representation initial.created initial.credential
            view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) mode (adversary initial.public) (initial.state,previous)) := by
  simp only [RegistrationNativePlatformIdentityOriginObserved.native,mem_support_bind_iff] at supported
  obtain ⟨initialized,started,continued⟩:=supported
  cases initialized with
  | none=>simp only [mem_support_pure_iff,reduceCtorEq] at continued
  | some initial=>
    simp only [support_map,Set.mem_image,Option.some.injEq] at continued
    obtain ⟨actual,reached,rfl⟩:=continued
    exact ⟨initial,started,RegistrationNativePlatformOrdinaryRunPacking.supported setup checks wire route representation initial.created initial.credential
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode (adversary initial.public) initial.state previous actual reached⟩
/-- The genuine initialized original corrected origin and both UKS events charge the same Changed event once or retain a pin-filtered parsed target. Failed startup and callback histories remain in their original profile. -/
theorem outcome_split (budget : Budget) (bounded : ∀publicInput,RegistrationNativeInterface.Respects budget (adversary publicInput))
    (shortRejects : ∀(publicKey:PqxdhEd25519EufCma.Ed25519PublicKey) bytes,bytes.length<64→setup.source.crypto.verify publicKey.toList bytes=none)
    (kind : RegistrationNativePlatformRecordSessionTargets.Kind) (observed : RegistrationNativeEvents.Observed A Native ×Platform)
    (supported : some observed∈support whole) (failed : event setup route source serverKeyId budget kind observed.1=true) :
    RegistrationNativeIdentityOriginEvents.Changed setup.joint canonical observed.1.2.1.transcript observed.1.2.2.beacons ∨
      ∃target:Fin budget.accept ×Fin budget.capacity,
        RegistrationNativePlatformRecordSessionTargets.PinnedAt setup.source.crypto canonical serverKeyId budget route kind target (observed.1.1,observed.1.2.1) := by
  classical
  obtain ⟨initial,started,ran⟩:=full_receipt setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds mode adversary previous observed supported
  have sender:=(RegistrationNativeKemCandidateStartup.start_facts setup source ensureInit identityIndex serverKeyId initial started).2.2
  have original:=of_decide_eq_true failed
  rw [←sender] at original ⊢
  exact RegistrationNativePlatformRecordSessionPinSplit.real_split setup checks route representation initial.created initial.credential
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets shortRejects bounds mode (adversary initial.public)
    budget (bounded initial.public) (initial.state,previous) (observed.1.1,(observed.1.2.1,(observed.1.2.2,observed.2))) ran kind [] original
local notation "job"=>RegistrationNativePlatformOrdinaryExperiment.profile (n:=n) setup checks wire route representation source ensureInit identityIndex serverKeyId
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
private theorem profile_probability (decision : RegistrationNativeEvents.Observed A Native→Bool) :
    Pr{let result←((job decision).run previous)}[result.1=true]=Pr{let result←whole}[result.any (fun observed=>decision observed.1)=true] := by
  rw [←RegistrationNativePlatformIdentityOriginProbability.native_profile setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds mode adversary previous decision,prEvent_map]
  apply prEvent_congr
  intro result
  cases result <;>rfl
/-- The broad original corrected source probability pays Changed once before the complete original parsed-accept times owner sum. No test/fresh eligibility or successful-session/raw-ordinal identification is added. -/
theorem broad_probability (budget : Budget) (bounded : ∀publicInput,RegistrationNativeInterface.Respects budget (adversary publicInput))
    (shortRejects : ∀(publicKey:PqxdhEd25519EufCma.Ed25519PublicKey) bytes,bytes.length<64→setup.source.crypto.verify publicKey.toList bytes=none)
    (kind : RegistrationNativePlatformRecordSessionTargets.Kind) :
    Pr{let result←((job (event setup route source serverKeyId budget kind)).run previous)}[result.1=true]≤
      Pr{let result←((job (RegistrationNativeIdentityOriginEvents.event setup.joint canonical)).run previous)}[result.1=true]+
      ∑target:Fin budget.accept ×Fin budget.capacity,
        Pr{let result←((job (targetEvent setup route source serverKeyId budget kind target)).run previous)}[result.1=true] := by
  classical
  simp only [profile_probability]
  calc
    _≤Pr{let result←whole}[result.any (fun actual=>RegistrationNativeIdentityOriginEvents.event setup.joint canonical actual.1)=true ∨
        ∃target:Fin budget.accept ×Fin budget.capacity,result.any (fun actual=>targetEvent setup route source serverKeyId budget kind target actual.1)=true] := by
      apply prEvent_mono_of_support
      intro result supported failed
      cases result with
      | none=>cases failed
      | some actual=>
        rcases outcome_split setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets
          source ensureInit identityIndex serverKeyId bounds mode adversary previous budget bounded shortRejects kind actual supported failed with changed|⟨target,pinned⟩
        · exact Or.inl (decide_eq_true changed)
        · exact Or.inr ⟨target,decide_eq_true pinned⟩
    _≤_:=(prEvent_or_le _ _ _).trans (add_le_add le_rfl (prEvent_exists_le _ _))
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionCoverage
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionCoverage.outcome_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionCoverage.outcome_split
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionCoverage.broad_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionCoverage.broad_probability
