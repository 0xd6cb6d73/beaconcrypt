-- SPDX-License-Identifier: 0BSD
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAppCoverage
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
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) A) (previous : Platform)
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "whole" => RegistrationNativePlatformOrdinaryStartupTargets.outcome setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer source ensureInit identityIndex serverKeyId bounds adversary previous

/-- Every original broad APP success has a canonical parsed-accept and owner target on the same actual source run. -/
theorem outcome_selected (budget : Budget) (bounded : ∀ publicInput,RegistrationNativeInterface.Respects budget (adversary publicInput))
    (claim : A → Option (Nat × Pqxdh.Bytes)) (observed : RegistrationNativeEvents.Observed A Native × Platform)
    (supported : some observed ∈ support whole)
    (winning : RegistrationNativeEvents.CEAppWin setup.source.crypto canonical serverKeyId budget claim observed.1) :
    ∃ target : Fin budget.accept × Fin budget.capacity,
      RegistrationNativeParsedTargetCanonical.CEAppAt setup.source.crypto canonical serverKeyId budget target claim observed.1 := by
  obtain ⟨initial,started,ran⟩ := RegistrationNativePlatformOrdinaryStartupTargets.full_receipt setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds adversary previous observed supported
  have sender := (RegistrationNativeKemCandidateStartup.start_facts setup source ensureInit identityIndex serverKeyId initial started).2.2
  rw [←sender] at winning ⊢
  exact (RegistrationNativeParsedTargetCanonical.broad_selected setup.source.crypto canonical _ bounds _ .P _ budget (bounded initial.public) _ claim
    (observed.1.1,(observed.1.2.1,(observed.1.2.2,observed.2))) ran).mp winning

/-- The literal original APP event pays one changed-prekey event or retains its same pinned canonical fresh target. -/
theorem outcome_split (budget : Budget) (bounded : ∀ publicInput,RegistrationNativeInterface.Respects budget (adversary publicInput))
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes,bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
    (claim : A → Option (Nat × Pqxdh.Bytes)) (observed : RegistrationNativeEvents.Observed A Native × Platform)
    (supported : some observed ∈ support whole)
    (winning : RegistrationNativeEvents.CEAppWin setup.source.crypto canonical serverKeyId budget claim observed.1) :
    RegistrationNativeIdentityOriginEvents.Changed setup.joint canonical observed.1.2.1.transcript observed.1.2.2.beacons ∨
      ∃ target : Fin budget.accept × Fin budget.capacity,
        RegistrationNativePrekeyEvents.GoodAt setup.source.crypto canonical serverKeyId budget target claim observed.1 := by
  obtain ⟨initial,started,ran⟩ := RegistrationNativePlatformOrdinaryStartupTargets.full_receipt setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds adversary previous observed supported
  have sender := (RegistrationNativeKemCandidateStartup.start_facts setup source ensureInit identityIndex serverKeyId initial started).2.2
  rw [←sender] at winning ⊢
  rcases RegistrationNativePlatformOrdinaryPrekeySplit.ceapp_split setup checks route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets shortRejects
    bounds .P (adversary initial.public) (initial.state,previous) budget claim (observed.1.1,(observed.1.2.1,(observed.1.2.2,observed.2))) ran winning with changed | good
  · exact Or.inl changed
  · exact Or.inr (RegistrationNativePrekeyEvents.good_selected setup.source.crypto canonical _ bounds _ .P _ budget (bounded initial.public) _ claim
      (observed.1.1,(observed.1.2.1,(observed.1.2.2,observed.2))) ran good)

local notation "job" => RegistrationNativePlatformOrdinaryExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds PqxdhDeploymentInterface.Mode.P adversary

/-- The original initialized APP probability pays one original signature-origin event and the canonical fresh target family. -/
theorem broad_probability (budget : Budget) (bounded : ∀ publicInput,RegistrationNativeInterface.Respects budget (adversary publicInput))
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes,bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
    (claim : A → Option (Nat × Pqxdh.Bytes)) :
    Pr{let result ← ((job (RegistrationNativeEvents.ceAppEvent setup.source.crypto canonical serverKeyId budget claim)).run previous)}[result.1 = true] ≤
    Pr{let result ← ((job (RegistrationNativeIdentityOriginEvents.event setup.joint canonical)).run previous)}[result.1 = true] +
    ∑ target : Fin budget.accept × Fin budget.capacity,
      Pr{let result ← ((job (RegistrationNativePrekeyEvents.targetEvent setup.source.crypto canonical serverKeyId budget target claim)).run previous)}[result.1 = true] := by
  classical
  simp only [RegistrationNativePlatformOrdinaryStartupTargets.profile_probability]
  calc
    _ ≤ Pr{let outcome ← whole}[
      outcome.any (fun actual => RegistrationNativeIdentityOriginEvents.event setup.joint canonical actual.1) = true ∨
      ∃ target : Fin budget.accept × Fin budget.capacity,
        outcome.any (fun actual => RegistrationNativePrekeyEvents.targetEvent setup.source.crypto canonical serverKeyId budget target claim actual.1) = true] := by
        apply prEvent_mono_of_support
        intro outcome supported observed
        cases outcome with
        | none => cases observed
        | some actual =>
          have winning : RegistrationNativeEvents.CEAppWin setup.source.crypto canonical serverKeyId budget claim actual.1 := of_decide_eq_true observed
          rcases outcome_split setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous
            budget bounded shortRejects claim actual supported winning with changed | chosen
          · exact Or.inl (decide_eq_true changed)
          · exact Or.inr (by
              obtain ⟨target,good⟩ := chosen
              exact ⟨target,decide_eq_true good⟩)
    _ ≤ _ := (prEvent_or_le _ _ _).trans (add_le_add le_rfl (prEvent_exists_le _ _))

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAppCoverage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAppCoverage.outcome_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAppCoverage.outcome_selected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAppCoverage.outcome_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAppCoverage.outcome_split

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAppCoverage.broad_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAppCoverage.broad_probability
