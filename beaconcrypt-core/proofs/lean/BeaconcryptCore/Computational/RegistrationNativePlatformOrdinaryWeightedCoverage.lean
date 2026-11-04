-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryStartupTargets
import BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityChangedBound
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCanonical
import BeaconcryptCore.Computational.RegistrationNativeLorCoverage
import BeaconcryptCore.Computational.RegistrationNativeIdentityOriginLedger
import BeaconcryptCore.Computational.RegistrationNativeLorCanonical
import BeaconcryptCore.Computational.RegistrationNativePlatformNativeBundleFields
import BeaconcryptCore.Computational.RegistrationNativeLedgerJournal
import BeaconcryptCore.Computational.RegistrationNativePrekeyPublicationTrace
import BeaconcryptCore.Computational.RegistrationNativeIdentityPublicationTrace
/-! The original initialized APP shares use the functional public claim selector in one actual native/platform experiment. Their selector masses are disjoint, and the original Changed event is charged once through the actual current signature-origin reduction. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWeightedCoverage
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

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

open PqxdhDeploymentInterface (Budget FreshBounds)
open RegistrationNativeLorCoverage (broad select)
variable (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) A) (previous : Platform)
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "whole" => RegistrationNativePlatformOrdinaryStartupTargets.outcome (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer source ensureInit identityIndex serverKeyId bounds adversary previous


/-- Each original APP success pays Changed or the unique public-selector good share on the same source result. -/
theorem outcome_split (budget : Budget) (bounded : ∀ publicInput,RegistrationNativeInterface.Respects budget (adversary publicInput))
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes,bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
    (claim : A → Option (Nat × Pqxdh.Bytes)) (observed : RegistrationNativeEvents.Observed A Native × Platform)
    (supported : some observed ∈ support whole)
    (winning : RegistrationNativeEvents.CEAppWin setup.source.crypto canonical serverKeyId budget claim observed.1) :
    RegistrationNativeIdentityOriginEvents.Changed setup.joint canonical observed.1.2.1.transcript observed.1.2.2.beacons ∨
      ∃ target : Fin budget.accept × Fin budget.capacity,
        RegistrationNativeCanonicalCoverage.GoodSelectedAt setup.source.crypto canonical serverKeyId budget claim target observed.1 := by
  obtain ⟨initial,started,ran⟩ := RegistrationNativePlatformOrdinaryStartupTargets.full_receipt setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds adversary previous observed supported
  have sender := (RegistrationNativeKemCandidateStartup.start_facts setup source ensureInit identityIndex serverKeyId initial started).2.2
  rw [←sender] at winning ⊢
  rcases RegistrationNativePlatformOrdinaryPrekeySplit.ceapp_split setup checks route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets shortRejects
    bounds .P (adversary initial.public) (initial.state,previous) budget claim (observed.1.1,(observed.1.2.1,(observed.1.2.2,observed.2))) ran winning with changed | good
  · exact Or.inl changed
  · exact Or.inr (RegistrationNativeCanonicalCoverage.good_selected setup.source.crypto canonical _ bounds _ .P _ budget (bounded initial.public) _ claim
      (observed.1.1,(observed.1.2.1,(observed.1.2.2,observed.2))) ran good)

local notation "job" => RegistrationNativePlatformOrdinaryExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds PqxdhDeploymentInterface.Mode.P adversary

/-- Selector probabilities belong to one original initialized experiment, including every native and platform failure. -/
theorem selector_mass (budget : Budget) (claim : A → Option (Nat × Pqxdh.Bytes)) :
    (∑ target : Fin budget.accept × Fin budget.capacity,
      Pr{let result ← ((job (fun actual => RegistrationNativeCanonicalSelector.selected setup.source.crypto canonical serverKeyId budget claim target actual.1 actual.2.1)).run previous)}[result.1 = true]) ≤ 1 := by
  classical
  have masses := sum_prEvent_eq_some_le_one whole
    (fun outcome => outcome.bind fun actual => RegistrationNativeCanonicalSelector.chooseLedger setup.source.crypto canonical serverKeyId budget
      ((claim actual.1.1).map Prod.fst) actual.1.2.1)
  convert masses using 1
  apply Finset.sum_congr rfl
  intro target _member
  simp only [RegistrationNativePlatformOrdinaryStartupTargets.profile_probability]
  apply prEvent_congr
  intro outcome
  cases outcome with
  | none => simp only [Option.any_none,Option.bind_none,reduceCtorEq,Bool.false_eq_true]
  | some actual => simp only [Option.any_some,Option.bind_some,RegistrationNativeCanonicalSelector.selected,decide_eq_true_eq]

/-- Broad APP retains the disjoint good-selector family and one original signature-origin event. -/
theorem broad_probability (budget : Budget) (bounded : ∀ publicInput,RegistrationNativeInterface.Respects budget (adversary publicInput))
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes,bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
    (claim : A → Option (Nat × Pqxdh.Bytes)) :
    Pr{let result ← ((job (RegistrationNativeEvents.ceAppEvent setup.source.crypto canonical serverKeyId budget claim)).run previous)}[result.1 = true] ≤
    Pr{let result ← ((job (RegistrationNativeIdentityOriginEvents.event setup.joint canonical)).run previous)}[result.1 = true] +
    ∑ target : Fin budget.accept × Fin budget.capacity,
      Pr{let result ← ((job (RegistrationNativeCanonicalCoverage.event setup.source.crypto canonical serverKeyId budget claim target)).run previous)}[result.1 = true] := by
  classical
  simp only [RegistrationNativePlatformOrdinaryStartupTargets.profile_probability]
  calc
    _ ≤ Pr{let outcome ← whole}[
      outcome.any (fun actual => RegistrationNativeIdentityOriginEvents.event setup.joint canonical actual.1) = true ∨
      ∃ target : Fin budget.accept × Fin budget.capacity,
        outcome.any (fun actual => RegistrationNativeCanonicalCoverage.event setup.source.crypto canonical serverKeyId budget claim target actual.1) = true] := by
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

/-- The original broad APP event pays the actual ordinary joint-signature family once, retaining the functional public target shares. -/
theorem broad_bound (budget : Budget) (bounded : ∀ publicInput,RegistrationNativeInterface.Respects budget (adversary publicInput))
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes,bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
    (claim : A → Option (Nat × Pqxdh.Bytes)) (count : Nat) (room : budget.create ≤ count+1)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    Pr{let result ← ((job (RegistrationNativeEvents.ceAppEvent setup.source.crypto canonical serverKeyId budget claim)).run previous)}[result.1 = true] ≤
    (∑ target : Fin (count+1), PqxdhJointIdentity.advantage setup.joint
      (RegistrationNativePlatformIdentityOriginBound.reduction (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        source ensureInit identityIndex serverKeyId bounds .P adversary (fun _ => false) previous count fallback ordinaryFallback target)) +
    ∑ target : Fin budget.accept × Fin budget.capacity,
      Pr{let result ← ((job (RegistrationNativeCanonicalCoverage.event setup.source.crypto canonical serverKeyId budget claim target)).run previous)}[result.1 = true] := by
  exact (broad_probability setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget bounded shortRejects claim).trans
    (add_le_add (RegistrationNativePlatformIdentityChangedBound.changed_prekey_bound setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer source ensureInit identityIndex serverKeyId bounds .P adversary previous budget bounded count room fallback ordinaryFallback) le_rfl)

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWeightedCoverage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWeightedCoverage.outcome_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWeightedCoverage.outcome_split

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWeightedCoverage.selector_mass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWeightedCoverage.selector_mass

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWeightedCoverage.broad_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWeightedCoverage.broad_probability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWeightedCoverage.broad_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWeightedCoverage.broad_bound
