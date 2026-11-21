-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryStartupTargets
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityChangedBound
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCanonical
import BeaconcryptCore.Computational.RegistrationNativeLorCoverage
import BeaconcryptCore.Computational.RegistrationNativeIdentityOriginLedger
import BeaconcryptCore.Computational.RegistrationNativeLorCanonical
import BeaconcryptCore.Computational.RegistrationNativePlatformNativeBundleFields
import BeaconcryptCore.Computational.RegistrationNativeLedgerJournal
import BeaconcryptCore.Computational.RegistrationNativePrekeyPublicationTrace
import BeaconcryptCore.Computational.RegistrationNativeIdentityPublicationTrace
/-! Original broad LR winning and eligibility events retain their actual initialized dynamic-writer profile. Concrete source publication fields derive the canonical split; its public shares are disjoint in that same original experiment and charge one changed-prekey event. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLorCoverage
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

/-- Literal current startup and full compilation retain the original ledger transcript at every supported outcome. -/
theorem outcome_consistent (observed : RegistrationNativeEvents.Observed A Native × Platform)
    (supported : some observed ∈ support whole) : RegistrationNativeLedger.Consistent observed.1.2.1 := by
  obtain ⟨initial,_started,ran⟩ := RegistrationNativePlatformOrdinaryStartupTargets.full_receipt setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds adversary previous observed supported
  exact RegistrationNativeFullCompiler.ledger_projection setup.source.crypto canonical _ bounds _ .P _ _
    (observed.1.1,(observed.1.2.1,(observed.1.2.2,observed.2))) ran

/-- The explicit test-existence conjunct is derived on actual current runtime support, including failed sends. -/
theorem outcome_observer (budget : Budget) (filter : RegistrationNativeLorEvents.Filter A) (guess : A → Bool)
    (target : Fin budget.accept × Fin budget.capacity) (winning : Bool)
    (observed : RegistrationNativeEvents.Observed A Native × Platform) (supported : some observed ∈ support whole) :
    RegistrationNativeLorRecordSecurity.observer setup.source.crypto canonical serverKeyId budget filter guess target winning (observed.1.1,observed.1.2.1) =
      if winning then RegistrationNativeLorCanonical.w setup.source.crypto canonical serverKeyId budget filter guess target (observed.1.1,observed.1.2.1)
      else RegistrationNativeLorCanonical.j setup.source.crypto canonical serverKeyId budget filter target (observed.1.1,observed.1.2.1) := by
  obtain ⟨initial,started,ran⟩ := RegistrationNativePlatformOrdinaryStartupTargets.full_receipt setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds adversary previous observed supported
  have sender := (RegistrationNativeKemCandidateStartup.start_facts setup source ensureInit identityIndex serverKeyId initial started).2.2
  rw [←sender]
  exact RegistrationNativeLorRecordSecurity.observer_run setup.source.crypto canonical _ bounds _ .P _ _ _ ran budget filter guess target winning

/-- Each broad original current-runtime LR hit pays one original changed-prekey event or names a canonical good-target share. -/
theorem outcome_split (budget : Budget) (filter : RegistrationNativeLorEvents.Filter A) (guess : A → Bool)
    (bounded : ∀ publicInput,RegistrationNativeInterface.Respects budget (adversary publicInput))
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes,bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
    (winning : Bool) (observed : RegistrationNativeEvents.Observed A Native × Platform)
    (supported : some observed ∈ support whole)
    (hit : broad setup.source.crypto canonical serverKeyId budget filter guess winning (observed.1.1,observed.1.2.1) = true) :
    RegistrationNativeIdentityOriginEvents.Changed setup.joint canonical observed.1.2.1.transcript observed.1.2.2.beacons ∨
      ∃ target : Fin budget.accept × Fin budget.capacity,
        RegistrationNativeLorRecordSecurity.observer setup.source.crypto canonical serverKeyId budget filter guess target winning (observed.1.1,observed.1.2.1) = true := by
  classical
  have eligibility : RegistrationNativeLorEvents.j setup.source.crypto canonical serverKeyId budget filter (observed.1.1,observed.1.2.1) = true := by
    cases winning with
    | false => exact hit
    | true =>
      have both : RegistrationNativeLorEvents.j setup.source.crypto canonical serverKeyId budget filter (observed.1.1,observed.1.2.1) = true ∧
          decide (observed.1.2.1.ledger.test.map PqxdhDeploymentSecrecy.TestState.bit = some (guess observed.1.1)) = true := by
        simpa only [broad,Bool.true_eq,ite_true,RegistrationNativeLorEvents.w_eq,Bool.and_eq_true] using hit
      exact both.1
  obtain ⟨initial,started,ran⟩ := RegistrationNativePlatformOrdinaryStartupTargets.run_receipt setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds adversary previous observed supported
  have sender := (RegistrationNativeKemCandidateStartup.start_facts setup source ensureInit identityIndex serverKeyId initial started).2.2
  rw [←sender] at eligibility hit ⊢
  rcases RegistrationNativePlatformOrdinaryCanonical.real_eligible_split setup checks route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets shortRejects
    bounds .P (adversary initial.public) budget (bounded initial.public) filter initial.state previous
    (((observed.1.1,observed.1.2.1),observed.1.2.2),observed.2) ran eligibility with changed | chosen
  · exact Or.inl changed
  · right
    obtain ⟨target,good⟩ := chosen
    refine ⟨target,?_⟩
    have packed := RegistrationNativePlatformOrdinaryRunPacking.supported setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      bounds .P (adversary initial.public) initial.state previous (((observed.1.1,observed.1.2.1),observed.1.2.2),observed.2) ran
    rw [RegistrationNativeLorRecordSecurity.observer_run setup.source.crypto canonical _ bounds _ .P _ _ _ packed budget filter guess target winning]
    cases winning with
    | false => exact decide_eq_true good
    | true =>
      have both : RegistrationNativeLorEvents.j setup.source.crypto canonical initial.created.server.server.metadata.sender budget filter (observed.1.1,observed.1.2.1) = true ∧
          decide (observed.1.2.1.ledger.test.map PqxdhDeploymentSecrecy.TestState.bit = some (guess observed.1.1)) = true := by
        simpa only [broad,Bool.true_eq,ite_true,RegistrationNativeLorEvents.w_eq,Bool.and_eq_true] using hit
      simpa only [Bool.true_eq,ite_true,RegistrationNativeLorCanonical.w,RegistrationNativeLorCanonical.j,Bool.and_eq_true,decide_eq_true_eq] using
        And.intro good (of_decide_eq_true both.2)

local notation "job" => RegistrationNativePlatformOrdinaryExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds PqxdhDeploymentInterface.Mode.P adversary

/-- Canonical share masses are disjoint in the same actual initialized native/platform experiment. -/
theorem share_mass (budget : Budget) (filter : RegistrationNativeLorEvents.Filter A) (guess : A → Bool) (winning : Bool) :
    (∑ target : Fin budget.accept × Fin budget.capacity,
      Pr{let result ← ((job (fun actual => RegistrationNativeLorRecordSecurity.observer setup.source.crypto canonical serverKeyId budget filter guess target winning (actual.1,actual.2.1))).run previous)}[result.1 = true]) ≤
    Pr{let result ← ((job (fun actual => broad setup.source.crypto canonical serverKeyId budget filter guess winning (actual.1,actual.2.1))).run previous)}[result.1 = true] := by
  classical
  let chosen := fun outcome : Option (RegistrationNativeEvents.Observed A Native × Platform) =>
    outcome.bind fun actual => select setup.source.crypto canonical serverKeyId budget filter guess winning (actual.1.1,actual.1.2.1)
  simp only [RegistrationNativePlatformOrdinaryStartupTargets.profile_probability]
  calc
    _ = ∑ target : Fin budget.accept × Fin budget.capacity,
      Pr{let outcome ← whole}[chosen outcome = some target] := by
        apply Finset.sum_congr rfl
        intro target _member
        apply prEvent_congr_of_support
        intro outcome supported
        cases outcome with
        | none => simp only [Option.any_none,chosen,Option.bind_none,reduceCtorEq,Bool.false_eq_true]
        | some actual =>
          exact (RegistrationNativeLorCoverage.selected_iff setup.source.crypto canonical serverKeyId budget filter guess winning _
            (outcome_consistent setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous actual supported) target).symm
    _ = Pr{let outcome ← whole}[(chosen outcome).isSome] := (prEvent_isSome_eq_sum _ chosen).symm
    _ ≤ _ := by
      apply prEvent_mono_of_support
      intro outcome supported selected
      cases outcome with
      | none => cases selected
      | some actual =>
        obtain ⟨target,picked⟩ := Option.isSome_iff_exists.mp selected
        have observed := (RegistrationNativeLorCoverage.selected_iff setup.source.crypto canonical serverKeyId budget filter guess winning _
          (outcome_consistent setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous actual supported) target).mp picked
        exact RegistrationNativeLorCoverage.share_broad setup.source.crypto canonical serverKeyId budget filter guess winning _ target observed

/-- Broad original winning and eligibility probabilities charge one original changed-prekey event and one canonical share family. -/
theorem broad_probability (budget : Budget) (filter : RegistrationNativeLorEvents.Filter A) (guess : A → Bool)
    (bounded : ∀ publicInput,RegistrationNativeInterface.Respects budget (adversary publicInput))
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes,bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
    (winning : Bool) :
    Pr{let result ← ((job (fun actual => broad setup.source.crypto canonical serverKeyId budget filter guess winning (actual.1,actual.2.1))).run previous)}[result.1 = true] ≤
    Pr{let result ← ((job (RegistrationNativeIdentityOriginEvents.event setup.joint canonical)).run previous)}[result.1 = true] +
    ∑ target : Fin budget.accept × Fin budget.capacity,
      Pr{let result ← ((job (fun actual => RegistrationNativeLorRecordSecurity.observer setup.source.crypto canonical serverKeyId budget filter guess target winning (actual.1,actual.2.1))).run previous)}[result.1 = true] := by
  classical
  simp only [RegistrationNativePlatformOrdinaryStartupTargets.profile_probability]
  calc
    _ ≤ Pr{let outcome ← whole}[
      outcome.any (fun actual => RegistrationNativeIdentityOriginEvents.event setup.joint canonical actual.1) = true ∨
      ∃ target : Fin budget.accept × Fin budget.capacity,
        outcome.any (fun actual => RegistrationNativeLorRecordSecurity.observer setup.source.crypto canonical serverKeyId budget filter guess target winning (actual.1.1,actual.1.2.1)) = true] := by
        apply prEvent_mono_of_support
        intro outcome supported observed
        cases outcome with
        | none => cases observed
        | some actual =>
          rcases outcome_split setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous
            budget filter guess bounded shortRejects winning actual supported observed with changed | chosen
          · exact Or.inl (decide_eq_true changed)
          · exact Or.inr chosen
    _ ≤ _ := (prEvent_or_le _ _ _).trans (add_le_add le_rfl (prEvent_exists_le _ _))

/-- Original broad winning and eligibility charge the actual ordinary joint-signature family once, with the same original canonical observer family. -/
theorem broad_bound (budget : Budget) (filter : RegistrationNativeLorEvents.Filter A) (guess : A → Bool)
    (bounded : ∀ publicInput,RegistrationNativeInterface.Respects budget (adversary publicInput))
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes,bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
    (winning : Bool) (count : Nat) (room : budget.create ≤ count+1)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    Pr{let result ← ((job (fun actual => broad setup.source.crypto canonical serverKeyId budget filter guess winning (actual.1,actual.2.1))).run previous)}[result.1 = true] ≤
    (∑ target : Fin (count+1), PqxdhJointIdentity.advantage setup.joint
      (RegistrationNativePlatformIdentityOriginBound.reduction (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        source ensureInit identityIndex serverKeyId bounds .P adversary (fun _ => false) previous count fallback ordinaryFallback target)) +
    ∑ target : Fin budget.accept × Fin budget.capacity,
      Pr{let result ← ((job (fun actual => RegistrationNativeLorRecordSecurity.observer setup.source.crypto canonical serverKeyId budget filter guess target winning (actual.1,actual.2.1))).run previous)}[result.1 = true] := by
  exact (broad_probability setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget filter guess bounded shortRejects winning).trans
    (add_le_add (RegistrationNativePlatformIdentityChangedBound.changed_prekey_bound setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer source ensureInit identityIndex serverKeyId bounds .P adversary previous budget bounded count room fallback ordinaryFallback) le_rfl)

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLorCoverage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLorCoverage.outcome_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLorCoverage.outcome_consistent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLorCoverage.outcome_observer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLorCoverage.outcome_observer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLorCoverage.outcome_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLorCoverage.outcome_split

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLorCoverage.share_mass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLorCoverage.share_mass

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLorCoverage.broad_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLorCoverage.broad_probability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLorCoverage.broad_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLorCoverage.broad_bound
