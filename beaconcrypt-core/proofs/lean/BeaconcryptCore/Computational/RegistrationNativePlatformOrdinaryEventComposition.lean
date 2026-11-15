-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLorCoverage
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWeightedCoverage
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityChangedBound
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCanonical
import BeaconcryptCore.Computational.RegistrationNativeLorCoverage
import BeaconcryptCore.Computational.RegistrationNativeIdentityOriginLedger
import BeaconcryptCore.Computational.RegistrationNativeLorCanonical
import BeaconcryptCore.Computational.RegistrationNativePlatformNativeBundleFields
import BeaconcryptCore.Computational.RegistrationNativeLedgerJournal
import BeaconcryptCore.Computational.RegistrationNativePrekeyPublicationTrace
import BeaconcryptCore.Computational.RegistrationNativeIdentityPublicationTrace
/-! Probability composition for the literal initialized ordinary source events. The target inequalities are supplied by the separately derived record comparison and ideal source baselines; this file preserves one original Changed charge and one same-run APP baseline when combining those targets. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryEventComposition
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

local notation "job" => RegistrationNativePlatformOrdinaryExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds PqxdhDeploymentInterface.Mode.P adversary
noncomputable def original (observe : A × RegistrationNativeLedger.State → Bool) : ProbComp Bool :=
  Prod.fst <$> ((job (fun actual => observe (actual.1,actual.2.1))).run previous)

noncomputable def lorShare (budget : Budget) (filter : RegistrationNativeLorEvents.Filter A) (guess : A → Bool)
    (target : Fin budget.accept × Fin budget.capacity) (winning : Bool) :=
  original (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous
    (RegistrationNativeLorRecordSecurity.observer setup.source.crypto canonical serverKeyId budget filter guess target winning)

noncomputable def lorBroad (budget : Budget) (filter : RegistrationNativeLorEvents.Filter A) (guess : A → Bool) (winning : Bool) :=
  original (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous
    (RegistrationNativeLorCoverage.broad setup.source.crypto canonical serverKeyId budget filter guess winning)

noncomputable def originLoss (count : Nat) (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) : ℝ≥0∞ :=
  ∑ target : Fin (count+1), PqxdhJointIdentity.advantage setup.joint
    (RegistrationNativePlatformIdentityOriginBound.reduction (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds .P adversary (fun _ => false) previous count fallback ordinaryFallback target)

/-- Combining separately proved target comparisons charges the original source Changed family once in both centered directions. -/
theorem lor_centered_of_targets (budget : Budget) (filter : RegistrationNativeLorEvents.Filter A) (guess : A → Bool)
    (bounded : ∀ publicInput,RegistrationNativeInterface.Respects budget (adversary publicInput))
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes,bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
    (count : Nat) (room : budget.create ≤ count+1) (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (loss : (Fin budget.accept × Fin budget.capacity) → Bool → ℝ≥0∞)
    (targets : ∀ target,
      (𝒟[lorShare (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget filter guess target true] {true} ≤
        2⁻¹ * 𝒟[lorShare (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget filter guess target false] {true} + loss target true + 2⁻¹ * loss target false) ∧
      (2⁻¹ * 𝒟[lorShare (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget filter guess target false] {true} ≤
        𝒟[lorShare (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget filter guess target true] {true} + loss target true + 2⁻¹ * loss target false)) :
    (𝒟[lorBroad (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget filter guess true] {true} ≤
      2⁻¹ * 𝒟[lorBroad (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget filter guess false] {true} +
      originLoss (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous count fallback ordinaryFallback +
      (∑ target,loss target true) + 2⁻¹ * (∑ target,loss target false)) ∧
    (2⁻¹ * 𝒟[lorBroad (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget filter guess false] {true} ≤
      𝒟[lorBroad (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget filter guess true] {true} +
      originLoss (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous count fallback ordinaryFallback +
      (∑ target,loss target true) + 2⁻¹ * (∑ target,loss target false)) := by
  have cover (winning : Bool) := RegistrationNativePlatformOrdinaryLorCoverage.broad_bound (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget filter guess bounded shortRejects winning count room fallback ordinaryFallback
  have masses (winning : Bool) := RegistrationNativePlatformOrdinaryLorCoverage.share_mass (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget filter guess winning
  have split (winning : Bool) :
      𝒟[lorBroad (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget filter guess winning] {true} ≤
      originLoss (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous count fallback ordinaryFallback +
      ∑ target,𝒟[lorShare (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget filter guess target winning] {true} := by
    simpa only [lorBroad,lorShare,original,originLoss,←prEvent_eq_evalDist_singleton _ true,prEvent_map] using cover winning
  have shares (winning : Bool) :
      (∑ target,𝒟[lorShare (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget filter guess target winning] {true}) ≤
      𝒟[lorBroad (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget filter guess winning] {true} := by
    simpa only [lorBroad,lorShare,original,←prEvent_eq_evalDist_singleton _ true,prEvent_map] using masses winning
  have forward := Finset.sum_le_sum (s := Finset.univ) (fun target _member => (targets target).1)
  have reverse := Finset.sum_le_sum (s := Finset.univ) (fun target _member => (targets target).2)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at forward reverse
  have fromShares := forward.trans (add_le_add (add_le_add (mul_le_mul' le_rfl (shares false)) le_rfl) le_rfl)
  have toShares := reverse.trans (add_le_add (add_le_add (shares true) le_rfl) le_rfl)
  have halfOrigin := mul_le_mul' (by norm_num : (2⁻¹ : ℝ≥0∞) ≤ 1)
    (le_refl (originLoss (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous count fallback ordinaryFallback))
  rw [one_mul] at halfOrigin
  constructor
  · simpa only [add_assoc,add_comm,add_left_comm] using (split true).trans (add_le_add le_rfl fromShares)
  · have scaled := mul_le_mul' (le_refl (2⁻¹ : ℝ≥0∞)) (split false)
    rw [mul_add] at scaled
    simpa only [add_assoc,add_comm,add_left_comm] using scaled.trans (add_le_add halfOrigin toShares)

noncomputable def appShare (budget : Budget) (claim : A → Option (Nat × Pqxdh.Bytes))
    (target : Fin budget.accept × Fin budget.capacity) (winning : Bool) :=
  original (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous
    (if winning then RegistrationNativeCanonicalCoverage.decision setup.source.crypto canonical serverKeyId budget claim target
      else fun actual => RegistrationNativeCanonicalSelector.selected setup.source.crypto canonical serverKeyId budget claim target actual.1 actual.2)

noncomputable def appBroad (budget : Budget) (claim : A → Option (Nat × Pqxdh.Bytes)) :=
  original (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous
    (fun actual => RegistrationNativeEvents.ceAppEvent setup.source.crypto canonical serverKeyId budget claim (actual.1,(actual.2,())))

/-- Returning each selector to the same original source experiment leaves one fresh-byte baseline. -/
theorem app_weighted_of_targets (budget : Budget) (claim : A → Option (Nat × Pqxdh.Bytes))
    (bounded : ∀ publicInput,RegistrationNativeInterface.Respects budget (adversary publicInput))
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes,bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
    (count : Nat) (room : budget.create ≤ count+1) (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (loss : (Fin budget.accept × Fin budget.capacity) → Bool → ℝ≥0∞)
    (targets : ∀ target,
      𝒟[appShare (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget claim target true] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
        𝒟[appShare (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget claim target false] {true} +
      loss target true + ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ * loss target false) :
    𝒟[appBroad (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget claim] {true} ≤
      originLoss (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous count fallback ordinaryFallback +
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ + (∑ target,loss target true) + ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ * (∑ target,loss target false) := by
  have cover := RegistrationNativePlatformOrdinaryWeightedCoverage.broad_bound (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget bounded shortRejects claim count room fallback ordinaryFallback
  have masses := RegistrationNativePlatformOrdinaryWeightedCoverage.selector_mass (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget claim
  have split :
      𝒟[appBroad (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget claim] {true} ≤
      originLoss (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous count fallback ordinaryFallback +
      ∑ target,𝒟[appShare (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget claim target true] {true} := by
    simp only [appBroad,appShare,original,originLoss,ite_true,←prEvent_eq_evalDist_singleton _ true,prEvent_map,RegistrationNativeCanonicalCoverage.decision]
    convert cover using 1 <;> rfl
  have shares :
      (∑ target,𝒟[appShare (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget claim target false] {true}) ≤ 1 := by
    simpa only [appShare,original,Bool.false_eq_true,ite_false,←prEvent_eq_evalDist_singleton _ true,prEvent_map] using masses
  have summed := Finset.sum_le_sum (s := Finset.univ) (fun target _member => targets target)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at summed
  have baseline := mul_le_mul' (le_refl (((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹)) shares
  rw [mul_one] at baseline
  have boundedShares := summed.trans (add_le_add (add_le_add baseline le_rfl) le_rfl)
  simpa only [add_assoc] using split.trans (add_le_add le_rfl boundedShares)

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryEventComposition

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryEventComposition.lor_centered_of_targets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryEventComposition.lor_centered_of_targets

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryEventComposition.app_weighted_of_targets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryEventComposition.app_weighted_of_targets
