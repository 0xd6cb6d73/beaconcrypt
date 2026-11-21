-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordKeyExperiment
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedRecordProfile
/-! The actual initialized dynamic runtime retains its terminal CTX cache, produced frames and raw attempt counters through its uniform108 key experiment through one related-input advantage and the five ordinary key-schedule losses. The material entry cap is derived from literal corrected build/finish syntax and the original raw resource budget. Opaque-slot and record-hybrid comparisons remain subsequent steps. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordKeyBound
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {I KemSK Platform E Value : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → RegistrationNativePlatformPublicWorldObservation.RecordView → Bool)

open RegistrationNativePlatformPublicRecordKeyExperiment (rootClient phaseClient entryClient)

omit primitive in
private theorem coin_free {Result : Type} (work : ProbComp Result) :
    (simulateQ RegistrationNativeKeyCompiler.coins work).IsQueryBoundP
      (PqxdhRegistrationJointKemSecondEntry.IsValue (D := Pqxdh.Bytes) (R := PqxdhServerAuthKeySchedule.Output)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [RegistrationNativeKeyCompiler.coins, PqxdhRegistrationJointKemSecondEntry.IsValue, isQueryBoundP_query_iff]

/-- Only the original actual build and finish allowances pay for admitted protected key entries; initialization and allocator randomness add none. -/
theorem entry_bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue)) (previous : Platform) :
    (entryClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous).IsQueryBoundP
      (PqxdhRegistrationJointKemSecondEntry.IsValue (D := Pqxdh.Bytes) (R := PqxdhServerAuthKeySchedule.Output))
      (budget.cap 4 + budget.cap 5) := by
  unfold entryClient
  refine (isQueryBoundP_bind (n := 0) (m := budget.cap 4 + budget.cap 5) (coin_free _) ?_).mono (by omega)
  intro seed _seed
  refine (isQueryBoundP_bind (n := 0) (m := budget.cap 4 + budget.cap 5) (coin_free _) ?_).mono (by omega)
  intro scalar _scalar
  apply RegistrationNativeKeyBounds.client_bound
  apply RegistrationNativeRetainedService.client_bound
  rw [phaseClient, isQueryBoundP_map_iff]
  exact RegistrationNativePlatformPublicRetainedRecordProfile.client_bound (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget bounded _ previous

/-- The actual corrected whole-runtime key experiment pays the five standard primitive losses under its derived source material bill. -/
theorem key_bound (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue)) (previous : Platform) :
    (RegistrationNativeRelatedRoot.idealRootGame setup.hmac setup.joint setup.dh
      (rootClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous)).boolDistance
      (RegistrationNativeKeyHybrid.uniform (entryClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous)) ≤
      ∑ index ∈ Finset.range (budget.cap 4 + budget.cap 5), RegistrationBoundKeySchedule.keyLoss setup.source setup.hmac
        (RegistrationNativeKeyHybrid.reduction setup.source setup.hmac (entryClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous) index) := by
  have first := RegistrationNativePlatformPublicRecordKeyExperiment.hybrid_zero (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision correct.root previous
  unfold ProbComp.boolDistance
  rw [first.evalDist_eq]
  exact RegistrationNativeKeyHybrid.bound setup.source setup.hmac correct _ _
    (entry_bound (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget bounded previous)

/-- Every original ledger-and-record observation in the actual initialized dynamic runtime has this source-backed first two-hop distance, with allocator failures retained. -/
theorem source_distance (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue)) (previous : Platform) :
    (Prod.fst <$> (RegistrationNativePlatformOrdinaryExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
      (fun result => decision (result.1, result.2.1)
        (RegistrationNativePlatformPublicWorldObservation.recordView (RegistrationNativePlatformPublicWorldObservation.world result.2.2)))).run previous).boolDistance
      (RegistrationNativeKeyHybrid.uniform (entryClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous)) ≤
      RegistrationNativeRelatedFamily.advantage setup.hmac setup.joint setup.dh
        (fun publicValue => simulateQ RegistrationNativeRelatedRoot.reduction (rootClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous publicValue)) +
      ∑ index ∈ Finset.range (budget.cap 4 + budget.cap 5), RegistrationBoundKeySchedule.keyLoss setup.source setup.hmac
        (RegistrationNativeKeyHybrid.reduction setup.source setup.hmac (entryClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous) index) := by
  have triangle := ProbComp.boolDistance_triangle
    (Prod.fst <$> (RegistrationNativePlatformOrdinaryExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
      (fun result => decision (result.1, result.2.1)
        (RegistrationNativePlatformPublicWorldObservation.recordView (RegistrationNativePlatformPublicWorldObservation.world result.2.2)))).run previous)
    (RegistrationNativeRelatedRoot.idealRootGame setup.hmac setup.joint setup.dh (rootClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous))
    (RegistrationNativeKeyHybrid.uniform (entryClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous))
  exact triangle.trans (add_le_add
    (le_of_eq (RegistrationNativePlatformPublicRecordKeyExperiment.family_distance (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision representation correct.root previous))
    (key_bound (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision correct budget bounded previous))
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordKeyBound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordKeyBound.entry_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordKeyBound.entry_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordKeyBound.key_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordKeyBound.key_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordKeyBound.source_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordKeyBound.source_distance
