-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicKeyBound
import BeaconcryptCore.Computational.RegistrationNativeG3SelectiveDirectGame
/-! The actual corrected initialized uniform108 client has its derived finite material44/seed64 table law. Source callback budgets exclude finite-slot overflow. This analytical table representation still returns full material to its private compiler; subsequent relocation into the opaque-slot World is separate. All dynamic platform behavior remains inside the unchanged concrete phase client. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicUniformTables
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
    (decision : Value × RegistrationNativeLedger.State → Bool)

open RegistrationNativePlatformPublicKeyExperiment (phaseClient entryClient)

omit primitive in
private theorem lazy_coins {Result : Type} (work : ProbComp Result)
    (before : (Pqxdh.Bytes →ₒ PqxdhServerAuthKeySchedule.Output).QueryCache) :
    (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl
      (simulateQ RegistrationNativeKeyCompiler.coins work)).run before =
      (fun value => (value, before)) <$> work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : PqxdhRegistrationJointKemSecondEntry.lazyImpl ∘ₛ RegistrationNativeKeyCompiler.coins =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT ((Pqxdh.Bytes →ₒ PqxdhServerAuthKeySchedule.Output).QueryCache) ProbComp) := by
    funext query
    rfl
  rw [same, simulateQ_liftTarget, simulateQ_ofLift_eq_self, StateT.run_liftM, bind_pure_comp]

/-- The actual fixed-challenge compiler inherits its entire material count from literal source callbacks, independently of allocator behavior. -/
theorem compiled_bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (previous : Platform) :
    (RegistrationNativeG3SelectiveDirectGame.compiled setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
      (phaseClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar))).IsQueryBoundP
        RegistrationNativeG3FirstTouchBound.IsValue (budget.cap 4 + budget.cap 5) := by
  apply RegistrationNativeKeyBounds.client_bound
  apply RegistrationNativeRetainedService.client_bound
  rw [phaseClient, isQueryBoundP_map_iff]
  exact RegistrationNativePlatformPublicRetainedCaps.client_bound (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget bounded _ previous

noncomputable def tableGame (budget : PqxdhDeploymentInterface.Budget)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (previous : Platform) : ProbComp Bool := do
  let seed ← PqxdhJointIdentity.sampleSeed
  let scalar ← PqxdhJointGapDh.sampleScalar
  let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)
  let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable (budget.cap 4 + budget.cap 5)
  (simulateQ (RegistrationNativeG3RetainedCallbacks.keys setup.source
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate materials seeds)
    (phaseClient (n := budget.cap 4 + budget.cap 5) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar))).run'
      (RegistrationNativeHiddenService.initial, ∅)

/-- The original concrete uniform108 key game equals its finite selective material44/seed64 table game, with no capacity or sampler premise. -/
theorem uniform_tables (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (previous : Platform) :
    RegistrationNativeKeyHybrid.uniform (entryClient (n := budget.cap 4 + budget.cap 5) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous) =ᵈ
      tableGame setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget candidate previous := by
  unfold RegistrationNativeKeyHybrid.uniform entryClient tableGame
  simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, lazy_coins, bind_map_left, map_bind]
  apply _root_.EvalDistEq.bind_right
  intro seed
  apply _root_.EvalDistEq.bind_right
  intro scalar
  rw [← StateT.run'_eq]
  exact EvalDistEq.of_evalDist_eq (RegistrationNativeG3SelectiveDirectGame.lazy_source setup.source
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate
    (phaseClient (n := budget.cap 4 + budget.cap 5) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar))
    (compiled_bound (n := budget.cap 4 + budget.cap 5) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget bounded seed scalar previous)).evalDist_eq
/-- The actual initialized full-ledger source decision has the same first two-hop bound against this concrete finite-table game. -/
theorem source_tables_distance (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (previous : Platform) :
    (Prod.fst <$> (RegistrationNativePlatformOrdinaryExperiment.profile (n := budget.cap 4 + budget.cap 5) setup checks wire route representation source ensureInit identityIndex serverKeyId
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
      (fun result => decision (result.1, result.2.1))).run previous).boolDistance
      (tableGame setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget candidate previous) ≤
      RegistrationNativeRelatedFamily.advantage setup.hmac setup.joint setup.dh
        (fun publicValue => simulateQ RegistrationNativeRelatedRoot.reduction
          (RegistrationNativePlatformPublicKeyExperiment.rootClient (n := budget.cap 4 + budget.cap 5) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous publicValue)) +
      ∑ index ∈ Finset.range (budget.cap 4 + budget.cap 5), RegistrationBoundKeySchedule.keyLoss setup.source setup.hmac
        (RegistrationNativeKeyHybrid.reduction setup.source setup.hmac (entryClient (n := budget.cap 4 + budget.cap 5) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous) index) := by
  have compared := RegistrationNativePlatformPublicKeyBound.source_distance (n := budget.cap 4 + budget.cap 5) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision representation correct budget bounded previous
  unfold ProbComp.boolDistance at compared ⊢
  rw [← (uniform_tables setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget bounded candidate previous).evalDist_eq]
  exact compared

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicUniformTables

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicUniformTables.compiled_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicUniformTables.compiled_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicUniformTables.uniform_tables' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicUniformTables.uniform_tables

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicUniformTables.source_tables_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicUniformTables.source_tables_distance
