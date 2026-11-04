-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordMaterializedTables
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicStartupFields
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordUniform
import BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedWhole
/-! The actual warmed startup cut supplies seed-table emptiness internally. The known-material source continuation therefore has the sampled opaque World interpretation, and the complete terminal record observer pays only the same actual repeated-role audit. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordOpaqueAfter
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
variable {I KemSK Platform E Value : Type} {base : OracleSpec I}
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

noncomputable def work (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (started : RegistrationNativePublicStartup.Started source) (reached : PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5)) :=
  Prod.fst <$> RegistrationNativePlatformMaterializedWhole.world setup wire (RegistrationNativeMldsa.owned source started.credential)
    seed scalar candidate (RegistrationNativeOpenRetainedReal.provider setup) checks source selectedOwner selectedAccept view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode
    (adversary ⟨setup.joint.publicKeys seed, started.credential.publicKey, serverKeyId⟩) (started.frontend, previous)
    (RegistrationNativeG3LocalMaterialCompletion.put
      (RegistrationNativeG3AuditTraceRun.cold (RegistrationNativeSelectiveHiddenInterpreter.initial
        (n := budget.cap 4 + budget.cap 5) (KemSK := KemSK) ()) ∅, reached)
      (RegistrationNativeG3LocalMaterialCompletedSource.cache materials)).1

private def observe {source : RegistrationNativeMldsa.Source}
    (decision : Value × RegistrationNativeLedger.State → RegistrationNativePlatformPublicWorldObservation.RecordView → Bool)
    (result : (((Value × RegistrationNativeLedger.State) × RegistrationNativePlatformPublicFrontend.State source Platform) ×
      RegistrationNativePlatformPublicWorldObservation.RecordView)) : Bool × Platform :=
  (decision result.1.1 result.2, result.1.2.2)

noncomputable def known (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (initialized : Option (RegistrationNativePublicStartup.Started source) × PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5)) :
    ProbComp (Bool × Platform) :=
  match initialized.1 with
  | none => do
      let _seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable (budget.cap 4 + budget.cap 5)
      pure (false, previous)
  | some started => observe decision <$>
      RegistrationNativePlatformG3RecordUniform.knownGame setup
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route
        (work setup checks wire source serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
          erased helper writer bounds mode adversary budget seed scalar candidate materials previous started initialized.2) initialized.2

noncomputable def hidden (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (initialized : Option (RegistrationNativePublicStartup.Started source) × PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5)) :
    ProbComp (Bool × Platform) :=
  match initialized.1 with
  | none => do
      let _seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable (budget.cap 4 + budget.cap 5)
      pure (false, previous)
  | some started => observe decision <$>
      RegistrationNativePlatformG3RecordCoupling.hidden setup
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route
        (work setup checks wire source serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
          erased helper writer bounds mode adversary budget seed scalar candidate materials previous started initialized.2) initialized.2

noncomputable def audit (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (initialized : Option (RegistrationNativePublicStartup.Started source) × PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5)) : ProbComp Bool :=
  match initialized.1 with
  | none => pure false
  | some started => do
      let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable (budget.cap 4 + budget.cap 5)
      let result ← RegistrationNativeG3GuardedCoupling.audit setup
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route
        (RegistrationNativeG3GuardedCoupling.overlay initialized.2 seeds)
        (work setup checks wire source serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
          erased helper writer bounds mode adversary budget seed scalar candidate materials previous started initialized.2) initialized.2
      pure result.2.2

/-- The actual startup supplies its own empty private seed table before the complete terminal-record source comparison. -/
theorem known_source (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (initialized : Option (RegistrationNativePublicStartup.Started source) × PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5))
    (supported : initialized ∈ support ((RegistrationNativePublicStartupFrame.startup setup source ensureInit identityIndex serverKeyId
      (setup.joint.publicKeys seed)).run PqxdhRecordLiftWorld.initial)) :
    (do
      let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable (budget.cap 4 + budget.cap 5)
      RegistrationNativePlatformPublicRecordMaterializedTables.after setup checks wire route source serverKeyId selectedOwner selectedAccept view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget seed scalar candidate materials seeds previous initialized) =
      known setup checks wire route source serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        bounds mode adversary decision budget seed scalar candidate materials previous initialized := by
  rcases initialized with ⟨_ | started, reached⟩
  · rfl
  · have empty : reached.seeds = PqxdhRecordLiftLazyTable.initial := (RegistrationNativePlatformPublicStartupFields.initialized setup source ensureInit identityIndex serverKeyId
      (setup.joint.publicKeys seed) (some started, reached) supported).1
    simp only [known, RegistrationNativePlatformG3RecordUniform.knownGame, map_bind]
    apply bind_congr
    intro seeds
    have overlay : RegistrationNativeG3GuardedCoupling.overlay reached seeds = seeds := by
      funext slot
      simp [RegistrationNativeG3GuardedCoupling.overlay, empty, PqxdhRecordLiftLazyTable.initial, OracleComp.completeTable]
    rw [overlay]
    have literal := RegistrationNativePlatformMaterializedWhole.run_record_source materials setup
      (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route wire
      (RegistrationNativeMldsa.owned source started.credential) seed scalar candidate (RegistrationNativeOpenRetainedReal.provider setup)
      checks source selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer seeds
      serverKeyId bounds mode (adversary ⟨setup.joint.publicKeys seed, started.credential.publicKey, serverKeyId⟩) (started.frontend, previous)
      (RegistrationNativeG3AuditTraceRun.cold (RegistrationNativeSelectiveHiddenInterpreter.initial
        (n := budget.cap 4 + budget.cap 5) (KemSK := KemSK) ()) ∅, reached)
    have observed := congrArg (Functor.map (observe decision)) literal
    simpa only [RegistrationNativePlatformPublicRecordMaterializedTables.after, RegistrationNativePlatformPublicRetainedRecordProfile.observed,
      PqxdhJointGapDh.challenge, RegistrationNativePlatformMaterializedWhole.tree, work, observe,
      RegistrationNativePlatformG3RecordCoupling.known, simulateQ_map, StateT.run_map, Functor.map_map] using observed

/-- The complete terminal-record observer at each literal startup cut pays only that same actual repeated-role audit. -/
theorem bound (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (initialized : Option (RegistrationNativePublicStartup.Started source) × PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5)) :
    ENNReal.ofReal (discreteDistance
      (known setup checks wire route source serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary decision budget seed scalar candidate materials previous initialized)
      (hidden setup checks wire route source serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary decision budget seed scalar candidate materials previous initialized)) ≤
      Pr{let flag ← (audit setup checks wire route source serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget seed scalar candidate materials previous initialized)}[flag = true] := by
  rcases initialized with ⟨_ | started, reached⟩
  · simp only [known, hidden, audit, discreteDistance_self, ENNReal.ofReal_zero, prEvent_pure, Bool.false_eq_true,
      ↓reduceIte]
    exact le_rfl
  · let job := work setup checks wire source serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget seed scalar candidate materials previous started reached
    have pointwise := RegistrationNativePlatformG3RecordUniform.bound setup
      (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route job reached
    have distance := discreteDistance_map_le (observe (source := source) (Platform := Platform) decision)
      (RegistrationNativePlatformG3RecordUniform.knownGame setup
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route job reached)
      (RegistrationNativePlatformG3RecordCoupling.hidden setup
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route job reached)
    have compared := (ENNReal.ofReal_le_ofReal distance).trans pointwise
    simpa only [known, hidden, audit, job, OracleComp.prEvent_bind_eq_tsum, bind_pure_comp, prEvent_map] using compared

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordOpaqueAfter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordOpaqueAfter.known_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordOpaqueAfter.known_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordOpaqueAfter.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordOpaqueAfter.bound
