-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordUniformTables
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedRecordEmbeddedProfile
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedRetainedSource
import BeaconcryptCore.Computational.RegistrationNativeOpenRetainedReal
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RetainedRecordSource
/-! The actual initialized terminal-record decision is transported through finite material tables to the literal corrected known-material World program. The original source callback budget derives table room, and every reached startup cache, failed writer outcome, produced frame, raw attempt and persistent platform result is retained. This is the known-material hop before the separate opaque comparison. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordMaterializedTables
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {I KemSK Platform E Value : Type} {base : OracleSpec I}
private theorem embedded_bound (work : OracleComp (RegistrationNativePlatformPublicFrontend.Spec n KemSK) Value)
    (count : Nat) (bounded : work.IsQueryBoundP (RegistrationNativePlatformPublicMaterialCaps.IsDemand (n := n) (KemSK := KemSK)) count) :
    (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed work).IsQueryBoundP
      (RegistrationNativePublicCaps.IsDemand (n := n) (KemSK := KemSK)) count := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work count bounded
  intro query
  cases query with
  | inl query =>
      by_cases counted : RegistrationNativePublicCaps.IsDemand (n := n) (KemSK := KemSK) query
      · simp only [RegistrationNativePlatformPublicCoinEmbedding.embed,
          RegistrationNativePlatformPublicMaterialLocal.IsDemand, ite_eq_left counted, isQueryBoundP_query_iff]
        intro _
        decide
      · simp only [RegistrationNativePlatformPublicCoinEmbedding.embed,
          RegistrationNativePlatformPublicMaterialLocal.IsDemand, ite_eq_right counted, isQueryBoundP_query_iff]
        intro impossible
        exact (counted impossible).elim
  | inr coin =>
      simp [RegistrationNativePlatformPublicCoinEmbedding.embed, RegistrationNativePublicFrontend.effect,
        RegistrationNativePublicFrontend.liftLocal, RegistrationNativePlatformPublicMaterialLocal.IsDemand,
        RegistrationNativePublicCaps.IsDemand, isQueryBoundP_query_iff]

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

noncomputable def after (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5))
    (seeds : RegistrationNativeG3Tables.SeedTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (initialized : Option (RegistrationNativePublicStartup.Started source) × PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5)) :
    ProbComp (Bool × Platform) :=
  match initialized.1 with
  | none => pure (false, previous)
  | some started =>
    (fun result => (decision result.1.1 (RegistrationNativePlatformPublicWorldObservation.recordView result.2.2), result.1.2.2)) <$>
      (simulateQ (RegistrationNativeG3MaterializedLocal.handler true materials seeds setup
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route
        (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) (RegistrationNativeMldsa.owned source started.credential)
        seed scalar candidate (RegistrationNativeOpenRetainedReal.provider setup))
        (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
          (RegistrationNativePlatformPublicRetainedRecordProfile.observed (n := budget.cap 4 + budget.cap 5) setup checks wire source serverKeyId
            selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
            (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) started previous))).run
              (RegistrationNativeG3AuditTraceRun.cold (RegistrationNativeSelectiveHiddenInterpreter.initial
                (n := budget.cap 4 + budget.cap 5) (KemSK := KemSK) ()) ∅, initialized.2)

/-- Each reached actual startup preserves the whole terminal record decision through its genuine known-material World interpretation. -/
theorem fixed_source (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5))
    (seeds : RegistrationNativeG3Tables.SeedTable (budget.cap 4 + budget.cap 5)) (previous : Platform) :
    (simulateQ (RegistrationNativeG3RetainedCallbacks.keys setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate materials seeds)
      (RegistrationNativePlatformPublicRetainedRecordProfile.client (n := budget.cap 4 + budget.cap 5) setup checks wire route source ensureInit
        identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        bounds mode adversary decision (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) previous)).run'
          (RegistrationNativeHiddenService.initial, ∅) = (do
      let initialized ← (RegistrationNativePublicStartupFrame.startup (n := budget.cap 4 + budget.cap 5) setup source ensureInit identityIndex serverKeyId
        (setup.joint.publicKeys seed)).run PqxdhRecordLiftWorld.initial
      after setup checks wire route source serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased
        helper writer bounds mode adversary decision budget seed scalar candidate materials seeds previous initialized) := by
  rw [RegistrationNativePlatformPublicRetainedRecordEmbeddedProfile.client_source (n := budget.cap 4 + budget.cap 5) setup checks wire route source ensureInit
    identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode
    adversary decision (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) previous]
  simp only [RegistrationNativePlatformPublicRetainedRecordEmbeddedProfile.client, StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_bind]
  rw [RegistrationNativeG3RetainedCallbacks.coins_source]
  simp only [bind_map_left, PqxdhJointGapDh.challenge]
  apply bind_congr
  rintro ⟨initialized, world⟩
  cases initialized with
  | none => simp only [after, simulateQ_pure, StateT.run_pure, map_pure]
  | some started =>
    let action := simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      (RegistrationNativePlatformPublicRetainedRecordProfile.observed (n := budget.cap 4 + budget.cap 5) setup checks wire source serverKeyId selectedOwner
        selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
        (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) started previous)
    have allowed : action.IsQueryBoundP (RegistrationNativePublicCaps.IsDemand (n := budget.cap 4 + budget.cap 5) (KemSK := KemSK))
        (budget.cap 4 + budget.cap 5) := by
      apply embedded_bound
      exact RegistrationNativePlatformPublicMaterialCaps.run_bound setup checks wire source (RegistrationNativeMldsa.owned source started.credential)
        selectedOwner selectedAccept (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        serverKeyId bounds mode (adversary ⟨setup.joint.publicKeys seed, started.credential.publicKey, serverKeyId⟩) budget (bounded _) (started.frontend, previous)
    let frame := RegistrationNativeSelectiveHiddenInterpreter.initial (n := budget.cap 4 + budget.cap 5) (KemSK := KemSK) ()
    let before : RegistrationNativePublicInterpreter.State (budget.cap 4 + budget.cap 5) KemSK :=
      { (RegistrationNativePublicInterpreter.initial (n := budget.cap 4 + budget.cap 5) (KemSK := KemSK)) with world }
    have reference := RegistrationNativePlatformG3RetainedRecordSource.program_source setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      route (RegistrationNativeMldsa.owned source started.credential) seed scalar candidate (RegistrationNativeOpenRetainedReal.provider setup)
      materials seeds action allowed frame world
    have actual := RegistrationNativePlatformG3RetainedRecordSource.real_client setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      route (RegistrationNativeMldsa.owned source started.credential) action before
    have clientEqual : RegistrationNativePlatformG3RetainedRecordSource.client setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
        route (RegistrationNativeMldsa.owned source started.credential) (RegistrationNativeOpenRetainedReal.provider setup) action
        (RegistrationNativeG3MaterializedRetainedSource.ordinary frame world, ()) =
      (fun result => (result.1, RegistrationNativePlatformPublicWorldObservation.recordView result.2.world)) <$>
        (simulateQ (RegistrationNativePublicRetained.compiler setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route
          (RegistrationNativeMldsa.owned source started.credential)) action).run (RegistrationNativePublicRetained.clear before) := by
      simpa only [before, frame, RegistrationNativeG3MaterializedRetainedSource.ordinary, RegistrationNativeSelectiveHiddenInterpreter.initial,
        RegistrationNativeHiddenInterpreter.initial, RegistrationNativePublicInterpreter.initial, RegistrationNativePublicRetained.clear,
        RegistrationNativePublicRootFrame.replace] using actual
    have compared := congrArg (Functor.map (fun result => (decision result.1.1 result.2, result.1.2.2))) reference.symm
    rw [clientEqual] at compared
    simpa only [action, before, frame, after, StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map,
      RegistrationNativePlatformPublicWorldObservation.recordView, PqxdhJointGapDh.challenge,
      RegistrationNativeSelectiveHiddenInterpreter.initial] using compared

noncomputable def game (budget : PqxdhDeploymentInterface.Budget)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (previous : Platform) : ProbComp Bool := do
  let seed ← PqxdhJointIdentity.sampleSeed
  let scalar ← PqxdhJointGapDh.sampleScalar
  let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)
  let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable (budget.cap 4 + budget.cap 5)
  let initialized ← (RegistrationNativePublicStartupFrame.startup (n := budget.cap 4 + budget.cap 5) setup source ensureInit identityIndex serverKeyId
    (setup.joint.publicKeys seed)).run PqxdhRecordLiftWorld.initial
  Prod.fst <$> after setup checks wire route source serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer
    reserveFrame erased helper writer bounds mode adversary decision budget seed scalar candidate materials seeds previous initialized

/-- The finite actual terminal-record experiment is the new initialized known-material World game, with the warmed cache and P retained. -/
theorem table_source (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (previous : Platform) :
    RegistrationNativePlatformPublicRecordUniformTables.tableGame setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget candidate previous =
      game setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer
        reserveFrame erased helper writer bounds mode adversary decision budget candidate previous := by
  unfold RegistrationNativePlatformPublicRecordUniformTables.tableGame game
  apply bind_congr
  intro seed
  apply bind_congr
  intro scalar
  apply bind_congr
  intro materials
  apply bind_congr
  intro seeds
  have original := congrArg (Functor.map Prod.fst)
    (fixed_source setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration
      reservePeer reserveFrame erased helper writer bounds mode adversary decision budget bounded seed scalar candidate materials seeds previous)
  simpa only [RegistrationNativePlatformPublicRecordKeyExperiment.phaseClient, simulateQ_map, StateT.run'_eq,
    StateT.run_map, Functor.map_map, map_bind] using original

/-- The actual corrected initialized ledger decision reaches the new known-material World game with exactly its original two-hop primitive losses. -/
theorem source_distance (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (previous : Platform) :
    (Prod.fst <$> (RegistrationNativePlatformOrdinaryExperiment.profile (n := budget.cap 4 + budget.cap 5) setup checks wire route representation source ensureInit identityIndex serverKeyId
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
      (fun result => decision (result.1, result.2.1)
        (RegistrationNativePlatformPublicWorldObservation.recordView (RegistrationNativePlatformPublicWorldObservation.world result.2.2)))).run previous).boolDistance
      (game setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget candidate previous) ≤
      RegistrationNativeRelatedFamily.advantage setup.hmac setup.joint setup.dh
        (fun publicValue => simulateQ RegistrationNativeRelatedRoot.reduction
          (RegistrationNativePlatformPublicRecordKeyExperiment.rootClient (n := budget.cap 4 + budget.cap 5) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous publicValue)) +
      ∑ index ∈ Finset.range (budget.cap 4 + budget.cap 5), RegistrationBoundKeySchedule.keyLoss setup.source setup.hmac
        (RegistrationNativeKeyHybrid.reduction setup.source setup.hmac
          (RegistrationNativePlatformPublicRecordKeyExperiment.entryClient (n := budget.cap 4 + budget.cap 5) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous) index) := by
  rw [← table_source setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget bounded candidate previous]
  exact RegistrationNativePlatformPublicRecordUniformTables.source_tables_distance setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision representation correct budget bounded candidate previous

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordMaterializedTables

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordMaterializedTables.fixed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordMaterializedTables.fixed_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordMaterializedTables.table_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordMaterializedTables.table_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordMaterializedTables.source_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordMaterializedTables.source_distance
