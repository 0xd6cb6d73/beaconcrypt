-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaque
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKnownSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordKeyBound
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordProviderSource
/-! The actual initialized runtime record event reaches the provider-parametrized opaque warm source through explicit related-input, key-schedule, one CCA and one initialized-recovery comparison. The original cache, crypto-produced frames, raw attempts and persistent platform failures stay available to the original observer. Ideal-record secrecy and origin are subsequent event-specific ports. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueSource
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicRecordOpaqueInitialized (Context prior)
variable {I KemSK Platform E Value : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → RegistrationNativePlatformPublicWorldObservation.RecordView → Bool)


noncomputable def known (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform) : ProbComp Bool :=
  Prod.fst <$> RegistrationNativePlatformG3UniformOpaque.known setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous
noncomputable def hidden (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform) : ProbComp Bool :=
  Prod.fst <$> RegistrationNativePlatformG3UniformOpaque.hidden setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous
noncomputable def uniform (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform) : ProbComp Bool :=
  RegistrationNativeKemEarlyObservedGame.branch setup.baseImpl setup.kem
    (RegistrationNativeOpenKeyKemGame.other setup.baseImpl setup.kem) (pure ∅)
    (simulateQ RegistrationNativeOpenKey.native (RegistrationNativePlatformG3RecordKem.program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected.val previous))
    (fun _ result => RegistrationNativePlatformG3RecordKem.observation source decision result) budget.create selected false
noncomputable def materialized (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) : ProbComp Bool :=
  RegistrationNativePlatformPublicRecordMaterializedTables.game setup checks wire route source ensureInit identityIndex serverKeyId selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget candidate previous
noncomputable def kemLoss (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform) : ℝ :=
  (setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
    (RegistrationNativeKemEarlyObservedGame.adversary setup.baseImpl setup.kem
      (RegistrationNativeOpenKeyKemGame.other setup.baseImpl setup.kem) (pure ∅)
      (simulateQ RegistrationNativeOpenKey.native (RegistrationNativePlatformG3RecordKem.program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected.val previous))
      (fun _ result => RegistrationNativePlatformG3RecordKem.observation source decision result) budget.create selected).toINDCCA).toReal +
    RegistrationNativeKemEarlyCorrectness.correctnessError setup.baseImpl setup.kem

/-- The one ordinary uniform KEM branch has the literal known-source event, including every terminal record coordinate used by the event. -/
theorem uniform_source (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (previous : Platform) :
    uniform setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous =ᵈ known setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous := by
  exact (RegistrationNativePlatformG3RecordUniformSource.uniform_source setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget bounded selected previous
    (fun _ result => RegistrationNativePlatformG3RecordKem.observation source decision result)).trans
      (RegistrationNativePlatformG3UniformOpaque.conditional_source setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget bounded selected previous)

/-- Exactly one CCA comparison transports the candidate-independent actual materialized source event to the warm uniform known side. -/
theorem known_close (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (previous : Platform) (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    (materialized setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous candidate).boolDistance
      (known setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous) ≤ kemLoss setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous := by
  have compared := RegistrationNativePlatformG3RecordKnownSource.game_close setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary functional decision budget bounded selected previous candidate
  have same := (uniform_source setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget bounded selected previous).evalDist_eq
  simp only [uniform] at same
  simpa only [materialized,kemLoss,ProbComp.boolDistance,same] using compared

noncomputable def actual (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (budget : PqxdhDeploymentInterface.Budget) (previous : Platform) : ProbComp Bool :=
  Prod.fst <$> (RegistrationNativePlatformOrdinaryExperiment.profile (n := budget.cap 4 + budget.cap 5) setup checks wire route representation source ensureInit identityIndex serverKeyId
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
    (fun result => decision (result.1,result.2.1)
      (RegistrationNativePlatformPublicWorldObservation.recordView (RegistrationNativePlatformPublicWorldObservation.world result.2.2)))).run previous

noncomputable def initialLoss (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform) : ℝ :=
  RegistrationNativeRelatedFamily.advantage setup.hmac setup.joint setup.dh
        (fun publicValue => simulateQ RegistrationNativeRelatedRoot.reduction
          (RegistrationNativePlatformPublicRecordKeyExperiment.rootClient (n := budget.cap 4 + budget.cap 5) setup checks wire route source ensureInit identityIndex serverKeyId selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous publicValue)) +
      ∑ index ∈ Finset.range (budget.cap 4 + budget.cap 5), RegistrationBoundKeySchedule.keyLoss setup.source setup.hmac
        (RegistrationNativeKeyHybrid.reduction setup.source setup.hmac
          (RegistrationNativePlatformPublicRecordKeyExperiment.entryClient (n := budget.cap 4 + budget.cap 5) setup checks wire route source ensureInit identityIndex serverKeyId selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous) index)

/-- The literal initialized runtime reaches the complete warm known event with its actual related-input/key losses and one CCA loss. -/
theorem source_known (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (previous : Platform) (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    (actual setup checks wire route source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision representation budget previous).boolDistance
      (known setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous) ≤
      initialLoss setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous + kemLoss setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous := by
  have first := RegistrationNativePlatformPublicRecordMaterializedTables.source_distance setup checks wire route source ensureInit identityIndex serverKeyId selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision representation correct budget bounded candidate previous
  have second := known_close setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision functional budget bounded selected previous candidate
  exact (ProbComp.boolDistance_triangle
    (actual setup checks wire route source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision representation budget previous)
    (materialized setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous candidate)
    (known setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous)).trans (add_le_add first second)

/-- The same full-observation distance controls every original Boolean event without discarding terminal record data. -/
theorem known_hidden_bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (previous : Platform) :
    ENNReal.ofReal ((known setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous).boolDistance
      (hidden setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous)) ≤
      RegistrationNativePlatformG3UniformOpaque.recoveryLoss setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous := by
  have projected := (boolDistance_le_discreteDistance
    (known setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous)
    (hidden setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous)).trans
      (discreteDistance_map_le Prod.fst
        (RegistrationNativePlatformG3UniformOpaque.known setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous)
        (RegistrationNativePlatformG3UniformOpaque.hidden setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous))
  exact (ENNReal.ofReal_le_ofReal projected).trans
    (RegistrationNativePlatformG3UniformOpaque.loss_bound setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget bounded selected previous)

/-- The original initialized runtime event reaches the opaque warm source with the stated primitive/key, single-CCA and single initialized-recovery losses. No callback, provider or security-event equivalence is a premise. -/
theorem source_distance (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (previous : Platform) (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    ENNReal.ofReal ((actual setup checks wire route source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision representation budget previous).boolDistance
      (hidden setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous)) ≤
      ENNReal.ofReal (initialLoss setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous + kemLoss setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous) +
        RegistrationNativePlatformG3UniformOpaque.recoveryLoss setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous := by
  have original := source_known setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision representation correct functional budget bounded selected previous candidate
  have hiddenBound := known_hidden_bound setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget bounded selected previous
  have triangle := ProbComp.boolDistance_triangle
    (actual setup checks wire route source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision representation budget previous)
    (known setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous)
    (hidden setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous)
  exact (ENNReal.ofReal_le_ofReal triangle).trans
    ((ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)).le.trans
      (add_le_add (ENNReal.ofReal_le_ofReal original) hiddenBound))

end BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueSource.uniform_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueSource.uniform_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueSource.known_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueSource.known_close

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueSource.source_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueSource.source_known

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueSource.known_hidden_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueSource.known_hidden_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueSource.source_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueSource.source_distance
