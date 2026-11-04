-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueSource
import BeaconcryptCore.Computational.RegistrationNativePlatformConcreteInitialized
/-! The actual initialized runtime record event reaches the provider-parametrized opaque warm source through explicit related-input, key-schedule, one CCA and one initialized-recovery comparison. The original cache, crypto-produced frames, raw attempts and persistent platform failures stay available to the original observer. Ideal-record secrecy and origin are subsequent event-specific ports. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.Computational.RegistrationNativePlatformConcreteRecordComparison
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicRecordOpaqueInitialized (Context prior)
variable {I KemSK Platform E Value : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveBytes : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → RegistrationNativePlatformPublicWorldObservation.RecordView → Bool)



open RegistrationNativePlatformG3UniformOpaqueSource (actual hidden initialLoss kemLoss)
local notation "wire" => RegistrationNativePlatformConcreteSource.wire
local notation "allocation" => RegistrationNativePlatformConcreteSource.rawAllocation reserveBytes
local notation "helper" => RegistrationNativePlatformConcreteSource.helper reserveBytes
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets
/-- The original initialized runtime event reaches the opaque warm source with the stated primitive/key, single-CCA and single initialized-recovery losses. No callback, provider or security-event equivalence is a premise. -/
theorem record_distance (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (previous : Platform) (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    ENNReal.ofReal ((actual setup checks wire route source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveBytes erased helper writer bounds mode adversary decision representation budget previous).boolDistance
      (hidden setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveBytes erased helper writer bounds mode adversary decision budget selected previous)) ≤
      ENNReal.ofReal (initialLoss setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveBytes erased helper writer bounds mode adversary decision budget selected previous + kemLoss setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveBytes erased helper writer bounds mode adversary decision budget selected previous) +
        RegistrationNativePlatformG3UniformOpaque.recoveryLoss setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveBytes erased helper writer bounds mode adversary budget selected previous := by
  exact RegistrationNativePlatformG3UniformOpaqueSource.source_distance setup checks wire route source ensureInit identityIndex serverKeyId
    selectedAccept view failure allocation reserveRegistration reservePeer reserveBytes erased helper writer bounds mode adversary decision
    representation correct functional budget bounded selected previous candidate
end BeaconcryptCore.Computational.RegistrationNativePlatformConcreteRecordComparison

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformConcreteRecordComparison.record_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformConcreteRecordComparison.record_distance
