-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPackageSource
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueNative
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyStartup
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordAccounting
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueAfter
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordTraceKnown
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformAudit
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicStartupFields
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordUniform
import BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedWhole
/-! The actual warm original produced-frame and raw-attempt event has the literal all-real source record-package law. The genuine complete World startup, stateful platform failures and opaque provider are unchanged; only the deterministic constructor envelope is omitted by the event. CTX-cache inspection is outside this record observation. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueRecord
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
variable {I KemSK Platform E ProviderState Value : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (serverKeyId : U64)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState) (providerState : ProviderState)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (observe : Value × RegistrationNativeLedger.State →
      List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame) → PqxdhRecordLiftWorld.RawCounters → Bool)

omit primitive in
def decision (value : Value × RegistrationNativeLedger.State) (record : RegistrationNativePlatformPublicWorldObservation.RecordView) : Bool :=
  observe value record.2.1 record.2.2

omit primitive in
def outcomeEvent {cap : Nat}
    (result : RegistrationNativeEntropyRun.Outcome
      (RegistrationNativePlatformSelectiveEntropyEnvironment.State cap KemSK ProviderState Platform source) Value)
    (produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame))
    (raw : PqxdhRecordLiftWorld.RawCounters) : Bool :=
  match result with
  | none => false
  | some born => observe born.2.1 produced raw

omit primitive in
def event {cap : Nat} (record : RegistrationNativeRecordPackage.View cap
    (RegistrationNativePlatformSelectiveEntropyEnvironment.State cap KemSK ProviderState Platform source) Value) : Bool :=
  outcomeEvent (KemSK := KemSK) (ProviderState := ProviderState) source observe record.result record.produced record.raw

/-- The exact actual warm event is the all-real source record package on its literal produced/raw fields. -/
theorem actual_source (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) :
    Prod.fst <$> RegistrationNativePlatformG3UniformOpaqueNative.actual setup checks wire route source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary (decision observe)
      budget seed scalar candidate materials previous ensureInit identityIndex =
      event (KemSK := KemSK) (ProviderState := ProviderState) (Platform := Platform) source observe <$>
        RegistrationNativeRecordViewCrypto.real setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route
          (RegistrationNativePlatformSelectiveEntropyStartup.program setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous
            (RegistrationNativePlatformG3UniformOpaqueNative.privateState providerState budget materials) bounds mode adversary) := by
  have packaged := RegistrationNativePlatformRecordPackageSource.real_source setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route
    (RegistrationNativePlatformSelectiveEntropyStartup.program setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous
      (RegistrationNativePlatformG3UniformOpaqueNative.privateState providerState budget materials) bounds mode adversary)
    (outcomeEvent (KemSK := KemSK) (ProviderState := ProviderState) source observe)
  change _ = (fun (result : RegistrationNativeRecordPackage.View (budget.cap 4 + budget.cap 5) (RegistrationNativePlatformSelectiveEntropyEnvironment.State (budget.cap 4 + budget.cap 5) KemSK ProviderState Platform source) Value) => outcomeEvent (KemSK := KemSK) (ProviderState := ProviderState) source observe result.result result.produced result.raw) <$> _
  refine Eq.trans ?_ packaged.symm
  unfold RegistrationNativePlatformG3UniformOpaqueNative.actual RegistrationNativePlatformG3RecordCoupling.hidden
  rw [← RegistrationNativePlatformG3UniformOpaqueNative.program_source]
  simp only [simulateQ_map,StateT.run_map,Functor.map_map]
  congr 1
  funext result
  cases result.1 <;>
    simp only [RegistrationNativePlatformG3UniformOpaqueNative.observation,outcomeEvent,decision,Option.map_none,Option.map_some, RegistrationNativePlatformPublicWorldObservation.recordView]
end BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueRecord

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueRecord.actual_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueRecord.actual_source
