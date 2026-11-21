-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperiment
import BeaconcryptCore.Computational.RegistrationNativeScalarProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleMetadata
import BeaconcryptCore.Computational.RegistrationNativePlatformFinishMetadata
/-! The selected-prekey eager experiment changes only actual owner creation. Every other corrected stateful registration and ordinary callback is retained literally, with the same persistent platform state and dynamic source writers. The independent early scalar is outside native counters; the original constructor draw remains at its actual source position. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarEager
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeExperiment (State Public)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformOrdinaryExperiment (M canonicalWire)
variable {n : Nat} {Platform E Value ι KemSK : Type} {base : OracleSpec ι}

noncomputable def handler [primitives : AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (source : RegistrationNativeMldsa.Source)
    (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes) : QueryImpl TypedSpec (M n KemSK source Platform)
  | .inr (.create edPin mlPin keyId) => RegistrationNativePlatformExperiment.liftNative RegistrationNativePlatformMldsaProgram.coins
      (RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativeScalarEager.create setup source selected scalar edPin mlPin keyId))
  | query => RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query

noncomputable def run [primitives : AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (source : RegistrationNativeMldsa.Source)
    (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source) :
    StateT Platform ProbComp ((Value × RegistrationNativeLedger.State) × State n KemSK source) :=
  (simulateQ (handler setup checks wire route representation created source credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer selected scalar)
    (RegistrationNativeFullCompiler.compile setup.source.crypto (canonicalWire wire) created.server.server.metadata.sender bounds mode work)).run before

noncomputable def profile [primitives : AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (selected : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (State n KemSK source) → Bool) : StateT Platform ProbComp Bool := do
  let scalar ← StateT.lift PqxdhJointGapDh.sampleScalar
  let initialized ← StateT.lift (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)
  match initialized with
  | none => pure false
  | some initial =>
      (fun result => event (result.1.1, (result.1.2, result.2))) <$>
        run setup checks wire route representation initial.created source initial.credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer selected scalar bounds mode (adversary initial.public) initial.state

theorem create_eq [primitives : AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (source : RegistrationNativeMldsa.Source)
    (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes) (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    handler (n := n) setup checks wire route representation created source credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer selected scalar (.inr (.create edPin mlPin keyId)) =
      RegistrationNativePlatformExperiment.liftNative RegistrationNativePlatformMldsaProgram.coins
        (RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativeScalarEager.create setup source selected scalar edPin mlPin keyId)) := rfl

theorem noncreate_eq [primitives : AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (source : RegistrationNativeMldsa.Source)
    (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes) (query : TypedSpec.Domain)
    (notCreate : ∀ edPin mlPin keyId, query ≠ .inr (.create edPin mlPin keyId)) :
    handler (n := n) setup checks wire route representation created source credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer selected scalar query =
      RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query := by
  cases query with
  | inl coin => rfl
  | inr command =>
    cases command
    case create edPin mlPin keyId => exact False.elim (notCreate edPin mlPin keyId rfl)
    all_goals rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarEager

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarEager.create_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarEager.create_eq

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarEager.noncreate_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarEager.noncreate_eq
