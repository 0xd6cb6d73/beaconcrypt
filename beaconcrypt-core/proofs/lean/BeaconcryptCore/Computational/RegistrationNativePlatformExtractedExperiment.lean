-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceExecution
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedRegistration
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperiment
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLower
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformExperiment
/-! The current native source dictionary executes the extracted registration request bodies and actual ordinary send/receive controllers on one persistent primitive and platform state. Its joint execution equality targets the unchanged corrected ordinary profile; SDK object projections are attached separately through their exact execution diagrams. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedExperiment
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire ledgerCodec)
open RegistrationNativeExperiment (State Initial Public)
open RegistrationNativeRawAdapter (TypedSpec)
open PqxdhRecordLiftInterface (RecordQuery WorldSpec)
variable {n : Nat} {Platform E Value ι KemSK : Type} {base : OracleSpec ι}

abbrev M (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) (Platform : Type) :=
  StateT (State n KemSK source) (StateT Platform ProbComp)

open RegistrationNativePlatformOrdinaryExperiment (canonicalWire)

def replaceWorld {source : RegistrationNativeMldsa.Source} (before : State n KemSK source)
    (after : PqxdhRecordLiftWorld.State n) : State n KemSK source :=
  { before with server := { before.server with world := { before.server.world with world := (after, before.server.world.world.2) } } }

def world {source : RegistrationNativeMldsa.Source}
    (work : RegistrationNativePlatformOrdinaryWorld.M n Platform Value) : M n KemSK source Platform Value :=
  fun before => (fun result => (result.1, replaceWorld before result.2)) <$> work.run before.server.world.world.1

noncomputable def record [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations] (setup : Setup base KemSK) (wire : Wire)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (route : RawCtxServerRouting.SenderDecoder) (query : RecordQuery) (source : RegistrationNativeMldsa.Source) :
    M n KemSK source Platform ((PqxdhRecordLiftInterface.RecordSpec .O).Range query) :=
  match query with
  | .inl query => world (RegistrationNativePlatformOrdinarySourceExecution.guarded setup wire reserveFrame view failure erased route (.inr (.inr (.inl query))))
  | .inr (owner, .inl plaintext) => fun before => match before.beacons[owner]? with
      | none => pure (none, before)
      | some selected => (world (RegistrationNativePlatformOrdinarySourceExecution.guarded setup wire reserveFrame view failure erased route
          (.inr (.inr (.inr (selected.worldOwner, .inl plaintext)))))).run before
  | .inr (owner, .inr raw) => fun before => match before.beacons[owner]? with
      | none => pure (.None, before)
      | some selected => (world (RegistrationNativePlatformOrdinarySourceExecution.guarded setup wire reserveFrame view failure erased route
          (.inr (.inr (.inr (selected.worldOwner, .inr raw)))))).run before

noncomputable def handler [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations] [AdapterInitEdPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (source : RegistrationNativeMldsa.Source)
    (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl TypedSpec (M n KemSK source Platform)
  | .inr (.serverSend keyId plaintext) => record (n:=n) setup wire reserveFrame view failure erased route (.inl (.inl (plaintext, keyId))) source
  | .inr (.serverRaw raw) => record (n:=n) setup wire reserveFrame view failure erased route (.inl (.inr raw)) source
  | .inr (.beaconSend owner plaintext) => record (n:=n) setup wire reserveFrame view failure erased route (.inr (owner, .inl plaintext)) source
  | .inr (.beaconRaw owner raw) => record (n:=n) setup wire reserveFrame view failure erased route (.inr (owner, .inr raw)) source
  | query => RegistrationNativePlatformExtractedRegistration.handler RegistrationNativePlatformMldsaProgram.coins setup checks (canonicalWire wire)
      route representation created source credential view failure allocation reserveRegistration reservePeer erased helper writer query

noncomputable def run [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations] [AdapterInitEdPrimitive.Operations]
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
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source) :
    StateT Platform ProbComp ((Value × RegistrationNativeLedger.State) × State n KemSK source) :=
  (simulateQ (handler (n:=n) setup checks wire route representation created source credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer)
    (RegistrationNativeFullCompiler.compile setup.source.crypto (canonicalWire wire) created.server.server.metadata.sender bounds mode work)).run before

noncomputable def profile [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations] [AdapterInitEdPrimitive.Operations]
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
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (State n KemSK source) → Bool) : StateT Platform ProbComp Bool := do
  let initialized ← StateT.lift (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)
  match initialized with
  | none => pure false
  | some initial =>
      (fun result => event (result.1.1, (result.1.2, result.2))) <$>
        run setup checks wire route representation initial.created source initial.credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer bounds mode (adversary initial.public) initial.state


/-- The actual ordinary source dictionary preserves the complete native/private/platform callback distribution. -/
theorem record_source [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
    (setup : Setup base KemSK) (wire : Wire)
    (reserveFrame : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (route : RawCtxServerRouting.SenderDecoder) (query : RecordQuery) (source : RegistrationNativeMldsa.Source)
    (sealLength : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (openLength : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view) :
    record (n:=n) setup wire reserveFrame view failure erased route query source=
      RegistrationNativePlatformOrdinaryExperiment.record (n:=n) setup wire reserveFrame route query source := by
  have same:=RegistrationNativePlatformOrdinarySourceExecution.guarded_source (n:=n) setup wire reserveFrame sealLength openLength view converted failure erased route
  simp only [record,RegistrationNativePlatformOrdinaryExperiment.record,same]
  rfl

/-- Every current typed callback consumes the actual extracted controller laws, preserving optional failure and the same shared primitive and platform state. -/
theorem handler_source [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations] [AdapterInitEdPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (source : RegistrationNativeMldsa.Source)
    (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat→StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (sealLength : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (openLength : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (edFunctional : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto) :
    handler (n:=n) setup checks wire route representation created source credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer=
      RegistrationNativePlatformOrdinaryExperiment.handler (n:=n) setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer := by
  have registered:=RegistrationNativePlatformExtractedRegistration.handler_source (n:=n) (m:=StateT Platform ProbComp)
    RegistrationNativePlatformMldsaProgram.coins setup checks (canonicalWire wire) route representation created source credential
    view failure allocation reserveRegistration reservePeer erased helper writer edFunctional
  have records : record (n:=n) setup wire reserveFrame view failure erased route=
      (fun query selectedSource=>RegistrationNativePlatformOrdinaryExperiment.record (n:=n) setup wire reserveFrame route query selectedSource) := by
    funext query selectedSource
    exact record_source (n:=n) setup wire reserveFrame view failure erased route query selectedSource sealLength openLength converted
  unfold handler RegistrationNativePlatformOrdinaryExperiment.handler
  rw [registered,records]
  rfl

/-- The full adaptive source program retains its joint value, private native state, primitive cache and external platform poststate. -/
theorem run_source [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations] [AdapterInitEdPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (source : RegistrationNativeMldsa.Source)
    (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat→StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (sealLength : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (openLength : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (edFunctional : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto) :
    run setup checks wire route representation created source credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work before=
      RegistrationNativePlatformOrdinaryExperiment.run setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work before := by
  unfold run RegistrationNativePlatformOrdinaryExperiment.run
  rw [handler_source (n:=n) setup checks wire route representation created source credential view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer sealLength openLength converted edFunctional]

private theorem bind_apply {S A B : Type} (work : StateT S ProbComp A) (next : A→StateT S ProbComp B) (before : S) :
    (work >>=next) before=(do let result←work before;next result.1 result.2) := rfl
private theorem lift_apply {S A : Type} (work : ProbComp A) (before : S) :
    (StateT.lift work : StateT S ProbComp A) before=(fun value=>(value,before)) <$>work :=
  bind_pure_comp _ _
private theorem map_apply {S A B : Type} (f : A→B) (work : StateT S ProbComp A) (before : S) :
    (f <$>work) before=Prod.map f id <$>work before := StateT.run_map f work before

/-- Genuine initialized source execution uses the unchanged startup law and the full extracted adaptive runtime, on the SAME persistent platform state. -/
theorem profile_source [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations] [AdapterInitEdPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat→StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : Public→OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (State n KemSK source)→Bool)
    (sealLength : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (openLength : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (edFunctional : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto) :
    profile (n:=n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      bounds mode adversary event=
    RegistrationNativePlatformOrdinaryExperiment.profile (n:=n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary event := by
  funext previous
  simp only [profile,RegistrationNativePlatformOrdinaryExperiment.profile,bind_apply,lift_apply,bind_map_left]
  apply bind_congr
  intro initialized
  cases initialized with
  | none=>rfl
  | some initial=>
      simp only [map_apply]
      rw [run_source setup checks wire route representation initial.created source initial.credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode (adversary initial.public) initial.state
        sealLength openLength converted edFunctional]

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedExperiment
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedExperiment.record_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedExperiment.record_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedExperiment.handler_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedExperiment.handler_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedExperiment.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedExperiment.run_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedExperiment.profile_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedExperiment.profile_source
