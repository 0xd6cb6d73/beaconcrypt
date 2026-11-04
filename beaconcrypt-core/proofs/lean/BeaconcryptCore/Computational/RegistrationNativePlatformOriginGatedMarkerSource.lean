-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginGatedMarker
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEntropy
/-! The selected receive marker is carried through the literal current native full source and exact ML-aware ledger restoration, at the same reached cursor/control/private state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginGatedMarkerSource
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode handleSlot)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftInterface (Environment)
open PqxdhDeploymentInterface (FullSpec Entry Handle FreshBounds)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {I KemSK Reader Response E Failure X : Type} {base : OracleSpec I}
variable (target : Label n) (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
local notation "service" => PqxdhRecordFactsOriginMarkerNative.service target modes replace setup codec
local notation "native" => RegistrationNativePlatformGatedRecordFlat.native service env reserve codec route
local notation "State" => RegistrationNativePlatformGatedRecordFlat.State n E (CtxPrivate n × Bool)

private def join (result : ((((X × PqxdhDeploymentSecrecy.Ledger) × E) × CborRecordWorldClient.Shell) ×
    PqxdhRecordLiftProtocol.Control n) × (CtxPrivate n × Bool)) : X × (PqxdhDeploymentSecrecy.Ledger × State) :=
  let flat := RegistrationNativePlatformGatedRecordFlat.join result
  (flat.1.1,(flat.1.2,flat.2))

/-- The current original full ledger is exactly its nested free source interpretation at the same reached controls and complete private state. -/
theorem source_run (serverKid : U64) (bounds : FreshBounds) (work : OracleComp FullSpec X)
    (before : E) (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n × Bool) :
    (simulateQ (RegistrationNativePlatformOriginGatedMarker.fullImpl target modes replace setup codec route env reserve serverKid bounds) work).run
      (PqxdhDeploymentSecrecy.Ledger.empty,(((before,shell),control),secret)) =
      join <$> (simulateQ service (RegistrationNativePlatformOriginNativeTails.source env reserve codec route
        (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec serverKid bounds work) before shell control)).run secret := by
  rw [RegistrationNativePlatformOriginGatedMarker.fullImpl,OracleComp.simulateQ_flattenStateT_run,←QueryImpl.simulateQ_mapStateTBase_run]
  rw [bind_pure_comp]
  change (fun result => (result.1.1,(result.1.2,result.2))) <$>
      (simulateQ native (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec serverKid bounds work)).run (((before,shell),control),secret) = _
  rw [RegistrationNativePlatformGatedRecordFlat.native_program]
  simp only [Functor.map_map,RegistrationNativePlatformOriginNativeTails.source,CborRawRecordOriginFlatten.interpret]
  rfl

/-- An original accepted ledger record raises the exact selected marker in this same actual free source execution. -/
theorem received (serverKid : U64) (bounds : FreshBounds) (work : OracleComp FullSpec X)
    (before : E) (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n × Bool)
    (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (result : ((((X × PqxdhDeploymentSecrecy.Ledger) × E) × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × (CtxPrivate n × Bool))
    (supported : result∈support ((simulateQ service (RegistrationNativePlatformOriginNativeTails.source env reserve codec route
      (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec serverKid bounds work) before shell control)).run secret))
    (entry : Entry) (member : entry∈result.1.1.1.1.2.transcript)
    (receiver : PqxdhDeploymentInterface.Receiver) (raw : Pqxdh.Bytes) (opened : RawCtxWholeOwner.Decrypted) (handle : Handle)
    (accepted : entry.received=some (receiver,raw,.Some opened))
    (routed : PqxdhRecordLiftIdeal.receivingHandle route receiver raw=some handle)
    (slot : handleSlot result.1.2 handle=some target.slot)
    (direction : target.direction = !PqxdhRecordFactsOriginHandles.handleDirection handle)
    (position : target.position+1=opened.sequence.val) : result.2.2=true := by
  have reached : join result∈support
      ((simulateQ (RegistrationNativePlatformOriginGatedMarker.fullImpl target modes replace setup codec route env reserve serverKid bounds) work).run
        (PqxdhDeploymentSecrecy.Ledger.empty,(((before,shell),control),secret))) := by
    rw [source_run,support_map]
    exact ⟨result,supported,rfl⟩
  exact RegistrationNativePlatformOriginGatedMarker.received target modes replace setup codec route env reserve serverKid bounds work
    (((before,shell),control),secret) safe (join result) reached entry member receiver raw opened handle accepted routed slot direction position

/-- The literal ML-aware current native program derives received-entry marker facts on its restored original ledger, from any same reached cursor/control/private prefix. -/
theorem program_entryFacts {Value : Type}
    (nativeEnv : RegistrationNativeEntropyInterface.Environment n E)
    (nativeReserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (serverKid : U64) (bounds : FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (created : PqxdhLiveServerConstruction.Created Unit) (before : E)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n × Bool)
    (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (result : ((RegistrationNativeEntropyRun.Outcome E Value × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × (CtxPrivate n × Bool))
    (supported : result∈support ((simulateQ service
      ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
        ((simulateQ CborRecordWorldClient.handler
          (RegistrationNativePlatformGatedNativeEntropy.program nativeEnv nativeReserve setup.source.crypto codec serverKid bounds mode work created before)).run shell)).run control)).run secret)) :
    ∀ finished∈result.1.1.1,∀entry∈finished.2.1.2.ledger.transcript,
      PqxdhRecordFactsOriginMarkerEntry.EntryFact target route result.1.2 result.2.2 entry := by
  rw [←RegistrationNativePlatformGatedNativeEntropy.program_transport nativeEnv nativeReserve setup.source.crypto codec serverKid bounds mode work created before] at supported
  simp only [RegistrationNativePlatformGatedEntropyWorld.program,simulateQ_map,StateT.run_map,Functor.map_map,support_map] at supported
  obtain ⟨old,oldSupported,rfl⟩ := supported
  let legacyWork := PqxdhDeploymentInterface.asModeO mode (RegistrationNativeEntropyCompile.compile mode work)
  have actual : join old ∈ support
      ((simulateQ (RegistrationNativePlatformOriginGatedMarker.fullImpl target modes replace setup codec route
        (RegistrationNativeEntropyPort.environment nativeEnv) (RegistrationNativePlatformGatedNativeEntropy.reserveLift nativeReserve)
        serverKid bounds) legacyWork).run (PqxdhDeploymentSecrecy.Ledger.empty,(((([],before),shell),control),secret))) := by
    rw [source_run,support_map]
    exact ⟨old,oldSupported,rfl⟩
  have invariant := RegistrationNativePlatformOriginGatedMarker.full_program_invariant target modes replace setup codec route
    (RegistrationNativeEntropyPort.environment nativeEnv) (RegistrationNativePlatformGatedNativeEntropy.reserveLift nativeReserve)
    serverKid bounds legacyWork (PqxdhDeploymentSecrecy.Ledger.empty,(((([],before),shell),control),secret))
    ⟨safe,by simp [PqxdhDeploymentSecrecy.Ledger.empty]⟩
    (join old) actual
  intro finished present entry member
  have same : finished=(PqxdhRegistrationJointServerBirth.encode created,
      ((old.1.1.1.1.1,RegistrationNativeEntropyRestore.ledger old.1.1.1.1.2),old.1.1.1.2.2)) := by
    symm
    simpa only [RegistrationNativeEntropyProgram.outcome,RegistrationNativeEntropyExecution.result,Option.map_some,Option.mem_some_iff] using present
  subst finished
  rw [RegistrationNativeEntropyRestore.ledger_transcript] at member
  intro receiver raw opened handle received routed
  have original : ∃ original∈old.1.1.1.1.2.transcript,original.received=some (receiver,raw,.Some opened) := by
    apply List.mem_filterMap.mp
    rw [←RegistrationNativeEntropyTrace.projection_strip Entry.received (fun _ _ _ => rfl)]
    exact List.mem_filterMap.mpr ⟨entry,member,received⟩
  obtain ⟨original,recorded,returned⟩ := original
  exact invariant.2 original recorded receiver raw opened handle returned routed
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginGatedMarkerSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginGatedMarkerSource.source_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginGatedMarkerSource.source_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginGatedMarkerSource.received' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginGatedMarkerSource.received

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginGatedMarkerSource.program_entryFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginGatedMarkerSource.program_entryFacts
