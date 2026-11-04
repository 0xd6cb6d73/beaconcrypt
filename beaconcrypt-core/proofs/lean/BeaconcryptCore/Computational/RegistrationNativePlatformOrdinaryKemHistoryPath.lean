-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemActualBlocks
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHistorySource
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOriginJournal

/-! Every initialized retained analysis history comes from its own genuine full native chronological path. The proof reconstructs the private full-state journal by exact source interpretation and snapshot projection; no desired partner or security conclusion is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHistoryPath
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open RegistrationNativeStageTrace (Call)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformKemInitializedJournal (History)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι}

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (source : RegistrationNativeMldsa.Source)
variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (bounds : FreshBounds) (mode : Mode)
variable (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
variable (previous : Platform)


local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Whole" => Native × Platform

/-- The actual initial object, full native path and final private pool underlying this retained client history. -/
structure Receipt (history : History n source Value Platform) (finalPlatform : Platform) (pool : PqxdhLiveKemBirth.Pool KemSK) where
  initial : RegistrationNativeExperiment.Initial n KemSK source
  startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)
  calls : List (Call TypedSpec Whole)
  finalNative : Native
  reached : RegistrationNativeStageTrace.Path (RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) (initial.state, previous) calls (finalNative, finalPlatform)
  initialEq : history.initial = RegistrationNativePlatformKemCountedProfile.ofInitial initial
  stateEq : history.state = RegistrationNativeKemServerState.ofNative finalNative
  poolEq : pool = finalNative.pool
  callsEq : history.calls = calls.map (RegistrationNativeObservedStageTrace.mapCall RegistrationNativePlatformOrdinaryKemClientJournal.observe)

/-- An actual evaluated initialized history derives its own full-state source path, with exactly the same snapshots, returned pool and platform. -/
theorem actual (history : History n source Value Platform) (finalPlatform : Platform) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (supported : ((some history, finalPlatform), pool) ∈ support
      (RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem
        ((RegistrationNativePlatformOrdinaryKemInitializedJournal.program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary).run previous) PqxdhLiveKemBirth.empty)) :
    Nonempty (Receipt setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer previous history finalPlatform pool) := by
  rw [RegistrationNativePlatformOrdinaryKemHistorySource.source_history] at supported
  unfold RegistrationNativePlatformOrdinaryKemHistorySource.native at supported
  simp only [mem_support_bind_iff] at supported
  obtain ⟨initialized, startup, continued⟩ := supported
  cases initialized with
  | none =>
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at continued
      cases continued.1.1
  | some initial =>
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at continued
      obtain ⟨result, ran, returned⟩ := continued
      have projection := RegistrationNativeObservedStageTrace.full_project RegistrationNativePlatformOrdinaryKemClientJournal.observe
        (RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route representation initial.created initial.credential
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
        (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) initial.created.server.server.metadata.sender bounds mode (adversary initial.public))
        ((initial.state, previous), [])
      simp only [List.map_nil] at projection
      rw [← projection, support_map] at ran
      obtain ⟨⟨value, ⟨⟨finalNative, actualPlatform⟩, calls⟩⟩, actualRun, same⟩ := ran
      cases same
      simp only [Prod.mk.injEq, Option.some.injEq] at returned
      rcases returned with ⟨⟨historyEq, platformEq⟩, poolEq⟩
      cases historyEq
      cases platformEq
      have path := RegistrationNativeStageTrace.path
        (RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route representation initial.created initial.credential
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
        (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) initial.created.server.server.metadata.sender bounds mode (adversary initial.public))
        (initial.state, previous) (value, ((finalNative, actualPlatform), calls)) actualRun
      exact ⟨⟨initial, startup, calls, finalNative, path, rfl, rfl, poolEq, rfl⟩⟩

/-- The finite genuine-row recipient execution has the same actual initialized full-state source path and private pool. -/
theorem experiment (budget : Budget) (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (result : RegistrationNativeKemRecipientLogSource.Result KemSK (Option (History n source Value Platform) × Platform) budget.create)
    (supported : result ∈ support (RegistrationNativePlatformOrdinaryKemInitializedJournal.experiment (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous budget functional))
    (history : History n source Value Platform) (returned : result.2.1.1.1.1 = some history) :
    Nonempty (Receipt setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer previous history result.2.1.1.1.2 result.2.1.2) := by
  have evaluated := RegistrationNativeKemReservedSupport.logged setup functional
    ((RegistrationNativePlatformOrdinaryKemInitializedJournal.program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary).run previous) budget.create result supported
  have unlogged : ((result.2.1.1.1.1, result.2.1.1.1.2), result.2.1.2) ∈ support
      (RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem
        ((RegistrationNativePlatformOrdinaryKemInitializedJournal.program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary).run previous) PqxdhLiveKemBirth.empty) := by
    have law := congrArg (fun program => RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem program PqxdhLiveKemBirth.empty)
      (loggingOracle.fst_map_run_simulateQ ((RegistrationNativePlatformOrdinaryKemInitializedJournal.program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary).run previous))
    simp only [RegistrationNativeKemCountedProgram.evaluate, simulateQ_map, StateT.run_map] at law
    unfold RegistrationNativeKemCountedProgram.evaluate
    rw [← law, support_map]
    exact ⟨_, evaluated, rfl⟩
  rw [returned] at unlogged
  exact actual setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous history result.2.1.1.1.2 result.2.1.2 unlogged

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHistoryPath

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHistoryPath.actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHistoryPath.actual

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHistoryPath.experiment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHistoryPath.experiment
