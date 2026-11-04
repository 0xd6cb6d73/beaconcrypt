-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemInitializedJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformKemInitializedJournal

/-! The initialized counted typed history is the same actual corrected Native source history, with complete final private pool and platform state. The protected-origin/cache observation uses the existing proved chronological projection rather than a final-state marginal. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHistorySource
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


noncomputable def native : ProbComp ((Option (History n source Value Platform) × Platform) × PqxdhLiveKemBirth.Pool KemSK) := do
  let initialized ← RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId
  match initialized with
  | none => pure ((none, previous), PqxdhLiveKemBirth.empty)
  | some initial =>
    let result ← (simulateQ (RegistrationNativeObservedStageTrace.handler RegistrationNativePlatformOrdinaryKemClientJournal.observe
      (RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route representation initial.created initial.credential
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer))
      (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) initial.created.server.server.metadata.sender bounds mode
        (adversary initial.public))).run ((initial.state, previous), [])
    pure ((some ⟨RegistrationNativePlatformKemCountedProfile.ofInitial initial, result.1,
      RegistrationNativeKemServerState.ofNative result.2.1.1, result.2.2⟩, result.2.1.2), result.2.1.1.pool)

omit primitives in
private theorem evaluate_bind {A B : Type} (setup : Setup base KemSK)
    (work : OracleComp (RegistrationNativeKemCountedProgram.Spec KemSK) A)
    (next : A → OracleComp (RegistrationNativeKemCountedProgram.Spec KemSK) B) (pool : PqxdhLiveKemBirth.Pool KemSK) :
    RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem (work >>= next) pool = (do
      let result ← RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem work pool
      RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem (next result.1) result.2) := by
  simp only [RegistrationNativeKemCountedProgram.evaluate, simulateQ_bind, StateT.run_bind]

/-- Complete startup and the unchanged raw adaptive compilation have the same actual Native/client journal, final private recipient pool and platform state. -/
theorem source_history :
    RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem
      ((RegistrationNativePlatformOrdinaryKemInitializedJournal.program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary).run previous) PqxdhLiveKemBirth.empty =
      native (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous := by
  unfold RegistrationNativePlatformOrdinaryKemInitializedJournal.program
  dsimp only [StateT.run]
  rw [evaluate_bind, RegistrationNativeKemCountedProgram.ordinary_source]
  simp only [native, RegistrationNativePlatformKemCountedProfile.start, bind_map_left]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro initialized supported
  cases initialized with
  | none => rfl
  | some initial =>
    have empty := RegistrationNativePlatformKemCountedProfile.start_empty setup source ensureInit identityIndex serverKeyId initial supported
    have sourceLaw := RegistrationNativePlatformOrdinaryKemClientJournal.source_program setup checks wire route representation initial.created initial.credential
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) initial.created.server.server.metadata.sender bounds mode
        (adversary initial.public)) ((initial.state, previous), [])
    simp only [RegistrationNativeStateInterpreter.interpret, RegistrationNativePlatformPackedState.pack,
      RegistrationNativePlatformInterpret.state, StateT.run, RegistrationNativePlatformOrdinaryKemClientJournal.projected] at sourceLaw
    rw [empty] at sourceLaw
    have packed := congrArg (fun distribution =>
      (fun result : (Value × RegistrationNativeLedger.State) ×
          (((RegistrationNativeKemServerState.State n source × Platform) ×
            List (Call TypedSpec (RegistrationNativeKemServerState.State n source × Platform))) × PqxdhLiveKemBirth.Pool KemSK) =>
        ((some (⟨RegistrationNativePlatformKemCountedProfile.ofInitial initial, result.1, result.2.1.1.1, result.2.1.2⟩ : History n source Value Platform),
          result.2.1.1.2), result.2.2)) <$> distribution) sourceLaw
    simp only [Functor.map_map] at packed
    simp only [Option.map_some, bind_pure_comp, RegistrationNativeKemCountedProgram.evaluate,
      simulateQ_map, StateT.run_map] at ⊢
    simp only [RegistrationNativePlatformKemCountedProfile.ofInitial, RegistrationNativePlatformOrdinaryKemClientJournal.projected,
      RegistrationNativeKemServerState.ofNative, Prod.map, id_eq] at packed ⊢
    exact packed

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHistorySource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHistorySource.source_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHistorySource.source_history
