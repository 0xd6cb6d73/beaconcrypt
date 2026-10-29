-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBoundSource
import BeaconcryptCore.Computational.RegistrationBoundSourceCompiler

/-! Actual Server initial64 and ongoing76 source callbacks factor before interpreting their public hash effects. The result is the same bound108 native record program, including all later AEAD, hash, writer and failure effects. No World or source-program equality is supplied as a premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerRecordSourceProgram
open PqxdhSecretInputKdf (RootOutput)
open PqxdhServerAuthKeySchedule (initializer fromRoot)
open RegistrationBoundKeySchedule (publicInitial factored supplied)
variable {n : Nat}

noncomputable def native (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) :
    QueryImpl RegistrationRecordPrimitives.Spec (OracleComp (PqxdhRecordLiftInterface.EnvEffects n)) :=
  RegistrationBoundSourceCompiler.rawCompiler source writer ∘ₛ RegistrationRawSealBridge.nativeAdapter

/-- The actual initial64 source reply is evaluated locally, retaining every hash request for the shared World. -/
theorem initial_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (request : SymmetricRatchetKdfRequest) :
    native (n := n) source writer (.initialKdf request) =
      pure (.Some (RawCtxSourceHkdf.initialResponse source.crypto request)) := rfl

/-- The actual ongoing76 source reply is evaluated locally with its literal native request. -/
theorem ratchet_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (request : SymmetricRatchetKdfRequest) :
    native (n := n) source writer (.ratchetKdf request) =
      pure (.Some (RawCtxSourceHkdf.response source.crypto request)) := rfl

/-- Real initial64 and ongoing76 replies yield the original supplied-material record continuation before any public effects are interpreted. -/
theorem initial_supplied (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (initial : registration.ServerInitialKdf) (root : RootOutput)
    (role : initial.pending = PqxdhInitialRatchetComplementarity.serverPending
      (PqxdhRootTableInitialization.rootArray root)) :
    simulateQ (native (n := n) source writer) (RegistrationServerRecordExecutor.fromInitial initial) =
      simulateQ (native source writer)
        (supplied initial (PqxdhSecretInputKdf.first32 (initializer source root))
          (RawCtxSelectedInitialSecond.secondChain (initializer source root)) (fromRoot source root).1) := by
  have initialRequested : initial.request =
      .ok ⟨PqxdhRootTableInitialization.rootArray root, SYM_RATCHET_INFO⟩ := by
    simp only [registration.ServerInitialKdf.request, role,
      pqxdh.concrete.InitialRatchetKdfPending.impl.request, PqxdhInitialRatchetComplementarity.serverPending]
  obtain ⟨next, initialRun, nextRequested⟩ := RegistrationBoundSource.next_request initial _ role
    (PqxdhSecretInputKdf.first32 (initializer source root))
    (RawCtxSelectedInitialSecond.secondChain (initializer source root))
  simp only [RegistrationServerRecordExecutor.fromInitial, initialRequested,
    RegistrationServerRecordExecutor.continueWith, simulateQ_bind, simulateQ_spec_query]
  rw [initial_source]
  simp only [pure_bind, RegistrationBoundSource.initial_response, initialRun,
    RegistrationServerRecordExecutor.continueResult, RegistrationServerRecordExecutor.fromRatchet, nextRequested,
    RegistrationServerRecordExecutor.continueWith, simulateQ_bind, simulateQ_spec_query,
    supplied, RegistrationSeedErasure.selected, bind_tc_ok]
  rw [ratchet_source]
  simp only [pure_bind, RegistrationBoundSource.ratchet_response, PqxdhServerAuthKeySchedule.fromRoot,
    PqxdhServerAuthKeySchedule.fromInitializer]

/-- The complete real sequence-one Server program is the public-initial bound108 program, with the same full optional result and later effects. -/
theorem initial_factored (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (initial : registration.ServerInitialKdf) (root : RootOutput)
    (role : initial.pending = PqxdhInitialRatchetComplementarity.serverPending
      (PqxdhRootTableInitialization.rootArray root)) :
    simulateQ (native (n := n) source writer) (RegistrationServerRecordExecutor.fromInitial initial) =
      simulateQ (RegistrationBoundSourceCompiler.rawCompiler source writer)
        (simulateQ RegistrationRawSealBridge.nativeAdapter
          (factored (publicInitial initial) (fromRoot source root))) := by
  rw [initial_supplied source writer initial root role]
  have erased : supplied initial (PqxdhSecretInputKdf.first32 (initializer source root))
      (RawCtxSelectedInitialSecond.secondChain (initializer source root)) (fromRoot source root).1 =
      factored (publicInitial initial) (fromRoot source root) := by
    unfold supplied factored
    dsimp only [PqxdhServerAuthKeySchedule.fromRoot, PqxdhServerAuthKeySchedule.fromInitializer]
    rw [RegistrationSeedErasure.left_unused initial (PqxdhRootTableInitialization.rootArray root) role
      (PqxdhSecretInputKdf.first32 (initializer source root)) RegistrationBoundKeySchedule.zero
      (RawCtxSelectedInitialSecond.secondChain (initializer source root))]
    rw [RegistrationBoundKeySchedule.root_unused initial (PqxdhRootTableInitialization.rootArray root) role]
  rw [erased, native, QueryImpl.simulateQ_compose]

end BeaconcryptCore.Computational.RegistrationServerRecordSourceProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordSourceProgram.initial_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordSourceProgram.initial_source
/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordSourceProgram.ratchet_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordSourceProgram.ratchet_source
/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordSourceProgram.initial_supplied' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordSourceProgram.initial_supplied
/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordSourceProgram.initial_factored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordSourceProgram.initial_factored
