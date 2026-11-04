-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPrivateKdfSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPrivateRecordPrefix
import BeaconcryptCore.Computational.RegistrationNativePlatformBoundPublication
/-! Exact source KDF callback accounting is independent of its private operands. Initial derivation appends its public kind marker; ongoing derivation additionally increments the actual native KDF counter. All World, cache, uniform and external coordinates are retained literally. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPrivateKdfState
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {Auxiliary ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m]

def initialState (before : RegistrationWorldAgreement.State n Auxiliary) : RegistrationWorldAgreement.State n Auxiliary :=
  { before with recordRequests := before.recordRequests ++ [.initialKdf] }

def ratchetState (before : RegistrationWorldAgreement.State n Auxiliary) : RegistrationWorldAgreement.State n Auxiliary :=
  { before with
    recordRequests := before.recordRequests ++ [.ratchetKdf]
    world := ({ before.world.1 with primitive :=
      ({ before.world.1.primitive.1 with native := Function.update before.world.1.primitive.1.native RawCtxMixedOwner.CallKind.kdf (before.world.1.primitive.1.native .kdf + 1) }, before.world.1.primitive.2) }, before.world.2) }

/-- The actual initial callback returns the actual fixed source response and records exactly its public kind. -/
theorem initial (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (request : ratchet.SymmetricRatchetKdfRequest) (before : RegistrationWorldAgreement.State n Auxiliary) :
    ((RegistrationNativePlatformServerCompletion.records coins setup codec (.initialKdf request)).run before) =
      pure (.Some (RawCtxSourceHkdf.initialResponse setup.source.crypto request), initialState before) := by
  rfl

/-- The actual ongoing callback returns the actual fixed response and records precisely one native KDF call and its chronological public kind. -/
theorem ratchet (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (request : ratchet.SymmetricRatchetKdfRequest) (before : RegistrationWorldAgreement.State n Auxiliary) :
    ((RegistrationNativePlatformServerCompletion.records coins setup codec (.ratchetKdf request)).run before) =
      pure (.Some (RawCtxSourceHkdf.response setup.source.crypto request), ratchetState before) := by
  rfl

variable [LawfulMonad m]

/-- The complete actual two-KDF prefix returns its fixed source-selected capability and its exact operand-independent accounting update. -/
theorem private_prefix (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (initial : registration.ServerInitialKdf) (root : PqxdhSecretInputKdf.RootOutput)
    (role : initial.pending = PqxdhInitialRatchetComplementarity.serverPending
      (PqxdhRootTableInitialization.rootArray root)) (before : RegistrationWorldAgreement.State n Auxiliary) :
    (RegistrationNativePlatformPrivateRecordPrefix.privatePrefix
      (RegistrationNativePlatformServerCompletion.records coins setup codec) initial).run before =
      pure (RegistrationSeedErasure.selected initial
        (RawCtxSelectedInitialConstructor.response64
          (PqxdhSecretInputKdf.first32 (PqxdhServerAuthKeySchedule.initializer setup.source root) ++
            RawCtxSelectedInitialSecond.secondChain (PqxdhServerAuthKeySchedule.initializer setup.source root)))
        (RawCtxKdfRequestTable.fullResponse (PqxdhServerAuthKeySchedule.fromRoot setup.source root).1),
        ratchetState (initialState before)) := by
  have initialRequested : initial.request =
      .ok ⟨PqxdhRootTableInitialization.rootArray root, ratchet.SYM_RATCHET_INFO⟩ := by
    simp only [registration.ServerInitialKdf.request, role,
      pqxdh.concrete.InitialRatchetKdfPending.impl.request, PqxdhInitialRatchetComplementarity.serverPending]
  obtain ⟨next, initialRun, nextRequested⟩ := RegistrationBoundSource.next_request initial _ role
    (PqxdhSecretInputKdf.first32 (PqxdhServerAuthKeySchedule.initializer setup.source root))
    (RawCtxSelectedInitialSecond.secondChain (PqxdhServerAuthKeySchedule.initializer setup.source root))
  simp only [RegistrationNativePlatformPrivateRecordPrefix.privatePrefix, initialRequested, StateT.run_bind]
  rw [RegistrationNativePlatformPrivateKdfState.initial coins setup codec _ before]
  simp only [pure_bind, RegistrationBoundSource.initial_response, initialRun, nextRequested, StateT.run_bind]
  rw [ratchet coins setup codec _ (initialState before)]
  simp only [pure_bind, StateT.run_pure, RegistrationSeedErasure.selected, initialRun, bind_tc_ok,
    RegistrationBoundSource.ratchet_response, PqxdhServerAuthKeySchedule.fromRoot,
    PqxdhServerAuthKeySchedule.fromInitializer]

/-- The literal full source first record executes its two private KDF calls with exact accounting, then the public-initial bound108 continuation at their reached state. All suffix allocation, AEAD, hash, writer and enclosing failures remain literal. -/
theorem source (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sealing : record_effects.AeadSealRequest → StateT (RegistrationWorldAgreement.State n Auxiliary) m
      (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → StateT (RegistrationWorldAgreement.State n Auxiliary) m RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → StateT (RegistrationWorldAgreement.State n Auxiliary) m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerInitialKdf) (root : PqxdhSecretInputKdf.RootOutput)
    (role : pending.pending = PqxdhInitialRatchetComplementarity.serverPending
      (PqxdhRootTableInitialization.rootArray root)) (before : RegistrationWorldAgreement.State n Auxiliary) :
    (RegistrationNativePlatformSourceRecord.fromInitialWithHash
      (RegistrationNativePlatformServerCompletion.records coins setup codec) sealing hash write pending).run before =
      (RegistrationNativePlatformBoundPublication.record sealing hash write
        (RegistrationBoundKeySchedule.publicInitial pending) (PqxdhServerAuthKeySchedule.fromRoot setup.source root)).run
          (ratchetState (initialState before)) := by
  rw [RegistrationNativePlatformPrivateRecordPrefix.source, StateT.run_bind,
    private_prefix coins setup codec pending root role before, pure_bind]
  unfold RegistrationNativePlatformBoundPublication.record
  have same : RegistrationSeedErasure.selected pending
      (RawCtxSelectedInitialConstructor.response64
        (PqxdhSecretInputKdf.first32 (PqxdhServerAuthKeySchedule.initializer setup.source root) ++
          RawCtxSelectedInitialSecond.secondChain (PqxdhServerAuthKeySchedule.initializer setup.source root)))
      (RawCtxKdfRequestTable.fullResponse (PqxdhServerAuthKeySchedule.fromRoot setup.source root).1) =
      RegistrationSeedErasure.selected (RegistrationBoundKeySchedule.restore (RegistrationBoundKeySchedule.publicInitial pending))
        (RawCtxSelectedInitialConstructor.response64 (RegistrationBoundKeySchedule.zero ++
          (PqxdhServerAuthKeySchedule.fromRoot setup.source root).2))
        (RawCtxKdfRequestTable.fullResponse (PqxdhServerAuthKeySchedule.fromRoot setup.source root).1) := by
    dsimp only [PqxdhServerAuthKeySchedule.fromRoot, PqxdhServerAuthKeySchedule.fromInitializer]
    rw [RegistrationSeedErasure.left_unused pending (PqxdhRootTableInitialization.rootArray root) role
      (PqxdhSecretInputKdf.first32 (PqxdhServerAuthKeySchedule.initializer setup.source root)) RegistrationBoundKeySchedule.zero
      (RawCtxSelectedInitialSecond.secondChain (PqxdhServerAuthKeySchedule.initializer setup.source root))]
    exact RegistrationBoundKeySchedule.root_unused pending _ role _ _
  rw [same]

end BeaconcryptCore.Computational.RegistrationNativePlatformPrivateKdfState

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPrivateKdfState.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPrivateKdfState.initial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPrivateKdfState.ratchet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPrivateKdfState.ratchet

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPrivateKdfState.private_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPrivateKdfState.private_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPrivateKdfState.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPrivateKdfState.source
