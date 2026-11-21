import BeaconcryptCore.Computational.RawCtxSelectedSendCompiler

/-!
A saved predecessor send resumes with its supplied known material and new concrete chain. Its pending seal retains the original writer result and every shared-cache effect. Selected child-message material can arise only during subsequent derivations; known byte aliases do not become hidden slots.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedPendingSendCompiler
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedMessageKey RawCtxSelectedMessageKdf RawCtxSelectedMessageDriver
open RawCtxSelectedParentTable RawCtxSelectedParentEntry
open RawCtxSelectedReceiveCompiler (State project evaluated)
variable {A : Type}

/-- Known pending material retains the complete native advanced kernel and seal context for every selected key, without testing byte equality. -/
theorem known_seal (key : RootOutput)
    (pending : RawCtxInterpretedSend.Seal RatchetMaterial RawCtxSourceSend.SealContext) :
    RawCtxInterpretedSend.mapSeal (interpret key) (RawCtxInterpretedSend.mapSeal Slot.known pending) = pending := by
  cases pending
  simp only [RawCtxInterpretedSend.mapSeal, known_kernel, interpret]

noncomputable def sealing (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (pending : RawCtxInterpretedSend.Seal RatchetMaterial RawCtxSourceSend.SealContext) :=
  Option.join <$> RawCtxSelectedSealConsumer.sealing c writer (RawCtxInterpretedSend.mapSeal Slot.known pending)

/-- The known predecessor seal always completes its outer interface. Flattening that proved-present outer option retains the original inner writer failure or ciphertext. -/
theorem sealing_completed (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (pending : RawCtxInterpretedSend.Seal RatchetMaterial RawCtxSourceSend.SealContext) :
    RawCtxSelectedSealConsumer.sealing c writer (RawCtxInterpretedSend.mapSeal Slot.known pending) =
      some <$> sealing c writer pending := by
  simp only [sealing, RawCtxSelectedSealConsumer.sealing, RawCtxSelectedSealConsumer.call,
    RawCtxInterpretedArguments.sealArguments, RawCtxInterpretedSend.mapSeal, simulateQ_map, Functor.map_map]
  rfl

/-- The known saved seal returns the actual optional native ciphertext and full cache without any selected-nonce premise. -/
theorem sealing_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder)
    (pending : RawCtxInterpretedSend.Seal RatchetMaterial RawCtxSourceSend.SealContext) (state : State A) :
    (RawCtxFunctionalFamily.sealing source writer (privateTable prior parent target (response key nonce next))
      (RawCtxInterpretedSend.nativeSeal pending)).run (project state) =
      Prod.map id project <$> (evaluated source key read (sealing source.crypto writer pending)).run state := by
  have completed := congrArg
    (fun work : ProbComp (Option (Option RawCtxSourceSend.Encrypted) × RawCtxSharedPrimitive.SharedState A) =>
      (fun result => (result.1.join, result.2)) <$> work)
    (RawCtxSelectedSendCompiler.sealing_project source writer prior parent key target nonce next read
      (RawCtxInterpretedSend.mapSeal Slot.known pending) state (fun _ impossible _ => by cases impossible))
  simpa only [sealing, RawCtxSelectedReceiveCompiler.evaluated_map, StateT.run_map, sendServices,
    known_seal, Functor.map_map, Prod.map_def, id_eq, Option.join, Option.bind_some, Prod.mk.eta, id_map'] using completed

/-- Retaining a private KDF table does not alter the actual source seal or writer callback; this endpoint contains no KDF request. -/
theorem source_seal (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (pending : SendSeal RawCtxSourceSend.SealContext) :
    RawCtxSourceChainHandles.sendNative (Auxiliary := A) source writer (.inr pending) =
      RawCtxFunctionalFamily.sealing source writer prior pending := by
  rw [RawCtxSelectedSendCompiler.sealing_native]
  simp only [RawCtxSourceChainHandles.sendNative, RawCtxSourceMaterialLabels.nativeImpl,
    QueryImpl.compose, RawCtxSourceSend.adapter, bind_pure_comp, RawCtxMixedOwner.sendAdapter,
    simulateQ_map, simulateQ_spec_query, RawCtxSourceSeal.nativeAdapter]
  simp only [RawCtxCanonicalSeal.sharedImpl, QueryImpl.simulateQ_compose]

/-- The saved known seal makes at most one dynamic call, paying its real shared-ROM work. -/
theorem sealing_queries (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (pending : RawCtxInterpretedSend.Seal RatchetMaterial RawCtxSourceSend.SealContext) :
    (sealing c writer pending).IsTotalQueryBound 1 := by
  simpa only [sealing, IsTotalQueryBound, isQueryBound_map_iff] using
    RawCtxSelectedSendCompiler.sealing_queries c writer (RawCtxInterpretedSend.mapSeal Slot.known pending)

/-- Known aliases retain their one-hash source allowance and issue no selected sealing, raw opening or uniform request. -/
theorem sealing_bills (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (pending : RawCtxInterpretedSend.Seal RatchetMaterial RawCtxSourceSend.SealContext) :
    (sealing c writer pending).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute 1 ∧
      (sealing c writer pending).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 ∧
      (sealing c writer pending).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 ∧
      (sealing c writer pending).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute 0 := by
  simpa only [sealing, isQueryBoundP_map_iff, RawCtxInterpretedSend.mapSeal] using
    RawCtxSelectedSealConsumer.sealing_bills c writer (RawCtxInterpretedSend.mapSeal Slot.known pending)

end BeaconcryptCore.Computational.RawCtxSelectedPendingSendCompiler

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingSendCompiler.known_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingSendCompiler.known_seal

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingSendCompiler.sealing_completed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingSendCompiler.sealing_completed

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingSendCompiler.sealing_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingSendCompiler.sealing_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingSendCompiler.source_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingSendCompiler.source_seal

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingSendCompiler.sealing_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingSendCompiler.sealing_queries

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingSendCompiler.sealing_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingSendCompiler.sealing_bills
