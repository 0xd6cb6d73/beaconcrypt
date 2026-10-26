import BeaconcryptCore.Computational.PqxdhLaterSavedFinish

/-! The saved Server builder seals its actual supplied predecessor material, runs the original erase/write/publication tail, and resumes the complete Post client with every native field retained. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterSavedBuilder
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedMessageDriver
open PqxdhSelectedFirstRecord
variable {ι I D K X Response Shared A N C M P Result : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (trace : PqxdhInitialOriginPost.Trace Bool S B) (origin : Option Bool)
    (builder : PqxdhInitialBuilderContext.Builder extra M P I D K Result S B)
    (material : PqxdhOrderedChainHybrids.Material)

local notation "parent" => Entry.mk (RawCtxSelectedPendingCut.requestAddress builder.pending.request) material
local notation "ready" => RawCtxChainSend.ready builder.pending
  (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse (realize parent target)))
local notation "table" => privateTable prior (some parent) target (RawCtxSelectedMessageKdf.response key nonce next)

noncomputable def nativeBuilder (state : RawCtxSelectedReceiveCompiler.State (Local A N C)) := do
  let sealed ← (RawCtxFunctionalFamily.sealing source writer table
    (RawCtxInterpretedSend.nativeSeal (RawCtxChainSend.nativeSeal id id ready))).run
      (RawCtxSelectedReceiveCompiler.project state)
  let published ← (PqxdhInitialBuilderContext.afterSend (serverAux pre application initial selector aux)
    builder.candidate builder.authenticated builder.metadata
    (PqxdhInitialPendingBuilder.selected sender builder.index builder.before) ((ready).advanced, sealed.1)).run sealed.2
  let installed := PqxdhInitialPendingBuilder.reinstall builder.index builder.before (.ok published.1)
  (simulateQ (nativeFlat pre application initial selector aux source writer prior (some parent) key target nonce next
    sender route read mark) (builder.outside installed.1)).run
      ((installed.2, PqxdhInitialOriginContext.builtTrace trace origin installed.2 builder.index installed.1), published.2)

noncomputable def selectedBuilder (state : RawCtxSelectedReceiveCompiler.State (Local A N C)) := do
  let sealed ← (RawCtxSelectedReceiveCompiler.evaluated source key read
    (RawCtxSelectedPendingSendCompiler.sealing source.crypto writer (RawCtxChainSend.nativeSeal id id ready))).run state
  let published ← (PqxdhInitialBuilderContext.afterSend (serverAux pre application initial selector aux)
    builder.candidate builder.authenticated builder.metadata
    (PqxdhInitialPendingBuilder.selected sender builder.index builder.before) ((ready).advanced, sealed.1)).run
      (RawCtxSelectedReceiveCompiler.project sealed.2)
  let installed := PqxdhInitialPendingBuilder.reinstall builder.index builder.before (.ok published.1)
  Prod.map id (tracedProj key) <$>
    (simulateQ (tracedPlain pre application initial selector aux source writer prior (some parent) key target nonce next
      sender route read mark) (builder.outside installed.1)).run
        ((initialFront installed.2, published.2),
          PqxdhInitialOriginContext.builtTrace trace origin installed.2 builder.index installed.1)

/-- The known predecessor seal and both writer outcomes retain the exact publication state, installation trace and full outside execution. -/
theorem builder_source (state : RawCtxSelectedReceiveCompiler.State (Local A N C)) :
    nativeBuilder pre application initial selector aux source writer prior key target nonce next mark sender route read
      trace origin builder material state =
    selectedBuilder pre application initial selector aux source writer prior key target nonce next mark sender route read
      trace origin builder material state := by
  rw [nativeBuilder, RawCtxSelectedPendingSendCompiler.sealing_source source writer prior (some parent)
    key target nonce next read]
  simp only [selectedBuilder, bind_map_left]
  apply bind_congr
  intro sealed
  apply bind_congr
  intro published
  let installed := PqxdhInitialPendingBuilder.reinstall builder.index builder.before (.ok published.1)
  simpa only [tracedProj, frontOf_initial] using
    (post_program (P := P) (S := S) (B := B) pre application initial selector aux source writer prior
      (some parent) key target nonce next sender route read mark (builder.outside installed.1)
      ((initialFront installed.2, published.2),
        PqxdhInitialOriginContext.builtTrace trace origin installed.2 builder.index installed.1)).symm

/-- The literal pending seal request uses exactly the original source sealing and writer callback; it performs no private KDF lookup. -/
theorem builder_seal :
    lowered (S := S) (B := B) pre application initial selector aux source writer table
      (.inl (.inl (.inr (.inl (.inr ready))))) =
      RawCtxFunctionalFamily.sealing source writer table
        (RawCtxInterpretedSend.nativeSeal (RawCtxChainSend.nativeSeal id id ready)) := by
  simp only [lowered, privateTable, RawCtxRetainedParentBackend.retained_live,
    RawCtxSelectedParentFamilyMap.nativeLive, RawCtxPendingFamilyLiveQueries.handler,
    RawCtxSelectedParentNativeCompiler.pending, QueryImpl.compose,
    RawCtxPendingOwnerQueries.erase, simulateQ_spec_query, RawCtxSelectedParentNativeCompiler.original,
    RawCtxSelectedParentSource.nativeSend]
  exact RawCtxSelectedPendingSendCompiler.source_seal source writer table _

/-- Forwarding the concrete saved publication tail preserves the real erasure and optional writer effects. -/
theorem afterSend_lowered (sealed : Option RawCtxSourceSend.Encrypted) :
    simulateQ (lowered (S := S) (B := B) pre application initial selector aux source writer table)
      (PqxdhInitialBuilderContext.afterSend PqxdhInitialPendingPost.auxForward
        builder.candidate builder.authenticated builder.metadata
        (PqxdhInitialPendingBuilder.selected sender builder.index builder.before) ((ready).advanced, sealed)) =
      PqxdhInitialBuilderContext.afterSend (serverAux pre application initial selector aux)
        builder.candidate builder.authenticated builder.metadata
        (PqxdhInitialPendingBuilder.selected sender builder.index builder.before) ((ready).advanced, sealed) := by
  simp only [PqxdhInitialBuilderContext.afterSend, simulateQ_bind,
    PqxdhInitialPendingPost.auxForward, simulateQ_spec_query, lowered, serverAux]
  apply bind_congr
  intro erased
  cases sealed
  all_goals simp only [simulateQ_bind, simulateQ_pure, simulateQ_spec_query, lowered]
  apply bind_congr
  intro serialized
  cases serialized <;> rfl

/-- The complete source run is the literal saved builder descriptor after its supplied full predecessor response. -/
theorem builder_resume (state : RawCtxSelectedReceiveCompiler.State (Local A N C)) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (lowered pre application initial selector aux source writer table)
      (PqxdhInitialOriginContext.resume mark sender route read ⟨.inr builder, trace, origin⟩
        (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse (realize parent target))))).run
          (RawCtxSelectedReceiveCompiler.project state) =
      nativeBuilder pre application initial selector aux source writer prior key target nonce next mark sender route read
        trace origin builder material state := by
  simp only [PqxdhInitialOriginContext.resume, PqxdhInitialOriginContext.complete,
    simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  simp only [builder_seal, afterSend_lowered, map_bind,
    simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map, nativeBuilder, nativeFlat, Prod.eta, id_map']
  rfl

/-- Retaining the original native source state gives the same saved builder and complete Post continuation after projecting only auxiliary instrumentation. -/
theorem retained_builder (state : RawCtxSelectedReceiveCompiler.State (Local A N C)) :
    (simulateQ (PqxdhInitialNativeRetained.retained source writer table
      (lifted pre application initial selector aux))
      (PqxdhInitialOriginContext.resume mark sender route read ⟨.inr builder, trace, origin⟩
        (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse (realize parent target))))).run
          (retainedOf (RawCtxSelectedReceiveCompiler.project state)) =
      (fun result => ((result.1, result.2.1), retainedOf result.2.2)) <$>
        selectedBuilder pre application initial selector aux source writer prior key target nonce next mark sender route read
          trace origin builder material state := by
  rw [← low_program pre application initial selector aux]
  have actual := congrArg (fun work => (fun result => ((result.1, result.2.1), retainedOf result.2.2)) <$> work)
    ((builder_resume pre application initial selector aux source writer prior key target nonce next mark sender route read
      trace origin builder material state).trans
      (builder_source pre application initial selector aux source writer prior key target nonce next mark sender route read
        trace origin builder material state))
  simpa only [Functor.map_map, Prod.map_def, id_eq] using actual

end BeaconcryptCore.Computational.PqxdhLaterSavedBuilder

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedBuilder.builder_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedBuilder.builder_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedBuilder.builder_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedBuilder.builder_seal
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedBuilder.afterSend_lowered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedBuilder.afterSend_lowered
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedBuilder.builder_resume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedBuilder.builder_resume
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedBuilder.retained_builder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedBuilder.retained_builder
