import BeaconcryptCore.Computational.PqxdhInitialParentContext

/-!
The selected Server first-send continuation preserves its actual erase, serialization and peer publication before resuming the full original post schedule. Only the new chain is represented privately; all saved state and later initializer results remain known. The same concrete retained-parent interpreter preserves all ambient effects and optional failures.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialParentBuilderContext
open PqxdhInitialPendingPost PqxdhInitialPostContext PqxdhInitialParentPost PqxdhInitialBuilderContext
open RawCtxSelectedParentCalls RawCtxSelectedParentEntry RawCtxSelectedFamilyContext
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily PqxdhJointKdfGame PqxdhSecretInputKdf
open PqxdhInitialBeaconAmbient PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids
variable {ι Chain Other M P I D K X Response Shared Result A N C : Type} {extra : OracleSpec ι} {S B : Nat}

abbrev Publication (Kernel M P : Type) := PqxdhInitialGenericPublication.State Kernel M P (List Pqxdh.Bytes)
def mapPublication (f : KernelOf Chain → KernelOf Other) (before : Publication (KernelOf Chain) M P) :
    Publication (KernelOf Other) M P :=
  ⟨(mapServer f ⟨before.server, 0⟩).server, before.identityKeyId, before.control, before.consumed⟩

private theorem publish_map (f : KernelOf Chain → KernelOf Other) (before : Publication (KernelOf Chain) M P)
    (candidate : pqxdh.ServerRegistrationCandidate) (kernel : KernelOf Chain) (metadata : P) :
    PqxdhInitialGenericPublication.publish (mapPublication f before) candidate (f kernel) metadata =
      mapPublication f (PqxdhInitialGenericPublication.publish before candidate kernel metadata) := by
  simp only [PqxdhInitialGenericPublication.publish, mapPublication, mapServer]
  congr 1
  congr 1
  funext key
  by_cases same : key = candidate.key_id
  · subst key
    simp only [Function.update_self, Option.map_some, mapPeer]
  · simp only [Function.update_of_ne same]

private theorem install_map (f : KernelOf Chain → KernelOf Other) (index : Fin S)
    (before : Front Chain M P I D K S B) (updated : Publication (KernelOf Chain) M P) :
    PqxdhInitialPendingBuilder.install index (mapFront f before) (mapPublication f updated) =
      mapFront f (PqxdhInitialPendingBuilder.install index before updated) := by
  unfold PqxdhInitialPendingBuilder.install mapFront mapPublication RawCtxGenericFamilyLive.mapState mapRoles
  congr 3
  funext other
  by_cases same : other = index
  · subst other
    simp only [Function.update_self, mapServer]
  · simp only [Function.update_of_ne same]

private theorem selected_map (f : KernelOf Chain → KernelOf Other) (sender : M → Std.U64)
    (index : Fin S) (before : Front Chain M P I D K S B) :
    PqxdhInitialPendingBuilder.selected sender index (mapFront f before) =
      mapPublication f (PqxdhInitialPendingBuilder.selected sender index before) := rfl

/-- The original pending first send consumes its full reply and produces the same advanced kernel and optional ciphertext from the material-only sealing tail. -/
theorem send_reply (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior)
    (pending : RawCtxChainSend.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext)
    (output : FullOutput) (challenge : RatchetKdfResponse) :
    (do
      let ready := RawCtxChainSend.ready pending (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output))
      let encrypted ← RawCtxSelectedParentNativeCompiler.pending (Auxiliary := A) source writer prior
        (fromOutput (RawCtxSelectedPendingCut.requestAddress pending.request) output) (nextChain output)
        (.inr (.inl (.inr ready)))
      pure (ready.advanced, encrypted)) =
      Prod.map (nativeKernel (nextChain output)) id <$>
      (do
        let ready := RawCtxSelectedPendingCut.sendStop pending (material output)
        let encrypted ← RawCtxSelectedParentCompiler.pending source writer prior
          (fromOutput (RawCtxSelectedPendingCut.requestAddress pending.request) output) challenge
          (.inr (.inl (.inr ready)))
        pure (ready.advanced, encrypted)) := by
  have cut := congrArg (fun work => (fun result => (result.1.refined, result.2)) <$> work)
    (RawCtxSelectedPendingCut.send_cut (Auxiliary := A) source writer prior pending output challenge)
  rw [RawCtxInterpretedSend.ready_native] at cut
  simpa [RawCtxSelectedParentNativeCompiler.pending,
    RawCtxSelectedParentCompiler.pending, QueryImpl.compose, RawCtxPendingOwnerQueries.erase,
    RawCtxSelectedParentNativeCompiler.original, RawCtxSelectedParentCompiler.original, OracleSpec.query,
    RawCtxSelectedParentSource.nativeSend, RawCtxChainSend.nativeSeal, RawCtxChainSend.nativeKdf,
    RawCtxInterpretedSend.nativeSeal, RawCtxInterpretedSend.ready, RawCtxChainSend.ready,
    RawCtxChainInterpretation.mapChains, nativeKernel, RawCtxSelectedChain.nativeKernel,
    Functor.map_map] using cut

noncomputable def reply (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (context : PqxdhInitialBuilderContext.Context extra M P I D K Result S B)
    (output : FullOutput) :
    (Base extra RatchetChain I D K X Response Shared S B).Range
      (PqxdhInitialBuilderContext.frame sender route decode context).1 :=
  match context with
  | .inl context => PqxdhInitialParentContext.reply sender route decode context output
  | .inr _ => RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output)

section Services
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (prior : RawCtxSelectedParentTable.Prior)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C (Option (KernelOf RatchetChain)))
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))

/-- Actual first-send erase, serialization and publication retain the complete source state before the same adaptive full post continuation. -/
theorem complete_map (entry : Entry) (target : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (before : LabelFront M P I D K S B) (candidate : pqxdh.ServerRegistrationCandidate)
    (authenticated : Pqxdh.Bytes) (metadata : P) (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (result : KernelOf RawCtxSelectedChain.Slot × Option RawCtxSourceSend.Encrypted) :
    simulateQ (nativeHandler source writer prior entry target pre application initial selector aux)
      (complete sender route decode index (mapFront (nativeKernel target) before) candidate authenticated metadata outside
        (Prod.map (nativeKernel target) id result)) =
    Prod.map id (mapFront (nativeKernel target)) <$> simulateQ
      (labelHandler source writer prior entry target pre application initial selector aux (childResponse prior entry target))
      (complete sender route decode index before candidate authenticated metadata outside result) := by
  simp only [complete, afterSend, simulateQ_bind, map_bind]
  simp only [auxForward, nativeHandler, labelHandler, bind_assoc,
    Prod.map_def, id_eq]
  apply bind_congr
  intro erased
  cases sealed : result.2 with
  | none =>
    simp only [simulateQ_pure, pure_bind, PqxdhInitialPendingBuilder.reinstall, selected_map, install_map]
    exact PqxdhInitialParentPost.program source writer prior entry target pre application initial selector aux
      sender route decode _ _
  | some encrypted =>
    dsimp only
    simp only [simulateQ_bind, bind_assoc]
    apply bind_congr
    intro serialized
    cases serialized with
    | some bytes =>
      simp only [simulateQ_pure, pure_bind, PqxdhInitialPendingBuilder.reinstall, selected_map,
        publish_map, install_map]
      exact PqxdhInitialParentPost.program source writer prior entry target pre application initial selector aux
        sender route decode _ _
    | none =>
      simp only [simulateQ_pure, pure_bind, PqxdhInitialPendingBuilder.reinstall, selected_map, install_map]
      exact PqxdhInitialParentPost.program source writer prior entry target pre application initial selector aux
        sender route decode _ _

set_option backward.isDefEq.respectTransparency false in
/-- The actual first builder or later post frame receives its full source reply and equals the material-only stopped continuation under the private native interpretation. -/
theorem frame_cut (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (context : PqxdhInitialBuilderContext.Context extra M P I D K Result S B)
    (output : FullOutput) :
    simulateQ (nativeHandler source writer prior (fromOutput (PqxdhInitialBuilderContext.address context) output)
      (nextChain output) pre application initial selector aux)
      ((PqxdhInitialBuilderContext.frame sender route decode context).2 (reply sender route decode context output)) =
    Prod.map id (mapFront (nativeKernel (nextChain output))) <$> simulateQ
      (labelHandler source writer prior (fromOutput (PqxdhInitialBuilderContext.address context) output)
        (nextChain output) pre application initial selector aux
        (childResponse prior (fromOutput (PqxdhInitialBuilderContext.address context) output) (nextChain output)))
      (PqxdhInitialBuilderContext.stopped sender route decode context (material output)) := by
  cases context with
  | inr context =>
    have advanced : (RawCtxChainSend.ready context.pending
        (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output))).advanced =
        nativeKernel (nextChain output) (RawCtxSelectedPendingCut.sendStop context.pending (material output)).advanced := by
      rw [RawCtxFreshChainCut.decoded_parts]
      rfl
    have sealing := congrArg (fun work => Prod.snd <$> work)
      (send_reply (A := A) source writer prior context.pending output
        (childResponse prior (fromOutput (RawCtxSelectedPendingCut.requestAddress context.pending.request) output) (nextChain output)))
    simp only [map_bind, map_pure, Prod.map_apply, id_eq, bind_pure] at sealing
    simp only [PqxdhInitialBuilderContext.frame, builderFrame, reply, PqxdhInitialBuilderContext.address,
      PqxdhInitialBuilderContext.stopped, simulateQ_bind, simulateQ_spec_query, nativeHandler, labelHandler,
      handler, RawCtxPendingFamilyLiveQueries.handler, nativePrimitive, labelPrimitive]
    generalize nativeWork : (RawCtxSelectedParentNativeCompiler.pending (Auxiliary := A) source writer prior
      (fromOutput (RawCtxSelectedPendingCut.requestAddress context.pending.request) output) (nextChain output)
      (.inr (.inl (.inr (RawCtxChainSend.ready context.pending
        (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output)))))) :
      PqxdhInitialBeaconAmbient.Base A (Option RawCtxSourceSend.Encrypted)) = nativeSeal at sealing ⊢
    generalize labelWork : (RawCtxSelectedParentCompiler.pending (Auxiliary := A) source writer prior
      (fromOutput (RawCtxSelectedPendingCut.requestAddress context.pending.request) output)
      (childResponse prior (fromOutput (RawCtxSelectedPendingCut.requestAddress context.pending.request) output) (nextChain output))
      (.inr (.inl (.inr (RawCtxSelectedPendingCut.sendStop context.pending (material output))))) :
      PqxdhInitialBeaconAmbient.Base A (Option RawCtxSourceSend.Encrypted)) = labelSeal at sealing ⊢
    change PqxdhInitialBeaconAmbient.Base A (Option RawCtxSourceSend.Encrypted) at nativeSeal labelSeal
    change (PqxdhInitialBeaconAmbient.lift (α := Option RawCtxSourceSend.Encrypted) (N := N) (C := C) nativeSeal >>= fun encrypted =>
      simulateQ (nativeHandler source writer prior
        (fromOutput (RawCtxSelectedPendingCut.requestAddress context.pending.request) output) (nextChain output)
        pre application initial selector aux)
        (complete sender route decode context.index context.before context.candidate context.authenticated
          context.metadata context.outside
          ((RawCtxChainSend.ready context.pending
            (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output))).advanced, encrypted))) =
      Prod.map id (mapFront (nativeKernel (nextChain output))) <$>
        (PqxdhInitialBeaconAmbient.lift (α := Option RawCtxSourceSend.Encrypted) (N := N) (C := C) labelSeal >>= fun encrypted =>
          simulateQ (labelHandler source writer prior
            (fromOutput (RawCtxSelectedPendingCut.requestAddress context.pending.request) output) (nextChain output)
            pre application initial selector aux
            (childResponse prior (fromOutput (RawCtxSelectedPendingCut.requestAddress context.pending.request) output) (nextChain output)))
            (complete sender route decode context.index (knownFront context.before) context.candidate context.authenticated
              context.metadata context.outside ((RawCtxSelectedPendingCut.sendStop context.pending (material output)).advanced, encrypted)))
    rw [sealing]
    simp only [map_bind]
    apply bind_congr
    intro encrypted
    rw [advanced]
    simpa only [known_front, Prod.map_apply, id_eq] using complete_map source writer prior pre application initial selector aux
      (fromOutput (RawCtxSelectedPendingCut.requestAddress context.pending.request) output) (nextChain output)
      sender route decode context.index (knownFront context.before) context.candidate context.authenticated
      context.metadata context.outside ((RawCtxSelectedPendingCut.sendStop context.pending (material output)).advanced, encrypted)
  | inl context =>
    exact PqxdhInitialParentContext.frame_cut source writer prior pre application initial selector aux
      sender route decode context output

/-- The complete first-builder or later-post cut retains every shared, private and cache field at the evaluated distribution. -/
theorem frame_run (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (context : PqxdhInitialBuilderContext.Context extra M P I D K Result S B)
    (output : FullOutput) (state : RawCtxSharedPrimitive.SharedState A × N) (cache : C) :
    ((simulateQ (nativeHandler source writer prior (fromOutput (PqxdhInitialBuilderContext.address context) output)
      (nextChain output) pre application initial selector aux)
      ((PqxdhInitialBuilderContext.frame sender route decode context).2 (reply sender route decode context output))).run state).run cache =
    (fun result => ((Prod.map id (mapFront (nativeKernel (nextChain output))) result.1.1, result.1.2), result.2)) <$>
      ((simulateQ (labelHandler source writer prior (fromOutput (PqxdhInitialBuilderContext.address context) output)
        (nextChain output) pre application initial selector aux
        (childResponse prior (fromOutput (PqxdhInitialBuilderContext.address context) output) (nextChain output)))
      (PqxdhInitialBuilderContext.stopped sender route decode context (material output))).run state).run cache := by
  rw [frame_cut]
  rfl

end Services
end BeaconcryptCore.Computational.PqxdhInitialParentBuilderContext

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentBuilderContext.send_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentBuilderContext.send_reply

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentBuilderContext.complete_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentBuilderContext.complete_map

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentBuilderContext.frame_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentBuilderContext.frame_cut

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentBuilderContext.frame_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentBuilderContext.frame_run
