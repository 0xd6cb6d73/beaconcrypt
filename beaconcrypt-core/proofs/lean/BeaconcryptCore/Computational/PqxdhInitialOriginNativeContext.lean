import BeaconcryptCore.Computational.PqxdhInitialOriginContext

/-!
The complete original pending reply and material-only reply retain the same installation origins and successful-publication transcript under the concrete retained-parent interpreter. All original first-send, first-receive, full post and ambient effects remain present.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialOriginNativeContext
open PqxdhInitialPendingPost PqxdhInitialPostContext PqxdhInitialParentPost PqxdhInitialOriginPost
open RawCtxSelectedParentCalls RawCtxSelectedParentEntry RawCtxSelectedFamilyContext
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily PqxdhJointKdfGame PqxdhSecretInputKdf
open PqxdhInitialBeaconAmbient PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids
open PqxdhInitialParentBuilderContext
variable {ι Chain Other M P I D K X Response Shared Result Origin A N C : Type} {extra : OracleSpec ι} {S B : Nat}

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


private theorem built_trace_map (target : RootOutput) (trace : Trace Origin S B) (origin : Option Origin)
    (before : LabelFront M P I D K S B) (index : Fin S)
    (reply : RustM (Option PqxdhServerRegistrationPublication.Response)) :
    PqxdhInitialOriginContext.builtTrace trace origin (mapFront (nativeKernel target) before) index reply =
      PqxdhInitialOriginContext.builtTrace trace origin before index reply := by
  cases origin with
  | none => rfl
  | some origin => exact PqxdhInitialOriginPostMap.builder_trace target trace before index origin reply

section Services
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (prior : RawCtxSelectedParentTable.Prior)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C (Option (KernelOf RatchetChain)))
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))

/-- The actual first-send completion preserves its complete original publication and outside client together with every installed origin and transcript entry. -/
theorem complete_map (entry : Entry) (target : RootOutput)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (before : LabelFront M P I D K S B) (trace : Trace Origin S B) (origin : Option Origin)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (outside : PqxdhInitialBuilderContext.BuildResult → OracleComp (PostSpec extra S B) Result)
    (result : KernelOf RawCtxSelectedChain.Slot × Option RawCtxSourceSend.Encrypted) :
    simulateQ (nativeHandler source writer prior entry target pre application initial selector aux)
      (PqxdhInitialOriginContext.complete mark sender route decode index (mapFront (nativeKernel target) before)
        trace origin candidate authenticated metadata outside (Prod.map (nativeKernel target) id result)) =
    Prod.map id (Prod.map (mapFront (nativeKernel target)) id) <$> simulateQ
      (labelHandler source writer prior entry target pre application initial selector aux (childResponse prior entry target))
      (PqxdhInitialOriginContext.complete mark sender route decode index before trace origin candidate authenticated metadata outside result) := by
  simp only [PqxdhInitialOriginContext.complete, PqxdhInitialBuilderContext.afterSend, simulateQ_bind, map_bind]
  simp only [auxForward, nativeHandler, labelHandler, bind_assoc, Prod.map_def, id_eq]
  apply bind_congr
  intro erased
  cases sealed : result.2 with
  | none =>
    simp only [simulateQ_pure, pure_bind, PqxdhInitialPendingBuilder.reinstall, selected_map, install_map,
      built_trace_map]
    simpa only [nativeHandler, labelHandler, Prod.map_def, id_eq] using
      (PqxdhInitialOriginPostMap.program source writer prior entry target pre application initial selector aux
        mark sender route decode (outside (.ok none))
        (PqxdhInitialPendingBuilder.install index before (PqxdhInitialPendingBuilder.selected sender index before),
          PqxdhInitialOriginContext.builtTrace trace origin
            (PqxdhInitialPendingBuilder.install index before (PqxdhInitialPendingBuilder.selected sender index before)) index (.ok none)))
  | some encrypted =>
    dsimp only
    simp only [simulateQ_bind, bind_assoc]
    apply bind_congr
    intro serialized
    cases serialized with
    | none =>
      simp only [simulateQ_pure, pure_bind, PqxdhInitialPendingBuilder.reinstall, selected_map, install_map,
        built_trace_map]
      simpa only [nativeHandler, labelHandler, Prod.map_def, id_eq] using
        (PqxdhInitialOriginPostMap.program source writer prior entry target pre application initial selector aux
          mark sender route decode (outside (.ok none))
          (PqxdhInitialPendingBuilder.install index before (PqxdhInitialPendingBuilder.selected sender index before),
            PqxdhInitialOriginContext.builtTrace trace origin
              (PqxdhInitialPendingBuilder.install index before (PqxdhInitialPendingBuilder.selected sender index before)) index (.ok none)))
    | some bytes =>
      simp only [simulateQ_pure, pure_bind, PqxdhInitialPendingBuilder.reinstall, selected_map, publish_map,
        install_map, built_trace_map]
      simpa only [nativeHandler, labelHandler, Prod.map_def, id_eq] using
        (PqxdhInitialOriginPostMap.program source writer prior entry target pre application initial selector aux
          mark sender route decode (outside (.ok (some ⟨bytes, candidate.key_id⟩)))
          (PqxdhInitialPendingBuilder.install index before
              (PqxdhInitialGenericPublication.publish (PqxdhInitialPendingBuilder.selected sender index before) candidate result.1 metadata),
            PqxdhInitialOriginContext.builtTrace trace origin
              (PqxdhInitialPendingBuilder.install index before
                (PqxdhInitialGenericPublication.publish (PqxdhInitialPendingBuilder.selected sender index before) candidate result.1 metadata))
              index (.ok (some ⟨bytes, candidate.key_id⟩))))

/-- An actual record or first-receive cut preserves the complete original post continuation and every origin/publication entry under material-only private interpretation. -/
theorem post_cut (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : PqxdhInitialPostContext.Context extra M P I D K Result S B)
    (trace : Trace Origin S B) (origin : Option Origin) (output : FullOutput) :
    simulateQ (nativeHandler source writer prior (fromOutput (PqxdhInitialPostContext.address context) output)
      (nextChain output) pre application initial selector aux)
      (PqxdhInitialOriginContext.resume mark sender route decode ⟨.inl context, trace, origin⟩
        (PqxdhInitialParentContext.reply sender route decode context output)) =
    Prod.map id (Prod.map (mapFront (nativeKernel (nextChain output))) id) <$> simulateQ
      (labelHandler source writer prior (fromOutput (PqxdhInitialPostContext.address context) output)
        (nextChain output) pre application initial selector aux
        (childResponse prior (fromOutput (PqxdhInitialPostContext.address context) output) (nextChain output)))
      (PqxdhInitialOriginContext.stopped mark sender route decode ⟨.inl context, trace, origin⟩ (material output)) := by
  cases context with
  | finish index before control candidate outside inner =>
    simp only [PqxdhInitialOriginContext.resume, PqxdhInitialOriginContext.stopped, PqxdhInitialParentContext.reply,
      PqxdhInitialPostContext.address, simulateQ_bind, ← QueryImpl.simulateQ_compose,
      PqxdhInitialParentContext.native_primitive, PqxdhInitialParentContext.label_primitive]
    unfold nativePrimitive labelPrimitive
    rw [simulate_lift, simulate_lift, RawCtxSelectedFamilyNativeContext.owner_cut, lift_map]
    simp only [bind_map_left, map_bind]
    apply bind_congr
    intro result
    have finished := PqxdhInitialParentContext.finish_map (nextChain output) index (knownFront before) control candidate result
    rw [known_front] at finished
    rw [finished]
    exact PqxdhInitialOriginPostMap.program source writer prior (fromOutput (ownerAddress inner) output)
      (nextChain output) pre application initial selector aux mark sender route decode
      (outside (finishResult index (knownFront before) control candidate result).1)
      ((finishResult index (knownFront before) control candidate result).2,
        PqxdhInitialOriginContext.finishedTrace trace origin index (finishResult index (knownFront before) control candidate result).1)
  | record request before outside inner =>
    simp only [PqxdhInitialOriginContext.resume, PqxdhInitialOriginContext.stopped, PqxdhInitialParentContext.reply,
      PqxdhInitialPostContext.address, simulateQ_bind, ← QueryImpl.simulateQ_compose,
      native_live, label_live, simulate_lift]
    rw [RawCtxSelectedFamilyNativeContext.frame_cut, lift_map]
    simp only [bind_map_left, map_bind]
    apply bind_congr
    intro result
    exact PqxdhInitialOriginPostMap.program source writer prior (fromOutput (RawCtxSelectedFamilyContext.address inner) output)
      (nextChain output) pre application initial selector aux mark sender route decode (outside result.1)
      ({ knownFront before with roles := result.2 }, record trace request result.1)

set_option backward.isDefEq.respectTransparency false in
/-- The complete source cut, including the first builder, preserves its actual full transcript under the material-only private interpretation. -/
theorem frame_cut (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B) (output : FullOutput) :
    simulateQ (nativeHandler source writer prior (fromOutput (PqxdhInitialBuilderContext.address context.original) output)
      (nextChain output) pre application initial selector aux)
      ((PqxdhInitialOriginContext.frame mark sender route decode context).2
        (PqxdhInitialParentBuilderContext.reply sender route decode context.original output)) =
    Prod.map id (Prod.map (mapFront (nativeKernel (nextChain output))) id) <$> simulateQ
      (labelHandler source writer prior (fromOutput (PqxdhInitialBuilderContext.address context.original) output)
        (nextChain output) pre application initial selector aux
        (childResponse prior (fromOutput (PqxdhInitialBuilderContext.address context.original) output) (nextChain output)))
      (PqxdhInitialOriginContext.stopped mark sender route decode context (material output)) := by
  rcases context with ⟨original, trace, origin⟩
  cases original with
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
    simp only [PqxdhInitialOriginContext.frame, PqxdhInitialOriginContext.resume, reply, PqxdhInitialBuilderContext.address,
      PqxdhInitialOriginContext.stopped, simulateQ_bind, simulateQ_spec_query, nativeHandler, labelHandler,
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
        (PqxdhInitialOriginContext.complete mark sender route decode context.index context.before trace origin context.candidate context.authenticated
          context.metadata context.outside
          ((RawCtxChainSend.ready context.pending
            (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output))).advanced, encrypted))) =
      Prod.map id (Prod.map (mapFront (nativeKernel (nextChain output))) id) <$>
        (PqxdhInitialBeaconAmbient.lift (α := Option RawCtxSourceSend.Encrypted) (N := N) (C := C) labelSeal >>= fun encrypted =>
          simulateQ (labelHandler source writer prior
            (fromOutput (RawCtxSelectedPendingCut.requestAddress context.pending.request) output) (nextChain output)
            pre application initial selector aux
            (childResponse prior (fromOutput (RawCtxSelectedPendingCut.requestAddress context.pending.request) output) (nextChain output)))
            (PqxdhInitialOriginContext.complete mark sender route decode context.index (knownFront context.before) trace origin context.candidate context.authenticated
              context.metadata context.outside ((RawCtxSelectedPendingCut.sendStop context.pending (material output)).advanced, encrypted)))
    rw [sealing]
    simp only [map_bind]
    apply bind_congr
    intro encrypted
    rw [advanced]
    simpa only [known_front, Prod.map_apply, id_eq] using complete_map source writer prior pre application initial selector aux
      (fromOutput (RawCtxSelectedPendingCut.requestAddress context.pending.request) output) (nextChain output)
      mark sender route decode context.index (knownFront context.before) trace origin context.candidate context.authenticated
      context.metadata context.outside ((RawCtxSelectedPendingCut.sendStop context.pending (material output)).advanced, encrypted)
  | inl context =>
    exact post_cut source writer prior pre application initial selector aux
      mark sender route decode context trace origin output


/-- Evaluating the actual complete source cut retains the full transcript and every shared, private and cache field under the same material-only interpretation. -/
theorem frame_run (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B) (output : FullOutput)
    (state : RawCtxSharedPrimitive.SharedState A × N) (cache : C) :
    ((simulateQ (nativeHandler source writer prior (fromOutput (PqxdhInitialBuilderContext.address context.original) output)
      (nextChain output) pre application initial selector aux)
      ((PqxdhInitialOriginContext.frame mark sender route decode context).2
        (PqxdhInitialParentBuilderContext.reply sender route decode context.original output))).run state).run cache =
    (fun result => ((Prod.map id (Prod.map (mapFront (nativeKernel (nextChain output))) id) result.1.1, result.1.2), result.2)) <$>
      ((simulateQ (labelHandler source writer prior (fromOutput (PqxdhInitialBuilderContext.address context.original) output)
        (nextChain output) pre application initial selector aux
        (childResponse prior (fromOutput (PqxdhInitialBuilderContext.address context.original) output) (nextChain output)))
        (PqxdhInitialOriginContext.stopped mark sender route decode context (material output))).run state).run cache := by
  rw [frame_cut]
  rfl

end Services
end BeaconcryptCore.Computational.PqxdhInitialOriginNativeContext

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginNativeContext.complete_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginNativeContext.complete_map

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginNativeContext.post_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginNativeContext.post_cut

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginNativeContext.frame_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginNativeContext.frame_cut

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginNativeContext.frame_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginNativeContext.frame_run
