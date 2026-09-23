import BeaconcryptCore.Computational.PqxdhInitialHalfSourceMap
import BeaconcryptCore.Computational.PqxdhInitialOriginNativeContext

/-!
The first-half interpretation starts before the actual first Server send. It preserves admission, consumed registration, optional publication and the full original post schedule, with matching initializer kernels kept hidden on the ordinary side.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialHalfBuilderMap
open PqxdhInitialPendingPost PqxdhInitialPostContext PqxdhInitialParentPost PqxdhInitialOriginPost
open RawCtxSelectedParentCalls RawCtxSelectedParentEntry RawCtxSelectedFamilyContext
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily PqxdhJointKdfGame PqxdhSecretInputKdf
open PqxdhInitialBeaconAmbient PqxdhInitialParentBuilderContext
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

section Generic
variable {m : Type → Type} [Monad m] [LawfulMonad m]
  (f : KernelOf Chain → KernelOf Other)
  (left : RawCtxChainOwner.Calls (KernelOf Chain) m)
  (right : RawCtxChainOwner.Calls (KernelOf Other) m)
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec m)
  (sendLaw : ∀ kernel context, right.send (f kernel) context = Prod.map f id <$> left.send kernel context)

include sendLaw in
/-- The actual first-send tail preserves every erase and serialization effect under the complete kernel interpretation. -/
theorem after_map (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (kernel : KernelOf Chain) (metadata : P) (before : Publication (KernelOf Chain) M P) :
    PqxdhInitialGenericPublication.afterInitialization right aux candidate authenticated (f kernel) metadata (mapPublication f before) =
      Prod.map id (mapPublication f) <$>
        PqxdhInitialGenericPublication.afterInitialization left aux candidate authenticated kernel metadata before := by
  simp only [PqxdhInitialGenericPublication.afterInitialization, sendLaw, bind_map_left, map_bind]
  apply bind_congr
  rintro ⟨advanced, encrypted⟩
  apply bind_congr
  intro erased
  cases encrypted with
  | none => simp only [map_pure]; rfl
  | some encrypted =>
      simp only [map_bind]
      apply bind_congr
      intro serialized
      cases serialized <;> simp only [map_pure, Prod.map_apply, id_eq, publish_map]

include sendLaw in
/-- Identity, allocation and nonempty application admission precede the same complete mapped first send on every original branch. -/
theorem candidate_map (initial : RustM (KernelOf Chain)) (pending : pqxdh.ServerRegistrationCandidate)
    (data : Option Pqxdh.Bytes) (metadata : P) (before : Publication (KernelOf Chain) M P) :
    PqxdhInitialGenericBuilder.candidate right aux (f <$> initial) pending data metadata (mapPublication f before) =
      Functor.map (Prod.map id (mapPublication f)) <$>
        PqxdhInitialGenericBuilder.candidate left aux initial pending data metadata before := by
  simp only [PqxdhInitialGenericBuilder.candidate, map_bind]
  apply bind_congr
  intro valid
  cases valid
  · simp only [Bool.not_false, if_true, map_pure]; rfl
  · simp only [Bool.not_true, Bool.false_eq_true, if_false, map_bind]
    apply bind_congr
    intro reserved
    cases reserved
    · simp only [Bool.not_false, if_true, map_pure]; rfl
    · simp only [Bool.not_true, Bool.false_eq_true, if_false]
      cases initial with
      | fail error => simp only [PqxdhInitialGenericBuilder.continueRust, map_pure]; rfl
      | div => simp only [PqxdhInitialGenericBuilder.continueRust, map_pure]; rfl
      | ok kernel =>
          simp only [RawCtxMaterialInterpretation.rust_map_ok, PqxdhInitialGenericBuilder.continueRust]
          split
          · simp only [map_pure]; rfl
          · split
            · simp only [map_bind]
              apply bind_congr
              intro allocated
              cases allocated
              · simp only [Bool.not_false, if_true, map_pure]; rfl
              · simp only [Bool.not_true, Bool.false_eq_true, if_false]
                cases binding : pending.key_id_binding with
                | fail error => simp only [map_pure]; rfl
                | div => simp only [map_pure]; rfl
                | ok binding =>
                    simp only [after_map f left right aux sendLaw, Functor.map_map]
                    rfl
            · simp only [map_pure]; rfl

include sendLaw in
/-- Current peer allocation and the consumed-registration Ready fields commute with the complete kernel map. -/
theorem ready_map (source : FixedHkdfSha512NoSaltSource) (initial : RustM (KernelOf Chain))
    (binding : pqxdh.ServerBinding) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (metadata : P) (before : Publication (KernelOf Chain) M P) :
    PqxdhInitialGenericBuilder.readyBuild source right aux (f <$> initial) binding ready metadata (mapPublication f before) =
      Functor.map (Prod.map id (mapPublication f)) <$>
        PqxdhInitialGenericBuilder.readyBuild source left aux initial binding ready metadata before := by
  unfold PqxdhInitialGenericBuilder.readyBuild PqxdhInitialGenericBuilder.usedBuild
  simp only [mapPublication, mapServer, Option.isSome_map]
  cases next : pqxdh.server_next_key_id before.control with
  | fail error => simp only [PqxdhInitialGenericBuilder.continueRust, map_pure]; rfl
  | div => simp only [PqxdhInitialGenericBuilder.continueRust, map_pure]; rfl
  | ok result =>
      cases result with
      | Err error => simp only [PqxdhInitialGenericBuilder.continueRust, map_pure]; rfl
      | Ok key =>
          simp only [PqxdhInitialGenericBuilder.continueRust]
          cases preparation : PqxdhRegistrationInputs.prepare before.control
            (PqxdhAcceptedRegistration.usedReady source.crypto binding ready)
            ⟨before.server.identity, before.identityKeyId⟩
            (if (before.server.peers key).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) with
          | fail error => simp only [map_pure]; rfl
          | div => simp only [map_pure]; rfl
          | ok result =>
              cases result with
              | Err error => simp only [map_pure]; rfl
              | Ok candidate => exact candidate_map f left right aux sendLaw initial candidate ready.application metadata before

end Generic
section Source
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (prior : RawCtxSelectedParentTable.Prior) (entry : Entry) (target : RootOutput)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C (Option (KernelOf RawCtxSelectedChain.Slot)))
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))

private theorem native_calls :
    RawCtxGenericOwnerInterpretation.interpretedCalls
      (PqxdhInitialHalfSourceMap.nativeHandler (S := S) (B := B) source writer prior entry target pre application initial selector aux)
      PqxdhInitialPendingPost.calls = liftCalls (nativeCalls source writer prior entry target) := by
  have forwarding : PqxdhInitialHalfSourceMap.nativeHandler (S := S) (B := B) source writer prior entry target pre application initial selector aux ∘ₛ
      primitiveForward = nativePrimitive source writer prior entry target := by
    funext query
    simp [QueryImpl.compose, primitiveForward, PqxdhInitialHalfSourceMap.nativeHandler, handler, OracleSpec.query,
      RawCtxPendingFamilyLiveQueries.handler]
  simp only [PqxdhInitialPendingPost.calls, RawCtxGenericOwnerInterpretation.interpretedCalls,
    ← QueryImpl.simulateQ_compose, forwarding]
  unfold nativePrimitive
  simp only [simulate_lift, liftCalls,
    RawCtxSelectedParentNativeCompiler.receive_call, RawCtxSelectedParentNativeCompiler.send_call]

private theorem label_calls (response : RatchetKdfResponse) :
    RawCtxGenericOwnerInterpretation.interpretedCalls
      (PqxdhInitialHalfSourceMap.labelHandler (S := S) (B := B) source writer prior entry target pre application initial selector aux response)
      PqxdhInitialPendingPost.calls = liftCalls (labelCalls source writer prior entry response) := by
  have forwarding : PqxdhInitialHalfSourceMap.labelHandler (S := S) (B := B) source writer prior entry target pre application initial selector aux response ∘ₛ
      primitiveForward = labelPrimitive source writer prior entry response := by
    funext query
    simp [QueryImpl.compose, primitiveForward, PqxdhInitialHalfSourceMap.labelHandler, handler, OracleSpec.query,
      RawCtxPendingFamilyLiveQueries.handler]
  simp only [PqxdhInitialPendingPost.calls, RawCtxGenericOwnerInterpretation.interpretedCalls,
    ← QueryImpl.simulateQ_compose, forwarding]
  unfold labelPrimitive
  simp only [simulate_lift, liftCalls]
  exact congrArg (fun calls => liftCalls (N := N) (C := C) calls)
    (RawCtxSelectedParentFamilyMap.label_calls (A := A) source writer prior entry response)

/-- The first-half representation preserves the original consumed-registration builder from its admission checks through its first send and complete publication. -/
theorem build (first : RustM (KernelOf RawCtxSelectedChain.Slot))
    (sender : M → Std.U64) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (before : LabelFront M P I D K S B) :
    simulateQ (PqxdhInitialHalfSourceMap.nativeHandler source writer prior entry target pre application initial selector aux)
      ((PqxdhInitialPendingBuilder.build source (nativeKernel target <$> first) sender index metadata ready).run
        (mapFront (nativeKernel target) before)) =
      Prod.map id (mapFront (nativeKernel target)) <$> simulateQ
        (PqxdhInitialHalfSourceMap.labelHandler source writer prior entry target pre application initial selector aux
          (childResponse prior entry target))
        ((PqxdhInitialPendingBuilder.build source first sender index metadata ready).run before) := by
  rw [PqxdhInitialPendingBuilder.build_interpretation, PqxdhInitialPendingBuilder.build_interpretation]
  simp only [PqxdhInitialPendingBuilder.interpretedBuild, StateT.run, native_calls, label_calls]
  have nativeAux : PqxdhInitialHalfSourceMap.nativeHandler (S := S) (B := B) source writer prior entry target pre application initial selector aux ∘ₛ auxForward = aux := by
    funext query
    simp [QueryImpl.compose, auxForward, PqxdhInitialHalfSourceMap.nativeHandler, handler, OracleSpec.query]
  have labelAux : PqxdhInitialHalfSourceMap.labelHandler (S := S) (B := B) source writer prior entry target pre application initial selector aux
      (childResponse prior entry target) ∘ₛ auxForward = aux := by
    funext query
    simp [QueryImpl.compose, auxForward, PqxdhInitialHalfSourceMap.labelHandler, handler, OracleSpec.query]
  rw [nativeAux, labelAux]
  have sent : ∀ kernel context,
      (liftCalls (N := N) (C := C) (nativeCalls (Auxiliary := A) source writer prior entry target)).send
        (nativeKernel target kernel) context =
      Prod.map (nativeKernel target) id <$>
        (liftCalls (labelCalls source writer prior entry (childResponse prior entry target))).send kernel context := by
    intro kernel context
    simp only [liftCalls, send_map, lift_map]
  change PqxdhInitialPendingBuilder.reinstall index
      (mapFront (nativeKernel target) (PqxdhInitialPendingBuilder.consume index ready before)) <$>
    PqxdhInitialGenericBuilder.readyBuild source (liftCalls (nativeCalls source writer prior entry target)) aux
      (nativeKernel target <$> first) _ ready metadata
      (mapPublication (nativeKernel target) (PqxdhInitialPendingBuilder.selected sender index (PqxdhInitialPendingBuilder.consume index ready before))) = _
  rw [ready_map (nativeKernel target) _ _ aux sent]
  simp only [Functor.map_map]
  apply congrArg (fun function => function <$> _)
  funext result
  cases result with
  | fail error => rfl
  | div => rfl
  | ok result =>
      simp only [RawCtxMaterialInterpretation.rust_map_ok, Prod.map_def, id_eq,
        PqxdhInitialPendingBuilder.reinstall, install_map]

set_option backward.isDefEq.respectTransparency false in
/-- The exact original first builder and full adaptive post preserve all origins, successful publications and retained effects from before the first Server ciphertext. -/
theorem sequence (first : RustM (KernelOf RawCtxSelectedChain.Slot))
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PostSpec extra S B) Result)
    (before : LabelFront M P I D K S B × Trace Origin S B) :
    simulateQ (PqxdhInitialHalfSourceMap.nativeHandler source writer prior entry target pre application initial selector aux)
      ((PqxdhInitialOriginPost.sequence source (nativeKernel target <$> first) mark origin sender route decode index metadata ready post).run
        (mapFront (nativeKernel target) before.1, before.2)) =
      Prod.map id (Prod.map (mapFront (nativeKernel target)) id) <$> simulateQ
        (PqxdhInitialHalfSourceMap.labelHandler source writer prior entry target pre application initial selector aux
          (childResponse prior entry target))
        ((PqxdhInitialOriginPost.sequence source first mark origin sender route decode index metadata ready post).run before) := by
  change simulateQ (PqxdhInitialHalfSourceMap.nativeHandler source writer prior entry target pre application initial selector aux) (do
    let built ← (PqxdhInitialPendingBuilder.build source (nativeKernel target <$> first) sender index metadata ready).run
      (mapFront (nativeKernel target) before.1)
    (simulateQ (PqxdhInitialOriginPost.compiler mark sender route decode) (post built.1)).run
      (built.2, afterBuilder before.2 built.2 index origin built.1)) =
    Prod.map id (Prod.map (mapFront (nativeKernel target)) id) <$>
      simulateQ (PqxdhInitialHalfSourceMap.labelHandler source writer prior entry target pre application initial selector aux
        (childResponse prior entry target)) (do
        let built ← (PqxdhInitialPendingBuilder.build source first sender index metadata ready).run before.1
        (simulateQ (PqxdhInitialOriginPost.compiler mark sender route decode) (post built.1)).run
          (built.2, afterBuilder before.2 built.2 index origin built.1))
  simp only [simulateQ_bind, map_bind]
  rw [build]
  simp only [bind_map_left]
  apply bind_congr
  intro built
  simp only [Prod.map_def, id_eq, PqxdhInitialOriginPostMap.builder_trace]
  exact PqxdhInitialHalfSourceMap.program source writer prior entry target pre application initial selector aux
    mark sender route decode (post built.1)
    (built.2, PqxdhInitialOriginPost.afterBuilder before.2 built.2 index origin built.1)

end Source
end BeaconcryptCore.Computational.PqxdhInitialHalfBuilderMap

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfBuilderMap.after_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfBuilderMap.after_map

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfBuilderMap.candidate_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfBuilderMap.candidate_map

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfBuilderMap.ready_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfBuilderMap.ready_map

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfBuilderMap.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfBuilderMap.build

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfBuilderMap.sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfBuilderMap.sequence
