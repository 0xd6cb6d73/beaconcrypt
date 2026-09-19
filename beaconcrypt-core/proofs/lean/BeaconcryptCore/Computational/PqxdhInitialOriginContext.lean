import BeaconcryptCore.Computational.PqxdhInitialOriginPostMap
import BeaconcryptCore.Computational.PqxdhInitialParentBuilderContext

/-!
The saved source cut carries its original full descriptor, the complete installation/publication trace and the initializer or builder origin already computed before the selected draw. Its actual and material-only completions update that trace before resuming the same original outside client. The marker is proof-free runtime data; no saved continuation is inverted to recover it.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialOriginContext
open PqxdhInitialPendingPost PqxdhInitialPostContext PqxdhInitialOriginPost
open RawCtxSelectedFamilyContext
variable {ι Chain M P I D K X Response Shared Result Origin : Type} {extra : OracleSpec ι} {S B : Nat}

structure Context (extra : OracleSpec ι) (M P I D K Result Origin : Type) (S B : Nat) where
  original : PqxdhInitialBuilderContext.Context extra M P I D K Result S B
  trace : Trace Origin S B
  origin : Option Origin

def finishedTrace (trace : Trace Origin S B) (origin : Option Origin) (index : Fin B) (reply : Option Pqxdh.Bytes) :=
  PqxdhInitialOriginPost.finish trace index (if reply.isSome then origin else none)

def builtTrace (trace : Trace Origin S B) (origin : Option Origin)
    (front : Front Chain M P I D K S B) (index : Fin S)
    (reply : RustM (Option PqxdhServerRegistrationPublication.Response)) :=
  match origin with | none => trace | some origin => afterBuilder trace front index origin reply

noncomputable def complete (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (before : Front Chain M P I D K S B) (trace : Trace Origin S B) (origin : Option Origin)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (outside : PqxdhInitialBuilderContext.BuildResult → OracleComp (PostSpec extra S B) Result)
    (result : KernelOf Chain × Option RawCtxSourceSend.Encrypted) :
    OracleComp (Base extra Chain I D K X Response Shared S B) (Result × (Front Chain M P I D K S B × Trace Origin S B)) := do
  let published ← PqxdhInitialBuilderContext.afterSend auxForward candidate authenticated metadata
    (PqxdhInitialPendingBuilder.selected sender index before) result
  let installed := PqxdhInitialPendingBuilder.reinstall index before (.ok published)
  (simulateQ (PqxdhInitialOriginPost.compiler mark sender route decode) (outside installed.1)).run
    (installed.2, builtTrace trace origin installed.2 index installed.1)

/-- The initial send completion retains the original erase, serialization, optional publication and full outside post client when only its transcript is erased. -/
theorem complete_erase (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (before : Front Chain M P I D K S B) (trace : Trace Origin S B) (origin : Option Origin)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (outside : PqxdhInitialBuilderContext.BuildResult → OracleComp (PostSpec extra S B) Result)
    (result : KernelOf Chain × Option RawCtxSourceSend.Encrypted) :
    Prod.map id Prod.fst <$> complete (X := X) (Response := Response) mark sender route decode index before trace origin
      candidate authenticated metadata outside result =
      PqxdhInitialBuilderContext.complete sender route decode index before candidate authenticated metadata outside result := by
  simp only [complete, PqxdhInitialBuilderContext.complete, map_bind]
  apply bind_congr
  intro published
  exact PqxdhInitialOriginPost.program_erase mark sender route decode _ _

noncomputable def resume (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context extra M P I D K Result Origin S B) :
    (Base extra RatchetChain I D K X Response Shared S B).Range
      (PqxdhInitialBuilderContext.frame sender route decode context.original).1 →
    OracleComp (Base extra RatchetChain I D K X Response Shared S B)
      (Result × (NativeFront M P I D K S B × Trace Origin S B)) :=
  match context.original with
  | .inl (.record request before outside inner) => fun reply => do
      let result ← simulateQ liveForward ((RawCtxSelectedFamilyContext.frame sender route decode inner).2 reply)
      (simulateQ (PqxdhInitialOriginPost.compiler mark sender route decode) (outside result.1)).run
        ({ before with roles := result.2 }, record context.trace request result.1)
  | .inl (.finish index before control candidate outside inner) => fun reply => do
      let result ← simulateQ primitiveForward ((ownerFrame candidate.server_binding.identity_key_id decode inner).2 reply)
      let finished := finishResult index before control candidate result
      (simulateQ (PqxdhInitialOriginPost.compiler mark sender route decode) (outside finished.1)).run
        (finished.2, finishedTrace context.trace context.origin index finished.1)
  | .inr builder => fun reply => do
      let ready := RawCtxChainSend.ready builder.pending reply
      let sealed ← (Base extra RatchetChain I D K X Response Shared S B).query (.inl (.inl (.inr (.inl (.inr ready)))))
      complete mark sender route decode builder.index builder.before context.trace context.origin builder.candidate
        builder.authenticated builder.metadata builder.outside (ready.advanced, sealed)

noncomputable def frame (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context extra M P I D K Result Origin S B) :
    RawCtxForwardAnnotation.Frame (Base extra RatchetChain I D K X Response Shared S B)
      (Result × (NativeFront M P I D K S B × Trace Origin S B)) :=
  ⟨(PqxdhInitialBuilderContext.frame sender route decode context.original).1, resume mark sender route decode context⟩

noncomputable def stopped (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context extra M P I D K Result Origin S B) (material : PqxdhOrderedChainHybrids.Material) :
    OracleComp (Base extra RawCtxSelectedChain.Slot I D K X Response Shared S B)
      (Result × (LabelFront M P I D K S B × Trace Origin S B)) :=
  match context.original with
  | .inl (.record request before outside inner) => do
      let result ← simulateQ liveForward (RawCtxSelectedFamilyContext.stopped sender route decode inner material)
      (simulateQ (PqxdhInitialOriginPost.compiler mark sender route decode) (outside result.1)).run
        ({ knownFront before with roles := result.2 }, record context.trace request result.1)
  | .inl (.finish index before control candidate outside inner) => do
      let result ← simulateQ primitiveForward (ownerStopped candidate.server_binding.identity_key_id decode inner material)
      let finished := finishResult index (knownFront before) control candidate result
      (simulateQ (PqxdhInitialOriginPost.compiler mark sender route decode) (outside finished.1)).run
        (finished.2, finishedTrace context.trace context.origin index finished.1)
  | .inr builder => do
      let ready := RawCtxSelectedPendingCut.sendStop builder.pending material
      let sealed ← (Base extra RawCtxSelectedChain.Slot I D K X Response Shared S B).query (.inl (.inl (.inr (.inl (.inr ready)))))
      complete mark sender route decode builder.index (knownFront builder.before) context.trace context.origin builder.candidate
        builder.authenticated builder.metadata builder.outside (ready.advanced, sealed)

/-- Removing only private transcript fields recovers the exact full original continuation at the same typed pending reply. -/
theorem resume_erase (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context extra M P I D K Result Origin S B)
    (reply : (Base extra RatchetChain I D K X Response Shared S B).Range
      (PqxdhInitialBuilderContext.frame sender route decode context.original).1) :
    Prod.map id Prod.fst <$> resume mark sender route decode context reply =
      (PqxdhInitialBuilderContext.frame sender route decode context.original).2 reply := by
  rcases context with ⟨original, trace, origin⟩
  cases original with
  | inl original =>
    cases original with
    | record request before outside inner =>
      simp only [resume, PqxdhInitialBuilderContext.frame, PqxdhInitialPostContext.frame, map_bind]
      apply bind_congr
      intro result
      exact PqxdhInitialOriginPost.program_erase mark sender route decode _ _
    | finish index before control candidate outside inner =>
      simp only [resume, PqxdhInitialBuilderContext.frame, PqxdhInitialPostContext.frame, map_bind]
      apply bind_congr
      intro result
      exact PqxdhInitialOriginPost.program_erase mark sender route decode _ _
  | inr builder =>
    simp only [resume, PqxdhInitialBuilderContext.frame, PqxdhInitialBuilderContext.builderFrame, map_bind]
    apply bind_congr
    intro encrypted
    exact complete_erase mark sender route decode _ _ _ _ _ _ _ _ _

/-- The material-only completion retains the same original stopped source program when the private trace is erased. -/
theorem stopped_erase (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context extra M P I D K Result Origin S B) (material : PqxdhOrderedChainHybrids.Material) :
    Prod.map id Prod.fst <$> stopped (X := X) (Response := Response) mark sender route decode context material =
      PqxdhInitialBuilderContext.stopped sender route decode context.original material := by
  rcases context with ⟨original, trace, origin⟩
  cases original with
  | inl original =>
    cases original with
    | record request before outside inner =>
      simp only [stopped, PqxdhInitialBuilderContext.stopped, PqxdhInitialPostContext.stopped, map_bind]
      apply bind_congr
      intro result
      exact PqxdhInitialOriginPost.program_erase mark sender route decode _ _
    | finish index before control candidate outside inner =>
      simp only [stopped, PqxdhInitialBuilderContext.stopped, PqxdhInitialPostContext.stopped, map_bind]
      apply bind_congr
      intro result
      exact PqxdhInitialOriginPost.program_erase mark sender route decode _ _
  | inr builder =>
    simp only [stopped, PqxdhInitialBuilderContext.stopped, map_bind]
    apply bind_congr
    intro encrypted
    exact complete_erase mark sender route decode _ _ _ _ _ _ _ _ _

/-- The carried origin metadata leaves the actual selected pending input unchanged. -/
theorem frame_address (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context extra M P I D K Result Origin S B) :
    PqxdhInitialPostContext.queryAddress (extra := extra)
      (frame (X := X) (Response := Response) mark sender route decode context).1 =
      some (PqxdhInitialBuilderContext.address context.original) :=
  PqxdhInitialBuilderContext.frame_address sender route decode context.original

/-- Every all-reply pending-callback budget survives the exact source trace instrumentation of the stopped continuation. -/
theorem stopped_query_bound (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context extra M P I D K Result Origin S B) (material : PqxdhOrderedChainHybrids.Material)
    (predicate : (Base extra RawCtxSelectedChain.Slot I D K X Response Shared S B).Domain → Prop)
    [DecidablePred predicate] (budget : Nat) :
    (stopped mark sender route decode context material).IsQueryBoundP predicate budget ↔
      (PqxdhInitialBuilderContext.stopped sender route decode context.original material).IsQueryBoundP predicate budget := by
  rw [← stopped_erase mark sender route decode context material]
  exact (isQueryBoundP_map_iff _ _ _).symm

end BeaconcryptCore.Computational.PqxdhInitialOriginContext

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginContext.complete_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginContext.complete_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginContext.resume_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginContext.resume_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginContext.stopped_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginContext.stopped_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginContext.frame_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginContext.frame_address

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginContext.stopped_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginContext.stopped_query_bound
