import BeaconcryptCore.Computational.PqxdhInitialOriginPostMap
import BeaconcryptCore.Computational.PqxdhInitialHalfInitializer

/-!
The first-half representation interprets original hidden/known initializer replies only at the source boundary. Complete post operations preserve all role fields, original optional replies, reveal history, installation origins and successful-publication records. The selected initializer remains hidden on the ordinary side before every matching first receive.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialHalfSourceMap
open PqxdhInitialPendingPost PqxdhInitialOriginPost PqxdhInitialParentPost PqxdhInitialPostContext RawCtxSelectedParentCalls
open RawCtxSelectedFamilyContext RawCtxGenericRoleStorage RawCtxGenericRoleFamily
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhInitialBeaconAmbient
open PqxdhInitialOriginPostMap (step_interpretation interpreted)
variable {ι M P I D K X Response Shared Result Origin A N C : Type} {extra : OracleSpec ι} {S B : Nat}

noncomputable def nativeInitial (target : RootOutput)
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C (Option (KernelOf RawCtxSelectedChain.Slot)))
    (secrets : PqxdhBeaconPhase2Shared.Secrets Shared) : Ambient A N C (Option (KernelOf RatchetChain)) :=
  Option.map (nativeKernel target) <$> initial secrets

/-- The actual audited first-half service supplies the source initializer equation, retaining the complete optional kernel and cache without a callback-compatibility premise. -/
theorem concrete_initial (source : FixedHkdfSha512NoSaltSource)
    (selected : PqxdhCorrelatedExtractFamily.Message) (previousRoot : RootOutput)
    (second : Bool) (other target : RootOutput) :
    nativeInitial (A := A) (N := N) target
      (fun secrets => Prod.snd <$> PqxdhInitialHalfInitializer.initial source selected previousRoot second other secrets) =
    (fun secrets => Prod.snd <$> PqxdhInitialNativeInitializer.initial source selected previousRoot
      (RawCtxSelectedInitialConstructor.response64 (RawCtxInitialSentinelSampler.join second other target)) secrets) := by
  funext secrets
  rw [← PqxdhInitialHalfInitializer.initial_native source selected previousRoot second other target secrets]
  simp only [nativeInitial, Functor.map_map]
  rfl

section Services
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry) (target : RootOutput)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C (Option (KernelOf RawCtxSelectedChain.Slot)))
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))

noncomputable def nativeHandler : QueryImpl (Base extra RatchetChain I D K X Response Shared S B) (Ambient A N C) :=
  handler (nativePrimitive source writer prior entry target) nativeReader pre application (nativeInitial target initial) selector aux

noncomputable def labelHandler (response : RatchetKdfResponse) :
    QueryImpl (Base extra RawCtxSelectedChain.Slot I D K X Response Shared S B) (Ambient A N C) :=
  handler (labelPrimitive source writer prior entry response) (labelReader target) pre application initial selector aux

private theorem native_live : nativeHandler source writer prior entry target pre application initial selector aux ∘ₛ
      liveForward (S := S) (B := B) =
    (fun query => PqxdhInitialBeaconAmbient.lift (RawCtxSelectedParentFamilyMap.nativeLive source writer prior entry target query)) := by
  funext query
  cases query <;> simp [QueryImpl.compose, liveForward, nativeHandler, handler, OracleSpec.query,
    RawCtxPendingFamilyLiveQueries.handler, RawCtxSelectedParentFamilyMap.nativeLive, nativePrimitive, nativeReader]

private theorem label_live : labelHandler source writer prior entry target pre application initial selector aux
      (childResponse prior entry target) ∘ₛ liveForward (S := S) (B := B) =
    (fun query => PqxdhInitialBeaconAmbient.lift (RawCtxSelectedParentFamilyMap.labelLive source writer prior entry target query)) := by
  funext query
  cases query <;> simp [QueryImpl.compose, liveForward, labelHandler, handler, OracleSpec.query,
    RawCtxPendingFamilyLiveQueries.handler, RawCtxSelectedParentFamilyMap.labelLive, labelPrimitive, labelReader]

private theorem native_calls :
    RawCtxGenericOwnerInterpretation.interpretedCalls (nativePrimitive (A := A) (N := N) (C := C) source writer prior entry target)
      RawCtxPendingOwnerQueries.calls = liftCalls (nativeCalls source writer prior entry target) := by
  unfold nativePrimitive
  simp only [RawCtxGenericOwnerInterpretation.interpretedCalls, simulate_lift, liftCalls,
    RawCtxSelectedParentNativeCompiler.receive_call, RawCtxSelectedParentNativeCompiler.send_call]

private theorem label_calls (response : RatchetKdfResponse) :
    RawCtxGenericOwnerInterpretation.interpretedCalls (labelPrimitive (A := A) (N := N) (C := C) source writer prior entry response)
      RawCtxPendingOwnerQueries.calls = liftCalls (labelCalls source writer prior entry response) := by
  unfold labelPrimitive
  simp only [RawCtxGenericOwnerInterpretation.interpretedCalls, simulate_lift, liftCalls]
  exact congrArg (fun calls => liftCalls (N := N) (C := C) calls)
    (RawCtxSelectedParentFamilyMap.label_calls (A := A) source writer prior entry response)

/-- Every actual first-half post operation preserves the same installation origins and published records while interpreting only private chain slots. -/
theorem step (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (PostSpec extra S B).Domain) (before : LabelFront M P I D K S B × Trace Origin S B) :
    simulateQ (nativeHandler source writer prior entry target pre application initial selector aux)
      ((PqxdhInitialOriginPost.compiler mark sender route decode query).run
        (mapFront (nativeKernel target) before.1, before.2)) =
    Prod.map id (Prod.map (mapFront (nativeKernel target)) id) <$> simulateQ
      (labelHandler source writer prior entry target pre application initial selector aux (childResponse prior entry target))
      ((PqxdhInitialOriginPost.compiler mark sender route decode query).run before) := by
  rcases query with (query | query) | query
  case inr =>
    cases query with
    | finish index raw =>
      unfold nativeHandler labelHandler
      rw [PqxdhInitialOriginPostMap.step_interpretation, PqxdhInitialOriginPostMap.step_interpretation]
      simp only [PqxdhInitialOriginPostMap.interpreted, StateT.run, native_calls, label_calls, mapFront,
        RawCtxGenericFamilyLive.mapState, mapRoles, bind_pure_comp]
      have receiveLaw : ∀ kernel sequence context,
          (liftCalls (N := N) (C := C) (nativeCalls (Auxiliary := A) source writer prior entry target)).receive
            (nativeKernel target kernel) sequence context =
          Prod.map (nativeKernel target) id <$>
            (liftCalls (labelCalls source writer prior entry (childResponse prior entry target))).receive kernel sequence context := by
        intro kernel sequence context
        simp only [liftCalls, receive_map, lift_map]
      have initialLaw : ∀ secrets, nativeInitial target initial secrets =
          Option.map (nativeKernel target) <$> initial secrets := fun _ => rfl
      rw [PqxdhInitialFinishOrigin.owner_map (nativeKernel target) mark pre
        (liftCalls (labelCalls source writer prior entry (childResponse prior entry target)))
        (liftCalls (nativeCalls source writer prior entry target)) receiveLaw application
        initial (nativeInitial target initial) initialLaw]
      simp only [Functor.map_map]
      apply congrArg (fun f => f <$> _)
      funext result
      exact congrArg (fun front => (result.1.1, (front, finish before.2 index result.2)))
        (install_map (nativeKernel target) index before.1 result.1.2)
  case inl.inl =>
    have live := RawCtxSelectedParentFamilyMap.live_program (A := A) source writer prior entry target
      sender route decode ((RawCtxProtocolReveals.SourceSpec S B).query query : OracleComp (RawCtxProtocolReveals.SourceSpec S B) _) before.1.roles
    simp only [RawCtxPendingFamilyLiveTails.program, simulateQ_spec_query, StateT.run] at live
    simp only [PqxdhInitialOriginPost.compiler, StateT.run, bind_pure_comp, simulateQ_map,
      ← QueryImpl.simulateQ_compose, native_live, label_live, simulate_lift, mapFront]
    rw [live, lift_map]
    simp only [Functor.map_map]
    rfl
  case inl.inr =>
    simp [PqxdhInitialOriginPost.compiler, StateT.run, selectorForward, OracleSpec.query,
      nativeHandler, labelHandler, handler, Functor.map_map, Prod.map_apply]
    cases before
    rfl

/-- The same origin and publication transcript survives the complete original adaptive post continuation under the actual first-half source interpretation. -/
theorem program (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (PostSpec extra S B) Result) (before : LabelFront M P I D K S B × Trace Origin S B) :
    simulateQ (nativeHandler source writer prior entry target pre application initial selector aux)
      ((simulateQ (PqxdhInitialOriginPost.compiler mark sender route decode) client).run
        (mapFront (nativeKernel target) before.1, before.2)) =
    Prod.map id (Prod.map (mapFront (nativeKernel target)) id) <$> simulateQ
      (labelHandler source writer prior entry target pre application initial selector aux (childResponse prior entry target))
      ((simulateQ (PqxdhInitialOriginPost.compiler mark sender route decode) client).run before) := by
  induction client using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]; rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [step]
    simp only [bind_map_left, map_bind]
    exact bind_congr fun result => ih result.1 result.2

end Services
end BeaconcryptCore.Computational.PqxdhInitialHalfSourceMap

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfSourceMap.concrete_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfSourceMap.concrete_initial

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfSourceMap.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfSourceMap.step

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfSourceMap.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfSourceMap.program
