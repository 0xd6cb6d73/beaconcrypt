import BeaconcryptCore.Computational.PqxdhInitialOriginPost
import BeaconcryptCore.Computational.PqxdhInitialParentPost

/-!
The complete installation-origin and publication transcript is preserved by the actual retained-parent native-to-label interpretation. Callback interpretation precedes this representation proof, so the private trace updates remain part of the executed source program rather than a supplied equality of final events.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialOriginPostMap
open PqxdhInitialPendingPost PqxdhInitialOriginPost
variable {ι Chain M P I D K X Response Shared Result Origin : Type} {extra : OracleSpec ι} {S B : Nat}

section Interpretation
variable {m : Type → Type} [Monad m] [LawfulMonad m]

noncomputable def interpreted
    (primitive : QueryImpl (RawCtxPendingOwnerQueries.Spec Chain) m)
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec (KernelOf Chain) S B) m)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) m)
    (application : Response → m (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → m (Option (KernelOf Chain)))
    (selector : QueryImpl extra m) (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (PqxdhInitialGenericPost.Spec extra S B) (StateT (Front Chain M P I D K S B × Trace Origin S B) m)
  | .inl (.inl query) => fun before => do
      let result ← (RawCtxGenericFamilyLive.impl
        (RawCtxGenericOwnerInterpretation.interpretedCalls primitive RawCtxPendingOwnerQueries.calls)
        (fun request => simulateQ primitive (RawCtxPendingOwnerQueries.publicForward request)) reader
        sender route decode query).run before.1.roles
      pure (result.1, ({ before.1 with roles := result.2 }, record before.2 query result.1))
  | .inl (.inr query) => fun before => do
      let reply ← selector query
      pure (reply, before)
  | .inr (.finish index raw) => fun before => do
      let result ← PqxdhInitialFinishOrigin.owner mark pre
        (RawCtxGenericOwnerInterpretation.interpretedCalls primitive RawCtxPendingOwnerQueries.calls)
        application initial decode raw (before.1.roles.1.2 index)
      pure (result.1.1, (install index before.1 result.1.2, finish before.2 index result.2))

variable
    (primitive : QueryImpl (RawCtxPendingOwnerQueries.Spec Chain) m)
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec (KernelOf Chain) S B) m)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) m)
    (application : Response → m (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → m (Option (KernelOf Chain)))
    (selector : QueryImpl extra m) (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec m)

private theorem calls_handler :
    RawCtxGenericOwnerInterpretation.interpretedCalls
      (handler primitive reader pre application initial selector aux) calls =
      RawCtxGenericOwnerInterpretation.interpretedCalls primitive RawCtxPendingOwnerQueries.calls := by
  have forwarding : handler primitive reader pre application initial selector aux ∘ₛ primitiveForward = primitive := by
    funext query
    simp [QueryImpl.compose, primitiveForward, handler, OracleSpec.query, RawCtxPendingFamilyLiveQueries.handler]
  simp only [calls, RawCtxGenericOwnerInterpretation.interpretedCalls, ← QueryImpl.simulateQ_compose, forwarding]

/-- The original full post callback compiler retains its exact origin and publication updates under the same actual primitive and initializer interpreter. -/
theorem step_interpretation (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (PqxdhInitialGenericPost.Spec extra S B).Domain)
    (before : Front Chain M P I D K S B × Trace Origin S B) :
    simulateQ (handler primitive reader pre application initial selector aux)
      ((PqxdhInitialOriginPost.compiler mark sender route decode query).run before) =
      (interpreted primitive reader pre application initial selector mark sender route decode query).run before := by
  rcases query with (query | query) | query
  · simp only [PqxdhInitialOriginPost.compiler, interpreted, StateT.run, bind_pure_comp, simulateQ_map,
      ← QueryImpl.simulateQ_compose]
    have forwarding : handler primitive reader pre application initial selector aux ∘ₛ liveForward =
        RawCtxPendingFamilyLiveQueries.handler primitive reader := by
      funext request
      simp [QueryImpl.compose, liveForward, handler, OracleSpec.query]
    rw [forwarding]
    exact congrArg (fun work => (fun result => (result.1, ({ before.1 with roles := result.2 }, record before.2 query result.1))) <$> work)
      (RawCtxPendingFamilyLiveQueries.step_interpretation primitive reader sender route decode query before.1.roles)
  · simp [PqxdhInitialOriginPost.compiler, interpreted, StateT.run, bind_pure_comp, simulateQ_map,
      selectorForward, handler, OracleSpec.query]
  · cases query with
    | finish index raw =>
      simp only [PqxdhInitialOriginPost.compiler, interpreted, StateT.run, bind_pure_comp, simulateQ_map,
        PqxdhInitialOriginPost.owner_interpretation, calls_handler]
      have forwarding : handler primitive reader pre application initial selector aux ∘ₛ preForward = pre := by
        funext request
        simp [QueryImpl.compose, preForward, handler, OracleSpec.query]
      rw [forwarding]
      simp [applicationForward, initialForward, handler, OracleSpec.query]

end Interpretation

open PqxdhInitialParentPost PqxdhInitialPostContext RawCtxSelectedParentCalls
open RawCtxSelectedFamilyContext RawCtxGenericRoleStorage RawCtxGenericRoleFamily
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhInitialBeaconAmbient
variable {A N C : Type}
section Retained
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry) (target : RootOutput)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C (Option (KernelOf RatchetChain)))
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))

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

/-- Every actual retained-parent post operation preserves the same installation origins and published records while interpreting only private chain slots. -/
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
      rw [step_interpretation, step_interpretation]
      simp only [interpreted, StateT.run, native_calls, label_calls, mapFront,
        RawCtxGenericFamilyLive.mapState, mapRoles, bind_pure_comp]
      have receiveLaw : ∀ kernel sequence context,
          (liftCalls (N := N) (C := C) (nativeCalls (Auxiliary := A) source writer prior entry target)).receive
            (nativeKernel target kernel) sequence context =
          Prod.map (nativeKernel target) id <$>
            (liftCalls (labelCalls source writer prior entry (childResponse prior entry target))).receive kernel sequence context := by
        intro kernel sequence context
        simp only [liftCalls, receive_map, lift_map]
      have initialLaw : ∀ secrets, initial secrets = Option.map (nativeKernel target) <$> knownInitial initial secrets := by
        intro secrets
        simp [knownInitial, Functor.map_map, Option.map_map, Function.comp_def,
          nativeKernel, knownKernel, RawCtxChainInterpretation.mapChains, RawCtxSelectedChain.interpret]
      rw [PqxdhInitialFinishOrigin.owner_map (nativeKernel target) mark pre
        (liftCalls (labelCalls source writer prior entry (childResponse prior entry target)))
        (liftCalls (nativeCalls source writer prior entry target)) receiveLaw application
        (knownInitial initial) initial initialLaw]
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

/-- The same origin and publication transcript survives the complete original adaptive post continuation under the actual retained-parent source interpretation. -/
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

/-- Recording the actual first Server response preserves its installed owner, returned kernel counter and origin under private chain interpretation. -/
theorem builder_trace (before : Trace Origin S B) (front : LabelFront M P I D K S B)
    (index : Fin S) (origin : Origin) (reply : RustM (Option PqxdhServerRegistrationPublication.Response)) :
    afterBuilder before (mapFront (nativeKernel target) front) index origin reply =
      afterBuilder before front index origin reply := by
  cases reply with
  | fail error => rfl
  | div => rfl
  | ok reply =>
    cases reply with
    | none => rfl
    | some response =>
      simp only [afterBuilder, mapFront, RawCtxGenericFamilyLive.mapState, mapRoles, mapServer]
      cases found : (front.roles.1.1 index).server.peers response.keyId <;> rfl

end Retained
end BeaconcryptCore.Computational.PqxdhInitialOriginPostMap

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginPostMap.step_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginPostMap.step_interpretation

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginPostMap.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginPostMap.step

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginPostMap.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginPostMap.program

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginPostMap.builder_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginPostMap.builder_trace
