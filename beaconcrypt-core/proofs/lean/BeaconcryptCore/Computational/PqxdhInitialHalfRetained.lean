import BeaconcryptCore.Computational.PqxdhInitialHalfNative
import BeaconcryptCore.Computational.RawCtxInitialSentinelBackend

/-!
The complete retained source interpreter for the first initial half is the exact original firstbuilder/post program. Its marker lies in the unused root domain, so it creates no source cache binding. The private child patch changes only ratchet requests; initializer replies and all external effects retain their original kernels and state.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialHalfRetained
open PqxdhJointKdfGame PqxdhJointKdf PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhInitialBeaconAmbient PqxdhInitialHalfProgram PqxdhInitialNativeParentRealization
open PqxdhInitialNativeParentContinuation (ambient)
open RawCtxSelectedParentTable RawCtxSelectedParentPrivatePatch
open PqxdhInitialNativeRetained (RetainedState)
variable {ι M P I D K X Response Shared Result Origin A N C : Type} {extra : OracleSpec ι} {S B : Nat}

noncomputable def nativeInitial (target : RootOutput)
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C PqxdhInitialHalfObserverCompiler.InitialReply)
    (secrets : PqxdhBeaconPhase2Shared.Secrets Shared) : Ambient A N C PqxdhInitialNativeAudit.InitialReply :=
  Prod.map id (Option.map (RawCtxSelectedParentCalls.nativeKernel target)) <$> initial secrets

/-- Literal domain inequality separates the private initial-half address from the analysis marker, without a random-input premise. -/
theorem separate (other target : RootOutput) (extra : NonceOutput) :
    targetAddress target ≠ (RawCtxInitialSentinel.entry other extra).address :=
  RawCtxInitialSentinel.private_ne (RawCtxFreshChainCut.concreteChain target)

section Interpreter
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (prior : Prior) (other target : RootOutput) (padding : NonceOutput)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C PqxdhInitialHalfObserverCompiler.InitialReply)
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))

/-- The complete retained source callback is exactly the native half interpreter, retaining every optional initializer reply and all ambient state. -/
theorem retained_handler :
    PqxdhInitialNativeRetained.retained (S := S) (B := B) source writer prior
      (PqxdhInitialNativeAudit.external pre application (nativeInitial target initial) selector aux) =
    (fun query => ambient (PqxdhInitialHalfSourceMap.nativeHandler source writer prior
      (RawCtxInitialSentinel.entry other padding) target pre application (fun secrets => Prod.snd <$> initial secrets) selector aux query)) := by
  funext query
  cases query with
  | inl query =>
      unfold PqxdhInitialNativeRetained.retained
      rw [← RawCtxInitialSentinelBackend.native_marker source writer prior other target padding]
      cases query with
      | inr input => rfl
      | inl pending =>
          funext state
          change (fun result => (result.1, (result.2, state.2))) <$>
            (RawCtxSelectedParentNativeCompiler.pending source writer prior (RawCtxInitialSentinel.entry other padding) target pending).run state.1 =
            ambient (lift (RawCtxSelectedParentNativeCompiler.pending source writer prior (RawCtxInitialSentinel.entry other padding) target pending)) state
          simp only [ambient, PqxdhInitialBeaconAmbient.lift, StateT.run, Functor.map_map]
  | inr query =>
      rcases query with query | (reply | (secrets | (query | query)))
      all_goals try rfl
      change ambient (Prod.snd <$> nativeInitial target initial secrets) =
        ambient (PqxdhInitialHalfSourceMap.nativeInitial target (fun secrets => Prod.snd <$> initial secrets) secrets)
      simp only [nativeInitial, PqxdhInitialHalfSourceMap.nativeInitial, Functor.map_map]
      rfl

/-- The full retained original source program preserves the identical effects after ambient reassociation and marker removal. -/
theorem retained_program
    (client : OracleComp (PqxdhInitialPendingPost.Spec extra RatchetChain I D K X Response Shared S B) Result) :
    simulateQ (PqxdhInitialNativeRetained.retained source writer prior
      (PqxdhInitialNativeAudit.external pre application (nativeInitial target initial) selector aux)) client =
    ambient (simulateQ (PqxdhInitialHalfSourceMap.nativeHandler source writer prior
      (RawCtxInitialSentinel.entry other padding) target pre application (fun secrets => Prod.snd <$> initial secrets) selector aux) client) := by
  rw [retained_handler source writer prior other target padding pre application initial selector aux,
    PqxdhInitialNativeParentContinuation.ambient_program]

/-- Installing one complete first child realizes the full original builder and post under the audited private-alias observer. -/
theorem sequence_compiled (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (execution : Execution extra M P I D K Result Origin S B) (output : FullOutput)
    (state : RetainedState A N C) :
    (simulateQ (PqxdhInitialNativeRetained.retained source writer (privatePatch prior target output)
      (PqxdhInitialNativeAudit.external pre application (nativeInitial target initial) selector aux))
      ((PqxdhInitialOriginPost.sequence source (RawCtxSelectedParentCalls.nativeKernel target <$> execution.first)
        mark execution.origin sender route decode execution.index execution.metadata execution.ready execution.post).run
        (PqxdhInitialParentPost.mapFront (RawCtxSelectedParentCalls.nativeKernel target) execution.before, execution.trace))).run state =
    (fun result => (Prod.map id (Prod.map (PqxdhInitialParentPost.mapFront (RawCtxSelectedParentCalls.nativeKernel target)) id) result.1,
      flat result.2)) <$>
      (simulateQ (PqxdhInitialHalfPrivateObserver.handler source writer prior (RawCtxInitialSentinel.entry other padding) output
        pre application initial selector aux (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target)
        (baseProgram source mark sender route decode execution)).run (nested state) := by
  rw [retained_program source writer (privatePatch prior target output) other target padding pre application initial selector aux,
    PqxdhInitialHalfBuilderMap.sequence source writer (privatePatch prior target output)
      (RawCtxInitialSentinel.entry other padding) target pre application (fun secrets => Prod.snd <$> initial secrets) selector aux
      execution.first mark execution.origin sender route decode execution.index execution.metadata execution.ready execution.post
      (execution.before, execution.trace),
    RawCtxSelectedParentPrivatePatch.child_response _ _ _ _ (separate other target padding),
    PqxdhInitialNativeParentRealization.ambient_map, PqxdhInitialNativeParentRealization.ambient_flatten]
  rw [baseProgram, PqxdhInitialHalfPrivateObserver.compiled_source source writer prior _ output pre application initial selector aux
    target _ (separate other target padding)]
  simp only [Functor.map_map]
  rfl

/-- The first-half checker returns precisely the source lineage under the same private patch; the root-domain marker contributes no input or output. -/
theorem checker_lineage (output : FullOutput) (depth : Nat) :
    (RawCtxFiniteLineageCheck.trace RawCtxFiniteLineageCheck.labelKey
      (RawCtxFiniteLineageCheck.routedStep prior (RawCtxInitialSentinel.entry other padding) target output) depth .hidden).map
        (RawCtxSelectedChain.interpret (RawCtxFreshChainCut.concreteChain target)) =
      RawCtxPublishedLineage.lineage (privatePatch prior target output) (RawCtxFreshChainCut.concreteChain target) depth := by
  rw [RawCtxFiniteLineageCheck.native_trace _ _ _ _ (separate other target padding)]
  unfold RawCtxPublishedLineage.lineage
  congr 1
  funext chain
  exact congrArg (fun value => RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse value))
    (RawCtxInitialSentinel.lookup_private (privatePatch prior target output) other target padding chain)

noncomputable def decision (prior : Prior) (target : RootOutput) (depth : Nat)
    (ancestors disclosed : List RatchetChain) (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (result : Bool × (PqxdhInitialPendingPost.Front RatchetChain M P I D K S B × PqxdhInitialOriginPost.Trace Bool S B)) : Bool :=
  @decide (PqxdhInitialPublishedEvent.Gate selected number result ∧
    RawCtxLiveLineage.Fresh (RawCtxPublishedLineage.lineage prior (RawCtxFreshChainCut.concreteChain target) depth ++ ancestors)
      disclosed result.2.1.roles.2) (Classical.propDecidable _)

/-- The retained full source observation is exactly the complete native observer's publication-gated byte freshness, including the actual original history. -/
theorem decision_compiled (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (execution : Execution extra M P I D K Bool Bool S B) (output : FullOutput) (depth : Nat)
    (state : RetainedState A N C) (candidates : List RootOutput)
    (ancestors disclosed : List RatchetChain) (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64) :
    (fun result => decision (privatePatch prior target output) target depth ancestors disclosed selected number result.1) <$>
      (simulateQ (PqxdhInitialNativeRetained.retained source writer (privatePatch prior target output)
        (PqxdhInitialNativeAudit.external pre application (nativeInitial target initial) selector aux))
        ((PqxdhInitialOriginPost.sequence source (RawCtxSelectedParentCalls.nativeKernel target <$> execution.first)
          mark execution.origin sender route decode execution.index execution.metadata execution.ready execution.post).run
          (PqxdhInitialParentPost.mapFront (RawCtxSelectedParentCalls.nativeKernel target) execution.before, execution.trace))).run state =
      PqxdhInitialHalfCheckedFreshness.actualDecision target ancestors disclosed
        (fun result => PqxdhInitialPublishedEvent.Gate selected number result.1.1) <$>
      PqxdhInitialHalfCheckedFreshness.nativeRun source writer prior (RawCtxInitialSentinel.entry other padding)
        pre application initial selector aux mark sender route decode execution depth target output disclosed (nested state) candidates := by
  rw [sequence_compiled source writer prior other target padding pre application initial selector aux mark sender route decode execution output state]
  have observed := PqxdhInitialHalfNative.observation source writer prior (RawCtxInitialSentinel.entry other padding)
    pre application initial selector aux mark sender route decode execution depth target output disclosed (nested state) candidates
    (fun result slots => @decide (PqxdhInitialPublishedEvent.Gate selected number result ∧
      RawCtxLiveLineage.Fresh (slots.map (RawCtxSelectedChain.interpret (RawCtxFreshChainCut.concreteChain target)) ++ ancestors)
        disclosed result.2.1.roles.2) (Classical.propDecidable _))
  rw [show (PqxdhInitialHalfCheckedFreshness.actualDecision target ancestors disclosed
      (fun result => PqxdhInitialPublishedEvent.Gate selected number result.1.1) <$>
      PqxdhInitialHalfCheckedFreshness.nativeRun source writer prior (RawCtxInitialSentinel.entry other padding)
        pre application initial selector aux mark sender route decode execution depth target output disclosed (nested state) candidates) = _ from observed]
  simp only [Functor.map_map, decision]
  rw [checker_lineage prior other target padding output depth]
  rfl

end Interpreter
end BeaconcryptCore.Computational.PqxdhInitialHalfRetained

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfRetained.separate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfRetained.separate

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfRetained.retained_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfRetained.retained_handler

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfRetained.retained_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfRetained.retained_program

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfRetained.sequence_compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfRetained.sequence_compiled

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfRetained.checker_lineage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfRetained.checker_lineage

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfRetained.decision_compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfRetained.decision_compiled
