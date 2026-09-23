import BeaconcryptCore.Computational.PqxdhInitialHalfCheckedFreshness
import BeaconcryptCore.Computational.PqxdhInitialNativeParentChecked
import BeaconcryptCore.Computational.RawCtxInitialSentinelBackend

/-!
The first-half native observer keeps the entire original firstbuilder/post result and actual final lineage. Only its private candidate and disclosure instrumentation is removed when evaluating an observation independent of those fields.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialHalfNative
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open PqxdhInitialHalfProgram PqxdhInitialBeaconAmbient
open PqxdhInitialParentStoppedHop (Trace SourceFinal Final)
open PqxdhInitialNativeParentChecked (trace_project)
variable {ι M P I D K X Response Shared Result Origin A N C : Type} {extra : OracleSpec ι} {S B : Nat}

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
    (application : Response → Ambient A N C (Option Pqxdh.Bytes))
    (initializer : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C PqxdhInitialHalfObserverCompiler.InitialReply)
    (selector : QueryImpl extra (Ambient A N C)) (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (execution : Execution extra M P I D K Result Origin S B) (depth : Nat)
    (target : RootOutput) (output : FullOutput)

/-- Each appended checker query uses only the original private ratchet callback and returns the exact partial-routing step. -/
theorem checker_step (reader : RawCtxSelectedLiveTrace.Reader) (input : RawCtxSelectedChain.Slot) :
    simulateQ (PqxdhInitialHalfPrivateObserver.handler source writer prior entry output
      pre application initializer
      selector aux reader target) (checkerCompiler input) =
      pure (RawCtxFiniteLineageCheck.routedStep prior entry target output input) := by
  apply (simulateQ_spec_query _ _).trans
  rw [PqxdhInitialHalfPrivateObserver.old_source]
  cases input <;> simp only [RawCtxSelectedParentPrivate.known_send, RawCtxSelectedParentPrivate.hidden_send,
    RawCtxFiniteLineageCheck.routedStep]
  all_goals rfl

/-- The actual partial observer evaluates its appended finite checker without changing any ambient field. -/
theorem checker_source (reader : RawCtxSelectedLiveTrace.Reader) (depth : Nat) :
    simulateQ (PqxdhInitialHalfPrivateObserver.handler source writer prior entry output pre application initializer selector aux reader target)
      (checker depth) =
      pure (RawCtxFiniteLineageCheck.trace RawCtxFiniteLineageCheck.labelKey
        (RawCtxFiniteLineageCheck.routedStep prior entry target output) depth .hidden) := by
  rw [checker, ← QueryImpl.simulateQ_compose]
  have step : PqxdhInitialHalfPrivateObserver.handler source writer prior entry output pre application initializer selector aux reader target ∘ₛ checkerCompiler =
      (fun input => pure (RawCtxFiniteLineageCheck.routedStep prior entry target output input)) :=
    funext (checker_step source writer prior entry pre application initializer selector aux target output reader)
  rw [step]
  exact RawCtxFiniteLineageCheck.evaluate RawCtxFiniteLineageCheck.labelKey
    (RawCtxFiniteLineageCheck.routedStep prior entry target output) depth .hidden

/-- The complete native freshness run retains the original stopped result and actual finite checker list after erasing only private candidate/flag instrumentation. -/
theorem native_projection (disclosed : List RatchetChain) (state : PqxdhInitialParentObserver.State A N C)
    (candidates : List RootOutput) :
    (fun result => (result.1, result.2.1.1)) <$>
      PqxdhInitialHalfCheckedFreshness.nativeRun source writer prior entry pre application initializer selector aux mark sender route decode execution depth target output
        disclosed state candidates =
    (fun result => ((result.1, RawCtxFiniteLineageCheck.trace RawCtxFiniteLineageCheck.labelKey
      (RawCtxFiniteLineageCheck.routedStep prior entry target output) depth .hidden), result.2)) <$>
      (simulateQ (PqxdhInitialHalfPrivateObserver.handler source writer prior entry output
        pre application initializer
        selector aux
        (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target)
        (baseProgram source mark sender route decode execution)).run state := by
  rw [PqxdhInitialHalfCheckedFreshness.nativeRun, PqxdhInitialHalfPrivateObserver.observed, trace_project]
  simp only [program, simulateQ_bind, simulateQ_map, checker_source, map_pure, bind_pure_comp,
    StateT.run_map, PqxdhInitialHalfProgram.initial]

/-- An observation of only the complete original result and checker list retains exactly the same distribution after removing the query instrumentation. -/
theorem observation (disclosed : List RatchetChain) (state : PqxdhInitialParentObserver.State A N C)
    (candidates : List RootOutput) (observe : SourceFinal M P I D K Result Origin S B → List RawCtxSelectedChain.Slot → Bool) :
    (fun result => observe result.1.1 result.1.2) <$>
      PqxdhInitialHalfCheckedFreshness.nativeRun source writer prior entry pre application initializer selector aux mark sender route decode execution depth target output
        disclosed state candidates =
    (fun result => observe result.1 (RawCtxFiniteLineageCheck.trace RawCtxFiniteLineageCheck.labelKey
      (RawCtxFiniteLineageCheck.routedStep prior entry target output) depth .hidden)) <$>
      (simulateQ (PqxdhInitialHalfPrivateObserver.handler source writer prior entry output
        pre application initializer
        selector aux
        (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target)
        (baseProgram source mark sender route decode execution)).run state := by
  have actual := congrArg
    (fun work : ProbComp (Final M P I D K Result Origin S B × PqxdhInitialParentObserver.State A N C) =>
      (fun result => observe result.1.1 result.1.2) <$> work)
    (native_projection source writer prior entry pre application initializer selector aux mark sender route decode execution depth target output disclosed state candidates)
  simpa only [Functor.map_map] using actual

end BeaconcryptCore.Computational.PqxdhInitialHalfNative

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfNative.checker_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfNative.checker_step

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfNative.checker_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfNative.checker_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfNative.native_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfNative.native_projection

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfNative.observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfNative.observation
